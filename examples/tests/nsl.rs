//! Fuzz tests for the NSL properties. The adversary is a list of steps
//! whose messages are recipes over what it has seen, so that random lists
//! can forward and re-encrypt ciphertexts; each list is turned into the raw
//! actions that the property functions quantify over.

use examples::nsl::{
    self, ADVERSARY, Action, Adversary, Agent, LoweAttack, Msg, Nonce, Pke, RealOracle, Response,
    Symbolic, Tape,
};
use proptest::prelude::*;
use proptest::test_runner::{Config, RngAlgorithm, TestCaseError, TestRng, TestRunner};

/// Insecure public-key encryption whose ciphertexts carry the plaintext.
/// The properties are about the ideal world, which never puts an honest
/// plaintext in a ciphertext, so this is enough to test them; it also lets
/// the adversary read anything addressed to agent 0.
struct Toy;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Ct {
    to: Agent,
    tag: u8,
    a: Nonce,
    b: Nonce,
    x: Agent,
    coins: u64,
}

impl Pke for Toy {
    type Seed = Agent;
    type Coins = u64;
    type Pk = Agent;
    type Sk = Agent;
    type Ct = Ct;

    fn keygen(seed: &Agent) -> (Agent, Agent) {
        (*seed, *seed)
    }

    fn enc(pk: &Agent, m: Msg<Nonce>, coins: &u64) -> Ct {
        let (tag, a, b, x) = match m {
            Msg::One(a, x) => (1, a, 0, x),
            Msg::Two(a, b, x) => (2, a, b, x),
            Msg::Three(a) => (3, a, 0, 0),
        };
        Ct {
            to: *pk,
            tag,
            a,
            b,
            x,
            coins: *coins,
        }
    }

    fn dec(sk: &Agent, c: Ct) -> Option<Msg<Nonce>> {
        if c.to != *sk {
            return None;
        }
        match c.tag {
            1 => Some(Msg::One(c.a, c.x)),
            2 => Some(Msg::Two(c.a, c.b, c.x)),
            3 => Some(Msg::Three(c.a)),
            _ => None,
        }
    }
}

struct TestTape {
    seeds: Vec<Agent>,
    coins: Vec<u64>,
    nonces: Vec<Nonce>,
}

impl TestTape {
    /// Coins are offset by `salt` so that two tapes never produce the same
    /// ciphertext; nonces are 100, 101, ...
    fn new(salt: u64) -> Self {
        Self {
            seeds: (0..=255).collect(),
            coins: (0..256).map(|i| salt + i).collect(),
            nonces: (0..256).map(|k| 100 + k).collect(),
        }
    }
}

impl Tape<Agent, u64> for TestTape {
    fn seed(&self, agent: Agent) -> &Agent {
        &self.seeds[agent as usize]
    }

    fn coins(&self, i: usize) -> &u64 {
        &self.coins[i]
    }

    fn nonce(&self, session: usize) -> Nonce {
        self.nonces[session]
    }
}

const AGENTS: Agent = 3;

#[derive(Clone, Debug)]
enum NonceRef {
    Const(Nonce),
    /// The i-th nonce the adversary decrypted (wrapping).
    Learned(usize),
}

#[derive(Clone, Debug)]
enum Recipe {
    /// The i-th ciphertext the adversary saw (wrapping).
    Forward(usize),
    /// The i-th ciphertext, decrypted with the adversary's key and encrypted to `to`.
    Reencrypt { from: usize, to: Agent },
    /// A message of the adversary's choosing, encrypted to `to`.
    Forge {
        to: Agent,
        tag: u8,
        a: NonceRef,
        b: NonceRef,
        x: Agent,
    },
}

#[derive(Clone, Debug)]
enum Step {
    Start { owner: Agent, peer: Agent },
    Respond { owner: Agent, msg: Recipe },
    Deliver { session: usize, msg: Recipe },
}

fn agent() -> impl Strategy<Value = Agent> {
    0..AGENTS
}

fn nonce_ref() -> impl Strategy<Value = NonceRef> {
    prop_oneof![
        (99..104u64).prop_map(NonceRef::Const),
        (0..4usize).prop_map(NonceRef::Learned),
    ]
}

fn recipe() -> impl Strategy<Value = Recipe> {
    prop_oneof![
        (0..6usize).prop_map(Recipe::Forward),
        (0..6usize, agent()).prop_map(|(from, to)| Recipe::Reencrypt { from, to }),
        (agent(), 1..4u8, nonce_ref(), nonce_ref(), agent())
            .prop_map(|(to, tag, a, b, x)| Recipe::Forge { to, tag, a, b, x }),
    ]
}

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        (agent(), agent()).prop_map(|(owner, peer)| Step::Start { owner, peer }),
        (agent(), recipe()).prop_map(|(owner, msg)| Step::Respond { owner, msg }),
        (0..4usize, recipe()).prop_map(|(session, msg)| Step::Deliver { session, msg }),
    ]
}

fn steps() -> impl Strategy<Value = Vec<Step>> {
    prop::collection::vec(step(), 1..7)
}

/// What the adversary knows: every ciphertext it saw, and every nonce in a
/// ciphertext addressed to it.
#[derive(Default)]
struct Knowledge {
    seen: Vec<Ct>,
    learned: Vec<Nonce>,
}

impl Knowledge {
    fn observe(&mut self, r: Response<Ct>) {
        if let Response::Sent(c) = r {
            self.seen.push(c);
            match Toy::dec(&ADVERSARY, c) {
                Some(Msg::One(a, _)) | Some(Msg::Three(a)) => self.learned.push(a),
                Some(Msg::Two(a, b, _)) => self.learned.extend([a, b]),
                None => {}
            }
        }
    }

    fn nonce(&self, r: &NonceRef) -> Nonce {
        match *r {
            NonceRef::Const(v) => v,
            NonceRef::Learned(i) if !self.learned.is_empty() => {
                self.learned[i % self.learned.len()]
            }
            NonceRef::Learned(_) => 0,
        }
    }

    /// The ciphertext a recipe describes. Recipes that need a ciphertext the
    /// adversary has not seen, or cannot decrypt, fall back to a forgery.
    fn build(&self, r: &Recipe, coins: u64) -> Ct {
        let pick = |i: usize| self.seen.get(i % self.seen.len().max(1)).copied();
        match r {
            Recipe::Forward(i) => pick(*i).unwrap_or(Toy::enc(&1, Msg::Three(0), &coins)),
            Recipe::Reencrypt { from, to } => {
                match pick(*from).and_then(|c| Toy::dec(&ADVERSARY, c)) {
                    Some(m) => Toy::enc(to, m, &coins),
                    None => Toy::enc(to, Msg::Three(0), &coins),
                }
            }
            Recipe::Forge { to, tag, a, b, x } => {
                let (a, b) = (self.nonce(a), self.nonce(b));
                let m = match tag {
                    1 => Msg::One(a, *x),
                    2 => Msg::Two(a, b, *x),
                    _ => Msg::Three(a),
                };
                Toy::enc(to, m, &coins)
            }
        }
    }
}

/// Coins for the adversary's own encryptions, disjoint from both tapes.
const ADVERSARY_SALT: u64 = 1 << 40;

/// Runs `steps` in the symbolic world, building each message from what the
/// adversary has seen so far, and returns the resulting raw actions.
fn actions(
    lowe: bool,
    steps: &[Step],
    tape: &TestTape,
    oracle_tape: &TestTape,
    secret: usize,
) -> Vec<Action<Ct>> {
    let mut env = Symbolic::<Toy, TestTape, TestTape>::new(tape, oracle_tape, secret);
    let mut sessions = Vec::new();
    let mut known = Knowledge::default();
    let mut out = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        let coins = ADVERSARY_SALT + i as u64;
        let action = match s {
            Step::Start { owner, peer } => Action::Start {
                owner: *owner,
                peer: *peer,
            },
            Step::Respond { owner, msg } => Action::Respond {
                owner: *owner,
                msg: known.build(msg, coins),
            },
            Step::Deliver { session, msg } => Action::Deliver {
                session: *session,
                msg: known.build(msg, coins),
            },
        };
        known.observe(nsl::step(lowe, &mut env, &mut sessions, action));
        out.push(action);
    }
    out
}

fn tapes() -> (TestTape, TestTape) {
    (TestTape::new(0), TestTape::new(1 << 20))
}

fn config(cases: u32) -> Config {
    Config {
        cases,
        failure_persistence: None,
        ..Config::default()
    }
}

/// Checks `secrecy` for every session index.
fn check_secrecy(lowe: bool, steps: &[Step]) -> Result<(), TestCaseError> {
    let (tape, oracle_tape) = tapes();
    for secret in 0..steps.len() {
        let actions = actions(lowe, steps, &tape, &oracle_tape, secret);
        prop_assert!(
            nsl::secrecy::<Toy, _, _>(lowe, &tape, &oracle_tape, &actions, secret),
            "session {secret} leaks"
        );
    }
    Ok(())
}

#[test]
fn nsl_keeps_the_secret_symbolic() {
    let mut runner = TestRunner::new(config(20_000));
    runner
        .run(&steps(), |steps| check_secrecy(true, &steps))
        .unwrap();
}

/// The fuzzer rediscovers Lowe's attack on the original protocol.
#[test]
fn fuzzer_finds_lowe_attack_on_ns() {
    let rng = TestRng::deterministic_rng(RngAlgorithm::ChaCha);
    let mut runner = TestRunner::new_with_rng(config(200_000), rng);
    let result = runner.run(&steps(), |steps| check_secrecy(false, &steps));
    let Err(failure) = result else {
        panic!("no attack found on Needham–Schroeder");
    };
    println!("{failure}");
}

#[test]
fn symbolic_world_is_faithful() {
    // The nonce of the session under attack is drawn close to the constants
    // the adversary forges with, so that the adversary often guesses it.
    let strategy = (
        any::<bool>(),
        steps(),
        0..6usize,
        prop_oneof![3 => 99..104u64, 1 => any::<u64>()],
    );
    let mut runner = TestRunner::new(config(100_000));
    runner
        .run(&strategy, |(lowe, steps, secret, n)| {
            let (mut tape, oracle_tape) = tapes();
            tape.nonces[secret] = n;
            let actions = actions(lowe, &steps, &tape, &oracle_tape, secret);
            prop_assert!(nsl::faithful::<Toy, _, _>(
                lowe,
                &tape,
                &oracle_tape,
                &actions,
                secret
            ));
            Ok(())
        })
        .unwrap();
}

fn lowe_attack_wins(lowe: bool) -> bool {
    let (tape, oracle_tape) = tapes();
    let mut adversary = LoweAttack::<Toy>::new(ADVERSARY_SALT);
    nsl::secrecy_game::<Toy, _, _, _>(
        lowe,
        &tape,
        RealOracle::<Toy, _>::new(&oracle_tape),
        &mut adversary,
        3,
    )
}

#[test]
fn lowe_attack_breaks_ns_in_the_real_game() {
    assert!(lowe_attack_wins(false));
}

#[test]
fn lowe_attack_fails_against_nsl() {
    assert!(!lowe_attack_wins(true));
}

/// Relays the honest run between agents 1 and 2.
struct Relay {
    round: u8,
}

impl Adversary<Agent, Agent, Ct> for Relay {
    fn start(&mut self, _: Vec<Agent>, _: Agent) {}

    fn next(&mut self, last: Response<Ct>) -> Action<Ct> {
        self.round += 1;
        match (self.round, last) {
            (1, _) => Action::Start { owner: 1, peer: 2 },
            (2, Response::Sent(c)) => Action::Respond { owner: 2, msg: c },
            (3, Response::Sent(c)) => Action::Deliver { session: 0, msg: c },
            (4, Response::Sent(c)) => Action::Deliver { session: 1, msg: c },
            _ => panic!("honest run failed"),
        }
    }

    fn guess(&mut self, last: Response<Ct>) -> (usize, Nonce) {
        assert!(
            matches!(last, Response::Accepted),
            "responder did not accept"
        );
        (0, 0)
    }
}

#[test]
fn honest_run_completes() {
    let (tape, oracle_tape) = tapes();
    let mut relay = Relay { round: 0 };
    nsl::secrecy_game::<Toy, _, _, _>(
        true,
        &tape,
        RealOracle::<Toy, _>::new(&oracle_tape),
        &mut relay,
        4,
    );
}
