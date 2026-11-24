//! Needham–Schroeder–Lowe public-key authentication, with the games that
//! state its security.
//!
//! The protocol, between an initiator A and a responder B:
//!
//! ```text
//! A → B: {Na, A}pk(B)
//! B → A: {Na, Nb, B}pk(A)
//! A → B: {Nb}pk(B)
//! ```
//!
//! Needham–Schroeder is the same protocol without the check of B in the
//! second message, which Lowe added. [`step`] takes `lowe: bool` to choose,
//! so both protocols share one implementation.
//!
//! # The model
//!
//! Agent 0 is the adversary: its key pair is generated honestly and it gets
//! the secret key (static corruption). Every other agent is honest. The
//! adversary controls the network: an [`Action`] makes an honest agent
//! start a session or delivers a ciphertext, and it sees every
//! [`Response`]. Secrecy means the adversary cannot output the nonce of a
//! session whose peer is honest ([`secrecy_game`]).
//!
//! # Three worlds
//!
//! The protocol is written once against [`Env`] and run in three worlds.
//!
//! * **Real.** [`World`] over [`RealOracle`]: actual encryption.
//! * **Ideal.** [`World`] over [`IdealOracle`]: a ciphertext for an honest
//!   agent encrypts a fixed message, and decryption looks the plaintext up in
//!   a table. `World` is the context of the IND-CCA hop: it uses the oracle
//!   only through [`Oracle`], so the distance between the real and ideal
//!   games is the multi-user IND-CCA advantage of the adversary run inside
//!   `World`.
//! * **Symbolic.** [`Symbolic`]: the ideal world, except that the nonce of one
//!   session is the symbol [`Sym::Secret`] instead of a number. It records every
//!   value the secret was compared with, and whether the secret was ever
//!   encrypted to the adversary.
//!
//! The properties [`secrecy`] and [`faithful`] are deterministic and should hold
//! for every input; the fuzz tests sample inputs and the Lean side proves them
//! for all inputs. Together they say that in the ideal world the adversary's
//! view is computed without the secret, except when it hits one of the
//! recorded values. Probability enters only when the two are combined with the
//! IND-CCA hop.
//!
//! The code uses index loops and avoids iterator adapters, `?` and most std
//! helpers, which Aeneas cannot translate without hand-written models.

use core::marker::PhantomData;

// The protocol.

/// An agent's name.
pub type Agent = u8;

/// The adversary's name.
pub const ADVERSARY: Agent = 0;

/// A nonce.
pub type Nonce = u64;

/// The plaintexts of the protocol, with the nonce type left open so that the
/// symbolic world can use [`Sym`].
#[derive(Clone, Copy)]
pub enum Msg<N> {
    /// `{Na, A}`
    One(N, Agent),
    /// `{Na, Nb, B}`
    Two(N, N, Agent),
    /// `{Nb}`
    Three(N),
}

/// What the protocol needs from the world it runs in.
pub trait Env<Ct> {
    type Nonce: Copy;

    /// The nonce of session number `session`.
    fn nonce(&self, session: usize) -> Self::Nonce;
    /// Whether two nonces are equal.
    fn same(&mut self, a: Self::Nonce, b: Self::Nonce) -> bool;
    fn enc(&mut self, to: Agent, m: Msg<Self::Nonce>) -> Ct;
    fn dec(&self, by: Agent, c: Ct) -> Option<Msg<Self::Nonce>>;
}

/// An honest agent's session.
#[derive(Clone, Copy)]
pub struct Session<N> {
    pub owner: Agent,
    /// Who the owner believes it talks to.
    pub peer: Agent,
    /// The nonce this session generated.
    pub nonce: N,
    pub state: State,
}

/// How far a session has got.
#[derive(Clone, Copy)]
pub enum State {
    /// An initiator that sent message one and waits for message two.
    Initiating,
    /// A responder that sent message two and waits for message three.
    Responding,
    /// The session accepted its last message.
    Done,
}

/// What the adversary can make an honest agent do.
#[derive(Clone, Copy)]
pub enum Action<Ct> {
    /// Honest `owner` starts a session with `peer`, sending message one.
    Start { owner: Agent, peer: Agent },
    /// Honest `owner` receives `msg` as message one and starts a responder
    /// session.
    Respond { owner: Agent, msg: Ct },
    /// Session `session` receives `msg` as its next message.
    Deliver { session: usize, msg: Ct },
}

/// What the adversary sees after an action.
#[derive(Clone, Copy)]
pub enum Response<Ct> {
    Sent(Ct),
    Accepted,
    Rejected,
}

/// Runs one action. Sessions are numbered in creation order, and session `k`
/// gets nonce `env.nonce(k)`.
pub fn step<Ct, E: Env<Ct>>(
    lowe: bool,
    env: &mut E,
    sessions: &mut Vec<Session<E::Nonce>>,
    action: Action<Ct>,
) -> Response<Ct> {
    match action {
        Action::Start { owner, peer } => {
            if owner == ADVERSARY {
                return Response::Rejected;
            }
            let nonce = env.nonce(sessions.len());
            sessions.push(Session {
                owner,
                peer,
                nonce,
                state: State::Initiating,
            });
            Response::Sent(env.enc(peer, Msg::One(nonce, owner)))
        }
        Action::Respond { owner, msg } => {
            if owner == ADVERSARY {
                return Response::Rejected;
            }
            let Some(Msg::One(na, peer)) = env.dec(owner, msg) else {
                return Response::Rejected;
            };
            let nonce = env.nonce(sessions.len());
            sessions.push(Session {
                owner,
                peer,
                nonce,
                state: State::Responding,
            });
            Response::Sent(env.enc(peer, Msg::Two(na, nonce, owner)))
        }
        Action::Deliver { session, msg } => {
            if session >= sessions.len() {
                return Response::Rejected;
            }
            let Session {
                owner,
                peer,
                nonce,
                state,
            } = sessions[session];
            match state {
                State::Initiating => {
                    let Some(Msg::Two(na, nb, responder)) = env.dec(owner, msg) else {
                        return Response::Rejected;
                    };
                    // Lowe's fix: the responder must be the intended peer.
                    if !env.same(na, nonce) || (lowe && responder != peer) {
                        return Response::Rejected;
                    }
                    sessions[session].state = State::Done;
                    Response::Sent(env.enc(peer, Msg::Three(nb)))
                }
                State::Responding => {
                    let Some(Msg::Three(nb)) = env.dec(owner, msg) else {
                        return Response::Rejected;
                    };
                    if !env.same(nb, nonce) {
                        return Response::Rejected;
                    }
                    sessions[session].state = State::Done;
                    Response::Accepted
                }
                State::Done => Response::Rejected,
            }
        }
    }
}

/// Runs `actions` from no sessions, returning the sessions and every
/// response.
pub fn run<Ct: Copy, E: Env<Ct>>(
    lowe: bool,
    env: &mut E,
    actions: &[Action<Ct>],
) -> (Vec<Session<E::Nonce>>, Vec<Response<Ct>>) {
    let mut sessions = Vec::new();
    let mut seen = Vec::new();
    let mut i = 0;
    while i < actions.len() {
        seen.push(step(lowe, env, &mut sessions, actions[i]));
        i += 1;
    }
    (sessions, seen)
}

/// Whether session `k` exists and its peer is honest.
fn honest<N>(sessions: &[Session<N>], k: usize) -> bool {
    k < sessions.len() && sessions[k].peer != ADVERSARY
}

// Encryption.

/// Public-key encryption. It must encode every `Msg<Nonce>` to the same
/// length; otherwise the ideal world, which encrypts a fixed message, would
/// differ from the real one in ciphertext length.
///
/// The secrecy proofs assume nothing about it beyond totality; its security
/// enters only through the IND-CCA hop, as the distance between
/// [`RealOracle`] and [`IdealOracle`].
pub trait Pke {
    /// Key-generation randomness.
    type Seed;
    /// Encryption randomness.
    type Coins;
    type Pk;
    type Sk;
    type Ct: Copy + Eq;

    fn keygen(seed: &Self::Seed) -> (Self::Pk, Self::Sk);
    fn enc(pk: &Self::Pk, m: Msg<Nonce>, coins: &Self::Coins) -> Self::Ct;
    fn dec(sk: &Self::Sk, c: Self::Ct) -> Option<Msg<Nonce>>;
}

/// The randomness of one party of a game. Every use reads its own entry:
/// agent `a`'s key comes from `seed(a)`, the `i`-th encryption uses `coins(i)`,
/// and session `k`'s nonce is `nonce(k)`. So changing one nonce changes nothing
/// else.
pub trait Tape<Seed, Coins> {
    fn seed(&self, agent: Agent) -> &Seed;
    fn coins(&self, i: usize) -> &Coins;
    fn nonce(&self, session: usize) -> Nonce;
}

/// The interface of the multi-user IND-CCA game: public keys of, encryption
/// to, and decryption by the honest agents.
pub trait Oracle<Pk, Ct> {
    fn pk(&self, agent: Agent) -> Pk;
    fn enc(&mut self, to: Agent, m: Msg<Nonce>) -> Ct;
    fn dec(&self, by: Agent, c: Ct) -> Option<Msg<Nonce>>;
}

/// The real side of the IND-CCA game, with keys and coins from `tape`.
pub struct RealOracle<'a, P, T> {
    tape: &'a T,
    /// The number of encryptions so far.
    count: usize,
    pke: PhantomData<P>,
}

impl<'a, P: Pke, T: Tape<P::Seed, P::Coins>> RealOracle<'a, P, T> {
    pub fn new(tape: &'a T) -> Self {
        Self {
            tape,
            count: 0,
            pke: PhantomData,
        }
    }
}

impl<P: Pke, T: Tape<P::Seed, P::Coins>> Oracle<P::Pk, P::Ct> for RealOracle<'_, P, T> {
    fn pk(&self, agent: Agent) -> P::Pk {
        let (pk, _) = P::keygen(self.tape.seed(agent));
        pk
    }

    fn enc(&mut self, to: Agent, m: Msg<Nonce>) -> P::Ct {
        let c = P::enc(&self.pk(to), m, self.tape.coins(self.count));
        self.count += 1;
        c
    }

    fn dec(&self, by: Agent, c: P::Ct) -> Option<Msg<Nonce>> {
        let (_, sk) = P::keygen(self.tape.seed(by));
        P::dec(&sk, c)
    }
}

/// The message the ideal world encrypts in place of the real one.
const BLANK: Msg<Nonce> = Msg::Three(0);

/// A ciphertext an ideal world produced, and the plaintext it stands for.
struct Entry<C, N> {
    to: Agent,
    ct: C,
    msg: Msg<N>,
}

/// The plaintext of the first entry for `c` addressed to `by`.
fn lookup<C: Copy + Eq, N: Copy>(table: &[Entry<C, N>], by: Agent, c: C) -> Option<Msg<N>> {
    let mut i = 0;
    while i < table.len() {
        if table[i].to == by && table[i].ct == c {
            return Some(table[i].msg);
        }
        i += 1;
    }
    None
}

/// The ideal side of the IND-CCA game: encrypts [`BLANK`] instead of the
/// message and remembers the message, so that decrypting the ciphertext still
/// gives it back. Other ciphertexts are decrypted for real.
pub struct IdealOracle<'a, P: Pke, T> {
    real: RealOracle<'a, P, T>,
    table: Vec<Entry<P::Ct, Nonce>>,
}

impl<'a, P: Pke, T: Tape<P::Seed, P::Coins>> IdealOracle<'a, P, T> {
    pub fn new(tape: &'a T) -> Self {
        Self {
            real: RealOracle::new(tape),
            table: Vec::new(),
        }
    }
}

impl<P: Pke, T: Tape<P::Seed, P::Coins>> Oracle<P::Pk, P::Ct> for IdealOracle<'_, P, T> {
    fn pk(&self, agent: Agent) -> P::Pk {
        self.real.pk(agent)
    }

    fn enc(&mut self, to: Agent, m: Msg<Nonce>) -> P::Ct {
        let ct = self.real.enc(to, BLANK);
        self.table.push(Entry { to, ct, msg: m });
        ct
    }

    fn dec(&self, by: Agent, c: P::Ct) -> Option<Msg<Nonce>> {
        match lookup(&self.table, by, c) {
            Some(m) => Some(m),
            None => self.real.dec(by, c),
        }
    }
}

// The three worlds.

/// The world the adversary interacts with: nonces from `tape`, and
/// encryption to honest agents through `oracle`. It uses the oracle only
/// through [`Oracle`], which makes it the reduction of the IND-CCA hop.
pub struct World<'a, P, T, O> {
    tape: &'a T,
    /// Encrypts to the adversary, with its key and the coins from `tape`.
    adversary: RealOracle<'a, P, T>,
    oracle: O,
}

impl<'a, P: Pke, T: Tape<P::Seed, P::Coins>, O: Oracle<P::Pk, P::Ct>> World<'a, P, T, O> {
    pub fn new(tape: &'a T, oracle: O) -> Self {
        Self {
            tape,
            adversary: RealOracle::new(tape),
            oracle,
        }
    }
}

impl<P: Pke, T: Tape<P::Seed, P::Coins>, O: Oracle<P::Pk, P::Ct>> Env<P::Ct>
    for World<'_, P, T, O>
{
    type Nonce = Nonce;

    fn nonce(&self, session: usize) -> Nonce {
        self.tape.nonce(session)
    }

    fn same(&mut self, a: Nonce, b: Nonce) -> bool {
        a == b
    }

    fn enc(&mut self, to: Agent, m: Msg<Nonce>) -> P::Ct {
        if to == ADVERSARY {
            self.adversary.enc(to, m)
        } else {
            self.oracle.enc(to, m)
        }
    }

    fn dec(&self, by: Agent, c: P::Ct) -> Option<Msg<Nonce>> {
        self.oracle.dec(by, c)
    }
}

/// A nonce in the symbolic world.
#[derive(Clone, Copy)]
pub enum Sym {
    Val(Nonce),
    /// The nonce of the session under attack.
    Secret,
}

/// The message with every nonce a value, or `None` if it mentions the secret.
fn concretize(m: Msg<Sym>) -> Option<Msg<Nonce>> {
    match m {
        Msg::One(Sym::Val(a), x) => Some(Msg::One(a, x)),
        Msg::Two(Sym::Val(a), Sym::Val(b), x) => Some(Msg::Two(a, b, x)),
        Msg::Three(Sym::Val(a)) => Some(Msg::Three(a)),
        _ => None,
    }
}

fn symbolize(m: Msg<Nonce>) -> Msg<Sym> {
    match m {
        Msg::One(a, x) => Msg::One(Sym::Val(a), x),
        Msg::Two(a, b, x) => Msg::Two(Sym::Val(a), Sym::Val(b), x),
        Msg::Three(a) => Msg::Three(Sym::Val(a)),
    }
}

/// The ideal world with the nonce of session `secret` replaced by
/// [`Sym::Secret`]. It never looks at that nonce on the tape.
pub struct Symbolic<'a, P: Pke, T, U> {
    tape: &'a T,
    adversary: RealOracle<'a, P, T>,
    oracle: RealOracle<'a, P, U>,
    secret: usize,
    table: Vec<Entry<P::Ct, Sym>>,
    /// Every value the secret was compared with.
    guesses: Vec<Nonce>,
    /// Whether a message mentioning the secret was encrypted to the adversary.
    leaked: bool,
}

impl<'a, P: Pke, T: Tape<P::Seed, P::Coins>, U: Tape<P::Seed, P::Coins>> Symbolic<'a, P, T, U> {
    pub fn new(tape: &'a T, oracle_tape: &'a U, secret: usize) -> Self {
        Self {
            tape,
            adversary: RealOracle::new(tape),
            oracle: RealOracle::new(oracle_tape),
            secret,
            table: Vec::new(),
            guesses: Vec::new(),
            leaked: false,
        }
    }
}

impl<P: Pke, T: Tape<P::Seed, P::Coins>, U: Tape<P::Seed, P::Coins>> Env<P::Ct>
    for Symbolic<'_, P, T, U>
{
    type Nonce = Sym;

    fn nonce(&self, session: usize) -> Sym {
        if session == self.secret {
            Sym::Secret
        } else {
            Sym::Val(self.tape.nonce(session))
        }
    }

    fn same(&mut self, a: Sym, b: Sym) -> bool {
        match (a, b) {
            (Sym::Val(x), Sym::Val(y)) => x == y,
            (Sym::Secret, Sym::Secret) => true,
            (Sym::Val(x), Sym::Secret) | (Sym::Secret, Sym::Val(x)) => {
                self.guesses.push(x);
                false
            }
        }
    }

    fn enc(&mut self, to: Agent, m: Msg<Sym>) -> P::Ct {
        if to == ADVERSARY {
            let m = match concretize(m) {
                Some(m) => m,
                None => {
                    self.leaked = true;
                    BLANK
                }
            };
            self.adversary.enc(to, m)
        } else {
            let ct = self.oracle.enc(to, BLANK);
            self.table.push(Entry { to, ct, msg: m });
            ct
        }
    }

    // Aeneas has no model for `Option::map`.
    #[allow(clippy::manual_map)]
    fn dec(&self, by: Agent, c: P::Ct) -> Option<Msg<Sym>> {
        match lookup(&self.table, by, c) {
            Some(m) => Some(m),
            None => match self.oracle.dec(by, c) {
                Some(m) => Some(symbolize(m)),
                None => None,
            },
        }
    }
}

// Properties. Each function below should return `true` for every input and
// every `Pke` (with `lowe` for `secrecy`); the fuzz tests sample inputs and
// the Lean side proves it. They are specifications, not API.

/// Symbolic secrecy: with Lowe's fix, running any actions in the symbolic
/// world never encrypts a message mentioning the secret to the adversary,
/// if the session under attack has an honest peer. Without the fix this
/// fails (Lowe's attack).
pub fn secrecy<P: Pke, T: Tape<P::Seed, P::Coins>, U: Tape<P::Seed, P::Coins>>(
    lowe: bool,
    tape: &T,
    oracle_tape: &U,
    actions: &[Action<P::Ct>],
    secret: usize,
) -> bool {
    let mut symbolic = Symbolic::<P, T, U>::new(tape, oracle_tape, secret);
    let (sessions, _) = run(lowe, &mut symbolic, actions);
    !symbolic.leaked || !honest(&sessions, secret)
}

fn contains(values: &[Nonce], n: Nonce) -> bool {
    let mut i = 0;
    while i < values.len() {
        if values[i] == n {
            return true;
        }
        i += 1;
    }
    false
}

fn same_responses<C: Copy + Eq>(a: &[Response<C>], b: &[Response<C>]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        let same = match (a[i], b[i]) {
            (Response::Sent(x), Response::Sent(y)) => x == y,
            (Response::Accepted, Response::Accepted) => true,
            (Response::Rejected, Response::Rejected) => true,
            _ => false,
        };
        if !same {
            return false;
        }
        i += 1;
    }
    true
}

/// The symbolic world is faithful: on the same tapes, the ideal world gives
/// the adversary the same responses as the symbolic world, unless the
/// symbolic run leaked the secret or compared it with the nonce that the
/// tape gives session `secret`. This holds for both protocols.
pub fn faithful<P: Pke, T: Tape<P::Seed, P::Coins>, U: Tape<P::Seed, P::Coins>>(
    lowe: bool,
    tape: &T,
    oracle_tape: &U,
    actions: &[Action<P::Ct>],
    secret: usize,
) -> bool {
    let mut ideal = World::<P, T, _>::new(tape, IdealOracle::<P, U>::new(oracle_tape));
    let (_, seen) = run(lowe, &mut ideal, actions);
    let mut symbolic = Symbolic::<P, T, U>::new(tape, oracle_tape, secret);
    let (_, symbolic_seen) = run(lowe, &mut symbolic, actions);
    symbolic.leaked
        || contains(&symbolic.guesses, tape.nonce(secret))
        || same_responses(&seen, &symbolic_seen)
}

// The secrecy game.

/// An adversary: a state machine that sees only what the game gives it.
pub trait Adversary<Pk, Sk, Ct> {
    /// Receives every agent's public key, indexed by name, and the
    /// adversary's own secret key.
    fn start(&mut self, pks: Vec<Pk>, sk: Sk);
    fn next(&mut self, last: Response<Ct>) -> Action<Ct>;
    /// A session and a guess of its nonce.
    fn guess(&mut self, last: Response<Ct>) -> (usize, Nonce);
}

/// The secrecy game: `adversary` makes `queries` actions against honest agents
/// that encrypt through `oracle`, then wins if it names a session with an honest
/// peer and that session's nonce. With `RealOracle` this is the real game;
/// with `IdealOracle` it is the ideal one.
pub fn secrecy_game<P, T, O, A>(
    lowe: bool,
    tape: &T,
    oracle: O,
    adversary: &mut A,
    queries: usize,
) -> bool
where
    P: Pke,
    T: Tape<P::Seed, P::Coins>,
    O: Oracle<P::Pk, P::Ct>,
    A: Adversary<P::Pk, P::Sk, P::Ct>,
{
    let (pk, sk) = P::keygen(tape.seed(ADVERSARY));
    let mut pks = Vec::new();
    pks.push(pk);
    let mut agent: usize = 1;
    while agent < 256 {
        pks.push(oracle.pk(agent as Agent));
        agent += 1;
    }
    adversary.start(pks, sk);
    let mut world = World::<P, T, O>::new(tape, oracle);
    let mut sessions = Vec::new();
    let mut last = Response::Rejected;
    let mut i = 0;
    while i < queries {
        let action = adversary.next(last);
        last = step(lowe, &mut world, &mut sessions, action);
        i += 1;
    }
    let (k, guess) = adversary.guess(last);
    honest(&sessions, k) && sessions[k].nonce == guess
}

/// Lowe's attack on Needham–Schroeder. Honest A (agent 1) starts a session
/// with the adversary. The adversary re-encrypts A's first message to honest
/// B (agent 2), forwards B's reply to A, and A decrypts it and returns B's
/// nonce to the adversary. B believes it talked to A, so its session has an
/// honest peer. Three queries.
pub struct LoweAttack<P: Pke> {
    /// The randomness of the adversary's one encryption.
    coins: P::Coins,
    pks: Vec<P::Pk>,
    sk: Option<P::Sk>,
    next: Move,
}

/// The next query of [`LoweAttack`].
enum Move {
    /// Make A start a session with the adversary.
    Start,
    /// Re-encrypt A's message one to B.
    Relay,
    /// Forward B's reply to A's session.
    Forward,
    Done,
}

const A: Agent = 1;
const B: Agent = 2;

impl<P: Pke> LoweAttack<P> {
    pub fn new(coins: P::Coins) -> Self {
        Self {
            coins,
            pks: Vec::new(),
            sk: None,
            next: Move::Start,
        }
    }

    fn decrypt(&self, last: Response<P::Ct>) -> Option<Msg<Nonce>> {
        match (last, &self.sk) {
            (Response::Sent(c), Some(sk)) => P::dec(sk, c),
            _ => None,
        }
    }
}

impl<P: Pke> Adversary<P::Pk, P::Sk, P::Ct> for LoweAttack<P> {
    fn start(&mut self, pks: Vec<P::Pk>, sk: P::Sk) {
        self.pks = pks;
        self.sk = Some(sk);
    }

    fn next(&mut self, last: Response<P::Ct>) -> Action<P::Ct> {
        // A query that is always rejected, for when the run went wrong.
        let give_up = Action::Start {
            owner: ADVERSARY,
            peer: ADVERSARY,
        };
        match self.next {
            Move::Start => {
                self.next = Move::Relay;
                Action::Start {
                    owner: A,
                    peer: ADVERSARY,
                }
            }
            Move::Relay => {
                self.next = Move::Forward;
                match self.decrypt(last) {
                    Some(Msg::One(na, _)) => Action::Respond {
                        owner: B,
                        msg: P::enc(&self.pks[B as usize], Msg::One(na, A), &self.coins),
                    },
                    _ => give_up,
                }
            }
            Move::Forward => {
                self.next = Move::Done;
                match last {
                    // A's session is number 0.
                    Response::Sent(c) => Action::Deliver { session: 0, msg: c },
                    _ => give_up,
                }
            }
            Move::Done => give_up,
        }
    }

    fn guess(&mut self, last: Response<P::Ct>) -> (usize, Nonce) {
        // A's message three carries B's nonce; B's session is number 1.
        match self.decrypt(last) {
            Some(Msg::Three(nb)) => (1, nb),
            _ => (1, 0),
        }
    }
}
