//! A minimal binary Merkle tree, generic over the hash function.
//!
//! On a level with an odd number of nodes, the last node moves up unchanged
//! instead of being hashed with a copy of itself. The shape of a leaf's path
//! therefore depends on the number of leaves, so the root commits to it:
//! the published root is `H::size(inner_root, size)`. The verifier takes the
//! size as an argument. Two openings accepted for the same root with
//! different claimed sizes exhibit a collision in the size commitment.
//!
//! The code uses index loops and avoids iterator adapters and most std helpers,
//! which Aeneas cannot translate without hand-written models.

/// A hash function for Merkle trees. Leaves, inner nodes and the final size
/// commitment use separate operations. The verification contract below
/// states the assumptions on these operations and on digest equality.
pub trait Hash {
    type Digest: Copy + Eq;

    fn leaf(data: &[u8]) -> Self::Digest;
    fn node(left: &Self::Digest, right: &Self::Digest) -> Self::Digest;
    fn size(digest: &Self::Digest, size: usize) -> Self::Digest;
}

/// All three hash operations must return a digest on every input. Both
/// digest comparisons must return and agree with logical equality.
#[cfg(hax)]
fn lawful_hash<H: Hash>() -> hax_lib::Prop {
    use hax_lib::prop::constructors::{and, eq as logical_eq, exists, forall, from_bool, not};

    let leaf = forall(|s: &[u8]| exists(|d: H::Digest| logical_eq(H::leaf(s), d)));
    let node = forall(|(a, b): (H::Digest, H::Digest)| {
        exists(|d: H::Digest| logical_eq(H::node(&a, &b), d))
    });
    let size =
        forall(|(a, n): (H::Digest, usize)| exists(|d: H::Digest| logical_eq(H::size(&a, n), d)));
    let equal =
        forall(|(a, b): (H::Digest, H::Digest)| logical_eq(from_bool(a == b), logical_eq(a, b)));
    let unequal = forall(|(a, b): (H::Digest, H::Digest)| {
        logical_eq(from_bool(a != b), not(logical_eq(a, b)))
    });

    and(and(leaf, node), and(size, and(equal, unequal)))
}

/// A Merkle tree that stores every level, leaves first.
pub struct Tree<H: Hash> {
    levels: Vec<Vec<H::Digest>>,
}

impl<H: Hash> Tree<H> {
    pub fn new(data: &[Vec<u8>]) -> Self {
        let mut level = Vec::new();
        let mut i = 0;
        while i < data.len() {
            level.push(H::leaf(&data[i]));
            i += 1;
        }
        let mut levels = Vec::new();
        while level.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < level.len() {
                next.push(H::node(&level[i], &level[i + 1]));
                i += 2;
            }
            if i < level.len() {
                next.push(level[i]);
            }
            levels.push(level);
            level = next;
        }
        levels.push(level);
        Self { levels }
    }

    /// The number of leaves.
    pub fn size(&self) -> usize {
        self.levels[0].len()
    }

    /// The root, committing to the leaves and their number, or `None` for an
    /// empty tree.
    pub fn root(&self) -> Option<H::Digest> {
        let top = &self.levels[self.levels.len() - 1];
        if top.is_empty() {
            None
        } else {
            Some(H::size(&top[0], self.size()))
        }
    }

    /// The proof for the leaf at `index`: the sibling digests on its path to
    /// the inner root, leaf first. Levels where the node has no sibling are
    /// skipped.
    pub fn proof(&self, index: usize) -> Option<Vec<H::Digest>> {
        if index >= self.size() {
            return None;
        }
        let mut proof = Vec::new();
        let mut index = index;
        let mut k = 0;
        while k + 1 < self.levels.len() {
            let level = &self.levels[k];
            if index % 2 == 1 {
                proof.push(level[index - 1]);
            } else if index + 1 < level.len() {
                proof.push(level[index + 1]);
            }
            index /= 2;
            k += 1;
        }
        Some(proof)
    }
}

/// Whether the node at `index` on a level of `width` nodes has a sibling.
fn has_sibling(index: usize, width: usize) -> bool {
    index % 2 == 1 || index + 1 < width
}

/// Hashes `acc`, the node at `index`, with its sibling.
fn step<H: Hash>(index: usize, acc: &H::Digest, sibling: &H::Digest) -> H::Digest {
    if index % 2 == 1 {
        H::node(sibling, acc)
    } else {
        H::node(acc, sibling)
    }
}

/// The number of nodes on the level above a level of `width` nodes.
fn parent_width(width: usize) -> usize {
    width / 2 + width % 2
}

/// The inner root (before the size commitment) that `proof` gives for
/// `data` at `index` of `size` leaves, or `None` if the proof has the wrong
/// shape.
fn inner_root<H: Hash>(
    size: usize,
    index: usize,
    data: &[u8],
    proof: &[H::Digest],
) -> Option<H::Digest> {
    if index >= size {
        return None;
    }
    let mut acc = H::leaf(data);
    let mut index = index;
    let mut width = size;
    let mut i = 0;
    while width > 1 {
        if has_sibling(index, width) {
            if i >= proof.len() {
                return None;
            }
            acc = step::<H>(index, &acc, &proof[i]);
            i += 1;
        }
        index /= 2;
        width = parent_width(width);
    }
    if i == proof.len() { Some(acc) } else { None }
}

/// Checks that `data` is the leaf at `index` in the tree with `root` and
/// `size` leaves.
pub fn verify<H: Hash>(
    root: &H::Digest,
    size: usize,
    index: usize,
    data: &[u8],
    proof: &[H::Digest],
) -> bool {
    match inner_root::<H>(size, index, data, proof) {
        None => false,
        Some(inner) => H::size(&inner, size) == *root,
    }
}

/// Byte-slice equality as a loop, since Aeneas has no model for slice `==`.
fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

// Lean proves that these properties return true for every input when the
// hash satisfies lawful_hash.

/// Completeness: the honest proof for every leaf verifies.
#[cfg_attr(hax, hax_lib::requires(lawful_hash::<H>()))]
#[cfg_attr(hax, hax_lib::ensures(|result| result))]
pub fn completeness<H: Hash>(data: &[Vec<u8>], index: usize) -> bool {
    if index >= data.len() {
        return true;
    }
    let tree = Tree::<H>::new(data);
    match tree.root() {
        None => false,
        Some(root) => match tree.proof(index) {
            None => false,
            Some(proof) => verify::<H>(&root, data.len(), index, &data[index], &proof),
        },
    }
}

/// Two different inputs that `H` maps to the same digest.
pub enum Collision<'a, D> {
    /// `leaf(a) == leaf(b)` with `a != b`.
    Leaf(&'a [u8], &'a [u8]),
    /// `node(a, b) == node(c, d)` with `(a, b) != (c, d)`.
    Node(D, D, D, D),
    /// `size(a, n) == size(b, m)` with `(a, n) != (b, m)`.
    Size(D, usize, D, usize),
}

/// Checks that `c` really is a collision in `H`.
pub fn is_collision<H: Hash>(c: Collision<'_, H::Digest>) -> bool {
    match c {
        Collision::Leaf(a, b) => !bytes_eq(a, b) && H::leaf(a) == H::leaf(b),
        Collision::Node(a, b, c, d) => (a != c || b != d) && H::node(&a, &b) == H::node(&c, &d),
        Collision::Size(a, n, b, m) => (a != b || n != m) && H::size(&a, n) == H::size(&b, m),
    }
}

/// Given two proofs for different data at the same index, with possibly
/// different claimed sizes, finds where their computations of the root first
/// agree on different inputs.
pub fn extract<'a, H: Hash>(
    index: usize,
    n1: usize,
    d1: &'a [u8],
    p1: &[H::Digest],
    n2: usize,
    d2: &'a [u8],
    p2: &[H::Digest],
) -> Option<Collision<'a, H::Digest>> {
    // Different sizes: the size commitments collide.
    if n1 != n2 {
        return match (
            inner_root::<H>(n1, index, d1, p1),
            inner_root::<H>(n2, index, d2, p2),
        ) {
            (Some(r1), Some(r2)) => Some(Collision::Size(r1, n1, r2, n2)),
            _ => None,
        };
    }
    // Same size: both paths have the same shape, so walk them together.
    let mut a = H::leaf(d1);
    let mut b = H::leaf(d2);
    if !bytes_eq(d1, d2) && a == b {
        return Some(Collision::Leaf(d1, d2));
    }
    let mut index = index;
    let mut width = n1;
    let mut i = 0;
    while width > 1 {
        if has_sibling(index, width) {
            if i >= p1.len() || i >= p2.len() {
                return None;
            }
            let next_a = step::<H>(index, &a, &p1[i]);
            let next_b = step::<H>(index, &b, &p2[i]);
            if (a != b || p1[i] != p2[i]) && next_a == next_b {
                return Some(if index % 2 == 1 {
                    Collision::Node(p1[i], a, p2[i], b)
                } else {
                    Collision::Node(a, p1[i], b, p2[i])
                });
            }
            a = next_a;
            b = next_b;
            i += 1;
        }
        index /= 2;
        width = parent_width(width);
    }
    // Different inner roots under the same size commitment.
    if a != b {
        Some(Collision::Size(a, n1, b, n2))
    } else {
        None
    }
}

/// Binding: two accepting proofs for different data at the same index of the
/// tree with `root` yield a collision in `H`, even if the verifier is given
/// a different size for each.
#[allow(clippy::too_many_arguments)]
#[cfg_attr(hax, hax_lib::requires(lawful_hash::<H>()))]
#[cfg_attr(hax, hax_lib::ensures(|result| result))]
pub fn binding<H: Hash>(
    root: &H::Digest,
    index: usize,
    n1: usize,
    d1: &[u8],
    p1: &[H::Digest],
    n2: usize,
    d2: &[u8],
    p2: &[H::Digest],
) -> bool {
    if bytes_eq(d1, d2)
        || !verify::<H>(root, n1, index, d1, p1)
        || !verify::<H>(root, n2, index, d2, p2)
    {
        return true;
    }
    match extract::<H>(index, n1, d1, p1, n2, d2, p2) {
        None => false,
        Some(c) => is_collision::<H>(c),
    }
}
