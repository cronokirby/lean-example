//! A minimal binary Merkle tree, generic over the hash function.
//!
//! On a level with an odd number of nodes, the last node moves up unchanged
//! instead of being hashed with a copy of itself.

/// A hash function for Merkle trees. Leaves and inner nodes use separate
/// functions so that a leaf digest cannot be mistaken for a node digest.
pub trait Hash {
    type Digest: Copy + Eq;

    fn leaf(data: &[u8]) -> Self::Digest;
    fn node(left: &Self::Digest, right: &Self::Digest) -> Self::Digest;
}

/// One step of an inclusion proof: the sibling digest and its side.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sibling<D> {
    Left(D),
    Right(D),
}

/// A Merkle tree that stores every level, leaves first.
pub struct Tree<H: Hash> {
    levels: Vec<Vec<H::Digest>>,
}

impl<H: Hash> Tree<H> {
    pub fn new(data: &[Vec<u8>]) -> Self {
        // Index loops instead of iterator adapters, which Aeneas cannot translate.
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

    /// The root digest, or `None` for an empty tree.
    pub fn root(&self) -> Option<H::Digest> {
        let top = &self.levels[self.levels.len() - 1];
        if top.is_empty() { None } else { Some(top[0]) }
    }

    /// The inclusion proof for the leaf at `index`, ordered from leaf to root.
    pub fn proof(&self, mut index: usize) -> Option<Vec<Sibling<H::Digest>>> {
        if index >= self.levels[0].len() {
            return None;
        }
        let mut proof = Vec::new();
        for level in &self.levels[..self.levels.len() - 1] {
            // A promoted last node has no sibling on this level.
            if let Some(d) = level.get(index ^ 1) {
                proof.push(if index & 1 == 0 {
                    Sibling::Right(*d)
                } else {
                    Sibling::Left(*d)
                });
            }
            index /= 2;
        }
        Some(proof)
    }
}

/// Checks that `data` is a leaf of the tree with `root`.
pub fn verify<H: Hash>(root: &H::Digest, data: &[u8], proof: &[Sibling<H::Digest>]) -> bool {
    let mut acc = H::leaf(data);
    for step in proof {
        acc = match step {
            Sibling::Left(l) => H::node(l, &acc),
            Sibling::Right(r) => H::node(&acc, r),
        };
    }
    acc == *root
}
