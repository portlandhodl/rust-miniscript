// SPDX-License-Identifier: CC0-1.0

//! Abstract Policies
//!
//! We use the terms "semantic" and "abstract" interchangeably because
//! "abstract" is a reserved keyword in Rust.

use core::{cmp, fmt, str};

use bitcoin::{absolute, relative};

use super::ENTAILMENT_MAX_TERMINALS;
use crate::iter::{StackExt as _, Tree, TreeLike};
use crate::prelude::*;
use crate::sync::Arc;
use crate::{
    expression, AbsLockTime, Error, ForEachKey, FromStrKey, MiniscriptKey, ParseError, RelLockTime,
    Threshold, Translator,
};

/// Abstract policy which corresponds to the semantics of a miniscript and
/// which allows complex forms of analysis, e.g. filtering and normalization.
///
/// Semantic policies store only hashes of keys to ensure that objects
/// representing the same policy are lifted to the same abstract `Policy`,
/// regardless of their choice of `pk` or `pk_h` nodes.
#[derive(Clone, PartialEq, Eq)]
pub enum Policy<Pk: MiniscriptKey> {
    /// Unsatisfiable.
    Unsatisfiable,
    /// Trivially satisfiable.
    Trivial,
    /// Signature and public key matching a given hash is required.
    Key(Pk),
    /// An absolute locktime restriction.
    After(AbsLockTime),
    /// A relative locktime restriction.
    Older(RelLockTime),
    /// A SHA256 whose preimage must be provided to satisfy the descriptor.
    Sha256(Pk::Sha256),
    /// A SHA256d whose preimage must be provided to satisfy the descriptor.
    Hash256(Pk::Hash256),
    /// A RIPEMD160 whose preimage must be provided to satisfy the descriptor.
    Ripemd160(Pk::Ripemd160),
    /// A HASH160 whose preimage must be provided to satisfy the descriptor.
    Hash160(Pk::Hash160),
    /// A set of descriptors, satisfactions must be provided for `k` of them.
    Thresh(Threshold<Arc<Self>, 0>),
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    fn variant_name(&self) -> &'static str {
        match *self {
            Self::Unsatisfiable => "unsatisfiable",
            Self::Trivial => "trivial",
            Self::Key(_) => "key",
            Self::After(_) => "after",
            Self::Older(_) => "older",
            Self::Sha256(_) => "sha256",
            Self::Hash256(_) => "hash256",
            Self::Ripemd160(_) => "ripemd160",
            Self::Hash160(_) => "hash160",
            Self::Thresh(_) => "thresh",
        }
    }
}

impl<Pk: MiniscriptKey> PartialOrd for Policy<Pk> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl<Pk: MiniscriptKey> Ord for Policy<Pk> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match self.variant_name().cmp(other.variant_name()) {
            cmp::Ordering::Equal => {}
            ord => return ord,
        }
        match (self, other) {
            (Self::Unsatisfiable, Self::Unsatisfiable) => cmp::Ordering::Equal,
            (Self::Trivial, Self::Trivial) => cmp::Ordering::Equal,
            (Self::Key(a), Self::Key(b)) => a.cmp(b),
            (Self::After(a), Self::After(b)) => a.cmp_by_consensus(*b),
            (Self::Older(a), Self::Older(b)) => a.cmp_by_consensus(*b),
            (Self::Sha256(a), Self::Sha256(b)) => a.cmp(b),
            (Self::Hash256(a), Self::Hash256(b)) => a.cmp(b),
            (Self::Ripemd160(a), Self::Ripemd160(b)) => a.cmp(b),
            (Self::Hash160(a), Self::Hash160(b)) => a.cmp(b),
            (Self::Thresh(a), Self::Thresh(b)) => a.cmp(b),
            _ => unreachable!("variant_name ensures same variant"),
        }
    }
}

/// Represents the difference between two policies.
///
/// This is useful when trying to find the conditions under which two
/// policies differ. See [`PolicyDiff::new`] for the exact semantics.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PolicyDiff<Pk: MiniscriptKey> {
    /// Sub-policies of the first policy which have no exact match in the
    /// second policy.
    pub a: Vec<Policy<Pk>>,
    /// Sub-policies of the second policy which have no exact match in the
    /// first policy.
    pub b: Vec<Policy<Pk>>,
}

impl<Pk: MiniscriptKey> PolicyDiff<Pk> {
    /// Computes the difference between two policies.
    ///
    /// Both policies are first [normalized](Policy::normalized). If the
    /// normalized policies are equal, the difference is empty. Otherwise,
    /// if both policies are thresholds with equal `k` and `n`, children
    /// that compare equal are matched up (independently of their position)
    /// and the difference consists of the unmatched children of each policy.
    /// In all other cases the difference consists of the two policies
    /// themselves.
    ///
    /// Note that this is a purely syntactic comparison: it does not attempt
    /// to reason about the semantic equivalence of the differing
    /// sub-policies.
    pub fn new(a: Policy<Pk>, b: Policy<Pk>) -> Self {
        fn diff<Pk: MiniscriptKey>(a: Policy<Pk>, b: Policy<Pk>) -> PolicyDiff<Pk> {
            if a == b {
                return PolicyDiff { a: vec![], b: vec![] };
            }
            match (a, b) {
                (Policy::Thresh(t_a), Policy::Thresh(t_b))
                    if t_a.k() == t_b.k() && t_a.n() == t_b.n() =>
                {
                    // Match up children that compare equal, consuming each
                    // child of `b` at most once so that duplicated children
                    // are handled correctly.
                    let mut b_matched = vec![false; t_b.n()];
                    let mut diff_a = Vec::new();
                    for sub_a in t_a {
                        let pos = t_b
                            .iter()
                            .zip(b_matched.iter().copied())
                            .position(|(sub_b, matched)| !matched && **sub_b == *sub_a);
                        match pos {
                            Some(j) => b_matched[j] = true,
                            None => diff_a.push(sub_a.as_ref().clone()),
                        }
                    }
                    let diff_b = t_b
                        .into_iter()
                        .zip(b_matched)
                        .filter(|(_, matched)| !matched)
                        .map(|(sub_b, _)| sub_b.as_ref().clone())
                        .collect();
                    PolicyDiff { a: diff_a, b: diff_b }
                }
                (a, b) => PolicyDiff { a: vec![a], b: vec![b] },
            }
        }

        diff(a.normalized(), b.normalized())
    }

    /// Combines two policy differences into one.
    // Policies should not generally contain repeated conditions, so no
    // attempt is made to deduplicate the combined differences.
    pub fn combine(&mut self, second: Self) {
        self.a.extend(second.a);
        self.b.extend(second.b);
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Policy<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool {
        self.pre_order_iter().all(|policy| match policy {
            Self::Key(ref pk) => pred(pk),
            _ => true,
        })
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Converts a policy using one kind of public key to another type of public key.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::str::FromStr;
    /// use miniscript::bitcoin::{hashes::hash160, PublicKey};
    /// use miniscript::{translate_hash_fail, policy::semantic::Policy, Translator};
    /// let alice_pk = "02c79ef3ede6d14f72a00d0e49b4becfb152197b64c0707425c4f231df29500ee7";
    /// let bob_pk = "03d008a849fbf474bd17e9d2c1a827077a468150e58221582ec3410ab309f5afe4";
    /// let placeholder_policy = Policy::<String>::from_str("and(pk(alice_pk),pk(bob_pk))").unwrap();
    ///
    /// // Information to translate abstract string type keys to concrete `bitcoin::PublicKey`s.
    /// // In practice, wallets would map from string key names to BIP32 keys.
    /// struct StrPkTranslator {
    ///     pk_map: HashMap<String, bitcoin::PublicKey>
    /// }
    ///
    /// // If we also wanted to provide mapping of other associated types (sha256, older etc),
    /// // we would use the general [`Translator`] trait.
    /// impl Translator<String> for StrPkTranslator {
    ///     type TargetPk = bitcoin::PublicKey;
    ///     type Error = ();
    ///
    ///     fn pk(&mut self, pk: &String) -> Result<bitcoin::PublicKey, Self::Error> {
    ///         self.pk_map.get(pk).copied().ok_or(()) // Dummy Err
    ///     }
    ///
    ///     // Handy macro for failing if we encounter any other fragment.
    ///     // See also [`translate_hash_clone!`] for cloning instead of failing.
    ///     translate_hash_fail!(String);
    /// }
    ///
    /// let mut pk_map = HashMap::new();
    /// pk_map.insert(String::from("alice_pk"), bitcoin::PublicKey::from_str(alice_pk).unwrap());
    /// pk_map.insert(String::from("bob_pk"), bitcoin::PublicKey::from_str(bob_pk).unwrap());
    /// let mut t = StrPkTranslator { pk_map };
    ///
    /// let real_policy = placeholder_policy.translate_pk(&mut t).unwrap();
    ///
    /// let expected_policy = Policy::from_str(&format!("and(pk({}),pk({}))", alice_pk, bob_pk)).unwrap();
    /// assert_eq!(real_policy, expected_policy);
    /// ```
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Policy<T::TargetPk>, T::Error>
    where
        T: Translator<Pk>,
    {
        use Policy::*;

        let mut translated = vec![];
        for data in self.post_order_iter() {
            let new_policy = match data.node {
                Unsatisfiable => Unsatisfiable,
                Trivial => Trivial,
                Key(ref pk) => t.pk(pk).map(Key)?,
                Sha256(ref h) => t.sha256(h).map(Sha256)?,
                Hash256(ref h) => t.hash256(h).map(Hash256)?,
                Ripemd160(ref h) => t.ripemd160(h).map(Ripemd160)?,
                Hash160(ref h) => t.hash160(h).map(Hash160)?,
                Older(ref n) => Older(*n),
                After(ref n) => After(*n),
                Thresh(ref thresh) => Thresh(translated.pop_thresh(thresh)),
            };
            translated.push(Arc::new(new_policy));
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = translated.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        Ok(Arc::try_unwrap(root_node).unwrap())
    }

    /// Computes whether the current policy entails the second one.
    ///
    /// A |- B means every satisfaction of A is also a satisfaction of B.
    ///
    /// This implementation will run slowly for larger policies but should be
    /// sufficient for most practical policies.
    ///
    /// Returns None for very large policies for which entailment cannot
    /// be practically computed.
    // This algorithm has a naive implementation. It is possible to optimize this
    // by memoizing and maintaining a hashmap.
    pub fn entails(self, other: Self) -> Option<bool> {
        if self.n_terminals() > ENTAILMENT_MAX_TERMINALS {
            return None;
        }
        match (self, other) {
            (Self::Unsatisfiable, _) => Some(true),
            (Self::Trivial, Self::Trivial) => Some(true),
            (Self::Trivial, _) => Some(false),
            (_, Self::Unsatisfiable) => Some(false),
            (a, b) => {
                let (a_norm, b_norm) = (a.normalized(), b.normalized());
                let first_constraint = a_norm.first_constraint();
                let (a1, b1) = (
                    a_norm.clone().satisfy_constraint(&first_constraint, true),
                    b_norm.clone().satisfy_constraint(&first_constraint, true),
                );
                let (a2, b2) = (
                    a_norm.satisfy_constraint(&first_constraint, false),
                    b_norm.satisfy_constraint(&first_constraint, false),
                );
                Some(Self::entails(a1, b1)? && Self::entails(a2, b2)?)
            }
        }
    }

    // Helper function to compute the number of constraints in policy.
    fn n_terminals(&self) -> usize {
        let mut n_terminals = vec![];
        for data in self.post_order_iter() {
            let num = match data.node {
                Self::Thresh(thresh) => n_terminals.pop_n(thresh.n()).sum(),
                Self::Trivial | Self::Unsatisfiable => 0,
                _leaf => 1,
            };
            n_terminals.push(num);
        }
        // Ok to unwrap because we know we processed at least one node.
        n_terminals.pop().unwrap()
    }

    // Helper function to get the first constraint in the policy.
    // Returns the first leaf policy. Used in policy entailment.
    // Assumes that the current policy is normalized.
    fn first_constraint(&self) -> Self {
        debug_assert!(self.clone().normalized() == self.clone());
        match self {
            Self::Thresh(ref thresh) => thresh.data()[0].first_constraint(),
            first => first.clone(),
        }
    }

    // Helper function that takes in witness and its availability, changing it
    // to true or false and returning the resultant normalized policy. Witness
    // is currently encoded as policy. Only accepts leaf fragment and a
    // normalized policy
    pub(crate) fn satisfy_constraint(self, witness: &Self, available: bool) -> Self {
        debug_assert!(self.clone().normalized() == self);
        if let Self::Thresh { .. } = *witness {
            // We can't debug_assert on Policy::Thresh.
            panic!("should be unreachable")
        }

        let ret =
            match self {
                Self::Thresh(thresh) => Self::Thresh(thresh.map(|sub| {
                    Arc::new(sub.as_ref().clone().satisfy_constraint(witness, available))
                })),
                ref leaf if leaf == witness => {
                    if available {
                        Self::Trivial
                    } else {
                        Self::Unsatisfiable
                    }
                }
                x => x,
            };
        ret.normalized()
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Policy<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::Unsatisfiable => f.write_str("UNSATISFIABLE()"),
            Self::Trivial => f.write_str("TRIVIAL()"),
            Self::Key(ref pkh) => write!(f, "pk({:?})", pkh),
            Self::After(n) => write!(f, "after({})", n),
            Self::Older(n) => write!(f, "older({})", n),
            Self::Sha256(ref h) => write!(f, "sha256({})", h),
            Self::Hash256(ref h) => write!(f, "hash256({})", h),
            Self::Ripemd160(ref h) => write!(f, "ripemd160({})", h),
            Self::Hash160(ref h) => write!(f, "hash160({})", h),
            Self::Thresh(ref thresh) => {
                if thresh.k() == thresh.n() {
                    thresh.debug("and", false).fmt(f)
                } else if thresh.k() == 1 {
                    thresh.debug("or", false).fmt(f)
                } else {
                    thresh.debug("thresh", true).fmt(f)
                }
            }
        }
    }
}

/// Displays the policy using mathematical notation for readability.
///
/// - `and(a, b)` is displayed as `(a ∧ b)`
/// - `or(a, b)` is displayed as `(a ∨ b)`
/// - `thresh(k, a, b, c)` is displayed as `#{a, b, c} = k`
impl<Pk: MiniscriptKey> fmt::Display for Policy<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::Unsatisfiable => f.write_str("UNSATISFIABLE"),
            Self::Trivial => f.write_str("TRIVIAL"),
            Self::Key(ref pkh) => write!(f, "pk({})", pkh),
            Self::After(n) => write!(f, "after({})", n),
            Self::Older(n) => write!(f, "older({})", n),
            Self::Sha256(ref h) => write!(f, "sha256({})", h),
            Self::Hash256(ref h) => write!(f, "hash256({})", h),
            Self::Ripemd160(ref h) => write!(f, "ripemd160({})", h),
            Self::Hash160(ref h) => write!(f, "hash160({})", h),
            Self::Thresh(ref thresh) => {
                let mut iter = thresh.iter();
                let first = iter.next().expect("thresholds are never empty");
                if thresh.k() == thresh.n() {
                    write!(f, "({}", first)?;
                    for sub in iter {
                        write!(f, " ∧ {}", sub)?;
                    }
                    f.write_str(")")
                } else if thresh.k() == 1 {
                    write!(f, "({}", first)?;
                    for sub in iter {
                        write!(f, " ∨ {}", sub)?;
                    }
                    f.write_str(")")
                } else {
                    write!(f, "#{{{}", first)?;
                    for sub in iter {
                        write!(f, ", {}", sub)?;
                    }
                    write!(f, "}} = {}", thresh.k())
                }
            }
        }
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Serializes the policy using function-call notation
    /// (`and(..)`, `or(..)`, `thresh(k, ..)`).
    ///
    /// This is an alternative to [`fmt::Display`], which uses mathematical
    /// notation (`∧`, `∨`, `#{..} = k`). Both forms round-trip through
    /// [`str::FromStr`]; prefer [`fmt::Display`] for general use.
    pub fn to_policy_syntax_string(&self) -> String {
        let mut s = String::new();
        self.write_policy_syntax(&mut s)
            .expect("writing to a String is infallible");
        s
    }

    fn write_policy_syntax<W: fmt::Write>(&self, w: &mut W) -> fmt::Result {
        match *self {
            Self::Unsatisfiable => w.write_str("UNSATISFIABLE"),
            Self::Trivial => w.write_str("TRIVIAL"),
            Self::Key(ref pkh) => write!(w, "pk({})", pkh),
            Self::After(n) => write!(w, "after({})", n),
            Self::Older(n) => write!(w, "older({})", n),
            Self::Sha256(ref h) => write!(w, "sha256({})", h),
            Self::Hash256(ref h) => write!(w, "hash256({})", h),
            Self::Ripemd160(ref h) => write!(w, "ripemd160({})", h),
            Self::Hash160(ref h) => write!(w, "hash160({})", h),
            Self::Thresh(ref thresh) => {
                let (name, show_k) = if thresh.k() == thresh.n() {
                    ("and", false)
                } else if thresh.k() == 1 {
                    ("or", false)
                } else {
                    ("thresh", true)
                };
                w.write_str(name)?;
                w.write_str("(")?;
                let mut iter = thresh.iter();
                if show_k {
                    write!(w, "{}", thresh.k())?;
                    for child in iter {
                        w.write_str(",")?;
                        child.write_policy_syntax(w)?;
                    }
                } else {
                    let first = iter.next().expect("thresholds are never empty");
                    first.write_policy_syntax(w)?;
                    for child in iter {
                        w.write_str(",")?;
                        child.write_policy_syntax(w)?;
                    }
                }
                w.write_str(")")
            }
        }
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Renders the policy as a tree in the style of the UNIX `tree` command.
    ///
    /// Each node of the tree is rendered on its own line; threshold
    /// combiners are rendered as `and`, `or` or `thresh(k)` and leaf
    /// fragments are rendered in policy syntax (`pk(..)`, `older(..)`, ...).
    ///
    /// This is intended for debugging and display purposes; the output
    /// cannot be parsed back into a policy.
    pub fn to_tree_string(&self) -> String {
        let mut s = String::new();
        self.write_tree(&mut s, "", true, None)
            .expect("writing to a String is infallible");
        // Remove the trailing newline.
        s.pop();
        s
    }

    /// Renders the difference between two policies as a tree.
    ///
    /// Structure that is shared by both policies is rendered once, in the
    /// style of [`Policy::to_tree_string`]. Sub-policies that differ are
    /// rendered as a pair of trees whose root lines are prefixed with `- `
    /// (present only in `self`) and `+ ` (present only in `other`).
    ///
    /// The policies are compared as-is; call [`Policy::normalized`] on both
    /// policies first to erase differences that are removed by
    /// normalization.
    ///
    /// This is intended for debugging and display purposes; the output
    /// cannot be parsed back into a policy.
    pub fn to_diff_string(&self, other: &Self) -> String {
        let mut s = String::new();
        self.write_diff(other, &mut s, "", true)
            .expect("writing to a String is infallible");
        // Remove the trailing newline.
        s.pop();
        s
    }

    // Writes the label of a single node: the combiner name for thresholds
    // (whose children are rendered on their own lines) or the full fragment
    // in policy syntax for leaves.
    fn write_node_label<W: fmt::Write>(&self, w: &mut W) -> fmt::Result {
        match *self {
            Self::Thresh(ref thresh) if thresh.is_and() => w.write_str("and"),
            Self::Thresh(ref thresh) if thresh.is_or() => w.write_str("or"),
            Self::Thresh(ref thresh) => write!(w, "thresh({})", thresh.k()),
            _ => self.write_policy_syntax(w),
        }
    }

    // Helper for `to_tree_string`. Renders the policy as a tree where
    // `prefix` is prepended to the line of the root node and `last`
    // indicates whether the policy is the last child of its parent. If
    // `mark` is set, the root line is additionally prefixed with the given
    // character (used by `to_diff_string` to mark differing sub-policies).
    fn write_tree<W: fmt::Write>(
        &self,
        w: &mut W,
        prefix: &str,
        last: bool,
        mark: Option<char>,
    ) -> fmt::Result {
        w.write_str(prefix)?;
        w.write_str(if last { "`-- " } else { "|-- " })?;
        if let Some(mark) = mark {
            write!(w, "{} ", mark)?;
        }
        self.write_node_label(w)?;
        w.write_str("\n")?;

        if let Self::Thresh(ref thresh) = *self {
            let mut child_prefix = String::from(prefix);
            child_prefix.push_str(if last { "    " } else { "|   " });
            let last_child = thresh.n() - 1;
            for (i, child) in thresh.iter().enumerate() {
                child.write_tree(w, &child_prefix, i == last_child, None)?;
            }
        }
        Ok(())
    }

    // Helper for `to_diff_string`; see `write_tree` for the meaning of the
    // `prefix` and `last` arguments.
    fn write_diff<W: fmt::Write>(
        &self,
        other: &Self,
        w: &mut W,
        prefix: &str,
        last: bool,
    ) -> fmt::Result {
        match (self, other) {
            (x, y) if x == y => x.write_tree(w, prefix, last, None),
            (Self::Thresh(t_a), Self::Thresh(t_b)) if t_a.k() == t_b.k() && t_a.n() == t_b.n() => {
                // The two thresholds have the same shape; render a single
                // node and recurse into the children, pairing up children
                // that do not compare equal.
                w.write_str(prefix)?;
                w.write_str(if last { "`-- " } else { "|-- " })?;
                self.write_node_label(w)?;
                w.write_str("\n")?;

                let mut child_prefix = String::from(prefix);
                child_prefix.push_str(if last { "    " } else { "|   " });

                // Match up children that compare equal, consuming each child
                // of `other` at most once. Since both thresholds have the
                // same number of children, the unmatched children of `self`
                // and `other` can be paired up in order.
                let mut b_matched = vec![false; t_b.n()];
                let mut a_matched = Vec::with_capacity(t_a.n());
                for sub_a in t_a.iter() {
                    let pos = t_b
                        .iter()
                        .zip(b_matched.iter().copied())
                        .position(|(sub_b, matched)| !matched && sub_b == sub_a);
                    match pos {
                        Some(j) => {
                            b_matched[j] = true;
                            a_matched.push(true);
                        }
                        None => a_matched.push(false),
                    }
                }

                let last_child = t_a.n() - 1;
                let mut j = 0; // index of the next unmatched child of `other`
                for (i, sub_a) in t_a.iter().enumerate() {
                    if a_matched[i] {
                        sub_a.write_tree(w, &child_prefix, i == last_child, None)?;
                    } else {
                        while b_matched[j] {
                            j += 1;
                        }
                        sub_a.write_diff(&t_b.data()[j], w, &child_prefix, i == last_child)?;
                        j += 1;
                    }
                }
                Ok(())
            }
            (x, y) => {
                // The sub-policies have nothing in common; render both,
                // marking the root lines with `- ` and `+ ` respectively.
                x.write_tree(w, prefix, last, Some('-'))?;
                y.write_tree(w, prefix, last, Some('+'))
            }
        }
    }
}

impl<Pk: FromStrKey> str::FromStr for Policy<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Error> {
        if s.starts_with('(') || s.contains('∧') || s.contains('∨') || s.contains("#{") {
            MathParser::parse(s)
        } else {
            let tree = expression::Tree::from_str(s)?;
            expression::FromTree::from_tree(tree.root())
        }
    }
}

/// Syntax error parsing a `policy::Semantic` written in mathematical notation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MathSyntaxError {
    /// `(pk(A))`-style group containing only a single operand.
    SingletonGroup,
    /// `∧` and `∨` were mixed in the same `(...)` group without explicit nesting.
    MixedOperators,
    /// A terminal name was not recognized.
    UnknownTerminal(String),
    /// Other math-notation syntax error.
    Other(String),
}

impl fmt::Display for MathSyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::SingletonGroup => {
                f.write_str("singleton group; expected `∧` or `∨` between operands")
            }
            Self::MixedOperators => f.write_str("mixed `∧`/`∨` in same group"),
            Self::UnknownTerminal(name) => write!(f, "unknown terminal `{}`", name),
            Self::Other(s) => f.write_str(s),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MathSyntaxError {}

fn malformed_math(context: &str) -> Error {
    Error::Parse(ParseError::Math(MathSyntaxError::Other(context.to_owned())))
}

/// Character-level cursor over the input string for
/// mathematical-notation parsing.
struct MathParser<'a> {
    s: &'a str,
    iter: core::iter::Peekable<core::str::CharIndices<'a>>,
}

/// Low-level cursor primitives.
impl<'a> MathParser<'a> {
    fn new(s: &'a str) -> Self { Self { s, iter: s.char_indices().peekable() } }

    fn peek(&mut self) -> Option<char> { self.iter.peek().map(|&(_, c)| c) }

    fn next(&mut self) -> Option<char> { self.iter.next().map(|(_, c)| c) }

    fn pos(&mut self) -> usize { self.iter.peek().map(|&(i, _)| i).unwrap_or(self.s.len()) }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(c) if c.is_whitespace()) {
            self.next();
        }
    }

    fn expect(&mut self, want: char) -> Result<(), Error> {
        if self.peek() == Some(want) {
            self.next();
            Ok(())
        } else {
            Err(malformed_math(&format!("expected `{}`", want)))
        }
    }

    fn consume_while(&mut self, pred: impl Fn(char) -> bool) -> &'a str {
        let start = self.pos();
        while matches!(self.peek(), Some(c) if pred(c)) {
            self.next();
        }
        &self.s[start..self.pos()]
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Op {
    And,
    Or,
}

impl From<char> for Op {
    fn from(c: char) -> Self {
        match c {
            '∧' => Self::And,
            '∨' => Self::Or,
            _ => unreachable!(),
        }
    }
}

#[derive(PartialEq, Eq)]
enum Kind {
    Group(Option<Op>),
    Thresh,
}

/// One pending node on the parser's frame stack: a parenthesised
/// `∧`/`∨` group or a `#{ ... } = k` threshold whose children are
/// being collected.
struct Frame<Pk: MiniscriptKey> {
    subs: Vec<Arc<Policy<Pk>>>,
    kind: Kind,
}

/// Parses the mathematical-notation form produced by `Display`.
impl<'a> MathParser<'a> {
    fn parse<Pk: FromStrKey>(s: &'a str) -> Result<Policy<Pk>, Error> {
        let mut parser = Self::new(s);
        let mut frames: Vec<Frame<Pk>> = Vec::new();
        let mut cur: Option<Arc<Policy<Pk>>> = None;

        loop {
            parser.skip_ws();
            let c = match parser.peek() {
                Some(c) => c,
                None => break,
            };

            if cur.is_none() {
                match c {
                    '(' => {
                        parser.next();
                        frames.push(Frame { subs: Vec::new(), kind: Kind::Group(None) });
                    }
                    '#' => {
                        parser.next();
                        parser.expect('{')?;
                        frames.push(Frame { subs: Vec::new(), kind: Kind::Thresh });
                    }
                    '∧' | '∨' | ',' => {
                        return Err(malformed_math("missing sub-expression before operator"))
                    }
                    ')' | '}' => return Err(malformed_math("empty group or threshold")),
                    _ => cur = Some(Arc::new(parser.parse_terminal()?)),
                }
                continue;
            }

            let frame = frames
                .last_mut()
                .ok_or_else(|| malformed_math("trailing input after root expression"))?;
            match c {
                '∧' | '∨' => {
                    parser.next();
                    let op = Op::from(c);
                    match &mut frame.kind {
                        Kind::Group(slot @ None) => *slot = Some(op),
                        Kind::Group(Some(prev)) if *prev == op => {}
                        Kind::Group(Some(_)) => {
                            return Err(Error::Parse(ParseError::Math(
                                MathSyntaxError::MixedOperators,
                            )))
                        }
                        Kind::Thresh => {
                            return Err(malformed_math(
                                "expected `,` or `}` between `#{...}` threshold elements",
                            ))
                        }
                    }
                    frame.subs.push(cur.take().unwrap());
                }
                ',' => {
                    if frame.kind != Kind::Thresh {
                        return Err(malformed_math("`,` outside of `#{...}` threshold"));
                    }
                    parser.next();
                    frame.subs.push(cur.take().unwrap());
                }
                ')' => {
                    parser.next();
                    let mut frame = frames.pop().unwrap();
                    let op = match frame.kind {
                        Kind::Group(op) => op.ok_or_else(|| {
                            Error::Parse(ParseError::Math(MathSyntaxError::SingletonGroup))
                        })?,
                        Kind::Thresh => {
                            return Err(malformed_math(
                                "`)` cannot close `#{...}` threshold (use `}`)",
                            ))
                        }
                    };
                    frame.subs.push(cur.take().unwrap());
                    let k = if op == Op::And { frame.subs.len() } else { 1 };
                    cur = Some(Arc::new(Policy::Thresh(
                        Threshold::new(k, frame.subs).map_err(Error::Threshold)?,
                    )));
                }
                '}' => {
                    parser.next();
                    let mut frame = match frames.pop() {
                        Some(f) if f.kind == Kind::Thresh => f,
                        _ => {
                            return Err(malformed_math("`}` cannot close `(...)` group (use `)`)"))
                        }
                    };
                    frame.subs.push(cur.take().unwrap());
                    parser.skip_ws();
                    parser.expect('=')?;
                    parser.skip_ws();
                    let k_str = parser.consume_while(|c| c.is_ascii_digit());
                    if k_str.is_empty() {
                        return Err(malformed_math("expected digits after `#{...} =`"));
                    }
                    let k = expression::parse_num(k_str)
                        .map_err(ParseError::Num)
                        .map_err(Error::Parse)? as usize;
                    let thresh = Threshold::new(k, frame.subs).map_err(Error::Threshold)?;
                    // k=1 must be `∨`; k=n must be `∧`.
                    if thresh.is_or() {
                        return Err(Error::ParseThreshold(crate::ParseThresholdError::IllegalOr));
                    }
                    if thresh.is_and() {
                        return Err(Error::ParseThreshold(crate::ParseThresholdError::IllegalAnd));
                    }
                    cur = Some(Arc::new(Policy::Thresh(thresh)));
                }
                _ => return Err(malformed_math(&format!("unexpected character `{}`", c))),
            }
        }

        if !frames.is_empty() {
            return Err(malformed_math("unclosed group or threshold"));
        }
        let root = cur.ok_or_else(|| malformed_math("empty input"))?;
        Ok(Arc::try_unwrap(root).expect("root Arc is uniquely owned"))
    }

    fn parse_terminal<Pk: FromStrKey>(&mut self) -> Result<Policy<Pk>, Error> {
        let name = self.consume_while(|c| c.is_ascii_alphanumeric());
        if name.is_empty() {
            return Err(malformed_math("expected terminal name"));
        }

        self.skip_ws();
        if self.peek() != Some('(') {
            return match name {
                "UNSATISFIABLE" => Ok(Policy::Unsatisfiable),
                "TRIVIAL" => Ok(Policy::Trivial),
                "pk" | "after" | "older" | "sha256" | "hash256" | "ripemd160" | "hash160" => {
                    Err(malformed_math(&format!("`{}` requires arguments: `{}(...)`", name, name)))
                }
                _ => Err(Error::Parse(ParseError::Math(MathSyntaxError::UnknownTerminal(
                    name.to_owned(),
                )))),
            };
        }
        self.next();

        let arg = self.consume_while(|c| c != ')').trim();
        self.expect(')')?;

        Ok(match name {
            "pk" => Policy::Key(parse_arg(arg)?),
            "after" => {
                let n = expression::parse_num(arg)
                    .map_err(ParseError::Num)
                    .map_err(Error::Parse)?;
                Policy::After(
                    AbsLockTime::from_consensus(n)
                        .map_err(ParseError::AbsoluteLockTime)
                        .map_err(Error::Parse)?,
                )
            }
            "older" => {
                let n = expression::parse_num(arg)
                    .map_err(ParseError::Num)
                    .map_err(Error::Parse)?;
                Policy::Older(
                    RelLockTime::from_consensus(n)
                        .map_err(ParseError::RelativeLockTime)
                        .map_err(Error::Parse)?,
                )
            }
            "sha256" => Policy::Sha256(parse_arg(arg)?),
            "hash256" => Policy::Hash256(parse_arg(arg)?),
            "ripemd160" => Policy::Ripemd160(parse_arg(arg)?),
            "hash160" => Policy::Hash160(parse_arg(arg)?),
            _ => {
                return Err(Error::Parse(ParseError::Math(MathSyntaxError::UnknownTerminal(
                    name.to_owned(),
                ))))
            }
        })
    }
}

fn parse_arg<T: core::str::FromStr>(arg: &str) -> Result<T, Error>
where
    T::Err: crate::blanket_traits::StaticDebugAndDisplay,
{
    arg.parse::<T>()
        .map_err(ParseError::box_from_str)
        .map_err(Error::Parse)
}

serde_string_impl_pk!(Policy, "a miniscript semantic policy");

impl<Pk: FromStrKey> expression::FromTree for Policy<Pk> {
    fn from_tree(root: expression::TreeIterItem) -> Result<Self, Error> {
        root.verify_no_curly_braces()
            .map_err(From::from)
            .map_err(Error::Parse)?;

        let mut stack = Vec::with_capacity(128);
        for node in root.pre_order_iter().rev() {
            // Before doing anything else, check if this is the inner value of a terminal.
            // In that case, just skip the node. Conveniently, there are no combinators
            // in policy that have a single child that these might be confused with (we
            // require and, or and thresholds to all have >1 child).
            if let Some(parent) = node.parent() {
                if parent.n_children() == 1 {
                    continue;
                }
                if node.is_first_child() && parent.name() == "thresh" {
                    continue;
                }
            }

            let new = match node.name() {
                "UNSATISFIABLE" => {
                    node.verify_n_children("UNSATISFIABLE", 0..=0)
                        .map_err(From::from)
                        .map_err(Error::Parse)?;
                    Ok(Self::Unsatisfiable)
                }
                "TRIVIAL" => {
                    node.verify_n_children("TRIVIAL", 0..=0)
                        .map_err(From::from)
                        .map_err(Error::Parse)?;
                    Ok(Self::Trivial)
                }
                "pk" => node
                    .verify_terminal_parent("pk", "public key")
                    .map(Policy::Key)
                    .map_err(Error::Parse),
                "after" => node.verify_after().map_err(Error::Parse).map(Policy::After),
                "older" => node.verify_older().map_err(Error::Parse).map(Policy::Older),
                "sha256" => node
                    .verify_terminal_parent("sha256", "hash")
                    .map(Policy::Sha256)
                    .map_err(Error::Parse),
                "hash256" => node
                    .verify_terminal_parent("hash256", "hash")
                    .map(Policy::Hash256)
                    .map_err(Error::Parse),
                "ripemd160" => node
                    .verify_terminal_parent("ripemd160", "hash")
                    .map(Policy::Ripemd160)
                    .map_err(Error::Parse),
                "hash160" => node
                    .verify_terminal_parent("hash160", "hash")
                    .map(Policy::Hash160)
                    .map_err(Error::Parse),
                "and" => {
                    node.verify_n_children("and", 2..)
                        .map_err(From::from)
                        .map_err(Error::Parse)?;

                    let child_iter = (0..node.n_children()).map(|_| stack.pop().unwrap());
                    let thresh = Threshold::from_iter(node.n_children(), child_iter)
                        .map_err(Error::Threshold)?;
                    Ok(Self::Thresh(thresh))
                }
                "or" => {
                    node.verify_n_children("or", 2..)
                        .map_err(From::from)
                        .map_err(Error::Parse)?;
                    let child_iter = (0..node.n_children()).map(|_| stack.pop().unwrap());
                    let thresh = Threshold::from_iter(1, child_iter).map_err(Error::Threshold)?;
                    Ok(Self::Thresh(thresh))
                }
                "thresh" => {
                    let thresh = node.verify_threshold(|_| Ok::<_, Error>(stack.pop().unwrap()))?;

                    // thresh(1) and thresh(n) are disallowed in semantic policies
                    if thresh.is_or() {
                        return Err(Error::ParseThreshold(crate::ParseThresholdError::IllegalOr));
                    }
                    if thresh.is_and() {
                        return Err(Error::ParseThreshold(crate::ParseThresholdError::IllegalAnd));
                    }

                    Ok(Self::Thresh(thresh))
                }
                x => {
                    Err(Error::Parse(crate::ParseError::Tree(crate::ParseTreeError::UnknownName {
                        name: x.to_owned(),
                    })))
                }
            }?;

            stack.push(Arc::new(new));
        }

        assert_eq!(stack.len(), 1);
        Ok(Arc::try_unwrap(stack.pop().unwrap()).unwrap())
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Flattens out trees of `And`s and `Or`s; eliminate `Trivial` and
    /// `Unsatisfiable`s. Does not reorder any branches; use `.sort`.
    pub fn normalized(self) -> Self {
        match self {
            Self::Thresh(thresh) => {
                let mut ret_subs = Vec::with_capacity(thresh.n());

                let subs: Vec<_> = thresh
                    .iter()
                    .map(|sub| Arc::new(sub.as_ref().clone().normalized()))
                    .collect();
                let trivial_count = subs
                    .iter()
                    .filter(|&pol| *pol.as_ref() == Self::Trivial)
                    .count();
                let unsatisfied_count = subs
                    .iter()
                    .filter(|&pol| *pol.as_ref() == Self::Unsatisfiable)
                    .count();

                let n = subs.len() - unsatisfied_count - trivial_count; // remove all true/false
                let m = thresh.k().saturating_sub(trivial_count); // satisfy all trivial

                let is_and = m == n;
                let is_or = m == 1;

                for sub in subs {
                    match sub.as_ref() {
                        Self::Trivial | Self::Unsatisfiable => {}
                        Self::Thresh(ref subthresh) => {
                            match (is_and, is_or) {
                                (true, true) => {
                                    // means m = n = 1, thresh(1,X) type thing.
                                    ret_subs.push(Arc::new(Self::Thresh(subthresh.clone())));
                                }
                                (true, false) if subthresh.k() == subthresh.n() => {
                                    ret_subs.extend(subthresh.iter().cloned())
                                } // and case
                                (false, true) if subthresh.k() == 1 => {
                                    ret_subs.extend(subthresh.iter().cloned())
                                } // or case
                                _ => ret_subs.push(Arc::new(Self::Thresh(subthresh.clone()))),
                            }
                        }
                        x => ret_subs.push(Arc::new(x.clone())),
                    }
                }
                // Now reason about m of n threshold
                if m == 0 {
                    Self::Trivial
                } else if m > ret_subs.len() {
                    Self::Unsatisfiable
                } else if ret_subs.len() == 1 {
                    let policy = ret_subs.pop().unwrap();
                    // Only one strong reference because we created the Arc when pushing to ret_subs.
                    Arc::try_unwrap(policy).unwrap()
                } else if is_and {
                    // unwrap ok since ret_subs is nonempty
                    Self::Thresh(Threshold::new(ret_subs.len(), ret_subs).unwrap())
                } else if is_or {
                    // unwrap ok since ret_subs is nonempty
                    Self::Thresh(Threshold::new(1, ret_subs).unwrap())
                } else {
                    // unwrap ok since ret_subs is nonempty and we made sure m <= ret_subs.len
                    Self::Thresh(Threshold::new(m, ret_subs).unwrap())
                }
            }
            x => x,
        }
    }

    /// Detects a true/trivial policy.
    ///
    /// Only checks whether the policy is `Policy::Trivial`, to check if the
    /// normalized form is trivial, the caller is expected to normalize the
    /// policy first.
    pub fn is_trivial(&self) -> bool { matches!(*self, Self::Trivial) }

    /// Detects a false/unsatisfiable policy.
    ///
    /// Only checks whether the policy is `Policy::Unsatisfiable`, to check if
    /// the normalized form is unsatisfiable, the caller is expected to
    /// normalize the policy first.
    pub fn is_unsatisfiable(&self) -> bool { matches!(*self, Self::Unsatisfiable) }

    /// Helper function to do the recursion in `timelocks`.
    fn real_relative_timelocks(&self) -> Vec<u32> {
        self.pre_order_iter()
            .filter_map(|policy| match policy {
                Self::Older(t) => Some(t.to_consensus_u32()),
                _ => None,
            })
            .collect()
    }

    /// Returns a list of all relative timelocks, not including 0, which appear
    /// in the policy.
    pub fn relative_timelocks(&self) -> Vec<u32> {
        let mut ret = self.real_relative_timelocks();
        ret.sort_unstable();
        ret.dedup();
        ret
    }

    /// Helper function for recursion in `absolute timelocks`
    fn real_absolute_timelocks(&self) -> Vec<u32> {
        self.pre_order_iter()
            .filter_map(|policy| match policy {
                Self::After(t) => Some(t.to_consensus_u32()),
                _ => None,
            })
            .collect()
    }

    /// Returns a list of all absolute timelocks, not including 0, which appear
    /// in the policy.
    pub fn absolute_timelocks(&self) -> Vec<u32> {
        let mut ret = self.real_absolute_timelocks();
        ret.sort_unstable();
        ret.dedup();
        ret
    }

    /// Filters a policy by eliminating relative timelock constraints
    /// that are not satisfied at the given `age`.
    pub fn at_age(self, age: relative::LockTime) -> Self {
        let mut at_age = vec![];
        for data in Arc::new(self).post_order_iter() {
            let new_policy = match data.node.as_ref() {
                Self::Older(ref t) => {
                    if relative::LockTime::from(*t).is_implied_by(age) {
                        Some(Self::Older(*t))
                    } else {
                        Some(Self::Unsatisfiable)
                    }
                }
                Self::Thresh(ref thresh) => Some(Self::Thresh(at_age.pop_thresh(thresh))),
                _ => None,
            };
            match new_policy {
                Some(new_policy) => at_age.push(Arc::new(new_policy)),
                None => at_age.push(Arc::clone(data.node)),
            }
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = at_age.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        let policy = Arc::try_unwrap(root_node).unwrap();
        policy.normalized()
    }

    /// Filters a policy by eliminating absolute timelock constraints
    /// that are not satisfied at the given `n` (`n OP_CHECKLOCKTIMEVERIFY`).
    pub fn at_lock_time(self, n: absolute::LockTime) -> Self {
        let mut at_age = vec![];
        for data in Arc::new(self).post_order_iter() {
            let new_policy = match data.node.as_ref() {
                Self::After(t) => {
                    if absolute::LockTime::from(*t).is_implied_by(n) {
                        Some(Self::After(*t))
                    } else {
                        Some(Self::Unsatisfiable)
                    }
                }
                Self::Thresh(ref thresh) => Some(Self::Thresh(at_age.pop_thresh(thresh))),
                _ => None,
            };
            match new_policy {
                Some(new_policy) => at_age.push(Arc::new(new_policy)),
                None => at_age.push(Arc::clone(data.node)),
            }
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = at_age.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        let policy = Arc::try_unwrap(root_node).unwrap();
        policy.normalized()
    }

    /// Counts the number of public keys and keyhashes referenced in a policy.
    /// Duplicate keys will be double-counted.
    pub fn n_keys(&self) -> usize {
        self.pre_order_iter()
            .filter(|policy| matches!(policy, Self::Key(..)))
            .count()
    }

    /// Counts the minimum number of public keys for which signatures could be
    /// used to satisfy the policy.
    ///
    /// # Returns
    ///
    /// Returns `None` if the policy is not satisfiable.
    pub fn minimum_n_keys(&self) -> Option<usize> {
        let mut minimum_n_keys = vec![];
        for data in self.post_order_iter() {
            let minimum_n_key = match data.node {
                Self::Unsatisfiable => None,
                Self::Trivial
                | Self::After(..)
                | Self::Older(..)
                | Self::Sha256(..)
                | Self::Hash256(..)
                | Self::Ripemd160(..)
                | Self::Hash160(..) => Some(0),
                Self::Key(..) => Some(1),
                Self::Thresh(ref thresh) => {
                    let mut sublens = minimum_n_keys
                        .pop_n(thresh.n())
                        .flatten()
                        .collect::<Vec<usize>>();
                    if sublens.len() < thresh.k() {
                        // Not enough branches are satisfiable
                        None
                    } else {
                        sublens.sort_unstable();
                        Some(sublens[0..thresh.k()].iter().cloned().sum::<usize>())
                    }
                }
            };
            minimum_n_keys.push(minimum_n_key);
        }
        // Ok to unwrap because we know we processed at least one node.
        minimum_n_keys.pop().unwrap()
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// "Sorts" a policy to bring it into a canonical form to allow comparisons.
    ///
    /// Does **not** allow policies to be compared for functional equivalence;
    /// in general this appears to require Gröbner basis techniques that are not
    /// implemented.
    pub fn sorted(self) -> Self {
        let mut sorted = vec![];
        for data in Arc::new(self).post_order_iter() {
            let new_policy = match data.node.as_ref() {
                Self::Thresh(ref thresh) => {
                    let mut new_thresh = sorted.pop_thresh(thresh);
                    new_thresh.data_mut().sort();
                    Some(Self::Thresh(new_thresh))
                }
                _ => None,
            };
            match new_policy {
                Some(new_policy) => sorted.push(Arc::new(new_policy)),
                None => sorted.push(Arc::clone(data.node)),
            }
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = sorted.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        Arc::try_unwrap(root_node).unwrap()
    }
}

impl<'a, Pk: MiniscriptKey> TreeLike for &'a Policy<Pk> {
    type NaryChildren = &'a [Arc<Policy<Pk>>];

    fn nary_len(tc: &Self::NaryChildren) -> usize { tc.len() }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self { &tc[idx] }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        use Policy::*;

        match *self {
            Unsatisfiable | Trivial | Key(_) | After(_) | Older(_) | Sha256(_) | Hash256(_)
            | Ripemd160(_) | Hash160(_) => Tree::Nullary,
            Thresh(ref thresh) => Tree::Nary(thresh.data()),
        }
    }
}

impl<'a, Pk: MiniscriptKey> TreeLike for &'a Arc<Policy<Pk>> {
    type NaryChildren = &'a [Arc<Policy<Pk>>];

    fn nary_len(tc: &Self::NaryChildren) -> usize { tc.len() }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self { &tc[idx] }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        use Policy::*;

        match ***self {
            Unsatisfiable | Trivial | Key(_) | After(_) | Older(_) | Sha256(_) | Hash256(_)
            | Ripemd160(_) | Hash160(_) => Tree::Nullary,
            Thresh(ref thresh) => Tree::Nary(thresh.data()),
        }
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr as _;

    use bitcoin::PublicKey;

    use super::*;

    type StringPolicy = Policy<String>;

    #[test]
    fn policy_ord_is_consistent() {
        // Same direction as numeric — passes under both old and new scheme.
        let a = StringPolicy::from_str("after(100)").unwrap();
        let b = StringPolicy::from_str("after(200)").unwrap();
        assert!(a < b, "after(100) should be less than after(200)");

        // Cross-variant: must not be equal.
        let c = StringPolicy::from_str("older(100)").unwrap();
        assert!(a != c, "after and older variants must not compare equal");

        // Numeric consensus ordering: 9 < 10.
        let d = StringPolicy::from_str("after(9)").unwrap();
        let e = StringPolicy::from_str("after(10)").unwrap();
        assert!(d < e, "after(9) < after(10) under consensus u32 ordering");

        // "trivial" < "unsatisfiable" alphabetically.
        let trivial = StringPolicy::from_str("TRIVIAL").unwrap();
        let unsat = StringPolicy::from_str("UNSATISFIABLE").unwrap();
        assert!(trivial < unsat, "trivial < unsatisfiable under variant_name ordering");
    }

    #[test]
    fn parse_policy_err() {
        assert!(StringPolicy::from_str("(").is_err());
        assert!(StringPolicy::from_str("(x()").is_err());
        assert!(StringPolicy::from_str("(\u{7f}()3").is_err());
        assert!(StringPolicy::from_str("pk()").is_ok());

        assert!(StringPolicy::from_str("or(or)").is_err());

        assert!(Policy::<PublicKey>::from_str("pk()").is_err());
        assert!(Policy::<PublicKey>::from_str(
            "pk(\
             0200000000000000000000000000000000000002\
             )"
        )
        .is_err());
        assert!(Policy::<PublicKey>::from_str(
            "pk(\
                02c79ef3ede6d14f72a00d0e49b4becfb152197b64c0707425c4f231df29500ee7\
             )"
        )
        .is_ok());
    }

    #[test]
    fn parse_math_notation() {
        let a = StringPolicy::from_str("((pk(A) ∧ pk(B)) ∨ pk(C))").unwrap();
        let b = StringPolicy::from_str("or(and(pk(A),pk(B)),pk(C))").unwrap();
        assert_eq!(a, b);

        let a = StringPolicy::from_str("(pk(A) ∧ #{pk(B), pk(C), pk(D)} = 2)").unwrap();
        let b = StringPolicy::from_str("and(pk(A),thresh(2,pk(B),pk(C),pk(D)))").unwrap();
        assert_eq!(a, b);

        assert_eq!(StringPolicy::from_str("TRIVIAL").unwrap(), Policy::Trivial);

        assert!(StringPolicy::from_str("(pk(A) ∧ pk(B)").is_err());
        assert!(StringPolicy::from_str("#{pk(A), pk(B)} = 1").is_err());
        assert!(StringPolicy::from_str("(and(pk(A),pk(B)) ∧ pk(C))").is_err());

        let err = StringPolicy::from_str("(pk(A))").unwrap_err().to_string();
        assert!(err.contains("singleton"), "unexpected singleton error: {}", err);
        assert!(StringPolicy::from_str("(TRIVIAL)").is_err());

        // 4294967296 == u32::MAX + 1
        let err = StringPolicy::from_str("#{pk(A), pk(B), pk(C)} = 4294967296")
            .unwrap_err()
            .to_string();
        assert!(err.to_lowercase().contains("num"), "expected num error: {}", err);

        // Whitespace flexibility: any amount of whitespace between tokens.
        let canonical = StringPolicy::from_str("(pk(A) ∧ pk(B))").unwrap();
        assert_eq!(StringPolicy::from_str("(pk(A)∧pk(B))").unwrap(), canonical);
        assert_eq!(StringPolicy::from_str("( pk(A)   ∧   pk(B) )").unwrap(), canonical);

        let thresh = StringPolicy::from_str("#{pk(A), pk(B), pk(C)} = 2").unwrap();
        assert_eq!(StringPolicy::from_str("#{pk(A),pk(B),pk(C)}=2").unwrap(), thresh);
        assert_eq!(StringPolicy::from_str("#{ pk(A) , pk(B) , pk(C) }  =  2").unwrap(), thresh);

        // `#{` is a digraph; whitespace between `#` and `{` is rejected.
        assert!(StringPolicy::from_str("# {pk(A), pk(B), pk(C)} = 2").is_err());
    }

    fn roundtrip(s: &str) {
        let policy = StringPolicy::from_str(s).unwrap();
        assert_eq!(StringPolicy::from_str(&policy.to_string()).unwrap(), policy);
    }

    #[test]
    fn display_roundtrip() {
        roundtrip("TRIVIAL");
        roundtrip("UNSATISFIABLE");
        roundtrip("pk(A)");
        roundtrip("after(100)");
        roundtrip("older(50)");
        roundtrip("(pk(A) ∧ pk(B))");
        roundtrip("(pk(A) ∨ pk(B))");
        roundtrip("(pk(A) ∧ pk(B) ∧ pk(C))");
        roundtrip("(pk(A) ∨ pk(B) ∨ pk(C))");
        roundtrip("((pk(A) ∧ pk(B)) ∨ pk(C))");
        roundtrip("#{pk(A), pk(B), pk(C)} = 2");
        roundtrip("(pk(A) ∧ #{pk(B), pk(C), pk(D)} = 2)");
        // Display always emits the mathematical form, so feeding it the
        // function-call form exercises the parser → Display → parser path.
        roundtrip("or(and(pk(A),pk(B)),pk(C))");
        roundtrip("thresh(2,pk(A),pk(B),pk(C))");
    }

    #[test]
    fn semantic_analysis() {
        let policy = StringPolicy::from_str("pk()").unwrap();
        assert_eq!(policy, Policy::Key("".to_owned()));
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.clone().at_age(RelLockTime::ZERO.into()), policy);
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(10000).unwrap().into()),
            policy
        );
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(1));

        let policy = StringPolicy::from_str("older(1000)").unwrap();
        assert_eq!(policy, Policy::Older(RelLockTime::from_height(1000).unwrap()));
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.relative_timelocks(), vec![1000]);
        assert_eq!(policy.clone().at_age(RelLockTime::ZERO.into()), Policy::Unsatisfiable);
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(999).unwrap().into()),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(1000).unwrap().into()),
            policy
        );
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(10000).unwrap().into()),
            policy
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        let policy = StringPolicy::from_str("or(pk(),older(1000))").unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(Threshold::or(
                Policy::Key("".to_owned()).into(),
                Policy::Older(RelLockTime::from_height(1000).unwrap()).into(),
            ))
        );
        assert_eq!(policy.relative_timelocks(), vec![1000]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.clone().at_age(RelLockTime::ZERO.into()), Policy::Key("".to_owned()));
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(999).unwrap().into()),
            Policy::Key("".to_owned())
        );
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(1000).unwrap().into()),
            policy.clone().normalized()
        );
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(10000).unwrap().into()),
            policy.clone().normalized()
        );
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        let policy = StringPolicy::from_str("or(pk(),UNSATISFIABLE)").unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(Threshold::or(
                Policy::Key("".to_owned()).into(),
                Policy::Unsatisfiable.into()
            ))
        );
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(1));

        let policy = StringPolicy::from_str("and(pk(),UNSATISFIABLE)").unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(Threshold::and(
                Policy::Key("".to_owned()).into(),
                Policy::Unsatisfiable.into()
            ))
        );
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), None);

        let policy = StringPolicy::from_str(
            "thresh(\
             2,older(1000),older(10000),older(1000),older(2000),older(2000)\
             )",
        )
        .unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(
                Threshold::new(
                    2,
                    vec![
                        Policy::Older(RelLockTime::from_height(1000).unwrap()).into(),
                        Policy::Older(RelLockTime::from_height(10000).unwrap()).into(),
                        Policy::Older(RelLockTime::from_height(1000).unwrap()).into(),
                        Policy::Older(RelLockTime::from_height(2000).unwrap()).into(),
                        Policy::Older(RelLockTime::from_height(2000).unwrap()).into(),
                    ]
                )
                .unwrap()
            )
        );
        assert_eq!(
            policy.relative_timelocks(),
            vec![1000, 2000, 10000] //sorted and dedup'd
        );

        let policy = StringPolicy::from_str(
            "thresh(\
             2,older(1000),older(10000),older(1000),UNSATISFIABLE,UNSATISFIABLE\
             )",
        )
        .unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(
                Threshold::new(
                    2,
                    vec![
                        Policy::Older(RelLockTime::from_height(1000).unwrap()).into(),
                        Policy::Older(RelLockTime::from_height(10000).unwrap()).into(),
                        Policy::Older(RelLockTime::from_height(1000).unwrap()).into(),
                        Policy::Unsatisfiable.into(),
                        Policy::Unsatisfiable.into(),
                    ]
                )
                .unwrap()
            )
        );
        assert_eq!(
            policy.relative_timelocks(),
            vec![1000, 10000] //sorted and dedup'd
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        // Block height 1000.
        let policy = StringPolicy::from_str("after(1000)").unwrap();
        assert_eq!(policy, Policy::After(AbsLockTime::from_consensus(1000).unwrap()));
        assert_eq!(policy.absolute_timelocks(), vec![1000]);
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.clone().at_lock_time(absolute::LockTime::ZERO), Policy::Unsatisfiable);
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(999).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(1000).expect("valid block height")),
            policy
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(10000).expect("valid block height")),
            policy
        );
        // Pass a UNIX timestamp to at_lock_time while policy uses a block height.
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_001).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        // UNIX timestamp of 10 seconds after the epoch.
        let policy = StringPolicy::from_str("after(500000010)").unwrap();
        assert_eq!(policy, Policy::After(AbsLockTime::from_consensus(500_000_010).unwrap()));
        assert_eq!(policy.absolute_timelocks(), vec![500_000_010]);
        assert_eq!(policy.relative_timelocks(), vec![]);
        // Pass a block height to at_lock_time while policy uses a UNIX timestapm.
        assert_eq!(policy.clone().at_lock_time(absolute::LockTime::ZERO), Policy::Unsatisfiable);
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(999).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(1000).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(10000).expect("valid block height")),
            Policy::Unsatisfiable
        );
        // And now pass a UNIX timestamp to at_lock_time while policy also uses a timestamp.
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_000).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_001).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_010).expect("valid timestamp")),
            policy
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_012).expect("valid timestamp")),
            policy
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));
    }

    #[test]
    fn policy_diff() {
        let pol1 = StringPolicy::from_str("or(pk(A),pk(C))").unwrap();
        let pol2 = StringPolicy::from_str("or(pk(B),pk(C))").unwrap();
        let diff = PolicyDiff::new(pol1.clone(), pol2.clone());
        assert_eq!(
            diff,
            PolicyDiff::new(
                StringPolicy::from_str("pk(A)").unwrap(),
                StringPolicy::from_str("pk(B)").unwrap(),
            )
        );
        assert_eq!(diff.a, vec![StringPolicy::from_str("pk(A)").unwrap()]);
        assert_eq!(diff.b, vec![StringPolicy::from_str("pk(B)").unwrap()]);

        // The order of threshold children does not matter.
        let pol1 = StringPolicy::from_str("or(pk(A),pk(C))").unwrap();
        let pol2 = StringPolicy::from_str("or(pk(C),and(pk(B),older(9)))").unwrap();
        let diff = PolicyDiff::new(pol1, pol2);
        assert_eq!(
            diff,
            PolicyDiff::new(
                StringPolicy::from_str("pk(A)").unwrap(),
                StringPolicy::from_str("and(pk(B),older(9))").unwrap(),
            )
        );

        // Identical policies have an empty difference.
        let pol = StringPolicy::from_str("or(pk(A),and(pk(B),older(9)))").unwrap();
        let diff = PolicyDiff::new(pol.clone(), pol);
        assert_eq!(diff, PolicyDiff { a: vec![], b: vec![] });

        // Duplicated children are matched up one-for-one.
        let pol1 = StringPolicy::from_str("or(pk(A),pk(A))").unwrap();
        let pol2 = StringPolicy::from_str("or(pk(A),pk(B))").unwrap();
        let diff = PolicyDiff::new(pol1, pol2);
        assert_eq!(diff.a, vec![StringPolicy::from_str("pk(A)").unwrap()]);
        assert_eq!(diff.b, vec![StringPolicy::from_str("pk(B)").unwrap()]);

        // Thresholds with different `k` or `n` compare wholesale.
        let pol1 = StringPolicy::from_str("or(pk(A),pk(C))").unwrap();
        let pol2 = StringPolicy::from_str("and(pk(A),pk(C))").unwrap();
        let diff = PolicyDiff::new(pol1.clone(), pol2.clone());
        assert_eq!(diff, PolicyDiff { a: vec![pol1], b: vec![pol2] });

        // Combining differences concatenates both sides.
        let mut diff1 = PolicyDiff::new(
            StringPolicy::from_str("pk(A)").unwrap(),
            StringPolicy::from_str("pk(B)").unwrap(),
        );
        let diff2 = PolicyDiff::new(
            StringPolicy::from_str("pk(C)").unwrap(),
            StringPolicy::from_str("pk(D)").unwrap(),
        );
        diff1.combine(diff2);
        assert_eq!(
            diff1,
            PolicyDiff {
                a: vec![
                    StringPolicy::from_str("pk(A)").unwrap(),
                    StringPolicy::from_str("pk(C)").unwrap()
                ],
                b: vec![
                    StringPolicy::from_str("pk(B)").unwrap(),
                    StringPolicy::from_str("pk(D)").unwrap()
                ],
            }
        );
    }

    #[test]
    fn policy_tree_string() {
        let pol =
            StringPolicy::from_str("or(pk(A),and(pk(B),older(9)),thresh(2,pk(C),pk(D),pk(E)))")
                .unwrap();
        let expected = "\
`-- or
    |-- pk(A)
    |-- and
    |   |-- pk(B)
    |   `-- older(9)
    `-- thresh(2)
        |-- pk(C)
        |-- pk(D)
        `-- pk(E)";
        assert_eq!(pol.to_tree_string(), expected);

        // Leaves render as a single line.
        let pol = StringPolicy::from_str("pk(A)").unwrap();
        assert_eq!(pol.to_tree_string(), "`-- pk(A)");
    }

    #[test]
    fn policy_diff_string() {
        let pol1 = StringPolicy::from_str("or(pk(A),pk(C))").unwrap();
        let pol2 = StringPolicy::from_str("or(pk(C),and(pk(B),older(9)))").unwrap();
        let expected = "\
`-- or
    |-- - pk(A)
    |-- + and
    |   |-- pk(B)
    |   `-- older(9)
    `-- pk(C)";
        assert_eq!(pol1.to_diff_string(&pol2), expected);

        // Identical policies render as a single unmarked tree.
        let pol = StringPolicy::from_str("or(pk(A),pk(C))").unwrap();
        assert_eq!(pol.to_diff_string(&pol.clone()), pol.to_tree_string());

        // Policies with nothing in common render as a `- `/`+ ` pair.
        let pol1 = StringPolicy::from_str("pk(A)").unwrap();
        let pol2 = StringPolicy::from_str("older(9)").unwrap();
        let expected = "\
`-- - pk(A)
`-- + older(9)";
        assert_eq!(pol1.to_diff_string(&pol2), expected);

        // Differences nested inside shared structure are recursed into.
        let pol1 = StringPolicy::from_str("or(pk(A),and(pk(B),older(9)))").unwrap();
        let pol2 = StringPolicy::from_str("or(pk(A),and(pk(B),older(10)))").unwrap();
        let expected = "\
`-- or
    |-- pk(A)
    `-- and
        |-- pk(B)
        `-- - older(9)
        `-- + older(10)";
        assert_eq!(pol1.to_diff_string(&pol2), expected);
    }

    #[test]
    fn entailment_liquid_test() {
        //liquid policy
        let liquid_pol = StringPolicy::from_str(
            "or(and(older(4096),thresh(2,pk(A),pk(B),pk(C))),thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14)))").unwrap();
        // Very bad idea to add master key,pk but let's have it have 50M blocks
        let master_key = StringPolicy::from_str("and(older(50000000),pk(master))").unwrap();
        let new_liquid_pol =
            Policy::Thresh(Threshold::or(liquid_pol.clone().into(), master_key.into()));

        assert!(liquid_pol.clone().entails(new_liquid_pol.clone()).unwrap());
        assert!(!new_liquid_pol.entails(liquid_pol.clone()).unwrap());

        // test liquid backup policy before the emergency timeout
        let backup_policy = StringPolicy::from_str("thresh(2,pk(A),pk(B),pk(C))").unwrap();
        assert!(!backup_policy
            .entails(
                liquid_pol
                    .clone()
                    .at_age(RelLockTime::from_height(4095).unwrap().into())
            )
            .unwrap());

        // Finally test both spending paths
        let fed_pol = StringPolicy::from_str("thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14))").unwrap();
        let backup_policy_after_expiry =
            StringPolicy::from_str("and(older(4096),thresh(2,pk(A),pk(B),pk(C)))").unwrap();
        assert!(fed_pol.entails(liquid_pol.clone()).unwrap());
        assert!(backup_policy_after_expiry.entails(liquid_pol).unwrap());
    }

    #[test]
    fn entailment_escrow() {
        // Escrow contract
        let escrow_pol = StringPolicy::from_str("thresh(2,pk(Alice),pk(Bob),pk(Judge))").unwrap();
        // Alice's authorization constraint
        // Authorization is a constraint that states the conditions under which one party must
        // be able to redeem the funds.
        let auth_alice = StringPolicy::from_str("and(pk(Alice),pk(Judge))").unwrap();

        //Alice's Control constraint
        // The control constraint states the conditions that one party requires
        // must be met if the funds are spent by anyone
        // Either Alice must authorize the funds or both Judge and Bob must control it
        let control_alice = StringPolicy::from_str("or(pk(Alice),and(pk(Judge),pk(Bob)))").unwrap();

        // Entailment rules
        // Authorization entails |- policy |- control constraints
        assert!(auth_alice.entails(escrow_pol.clone()).unwrap());
        assert!(escrow_pol.entails(control_alice).unwrap());

        // Entailment HTLC's
        // Escrow contract
        let h = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let htlc_pol = StringPolicy::from_str(&format!(
            "or(and(pk(Alice),older(100)),and(pk(Bob),sha256({})))",
            h
        ))
        .unwrap();
        // Alice's authorization constraint
        // Authorization is a constraint that states the conditions under which one party must
        // be able to redeem the funds. In HLTC, alice only cares that she can
        // authorize her funds with Pk and CSV 100.
        let auth_alice = StringPolicy::from_str("and(pk(Alice),older(100))").unwrap();

        //Alice's Control constraint
        // The control constraint states the conditions that one party requires
        // must be met if the funds are spent by anyone
        // Either Alice must authorize the funds or sha2 preimage must be revealed.
        let control_alice =
            StringPolicy::from_str(&format!("or(pk(Alice),sha256({}))", h)).unwrap();

        // Entailment rules
        // Authorization entails |- policy |- control constraints
        assert!(auth_alice.entails(htlc_pol.clone()).unwrap());
        assert!(htlc_pol.entails(control_alice).unwrap());
    }

    #[test]
    fn for_each_key() {
        let liquid_pol = StringPolicy::from_str(
            "or(and(older(4096),thresh(2,pk(A),pk(B),pk(C))),thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14)))").unwrap();
        let mut count = 0;
        assert!(liquid_pol.for_each_key(|_| {
            count += 1;
            true
        }));
        assert_eq!(count, 17);
    }
}
