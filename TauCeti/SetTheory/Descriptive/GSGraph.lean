/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Logic.Equiv.List
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Topology.Instances.CantorSpace

/-!
# The graphs G_S and G₀ on Cantor space

For a set `S` of finite binary words, `orientedGS S` joins `s ⌢ false ⌢ x` to
`s ⌢ true ⌢ x`, for `s ∈ S` and a common infinite tail `x`. Its symmetrization is the
simple graph `gSGraph S`. Each word contributes a compact set of edges, so both edge
relations are Fσ and Borel. The endpoints differ at coordinate `s.length`, so
symmetrization removes no edges.

`DenseWords S` means that every word extends to a word of `S`; `SparseWords S` means
that `S` has at most one word of each length. Density is the hypothesis in Miller's
independence lemma, while sparseness permits a fusion construction to add at most one
new edge at each level. The explicit `canonicalWords` has both properties, and
`gZero` is its graph, the Kechris–Solecki–Todorcevic graph G₀.

## References

* A. S. Kechris, S. Solecki and S. Todorcevic, *Borel chromatic numbers*, Advances in
  Mathematics 141 (1999), 1–44.
* B. D. Miller, *The graph-theoretic approach to descriptive set theory*, Bulletin of
  Symbolic Logic 18 (2012), 554–575.

The word-and-common-tail description also appears in
`InfinitaryLogic/Descriptive/GSGraph.lean` of `cameronfreer/infinitary-logic`
(Apache-2.0), checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
Here the oriented relation and Mathlib simple graph are separate, and the canonical
words have every natural number as a length.
-/

public section

open Set PiNat

namespace TauCeti

/-- The oriented graph associated to binary words `S`: change the bit just after a word
of `S` from `false` to `true`, keeping the same tail. -/
def orientedGS (S : Set (List Bool)) : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  {p | ∃ s ∈ S, ∃ x : ℕ → Bool,
    p = (prependWord (s ++ [false]) x, prependWord (s ++ [true]) x)}

variable {S T : Set (List Bool)} {a b : ℕ → Bool}

/-- Membership in the oriented graph is witnessed by a word and a common tail. -/
theorem mem_orientedGS_iff : (a, b) ∈ orientedGS S ↔
    ∃ s ∈ S, ∃ x : ℕ → Bool,
      a = prependWord (s ++ [false]) x ∧ b = prependWord (s ++ [true]) x := by
  simp [orientedGS, Prod.mk.injEq]

/-- Every word of `S` and every tail give an oriented edge. -/
theorem prependWord_mem_orientedGS {s : List Bool} (hs : s ∈ S) (x : ℕ → Bool) :
    (prependWord (s ++ [false]) x, prependWord (s ++ [true]) x) ∈ orientedGS S :=
  ⟨s, hs, x, rfl⟩

/-- The two endpoints of an oriented edge are distinct. -/
theorem ne_of_mem_orientedGS (h : (a, b) ∈ orientedGS S) : a ≠ b := by
  obtain ⟨s, _, x, rfl, rfl⟩ := mem_orientedGS_iff.1 h
  intro heq
  have := congrFun heq s.length
  simp [prependWord_apply_of_lt] at this

/-- An oriented edge is the graph of a coordinate flip restricted to the `false` half
of a word cylinder. -/
theorem mem_orientedGS_iff_exists_flipAt : (a, b) ∈ orientedGS S ↔
    ∃ s ∈ S, a ∈ wordCylinder (s ++ [false]) ∧ flipAt s.length a = b := by
  constructor
  · intro h
    obtain ⟨s, hs, x, rfl, rfl⟩ := mem_orientedGS_iff.1 h
    exact ⟨s, hs, prependWord_mem_wordCylinder _ _,
      flipAt_prependWord_append_singleton s false x⟩
  · rintro ⟨s, hs, ha, hab⟩
    rw [← range_prependWord] at ha
    obtain ⟨x, rfl⟩ := ha
    rw [flipAt_prependWord_append_singleton] at hab
    exact mem_orientedGS_iff.2 ⟨s, hs, x, rfl, hab.symm⟩

/-- Enlarging the word set enlarges the oriented graph. -/
theorem orientedGS_mono (h : S ⊆ T) : orientedGS S ⊆ orientedGS T := by
  rintro p ⟨s, hs, x, rfl⟩
  exact ⟨s, h hs, x, rfl⟩

@[simp]
theorem orientedGS_empty : orientedGS ∅ = ∅ := by
  ext p
  simp [orientedGS]

/-- The simple graph obtained by forgetting the orientation of `orientedGS S`. -/
def gSGraph (S : Set (List Bool)) : SimpleGraph (ℕ → Bool) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ orientedGS S

/-- Adjacency is precisely an oriented edge in one of the two directions; no additional
inequality hypothesis is needed. -/
@[simp]
theorem gSGraph_adj_iff : (gSGraph S).Adj a b ↔
    (a, b) ∈ orientedGS S ∨ (b, a) ∈ orientedGS S := by
  rw [gSGraph, SimpleGraph.fromRel_adj]
  exact and_iff_right_of_imp fun h => h.elim ne_of_mem_orientedGS
    (fun h => (ne_of_mem_orientedGS h).symm)

/-- Enlarging the word set enlarges the simple graph. -/
theorem gSGraph_mono (h : S ⊆ T) : gSGraph S ≤ gSGraph T := by
  intro a b hab
  rw [gSGraph_adj_iff] at hab ⊢
  exact hab.imp (fun h' => orientedGS_mono h h') (fun h' => orientedGS_mono h h')

@[simp]
theorem gSGraph_empty : gSGraph ∅ = ⊥ := by
  ext a b
  simp

/-- The oriented graph is a countable union of compact edge sets, one for each word. -/
theorem orientedGS_eq_iUnion (S : Set (List Bool)) :
    orientedGS S = ⋃ s ∈ S, range (fun x : ℕ → Bool =>
      (prependWord (s ++ [false]) x, prependWord (s ++ [true]) x)) := by
  ext p
  simp [orientedGS, eq_comm]

/-- The edges contributed by one word form a closed set. -/
theorem isClosed_orientedGS_singleton (s : List Bool) : IsClosed (orientedGS {s}) := by
  have hc := isCompact_range ((continuous_prependWord (s ++ [false])).prodMk
    (continuous_prependWord (s ++ [true])))
  simpa [orientedGS_eq_iUnion] using hc.isClosed

/-- The oriented edge relation is Fσ, expressed as a Gδ complement. -/
theorem isGδ_compl_orientedGS (S : Set (List Bool)) : IsGδ (orientedGS S)ᶜ := by
  rw [orientedGS_eq_iUnion, compl_iUnion]
  refine IsGδ.iInter fun s => ?_
  rw [compl_iUnion]
  refine IsGδ.iInter fun _ => ?_
  simpa only [orientedGS_eq_iUnion, Set.biUnion_singleton] using
    (isClosed_orientedGS_singleton s).isOpen_compl.isGδ

/-- The oriented edge relation is Borel. -/
theorem measurableSet_orientedGS (S : Set (List Bool)) : MeasurableSet (orientedGS S) := by
  simpa only [compl_compl] using (isGδ_compl_orientedGS S).measurableSet.compl

/-- The unoriented edge relation is Fσ, expressed as a Gδ complement. -/
theorem isGδ_compl_gSGraph (S : Set (List Bool)) :
    IsGδ {p : (ℕ → Bool) × (ℕ → Bool) | (gSGraph S).Adj p.1 p.2}ᶜ := by
  have heq : {p : (ℕ → Bool) × (ℕ → Bool) | (gSGraph S).Adj p.1 p.2} =
      orientedGS S ∪ Prod.swap ⁻¹' orientedGS S := by
    ext ⟨a, b⟩
    simp
  rw [heq, compl_union, ← preimage_compl]
  exact (isGδ_compl_orientedGS S).inter
    ((isGδ_compl_orientedGS S).preimage continuous_swap)

/-- The simple graph has a Borel edge relation. -/
theorem measurableSet_gSGraph (S : Set (List Bool)) :
    MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | (gSGraph S).Adj p.1 p.2} := by
  simpa only [compl_compl] using (isGδ_compl_gSGraph S).measurableSet.compl

/-! ## Dense and sparse words -/

/-- A word set is dense if every word is a prefix of some member. -/
def DenseWords (S : Set (List Bool)) : Prop :=
  ∀ r : List Bool, ∃ s ∈ S, r <+: s

/-- A word set is sparse if it has at most one member of each length. -/
def SparseWords (S : Set (List Bool)) : Prop :=
  S.InjOn List.length

/-- Unfolding the density condition. -/
theorem denseWords_iff : DenseWords S ↔ ∀ r : List Bool, ∃ s ∈ S, r <+: s :=
  Iff.rfl

/-- Unfolding the sparseness condition. -/
theorem sparseWords_iff : SparseWords S ↔
    ∀ s ∈ S, ∀ t ∈ S, s.length = t.length → s = t :=
  Iff.rfl

/-- Density passes to larger word sets. -/
theorem DenseWords.mono (h : DenseWords S) (hST : S ⊆ T) : DenseWords T := by
  intro r
  obtain ⟨s, hs, hrs⟩ := h r
  exact ⟨s, hST hs, hrs⟩

/-- Sparseness passes to smaller word sets. -/
theorem SparseWords.mono (h : SparseWords T) (hST : S ⊆ T) : SparseWords S :=
  Set.InjOn.mono hST h

/-- Decode the first component of `Nat.unpair n`, then pad the decoded word with `false`
to length `n`. If decoding fails or the word is too long, use the all-`false` word. -/
def canonicalWord (n : ℕ) : List Bool :=
  let r := (Encodable.decode (α := List Bool) (Nat.unpair n).1).getD []
  if r.length ≤ n then r ++ List.replicate (n - r.length) false
  else List.replicate n false

/-- The canonical word at stage `n` has length exactly `n`. -/
@[simp]
theorem length_canonicalWord (n : ℕ) : (canonicalWord n).length = n := by
  simp only [canonicalWord]
  split_ifs <;> simp_all

/-- Coding a word in the first component of a sufficiently large pair produces an extension
of that word. -/
theorem prefix_canonicalWord_pair (r : List Bool) {k : ℕ} (hk : r.length ≤ k) :
    r <+: canonicalWord (Nat.pair (Encodable.encode r) k) := by
  have hle : r.length ≤ Nat.pair (Encodable.encode r) k := hk.trans (Nat.right_le_pair _ _)
  simp [canonicalWord, hle, List.prefix_append]

/-- Canonical words are distinguished by their lengths. -/
theorem canonicalWord_injective : Function.Injective canonicalWord := by
  intro m n h
  simpa using congrArg List.length h

/-- The canonical dense sparse word set defining G₀. -/
def canonicalWords : Set (List Bool) := range canonicalWord

@[simp]
theorem mem_canonicalWords_iff {s : List Bool} :
    s ∈ canonicalWords ↔ ∃ n, canonicalWord n = s :=
  Iff.rfl

/-- Every finite word extends to a canonical word. -/
theorem denseWords_canonicalWords : DenseWords canonicalWords := by
  intro r
  exact ⟨_, mem_range_self (Nat.pair (Encodable.encode r) r.length),
    prefix_canonicalWord_pair r le_rfl⟩

/-- There is only one canonical word of each length. -/
theorem sparseWords_canonicalWords : SparseWords canonicalWords := by
  rintro s ⟨m, rfl⟩ t ⟨n, rfl⟩ h
  simpa using congrArg canonicalWord (by simpa using h : m = n)

/-- The unique canonical word of length `n` is `canonicalWord n`. -/
theorem mem_canonicalWords_iff_eq_canonicalWord {s : List Bool} :
    s ∈ canonicalWords ↔ s = canonicalWord s.length := by
  constructor
  · rintro ⟨n, rfl⟩
    simp
  · intro h
    exact ⟨s.length, h.symm⟩

/-- The Kechris–Solecki–Todorcevic graph G₀ on Cantor space. -/
def gZero : SimpleGraph (ℕ → Bool) := gSGraph canonicalWords

/-- G₀ has exactly the two orientations of the canonical word edges. -/
@[simp]
theorem gZero_adj_iff : gZero.Adj a b ↔
    (a, b) ∈ orientedGS canonicalWords ∨ (b, a) ∈ orientedGS canonicalWords :=
  gSGraph_adj_iff

end TauCeti
