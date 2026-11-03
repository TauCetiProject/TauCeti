/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Logic.Equiv.List
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Baire.BaireMeasurable
public import TauCeti.SetTheory.Descriptive.BorelColoring
public import TauCeti.Topology.Instances.CantorSpace
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Topology.Baire.LocallyCompactRegular

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

Miller's independence lemma `exists_mem_orientedGS_of_not_isMeagre` says that for dense `S`
every non-meagre subset of Cantor space with the Baire property contains an oriented edge.
Consequently, for dense `S`:

* `isMeagre_of_isIndepSet_gSGraph`: independent sets with the Baire property are meagre;
* `exists_not_baireMeasurableSet_colorClass`: a coloring of `gSGraph S` by countably many colors
  has a color class without the Baire property, so `orientedGS S` has no countable Borel
  coloring (`not_hasCountableBorelColoring_orientedGS`) and `gSGraph S` has no measurable
  coloring by `ℕ`; and no relation `G` receiving a measurable map that sends the oriented edges
  of `orientedGS S` to pairs of `G` has a countable Borel coloring
  (`not_hasCountableBorelColoring_of_orientedGS_hom`);
* `isMeagre_setOf_comp_of_forall_gSGraph_adj`: if a measurable map `φ` sends the edges of
  `gSGraph S` to inequivalent pairs of an equivalence relation `E` with measurable classes, then
  every section `{b | E (φ a) (φ b)}` of the pulled-back relation is meagre.

The last statement is what makes pulled-back relations meagre, through the Kuratowski–Ulam
theorem, in the category proof of Silver's theorem. For the canonical words, G₀ itself has no
measurable coloring by `ℕ` (`not_exists_measurable_coloring_gZero`).

Density cannot be dropped. A dense word set has words of infinitely many lengths
(`DenseWords.infinite_image_length`), and when the words of `S` have only finitely many lengths,
the parity of the coordinates at those lengths changes along every edge. So `gSGraph S` then has
a continuous coloring by `Bool` (`exists_continuous_coloring_gSGraph`), and `orientedGS S` has a
countable Borel coloring (`hasCountableBorelColoring_orientedGS`). For `S = {[]}`, which is
sparse, this coloring is the first coordinate.

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
theorem orientedGS_eq_biUnion (S : Set (List Bool)) :
    orientedGS S = ⋃ s ∈ S, range (fun x : ℕ → Bool =>
      (prependWord (s ++ [false]) x, prependWord (s ++ [true]) x)) := by
  ext p
  simp [orientedGS, eq_comm]

/-- The edges contributed by one word form a closed set. -/
theorem isClosed_orientedGS_singleton (s : List Bool) : IsClosed (orientedGS {s}) := by
  have hc := isCompact_range ((continuous_prependWord (s ++ [false])).prodMk
    (continuous_prependWord (s ++ [true])))
  simpa [orientedGS_eq_biUnion] using hc.isClosed

/-- The oriented edge relation is Fσ, expressed as a Gδ complement. -/
theorem isGδ_compl_orientedGS (S : Set (List Bool)) : IsGδ (orientedGS S)ᶜ := by
  rw [orientedGS_eq_biUnion, compl_iUnion]
  refine IsGδ.iInter fun s => ?_
  rw [compl_iUnion]
  refine IsGδ.iInter fun _ => ?_
  simpa only [orientedGS_eq_biUnion, Set.biUnion_singleton] using
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

/-- A dense word set has words of infinitely many lengths. -/
theorem DenseWords.infinite_image_length (h : DenseWords S) : (List.length '' S).Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨s, hs, hrs⟩ := denseWords_iff.1 h (List.replicate (N + 1) false)
  have := hrs.length_le.trans (hN (mem_image_of_mem _ hs))
  simp at this

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

/-- The canonical word at every stage belongs to the canonical word set. -/
theorem canonicalWord_mem_canonicalWords (n : ℕ) : canonicalWord n ∈ canonicalWords :=
  mem_range_self n

/-- Every finite word extends to a canonical word. -/
theorem denseWords_canonicalWords : DenseWords canonicalWords := by
  intro r
  exact ⟨_, mem_range_self (Nat.pair (Encodable.encode r) r.length),
    prefix_canonicalWord_pair r le_rfl⟩

/-- There is only one canonical word of each length. -/
theorem sparseWords_canonicalWords : SparseWords canonicalWords := by
  rintro s ⟨m, rfl⟩ t ⟨n, rfl⟩ h
  simpa using congrArg canonicalWord (by simpa using h : m = n)

/-- There is exactly one canonical word of each length. -/
theorem exists_unique_mem_canonicalWords_length (n : ℕ) :
    ∃! s, s ∈ canonicalWords ∧ s.length = n := by
  refine ⟨canonicalWord n, ⟨canonicalWord_mem_canonicalWords n, length_canonicalWord n⟩, ?_⟩
  intro s hs
  exact sparseWords_canonicalWords hs.1 (canonicalWord_mem_canonicalWords n)
    (hs.2.trans (length_canonicalWord n).symm)

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

/-! ## Miller's independence lemma -/

section Independence

variable {A : Set (ℕ → Bool)}

/-- **Miller's independence lemma.** If every word extends to a word of `S`, then every
non-meagre subset of Cantor space with the Baire property contains both ends of an oriented
edge of `orientedGS S`. -/
theorem exists_mem_orientedGS_of_not_isMeagre (hS : DenseWords S) (hA : BaireMeasurableSet A)
    (hn : ¬ IsMeagre A) : ∃ a ∈ A, ∃ b ∈ A, (a, b) ∈ orientedGS S := by
  -- `A` differs from an open set `u` by a meagre set, so `u` is nonempty.
  obtain ⟨u, hu, hAu⟩ := hA.residualEq_isOpen
  have huA : IsMeagre (u \ A) := hAu.mono fun _ hx hxuA ↦ hxuA.2 ((iff_of_eq hx).2 hxuA.1)
  have hAu' : IsMeagre (A \ u) := hAu.mono fun _ hx hxAu ↦ hxAu.2 ((iff_of_eq hx).1 hxAu.1)
  obtain ⟨x, hx⟩ : u.Nonempty :=
    nonempty_of_not_isMeagre fun h ↦ hn ((hAu'.union h).mono (subset_sdiff_union A u))
  -- By density, `u` contains the cylinder of a word `s ∈ S`.
  obtain ⟨_, ⟨y, n, rfl⟩, -, hyu⟩ :=
    (isTopologicalBasis_cylinders fun _ ↦ Bool).exists_subset_of_mem_open hx hu
  obtain ⟨s, hs, hrs⟩ := hS (res y n).reverse
  have hsu : wordCylinder s ⊆ u :=
    hrs.wordCylinder_subset.trans ((wordCylinder_reverse_res y n).trans_subset hyu)
  -- The flip at `s.length` carries the `false` half of `wordCylinder s` onto the `true` half, so
  -- some point of the `false` half lies, together with its flip, outside `u \ A`.
  set f := flipAt s.length
  have hf : f '' wordCylinder (s ++ [false]) ⊆ wordCylinder s := by
    rw [image_flipAt_wordCylinder_append_singleton]
    exact (List.prefix_append s [!false]).wordCylinder_subset
  obtain ⟨a, ha, haM⟩ : (wordCylinder (s ++ [false]) \ (u \ A ∪ f ⁻¹' (u \ A))).Nonempty := by
    refine nonempty_of_not_isMeagre fun h ↦
      not_isMeagre_of_isOpen (isOpen_wordCylinder (s ++ [false])) (wordCylinder_nonempty _) ?_
    exact (h.union (huA.union (huA.preimage_of_isOpenMap f.continuous f.isOpenMap))).mono
      (subset_sdiff_union _ _)
  rw [mem_union, not_or, mem_preimage] at haM
  refine ⟨a, ?_, f a, ?_, mem_orientedGS_iff_exists_flipAt.2 ⟨s, hs, ha, rfl⟩⟩
  · by_contra haA
    exact haM.1 ⟨hsu ((List.prefix_append s [false]).wordCylinder_subset ha), haA⟩
  · by_contra haA
    exact haM.2 ⟨hsu (hf (mem_image_of_mem f ha)), haA⟩

/-- **Miller's independence lemma**, for the simple graph: if `S` is dense, then every
non-meagre subset of Cantor space with the Baire property contains two adjacent points of
`gSGraph S`. -/
theorem exists_gSGraph_adj_of_not_isMeagre (hS : DenseWords S) (hA : BaireMeasurableSet A)
    (hn : ¬ IsMeagre A) : ∃ a ∈ A, ∃ b ∈ A, (gSGraph S).Adj a b :=
  let ⟨a, ha, b, hb, hab⟩ := exists_mem_orientedGS_of_not_isMeagre hS hA hn
  ⟨a, ha, b, hb, gSGraph_adj_iff.2 (.inl hab)⟩

/-- If `S` is dense, then every independent set of `gSGraph S` with the Baire property is
meagre. -/
theorem isMeagre_of_isIndepSet_gSGraph (hS : DenseWords S) (hA : BaireMeasurableSet A)
    (hind : (gSGraph S).IsIndepSet A) : IsMeagre A := by
  by_contra hn
  obtain ⟨a, ha, b, hb, hab⟩ := exists_gSGraph_adj_of_not_isMeagre hS hA hn
  exact hind ha hb hab.ne hab

/-- If `S` is dense, then every coloring of `gSGraph S` by countably many colors has a color
class without the Baire property. -/
theorem exists_not_baireMeasurableSet_colorClass (hS : DenseWords S) {ι : Type*} [Countable ι]
    (c : (gSGraph S).Coloring ι) : ∃ i, ¬ BaireMeasurableSet (c.colorClass i) := by
  by_contra! h
  -- The color classes would be countably many meagre sets covering Cantor space.
  refine not_isMeagre_of_isOpen (s := (univ : Set (ℕ → Bool))) isOpen_univ univ_nonempty ?_
  refine (isMeagre_iUnion fun i ↦
    isMeagre_of_isIndepSet_gSGraph hS (h i) (c.isIndepSet_colorClass i)).mono fun x _ ↦ ?_
  exact mem_iUnion.2 ⟨c x, c.mem_colorClass x⟩

/-- If `S` is dense, then the oriented graph `orientedGS S` has no countable Borel coloring. -/
theorem not_hasCountableBorelColoring_orientedGS (hS : DenseWords S) :
    ¬ SetRel.HasCountableBorelColoring (orientedGS S) := by
  intro h
  obtain ⟨c, hc, hcol⟩ := SetRel.hasCountableBorelColoring_iff.1 h
  let c' : (gSGraph S).Coloring ℕ := SimpleGraph.Coloring.mk c fun hab ↦
    (gSGraph_adj_iff.1 hab).elim (fun h ↦ hcol h) fun h ↦ (hcol h).symm
  obtain ⟨n, hn⟩ := exists_not_baireMeasurableSet_colorClass hS c'
  -- The color class `c'.colorClass n` is `{x | c x = n}`, which is the preimage `c ⁻¹' {n}`.
  exact hn (hc (measurableSet_singleton n)).baireMeasurableSet

/-- If every word extends to a word of `S` and a measurable map of Cantor space sends every
oriented edge of `orientedGS S` to a pair of `G`, then `G` has no countable Borel coloring. This
is the exclusivity half of the G₀ dichotomy. -/
theorem not_hasCountableBorelColoring_of_orientedGS_hom {X : Type*} [MeasurableSpace X]
    {G : SetRel X X} (hS : DenseWords S) {φ : (ℕ → Bool) → X} (hφ : Measurable φ)
    (hφG : ∀ ⦃y z⦄, (y, z) ∈ orientedGS S → (φ y, φ z) ∈ G) :
    ¬ G.HasCountableBorelColoring := fun h ↦
  not_hasCountableBorelColoring_orientedGS hS ((h.preimage hφ).mono fun _ hp ↦ hφG hp)

/-- If `S` is dense, then `gSGraph S` has no measurable coloring by `ℕ`. -/
theorem not_exists_measurable_coloring_gSGraph (hS : DenseWords S) :
    ¬ ∃ c : (gSGraph S).Coloring ℕ, Measurable c := fun h ↦
  not_hasCountableBorelColoring_orientedGS hS <|
    ((SimpleGraph.hasCountableBorelColoring_adj_iff _).2 h).mono fun _ hp ↦
      gSGraph_adj_iff.2 (.inl hp)

/-- If `S` is dense and no edge of `gSGraph S` joins two `E`-equivalent points, then every
class of `E` with the Baire property is meagre. -/
theorem isMeagre_setOf_of_forall_gSGraph_adj (hS : DenseWords S) {E : Setoid (ℕ → Bool)}
    (hE : ∀ ⦃a b⦄, (gSGraph S).Adj a b → ¬ E a b) {a : ℕ → Bool}
    (ha : BaireMeasurableSet {b | E a b}) : IsMeagre {b | E a b} :=
  isMeagre_of_isIndepSet_gSGraph hS ha fun _ hb _ hc _ hbc ↦ hE hbc (E.trans (E.symm hb) hc)

/-- Let `E` be an equivalence relation with measurable classes and `φ` a measurable map from
Cantor space sending the edges of `gSGraph S` to `E`-inequivalent pairs. If `S` is dense, then
every section `{b | E (φ a) (φ b)}` of the pulled-back relation is meagre. -/
theorem isMeagre_setOf_comp_of_forall_gSGraph_adj (hS : DenseWords S) {X : Type*}
    [MeasurableSpace X] {E : Setoid X} (hE : ∀ x, MeasurableSet {y | E x y})
    {φ : (ℕ → Bool) → X} (hφ : Measurable φ)
    (hφE : ∀ ⦃a b⦄, (gSGraph S).Adj a b → ¬ E (φ a) (φ b)) (a : ℕ → Bool) :
    IsMeagre {b | E (φ a) (φ b)} :=
  isMeagre_of_isIndepSet_gSGraph hS (hφ (hE (φ a))).baireMeasurableSet
    fun _ hb _ hc _ hbc ↦ hφE hbc (E.trans (E.symm hb) hc)

/-- The Kechris–Solecki–Todorcevic graph G₀ has no measurable coloring by `ℕ`. -/
theorem not_exists_measurable_coloring_gZero : ¬ ∃ c : gZero.Coloring ℕ, Measurable c :=
  not_exists_measurable_coloring_gSGraph denseWords_canonicalWords

end Independence

/-! ## Word sets with finitely many lengths -/

/-- If the words of `S` have only finitely many lengths, then `gSGraph S` has a continuous
coloring by `Bool`: the parity of the coordinates at those lengths. In particular, `gSGraph S` is
two-colorable, although `S` may be sparse. -/
theorem exists_continuous_coloring_gSGraph (hS : (List.length '' S).Finite) :
    ∃ c : (gSGraph S).Coloring Bool, Continuous c := by
  set L := hS.toFinset
  -- An edge flips one coordinate in `L`, so it changes the sum in `Bool`, where `+` is `xor`.
  have hedge {a b : ℕ → Bool} (h : (a, b) ∈ orientedGS S) : ∑ n ∈ L, a n ≠ ∑ n ∈ L, b n := by
    obtain ⟨s, hs, -, rfl⟩ := mem_orientedGS_iff_exists_flipAt.1 h
    have hm : s.length ∈ L := hS.mem_toFinset.2 (mem_image_of_mem _ hs)
    rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm,
      Finset.sum_congr rfl fun n hn ↦ flipAt_apply_of_ne (Finset.ne_of_mem_erase hn) a]
    simp [flipAt_apply_self]
  refine ⟨SimpleGraph.Coloring.mk (fun x ↦ ∑ n ∈ L, x n) fun hab ↦ ?_,
    continuous_finsetSum _ fun n _ ↦ continuous_apply n⟩
  exact (gSGraph_adj_iff.1 hab).elim hedge fun h ↦ (hedge h).symm

/-- If the words of `S` have only finitely many lengths, then the oriented graph `orientedGS S`
has a countable Borel coloring. Since `{[]}` is such a word set and is sparse, the density
hypothesis of `not_hasCountableBorelColoring_orientedGS` cannot be dropped, even for sparse word
sets. -/
theorem hasCountableBorelColoring_orientedGS (hS : (List.length '' S).Finite) :
    SetRel.HasCountableBorelColoring (orientedGS S) := by
  obtain ⟨c, hc⟩ := exists_continuous_coloring_gSGraph hS
  refine SetRel.hasCountableBorelColoring_iff.2
    ⟨fun x ↦ Encodable.encode (c x), (measurable_of_countable _).comp hc.measurable,
      fun _ _ hab heq ↦ c.valid (gSGraph_adj_iff.2 (.inl hab)) (Encodable.encode_injective heq)⟩

end TauCeti
