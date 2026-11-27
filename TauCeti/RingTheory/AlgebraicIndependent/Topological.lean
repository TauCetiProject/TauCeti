/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.FieldTheory.IntermediateField.Adjoin.AlgebraicIndependent
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# Topological transcendence degree and topological algebraic independence

For a field extension `L / K` where `L` carries a topology, the *topological transcendence
degree* `TauCeti.topologicalTrdeg K L : ℕ∞` is the smallest transcendence degree over `K` of an
intermediate field `K ⊆ A ⊆ L` that is dense in `L`; it is `⊤` when no dense intermediate field
has finite transcendence degree. Equivalently, it is the infimum of the natural numbers `n` for
which some dense intermediate field has `Algebra.trdeg K A ≤ n`.

For extensions of complete algebraically closed nonarchimedean fields this is the invariant of
Scholze, *Étale cohomology of diamonds*, Definition 21.2, used there to bound the
cohomological dimension of points of diamonds. Unlike `Algebra.trdeg K L`, it sees the
topology: the algebraic closure of `ℚ_p` is dense in `ℂ_p`, so the topological transcendence
degree of `ℂ_p` over `ℚ_p` is zero, although `ℂ_p` has infinite transcendence degree over `ℚ_p`.

Temkin's dual notion measures independence instead of generation. A set `s ⊆ L` is
*topologically algebraically independent* over `K` (`TauCeti.IsTopAlgIndependent`) if no
`x ∈ s` lies in the closure of the elements of `L` algebraic over `K(s \ {x})`, and the
*topological independence degree* `TauCeti.topologicalIndependenceDegree K L : ℕ∞` is the
supremum of the sizes of finite such sets. For extensions of complete algebraically closed
nonarchimedean fields of finite topological transcendence degree, Temkin shows that the two
degrees agree; for an arbitrary topology both vanish under the same condition, density of the
algebraic elements.

## Main declarations

* `TauCeti.topologicalTrdeg K L`: the topological transcendence degree.
* `TauCeti.exists_dense_toENat_trdeg_eq_topologicalTrdeg`: the infimum is attained by a dense
  intermediate field.
* `TauCeti.topologicalTrdeg_le_natCast_iff`: `topologicalTrdeg K L ≤ n` if and only if some dense
  intermediate field has transcendence degree at most `n`.
* `TauCeti.topologicalTrdeg_eq_top_iff`: the value is `⊤` if and only if every dense intermediate
  field has infinite transcendence degree.
* `TauCeti.topologicalTrdeg_eq_zero_iff`: the value is zero if and only if some dense
  intermediate field is algebraic over `K`.
* `TauCeti.topologicalTrdeg_le_of_continuous_of_denseRange`: a continuous `K`-algebra map with
  dense range does not increase the invariant; in particular it is invariant under continuous
  `K`-algebra isomorphisms (`ContinuousAlgEquiv.topologicalTrdeg_eq`).
* `TauCeti.topologicalTrdeg_of_discreteTopology`: for the discrete topology the invariant is the
  transcendence degree.
* `TauCeti.topologicalTrdeg_eq_zero_iff_surjective`: over an algebraically closed field whose
  image is closed, the invariant vanishes exactly for the trivial extension.
* `TauCeti.IsTopAlgIndependent`: topological algebraic independence, with
  `TauCeti.IsTopAlgIndependent.mono` and `TauCeti.IsTopAlgIndependent.algebraicIndependent`; it is
  algebraic independence for the discrete topology
  (`TauCeti.isTopAlgIndependent_iff_algebraicIndependent`).
* `TauCeti.topologicalIndependenceDegree K L`: the topological independence degree, with the
  bounds `TauCeti.topologicalIndependenceDegree_le_iff` and
  `TauCeti.natCast_le_topologicalIndependenceDegree_iff`.
* `TauCeti.topologicalIndependenceDegree_eq_zero_iff`: the degree vanishes if and only if the
  elements algebraic over `K` are dense, that is, if and only if the topological transcendence
  degree vanishes (`TauCeti.topologicalIndependenceDegree_eq_zero_iff_topologicalTrdeg_eq_zero`).
* `TauCeti.topologicalIndependenceDegree_of_discreteTopology`: for the discrete topology the
  degree is the transcendence degree.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 21.2.
* M. Temkin, *Topological transcendence degree*, J. Algebra 568 (2021), §2.1.
-/

public section

open Cardinal Topology

namespace TauCeti

universe u v w

section Definition

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [TopologicalSpace L]

/-- The topological transcendence degree of `L` over `K`: the least transcendence degree over `K`
of an intermediate field that is dense in `L`, as an element of `ℕ∞` (so it is `⊤` when every
dense intermediate field has infinite transcendence degree).

For extensions of complete algebraically closed nonarchimedean fields this is Scholze's
`tr.deg` of *Étale cohomology of diamonds*, Definition 21.2. -/
noncomputable def topologicalTrdeg : ℕ∞ :=
  ⨅ (A : IntermediateField K L) (_ : Dense (A : Set L)), toENat (Algebra.trdeg K A)

end Definition

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [TopologicalSpace L]

/-- A dense intermediate field bounds the topological transcendence degree by its own
transcendence degree. -/
theorem topologicalTrdeg_le_of_dense (A : IntermediateField K L) (hA : Dense (A : Set L)) :
    topologicalTrdeg K L ≤ toENat (Algebra.trdeg K A) :=
  iInf₂_le A hA

/-- The topological transcendence degree is at least `m` if every dense intermediate field has
transcendence degree at least `m`. -/
theorem le_topologicalTrdeg {m : ℕ∞}
    (h : ∀ A : IntermediateField K L, Dense (A : Set L) → m ≤ toENat (Algebra.trdeg K A)) :
    m ≤ topologicalTrdeg K L :=
  le_iInf₂ h

/-- The infimum defining the topological transcendence degree is attained by a dense intermediate
field. -/
theorem exists_dense_toENat_trdeg_eq_topologicalTrdeg :
    ∃ A : IntermediateField K L, Dense (A : Set L) ∧
      toENat (Algebra.trdeg K A) = topologicalTrdeg K L := by
  have : Nonempty {A : IntermediateField K L // Dense (A : Set L)} :=
    ⟨⟨⊤, by simp [dense_univ]⟩⟩
  obtain ⟨⟨A, hA⟩, h⟩ :=
    ciInf_mem fun A : {A : IntermediateField K L // Dense (A : Set L)} ↦
      toENat (Algebra.trdeg K A.val)
  exact ⟨A, hA, by rw [topologicalTrdeg, iInf_subtype']; exact h⟩

/-- The topological transcendence degree is at most `m` if and only if some dense intermediate
field has transcendence degree at most `m`. -/
theorem topologicalTrdeg_le_iff {m : ℕ∞} :
    topologicalTrdeg K L ≤ m ↔
      ∃ A : IntermediateField K L, Dense (A : Set L) ∧ toENat (Algebra.trdeg K A) ≤ m := by
  refine ⟨fun h ↦ ?_, fun ⟨A, hA, hm⟩ ↦ (topologicalTrdeg_le_of_dense A hA).trans hm⟩
  obtain ⟨A, hA, hAeq⟩ := exists_dense_toENat_trdeg_eq_topologicalTrdeg (K := K) (L := L)
  exact ⟨A, hA, hAeq ▸ h⟩

/-- For a natural number `n`, the topological transcendence degree is at most `n` if and only if
some dense intermediate field has transcendence degree at most `n`. -/
theorem topologicalTrdeg_le_natCast_iff {n : ℕ} :
    topologicalTrdeg K L ≤ n ↔
      ∃ A : IntermediateField K L, Dense (A : Set L) ∧ Algebra.trdeg K A ≤ n := by
  simp [topologicalTrdeg_le_iff]

/-- The topological transcendence degree is infinite if and only if every dense intermediate
field has infinite transcendence degree. -/
theorem topologicalTrdeg_eq_top_iff :
    topologicalTrdeg K L = ⊤ ↔
      ∀ A : IntermediateField K L, Dense (A : Set L) → ℵ₀ ≤ Algebra.trdeg K A := by
  simp [topologicalTrdeg]

/-- The topological transcendence degree is finite if and only if some dense intermediate field
has finite transcendence degree. -/
theorem topologicalTrdeg_lt_top_iff :
    topologicalTrdeg K L < ⊤ ↔
      ∃ A : IntermediateField K L, Dense (A : Set L) ∧ Algebra.trdeg K A < ℵ₀ := by
  simp [lt_top_iff_ne_top, topologicalTrdeg_eq_top_iff]

/-- The topological transcendence degree vanishes if and only if some dense intermediate field is
algebraic over `K`. -/
theorem topologicalTrdeg_eq_zero_iff :
    topologicalTrdeg K L = 0 ↔
      ∃ A : IntermediateField K L, Dense (A : Set L) ∧ Algebra.IsAlgebraic K A := by
  rw [← nonpos_iff_eq_zero, ← Nat.cast_zero, topologicalTrdeg_le_natCast_iff]
  simp [trdeg_eq_zero_iff]

/-- A `K`-algebra map with dense range from a field `E` bounds the topological transcendence degree
of `L` by the transcendence degree of `E`: its image is a dense intermediate field isomorphic
to `E`. -/
theorem topologicalTrdeg_le_of_denseRange {E : Type w} [Field E] [Algebra K E] (f : E →ₐ[K] L)
    (hf : DenseRange f) : topologicalTrdeg K L ≤ toENat (Algebra.trdeg K E) := by
  refine (topologicalTrdeg_le_of_dense f.fieldRange (by rwa [AlgHom.coe_fieldRange])).trans_eq ?_
  simpa using congrArg toENat f.equivFieldRange.lift_trdeg_eq.symm

/-- The topological transcendence degree is at most the transcendence degree. -/
theorem topologicalTrdeg_le_toENat_trdeg :
    topologicalTrdeg K L ≤ toENat (Algebra.trdeg K L) :=
  topologicalTrdeg_le_of_denseRange (AlgHom.id K L) denseRange_id

/-- A `K`-algebra map with dense range from a field `E` algebraic over `K` forces the topological
transcendence degree to vanish. -/
theorem topologicalTrdeg_eq_zero_of_denseRange {E : Type w} [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] (f : E →ₐ[K] L) (hf : DenseRange f) : topologicalTrdeg K L = 0 :=
  nonpos_iff_eq_zero.mp <| (topologicalTrdeg_le_of_denseRange f hf).trans_eq <| by
    simp [trdeg_eq_zero]

/-- An algebraic extension has topological transcendence degree zero, for every topology. -/
theorem topologicalTrdeg_eq_zero_of_isAlgebraic [Algebra.IsAlgebraic K L] :
    topologicalTrdeg K L = 0 :=
  topologicalTrdeg_eq_zero_of_denseRange (AlgHom.id K L) denseRange_id

/-- A field has topological transcendence degree zero over itself, for every topology. -/
@[simp]
theorem topologicalTrdeg_self (K : Type u) [Field K] [TopologicalSpace K] :
    topologicalTrdeg K K = 0 :=
  topologicalTrdeg_eq_zero_of_isAlgebraic

/-- A continuous `K`-algebra map with dense range does not increase the topological
transcendence degree: it carries dense intermediate fields to dense intermediate fields of the
same transcendence degree. -/
theorem topologicalTrdeg_le_of_continuous_of_denseRange {L' : Type w} [Field L'] [Algebra K L']
    [TopologicalSpace L'] (f : L →ₐ[K] L') (hc : Continuous f) (hd : DenseRange f) :
    topologicalTrdeg K L' ≤ topologicalTrdeg K L := by
  obtain ⟨A, hA, hAeq⟩ := exists_dense_toENat_trdeg_eq_topologicalTrdeg (K := K) (L := L)
  exact hAeq ▸
    topologicalTrdeg_le_of_denseRange (f.comp A.val) (hd.comp hA.denseRange_subtypeVal hc)

/-- The topological transcendence degree is invariant under continuous `K`-algebra isomorphisms
with continuous inverse. -/
theorem _root_.ContinuousAlgEquiv.topologicalTrdeg_eq {L' : Type w} [Field L'] [Algebra K L']
    [TopologicalSpace L'] (e : L ≃A[K] L') : topologicalTrdeg K L = topologicalTrdeg K L' :=
  le_antisymm
    (topologicalTrdeg_le_of_continuous_of_denseRange (e.symm : L' ≃ₐ[K] L).toAlgHom
      e.symm.continuous e.symm.surjective.denseRange)
    (topologicalTrdeg_le_of_continuous_of_denseRange (e : L ≃ₐ[K] L').toAlgHom
      e.continuous e.surjective.denseRange)

/-- For the discrete topology, the only dense intermediate field is `L` itself, so the
topological transcendence degree is the transcendence degree. -/
@[simp]
theorem topologicalTrdeg_of_discreteTopology [DiscreteTopology L] :
    topologicalTrdeg K L = toENat (Algebra.trdeg K L) := by
  refine le_antisymm topologicalTrdeg_le_toENat_trdeg (le_topologicalTrdeg fun A hA ↦ ?_)
  obtain rfl : A = ⊤ := SetLike.coe_injective (by simpa using hA)
  rw [IntermediateField.topEquiv.trdeg_eq]

/-- Over an algebraically closed field `K`, the topological transcendence degree vanishes if and
only if the image of `K` is dense: a dense intermediate field algebraic over `K` is `K` itself. -/
theorem topologicalTrdeg_eq_zero_iff_denseRange [IsAlgClosed K] :
    topologicalTrdeg K L = 0 ↔ DenseRange (algebraMap K L) := by
  refine ⟨fun h ↦ ?_, topologicalTrdeg_eq_zero_of_denseRange (Algebra.ofId K L)⟩
  obtain ⟨A, hA, hAlg⟩ := topologicalTrdeg_eq_zero_iff.mp h
  rwa [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic A, IntermediateField.coe_bot]
    at hA

/-- Over an algebraically closed field `K` whose image is closed (for instance, a complete field
embedded isometrically), the topological transcendence degree vanishes if and only if the
extension is trivial. -/
theorem topologicalTrdeg_eq_zero_iff_surjective [IsAlgClosed K]
    (h : IsClosed (Set.range (algebraMap K L))) :
    topologicalTrdeg K L = 0 ↔ Function.Surjective (algebraMap K L) := by
  rw [topologicalTrdeg_eq_zero_iff_denseRange, DenseRange, h.dense_iff, Set.range_eq_univ]

section Independence

variable (K) in
/-- A set `s ⊆ L` is *topologically algebraically independent* over `K` if no `x ∈ s` lies in the
closure in `L` of the set of elements algebraic over the field `K(s \ {x})` generated over `K` by
the other elements of `s`. This is Temkin's *topgebraic independence*. Such a set is
algebraically independent over `K` (`TauCeti.IsTopAlgIndependent.algebraicIndependent`), and for
the discrete topology the two notions agree
(`TauCeti.isTopAlgIndependent_iff_algebraicIndependent`). -/
def IsTopAlgIndependent (s : Set L) : Prop :=
  ∀ x ∈ s, x ∉ closure {y : L | IsAlgebraic (IntermediateField.adjoin K (s \ {x})) y}

variable {s t : Set L}

/-- Unfolding lemma for `TauCeti.IsTopAlgIndependent`. -/
theorem isTopAlgIndependent_iff :
    IsTopAlgIndependent K s ↔
      ∀ x ∈ s, x ∉ closure {y : L | IsAlgebraic (IntermediateField.adjoin K (s \ {x})) y} :=
  Iff.rfl

/-- The empty set is topologically algebraically independent. -/
@[simp]
theorem isTopAlgIndependent_empty : IsTopAlgIndependent K (∅ : Set L) := by
  simp [isTopAlgIndependent_iff]

/-- A subset of a topologically algebraically independent set is topologically algebraically
independent: removing elements shrinks the fields `K(s \ {x})`, hence the closures of their
algebraic elements. -/
theorem IsTopAlgIndependent.mono (ht : IsTopAlgIndependent K t) (hst : s ⊆ t) :
    IsTopAlgIndependent K s := fun x hx hcl ↦
  ht x (hst hx) <| closure_mono (fun _ hy ↦ IsAlgebraic.tower_top_of_subalgebra_le
    (IntermediateField.toSubalgebra_le_toSubalgebra.mpr <|
      IntermediateField.adjoin.mono K _ _ (Set.sdiff_subset_sdiff_left hst)) hy) hcl

/-- A singleton `{x}` is topologically algebraically independent over `K` if and only if `x` is not
in the closure of the elements of `L` algebraic over `K`. -/
@[simp]
theorem isTopAlgIndependent_singleton_iff {x : L} :
    IsTopAlgIndependent K {x} ↔ x ∉ closure {y : L | IsAlgebraic K y} := by
  have : {y : L | IsAlgebraic (⊥ : IntermediateField K L) y} = {y : L | IsAlgebraic K y} :=
    Set.ext fun y ↦ ⟨fun h ↦ h.restrictScalars K, fun h ↦ h.tower_top _⟩
  simp only [isTopAlgIndependent_iff, Set.mem_singleton_iff, forall_eq]
  rw [Set.sdiff_self, IntermediateField.adjoin_empty, this]

/-- An element of a topologically algebraically independent set is not in the closure of the
elements of `L` algebraic over `K`. -/
theorem IsTopAlgIndependent.notMem_closure_isAlgebraic (hs : IsTopAlgIndependent K s) {x : L}
    (hx : x ∈ s) : x ∉ closure {y : L | IsAlgebraic K y} :=
  isTopAlgIndependent_singleton_iff.mp (hs.mono (Set.singleton_subset_iff.mpr hx))

/-- A topologically algebraically independent set is algebraically independent: an element
algebraic over the field generated by the other elements lies in the closure of such elements. -/
theorem IsTopAlgIndependent.algebraicIndependent (hs : IsTopAlgIndependent K s) :
    AlgebraicIndependent K ((↑) : s → L) :=
  algebraicIndependent_iff_forall_transcendental_adjoin.mpr fun x hx halg ↦
    hs x hx (subset_closure halg)

/-- For the discrete topology, topological algebraic independence is algebraic independence. -/
theorem isTopAlgIndependent_iff_algebraicIndependent [DiscreteTopology L] :
    IsTopAlgIndependent K s ↔ AlgebraicIndependent K ((↑) : s → L) := by
  simp [isTopAlgIndependent_iff, algebraicIndependent_iff_forall_transcendental_adjoin,
    Transcendental]

variable (K L) in
/-- Temkin's topological independence degree of `L` over `K`: the supremum in `ℕ∞` of the
cardinalities of finite topologically algebraically independent subsets of `L`.

For complete algebraically closed nonarchimedean fields with finite topological transcendence
degree, it is Temkin's `top.tr.deg`, which is compared there with `TauCeti.topologicalTrdeg`. -/
noncomputable def topologicalIndependenceDegree : ℕ∞ :=
  ⨆ (s : Finset L) (_ : IsTopAlgIndependent K (s : Set L)), (s.card : ℕ∞)

/-- Every topologically algebraically independent set, finite or not, has cardinality at most the
topological independence degree. -/
theorem IsTopAlgIndependent.encard_le_topologicalIndependenceDegree
    (hs : IsTopAlgIndependent K s) : s.encard ≤ topologicalIndependenceDegree K L := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  obtain ⟨t, hts, htn⟩ := Set.exists_subset_encard_eq hn
  lift t to Finset L using Set.finite_of_encard_eq_coe htn
  rw [← htn, Set.encard_coe_eq_coe_finsetCard]
  exact le_iSup₂_of_le (f := fun (s : Finset L) (_ : IsTopAlgIndependent K (s : Set L)) ↦
    (s.card : ℕ∞)) t (hs.mono hts) le_rfl

/-- The topological independence degree is at most `m` if and only if every topologically
algebraically independent set has cardinality at most `m`. -/
theorem topologicalIndependenceDegree_le_iff {m : ℕ∞} :
    topologicalIndependenceDegree K L ≤ m ↔
      ∀ s : Set L, IsTopAlgIndependent K s → s.encard ≤ m :=
  ⟨fun h _ hs ↦ hs.encard_le_topologicalIndependenceDegree.trans h,
    fun h ↦ iSup₂_le fun s hs ↦ by simpa using h s hs⟩

/-- For a natural number `n`, the topological independence degree is at most `n` if and only if
every finite topologically algebraically independent set has at most `n` elements. -/
theorem topologicalIndependenceDegree_le_natCast_iff {n : ℕ} :
    topologicalIndependenceDegree K L ≤ n ↔
      ∀ s : Finset L, IsTopAlgIndependent K (s : Set L) → s.card ≤ n := by
  simp [topologicalIndependenceDegree]

/-- For a natural number `n`, the topological independence degree is at least `n` if and only if
some topologically algebraically independent set has exactly `n` elements. -/
theorem natCast_le_topologicalIndependenceDegree_iff {n : ℕ} :
    (n : ℕ∞) ≤ topologicalIndependenceDegree K L ↔
      ∃ s : Finset L, IsTopAlgIndependent K (s : Set L) ∧ s.card = n := by
  refine ⟨fun h ↦ ?_, fun ⟨s, hs, hn⟩ ↦ by
    simpa [hn] using hs.encard_le_topologicalIndependenceDegree⟩
  obtain ⟨s, hs, hns⟩ : ∃ s : Finset L, IsTopAlgIndependent K (s : Set L) ∧ n ≤ s.card := by
    by_contra! hlt
    cases n with
    | zero => simpa using hlt ∅
    | succ m =>
      have : topologicalIndependenceDegree K L ≤ m :=
        topologicalIndependenceDegree_le_natCast_iff.mpr fun s hs ↦ Nat.lt_succ_iff.mp (hlt s hs)
      exact absurd (h.trans this) (by norm_cast; omega)
  obtain ⟨t, hts, rfl⟩ := Finset.exists_subset_card_eq hns
  exact ⟨t, hs.mono (by exact_mod_cast hts), rfl⟩

/-- The topological independence degree is at most the transcendence degree. -/
theorem topologicalIndependenceDegree_le_toENat_trdeg :
    topologicalIndependenceDegree K L ≤ toENat (Algebra.trdeg K L) :=
  topologicalIndependenceDegree_le_iff.mpr fun s hs ↦ by
    rw [← Set.toENat_cardinalMk]
    exact toENat.monotone' hs.algebraicIndependent.cardinalMk_le_trdeg

/-- The topological independence degree vanishes if and only if the elements of `L` algebraic over
`K` are dense in `L`. -/
theorem topologicalIndependenceDegree_eq_zero_iff :
    topologicalIndependenceDegree K L = 0 ↔ Dense {y : L | IsAlgebraic K y} := by
  rw [← Order.lt_one_iff, ← not_le, ← Nat.cast_one,
    natCast_le_topologicalIndependenceDegree_iff, Dense]
  simp [Finset.card_eq_one, isTopAlgIndependent_singleton_iff]

/-- The topological independence degree vanishes exactly when the topological transcendence degree
does: both say that the elements algebraic over `K` are dense. -/
theorem topologicalIndependenceDegree_eq_zero_iff_topologicalTrdeg_eq_zero :
    topologicalIndependenceDegree K L = 0 ↔ topologicalTrdeg K L = 0 := by
  have hcl : ((algebraicClosure K L : IntermediateField K L) : Set L) =
      {y : L | IsAlgebraic K y} := Set.ext fun _ ↦ mem_algebraicClosure_iff
  rw [topologicalIndependenceDegree_eq_zero_iff, topologicalTrdeg_eq_zero_iff]
  refine ⟨fun h ↦ ⟨algebraicClosure K L, hcl ▸ h, inferInstance⟩, fun ⟨A, hA, _⟩ ↦
    hA.mono fun y hy ↦ ?_⟩
  exact (IntermediateField.isAlgebraic_iff (x := ⟨y, hy⟩)).mp (Algebra.IsAlgebraic.isAlgebraic _)

/-- An algebraic extension has topological independence degree zero, for every topology. -/
theorem topologicalIndependenceDegree_eq_zero_of_isAlgebraic [Algebra.IsAlgebraic K L] :
    topologicalIndependenceDegree K L = 0 :=
  topologicalIndependenceDegree_eq_zero_iff_topologicalTrdeg_eq_zero.mpr
    topologicalTrdeg_eq_zero_of_isAlgebraic

/-- A field has topological independence degree zero over itself, for every topology. -/
@[simp]
theorem topologicalIndependenceDegree_self (K : Type u) [Field K] [TopologicalSpace K] :
    topologicalIndependenceDegree K K = 0 :=
  topologicalIndependenceDegree_eq_zero_of_isAlgebraic

/-- For the discrete topology the topological independence degree is the transcendence degree. -/
@[simp]
theorem topologicalIndependenceDegree_of_discreteTopology [DiscreteTopology L] :
    topologicalIndependenceDegree K L = toENat (Algebra.trdeg K L) := by
  refine le_antisymm topologicalIndependenceDegree_le_toENat_trdeg ?_
  obtain ⟨b, hb⟩ := exists_isTranscendenceBasis K L
  rw [← hb.cardinalMk_eq_trdeg, Set.toENat_cardinalMk]
  exact (isTopAlgIndependent_iff_algebraicIndependent.mpr hb.1)
    |>.encard_le_topologicalIndependenceDegree

end Independence

end TauCeti
