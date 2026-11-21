/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Topological transcendence degree

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

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 21.2.
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

end TauCeti
