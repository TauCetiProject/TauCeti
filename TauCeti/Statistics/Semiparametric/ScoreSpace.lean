/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Gram.Projection
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.Analysis.InnerProductSpace.RangeProjection

/-!
# Hilbert geometry of score spaces

This file develops the Hilbert-space geometry of score functions in `Lp ℝ 2 P` underlying
semiparametric efficiency theory. The generic `L²` background lives in its measure-theoretic homes:
`TauCeti.MeasureTheory.Function.L2Space.MeanZero` for the mean-zero subspace `L²₀(P)`
(`MeasureTheory.Measure.meanZeroL2`) and its projection/density properties (together with
`TauCeti.MeasureTheory.Function.L2Space.MeanZero.Density` for bounded continuous density), and
`TauCeti.MeasureTheory.Function.ConditionalExpectation.Pullback` for the `L²` pullback isometry
(`MeasureTheory.Measure.pullbackL2`) and its conditional-expectation adjoint
(`MeasureTheory.Measure.condExpOperator`).

* **Tangent spaces:** `MeasureTheory.Measure.tangentSpace P T` is the closed linear span of a
  tangent set `T ⊆ Lp ℝ 2 P` as a `ClosedSubmodule`. It satisfies the universal property of the
  smallest closed submodule containing `T`, sends unions to joins in `ClosedSubmodule`, and reduces
  to an algebraic orthogonal sum with additive orthogonal projections when the two tangent spaces
  are orthogonal.
* **Efficient scores and information matrices:** `MeasureTheory.Measure.efficientScore P N` is the
  orthogonal projection `(tangentSpace P N).toSubmoduleᗮ.starProjection` onto the orthogonal
  complement of the nuisance tangent space `P.tangentSpace N`, so `efficientScore P N ℓ` is the
  residual of a score `ℓ` after projecting onto `P.tangentSpace N`.
  `MeasureTheory.Measure.efficientInformationMatrix P N ℓ` is the Gram matrix
  `Matrix.gram ℝ (fun i ↦ efficientScore P N (ℓ i))`. Enlarging the nuisance set decreases the
  efficient information matrix in the Loewner order, yielding the information-loss inequality
  `Matrix.gram ℝ ℓ - I_eff ≥ 0`, the adaptation criterion `I_eff = Matrix.gram ℝ ℓ` iff every score
  is orthogonal to `N`, and positive definiteness iff the efficient scores are linearly independent
  (`MeasureTheory.Measure.posDef_efficientInformationMatrix_iff`).
* **Score operators:** For a continuous linear score operator `A : H →L[ℝ] Lp ℝ 2 P` with closed
  range, the tangent space of `Set.range A` equals `A.range`; when the Gram operator `A† A` is
  invertible, the orthogonal projection onto it is `A (A† A)⁻¹ A†`.

## Main definitions

* `MeasureTheory.Measure.tangentSpace`: the closed linear span of a set of scores in `Lp ℝ 2 P`.
* `MeasureTheory.Measure.efficientScore`: the orthogonal projection onto
  `(tangentSpace P N).toSubmoduleᗮ`.
* `MeasureTheory.Measure.efficientInformationMatrix`: the Gram matrix of the efficient scores.

## Main results

* `MeasureTheory.Measure.tangentSpace_union`,
  `MeasureTheory.Measure.toSubmodule_tangentSpace_union_of_isOrtho`,
  `MeasureTheory.Measure.starProjection_tangentSpace_union_of_isOrtho`: tangent space of a union,
  orthogonal sum decomposition, and additivity of projections.
* `MeasureTheory.Measure.efficientScore_efficientScore`: idempotence of `efficientScore`.
* `MeasureTheory.Measure.posSemidef_efficientInformationMatrix`,
  `MeasureTheory.Measure.posDef_efficientInformationMatrix_iff`: positive semidefiniteness and
  the positive-definiteness criterion (via `Matrix.posDef_gram_iff_linearIndependent`).
* `MeasureTheory.Measure.posSemidef_efficientInformationMatrix_sub_of_subset`,
  `MeasureTheory.Measure.posSemidef_gram_sub_efficientInformationMatrix`,
  `MeasureTheory.Measure.efficientInformationMatrix_eq_gram_iff`: information-loss inequalities
  and adaptation criterion.
* `MeasureTheory.Measure.tangentSpace_range_eq_range`,
  `MeasureTheory.Measure.starProjection_tangentSpace_range_eq`: closed range and projection formula
  `A (A† A)⁻¹ A†` for a score operator with invertible `A† A`, specializing
  `ContinuousLinearMap.starProjection_range_eq`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.2, §25.4,
  §25.5.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace MeasureTheory.Measure

/-! ### Tangent spaces -/

section TangentSpace

variable {X : Type*} [MeasurableSpace X]

/-- The tangent space of a tangent set `T ⊆ Lp ℝ 2 P`: the closed linear span of `T`. -/
def tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) : ClosedSubmodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ T).closure

theorem tangentSpace_def {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    tangentSpace P T = (Submodule.span ℝ T).closure :=
  (rfl)

theorem toSubmodule_tangentSpace {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    (tangentSpace P T).toSubmodule = (Submodule.span ℝ T).topologicalClosure :=
  (rfl)

/-- Universal property of `tangentSpace`: `tangentSpace P T` is the smallest closed submodule
containing `T`. -/
theorem tangentSpace_le_iff {P : Measure X} {T : Set (Lp ℝ 2 P)}
    {K : ClosedSubmodule ℝ (Lp ℝ 2 P)} :
    tangentSpace P T ≤ K ↔ T ⊆ K := by
  rw [tangentSpace_def, Submodule.closure_le, Submodule.span_le, ClosedSubmodule.coe_toSubmodule]

/-- `tangentSpace P` forms a Galois connection with coercion of closed submodules to sets. -/
theorem tangentSpace_gc (P : Measure X) :
    GaloisConnection (tangentSpace P)
      (fun K : ClosedSubmodule ℝ (Lp ℝ 2 P) ↦ (K : Set (Lp ℝ 2 P))) :=
  fun _ _ ↦ tangentSpace_le_iff

/-- Every tangent set is contained in its tangent space. -/
theorem subset_tangentSpace {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    T ⊆ (tangentSpace P T : Set (Lp ℝ 2 P)) :=
  tangentSpace_le_iff.mp le_rfl

/-- Every element of a tangent set belongs to its tangent space. -/
theorem mem_tangentSpace_of_mem {P : Measure X} {T : Set (Lp ℝ 2 P)} {g : Lp ℝ 2 P} (hg : g ∈ T) :
    g ∈ tangentSpace P T :=
  subset_tangentSpace T hg

/-- A vector lies in the tangent space of `T` if and only if it lies in the closure of the linear
span of `T`. -/
theorem mem_tangentSpace_iff {P : Measure X} {T : Set (Lp ℝ 2 P)} {g : Lp ℝ 2 P} :
    g ∈ tangentSpace P T ↔ g ∈ closure (Submodule.span ℝ T : Set (Lp ℝ 2 P)) := by
  rw [tangentSpace_def, Submodule.mem_closure_iff, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]

/-- The tangent space is monotone in the generating set. -/
theorem tangentSpace_mono {P : Measure X} {T T' : Set (Lp ℝ 2 P)} (h : T ⊆ T') :
    tangentSpace P T ≤ tangentSpace P T' :=
  tangentSpace_le_iff.mpr (h.trans (subset_tangentSpace T'))

/-- The tangent space of the empty set is the zero subspace. -/
@[simp]
theorem tangentSpace_empty (P : Measure X) : tangentSpace P ∅ = ⊥ :=
  le_bot_iff.mp (tangentSpace_le_iff.mpr (Set.empty_subset _))

/-- The tangent space of a closed submodule is itself. -/
@[simp]
theorem tangentSpace_coe {P : Measure X} (K : ClosedSubmodule ℝ (Lp ℝ 2 P)) :
    tangentSpace P (K : Set (Lp ℝ 2 P)) = K := by
  rw [tangentSpace_def, ← ClosedSubmodule.coe_toSubmodule, Submodule.span_eq,
    ClosedSubmodule.closure_toSubmodule_eq]

/-- The underlying submodule of the tangent space of a closed submodule is that submodule. -/
theorem toSubmodule_tangentSpace_coe {P : Measure X} {K : Submodule ℝ (Lp ℝ 2 P)}
    (hK : IsClosed (K : Set (Lp ℝ 2 P))) :
    (tangentSpace P (K : Set (Lp ℝ 2 P))).toSubmodule = K :=
  congrArg ClosedSubmodule.toSubmodule (tangentSpace_coe ⟨K, hK⟩)

/-- The tangent space of a singleton is its linear span. -/
theorem toSubmodule_tangentSpace_singleton {P : Measure X} (g : Lp ℝ 2 P) :
    (tangentSpace P {g}).toSubmodule = Submodule.span ℝ {g} := by
  rw [tangentSpace_def,
    Submodule.closure_eq' (Submodule.span ℝ {g}).isClosed_of_finiteDimensional]

/-- If every score in `T` has mean zero, then `tangentSpace P T` is contained in `L²₀(P)`. -/
theorem tangentSpace_le_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {T : Set (Lp ℝ 2 P)}
    (hT : T ⊆ meanZeroL2 P ℝ (E := ℝ)) : (tangentSpace P T).toSubmodule ≤ meanZeroL2 P ℝ :=
  ClosedSubmodule.toSubmodule_le_toSubmodule.mp
    ((tangentSpace_le_iff (K := ⟨meanZeroL2 P ℝ, isClosed_meanZeroL2 P ℝ⟩)).mpr hT)

/-- A vector is orthogonal to `tangentSpace P T` if and only if it is orthogonal to every element
of `T`. -/
theorem mem_orthogonal_tangentSpace_iff {P : Measure X} {T : Set (Lp ℝ 2 P)} {f : Lp ℝ 2 P} :
    f ∈ (tangentSpace P T).toSubmoduleᗮ ↔ ∀ g ∈ T, ⟪g, f⟫_ℝ = 0 := by
  rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le,
    toSubmodule_tangentSpace, Submodule.isOrtho_topologicalClosure_right,
    Submodule.isOrtho_comm, Submodule.isOrtho_span]
  simp

/-- Two tangent spaces are orthogonal if and only if every element of the first tangent set is
orthogonal to every element of the second. -/
theorem isOrtho_tangentSpace_iff {P : Measure X} {T T' : Set (Lp ℝ 2 P)} :
    (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule ↔
      ∀ g ∈ T, ∀ g' ∈ T', ⟪g, g'⟫_ℝ = 0 := by
  rw [toSubmodule_tangentSpace, toSubmodule_tangentSpace,
    Submodule.isOrtho_topologicalClosure_left, Submodule.isOrtho_topologicalClosure_right,
    Submodule.isOrtho_span]

/-- The tangent space of a union is the join of the two tangent spaces in `ClosedSubmodule` (the
closure of their sum). -/
@[simp]
theorem tangentSpace_union {P : Measure X} (T T' : Set (Lp ℝ 2 P)) :
    tangentSpace P (T ∪ T') = tangentSpace P T ⊔ tangentSpace P T' :=
  (tangentSpace_gc P).l_sup

/-- When two tangent spaces are orthogonal, the tangent space of their union is their algebraic
sum. -/
theorem toSubmodule_tangentSpace_union_of_isOrtho {P : Measure X} {T T' : Set (Lp ℝ 2 P)}
    (h : (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule) :
    (tangentSpace P (T ∪ T')).toSubmodule =
      (tangentSpace P T).toSubmodule ⊔ (tangentSpace P T').toSubmodule := by
  rw [tangentSpace_union, ClosedSubmodule.toSubmodule_sup]
  exact h.isClosed_sup.submodule_topologicalClosure_eq

/-- When two tangent spaces are orthogonal, the orthogonal projection onto the tangent space of
their union is the sum of their orthogonal projections. -/
theorem starProjection_tangentSpace_union_of_isOrtho {P : Measure X} {T T' : Set (Lp ℝ 2 P)}
    (h : (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule) :
    (tangentSpace P (T ∪ T')).toSubmodule.starProjection =
      (tangentSpace P T).toSubmodule.starProjection +
        (tangentSpace P T').toSubmodule.starProjection := by
  let := h.hasOrthogonalProjection_sup
  rw [← h.starProjection_sup]
  -- `Submodule.HasOrthogonalProjection` is a `Prop`, so `simp_rw` unifies the projection instances.
  simp_rw [toSubmodule_tangentSpace_union_of_isOrtho h]

end TangentSpace

/-! ### Efficient scores and information matrices -/

section EfficientScore

variable {X : Type*} [MeasurableSpace X]

/-- The efficient score operator: orthogonal projection onto the orthogonal complement of the
nuisance tangent space generated by `N`. -/
def efficientScore (P : Measure X) (N : Set (Lp ℝ 2 P)) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (tangentSpace P N).toSubmoduleᗮ.starProjection

theorem efficientScore_def {P : Measure X} (N : Set (Lp ℝ 2 P)) :
    efficientScore P N = (tangentSpace P N).toSubmoduleᗮ.starProjection :=
  (rfl)

/-- The efficient score is the residual of `ℓ` after orthogonal projection onto the nuisance tangent
space. -/
theorem efficientScore_eq_sub_starProjection {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ :=
  Submodule.starProjection_orthogonal_val ℓ

/-- The efficient score is orthogonal to the nuisance tangent space. -/
theorem efficientScore_mem_orthogonal {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ ∈ (tangentSpace P N).toSubmoduleᗮ :=
  Submodule.starProjection_apply_mem _ ℓ

/-- Applying the efficient score projection twice leaves it unchanged. -/
@[simp]
theorem efficientScore_efficientScore {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (efficientScore P N ℓ) = efficientScore P N ℓ :=
  Submodule.starProjection_eq_self_iff.mpr (efficientScore_mem_orthogonal N ℓ)

/-- The efficient score is orthogonal to every element of the nuisance tangent space. -/
theorem inner_efficientScore_eq_zero_of_mem_tangentSpace {P : Measure X} (N : Set (Lp ℝ 2 P))
    (ℓ : Lp ℝ 2 P) {g : Lp ℝ 2 P} (hg : g ∈ tangentSpace P N) :
    ⟪g, efficientScore P N ℓ⟫_ℝ = 0 :=
  Submodule.inner_right_of_mem_orthogonal hg (efficientScore_mem_orthogonal N ℓ)

/-- The efficient score is orthogonal to every nuisance score in `N`. -/
theorem inner_efficientScore_eq_zero_of_mem {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P)
    {g : Lp ℝ 2 P} (hg : g ∈ N) : ⟪g, efficientScore P N ℓ⟫_ℝ = 0 :=
  inner_efficientScore_eq_zero_of_mem_tangentSpace N ℓ (mem_tangentSpace_of_mem hg)

/-- The efficient score equals `ℓ` if and only if `ℓ` is orthogonal to every nuisance score. -/
theorem efficientScore_eq_self_iff {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ ↔ ∀ g ∈ N, ⟪g, ℓ⟫_ℝ = 0 := by
  rw [efficientScore_def, Submodule.starProjection_eq_self_iff, mem_orthogonal_tangentSpace_iff]

/-- The efficient score vanishes if and only if `ℓ` lies in the nuisance tangent space. -/
theorem efficientScore_eq_zero_iff {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = 0 ↔ ℓ ∈ tangentSpace P N := by
  rw [efficientScore_eq_sub_starProjection, sub_eq_zero, eq_comm,
    Submodule.starProjection_eq_self_iff, ClosedSubmodule.mem_toSubmodule_iff]

/-- With no nuisance scores, the efficient score is the score itself. -/
@[simp]
theorem efficientScore_empty {P : Measure X} (ℓ : Lp ℝ 2 P) : efficientScore P ∅ ℓ = ℓ :=
  (efficientScore_eq_self_iff ∅ ℓ).mpr fun _ h ↦ h.elim

/-- For a single nuisance score `n`, the efficient score is `ℓ - (⟪n, ℓ⟫ / ‖n‖²) n`. -/
theorem efficientScore_singleton {P : Measure X} (n ℓ : Lp ℝ 2 P) :
    efficientScore P {n} ℓ = ℓ - (⟪n, ℓ⟫_ℝ / ‖n‖ ^ 2) • n := by
  rw [efficientScore_eq_sub_starProjection]
  simp_rw [toSubmodule_tangentSpace_singleton n]
  simp [Submodule.starProjection_singleton ℝ ℓ]

/-- If `ℓ` and every nuisance score in `N` have mean zero, then so does the efficient score. -/
theorem efficientScore_mem_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {N : Set (Lp ℝ 2 P)}
    {ℓ : Lp ℝ 2 P} (hN : N ⊆ meanZeroL2 P ℝ (E := ℝ)) (hℓ : ℓ ∈ meanZeroL2 P ℝ) :
    efficientScore P N ℓ ∈ meanZeroL2 P ℝ := by
  rw [efficientScore_eq_sub_starProjection]
  exact Submodule.sub_mem _ hℓ
    (tangentSpace_le_meanZeroL2 hN (Submodule.starProjection_apply_mem _ ℓ))

/-- The efficient information matrix of a family of scores relative to a nuisance set `N`: the
Gram matrix of the efficient scores `efficientScore P N (ℓ i)`. -/
def efficientInformationMatrix (P : Measure X) {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i ↦ efficientScore P N (ℓ i))

theorem efficientInformationMatrix_def {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = Matrix.gram ℝ (fun i ↦ efficientScore P N (ℓ i)) :=
  (rfl)

/-- The entries of the efficient information matrix. -/
@[simp]
theorem efficientInformationMatrix_apply {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    efficientInformationMatrix P N ℓ i j = ⟪efficientScore P N (ℓ i), efficientScore P N (ℓ j)⟫_ℝ :=
  (rfl)

/-- With no nuisance scores, the efficient information matrix equals the Gram matrix. -/
@[simp]
theorem efficientInformationMatrix_empty {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P ∅ ℓ = Matrix.gram ℝ ℓ := by
  simp [efficientInformationMatrix_def]

/-- The efficient information matrix is positive semidefinite. -/
theorem posSemidef_efficientInformationMatrix {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : (efficientInformationMatrix P N ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

/-- The efficient information matrix is positive definite if and only if the efficient scores are
linearly independent. -/
theorem posDef_efficientInformationMatrix_iff {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ).PosDef ↔
      LinearIndependent ℝ (fun i ↦ efficientScore P N (ℓ i)) :=
  Matrix.posDef_gram_iff_linearIndependent

/-- Enlarging the nuisance set from `N` to `N'` lowers the efficient information matrix by the Gram
matrix of the projection difference `(Π_{N'} - Π_N) ℓ`. -/
theorem efficientInformationMatrix_sub_eq_gram_of_subset {P : Measure X} {ι : Type*}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ =
      Matrix.gram ℝ (fun i ↦ (tangentSpace P N').toSubmodule.starProjection (ℓ i) -
        (tangentSpace P N).toSubmodule.starProjection (ℓ i)) := by
  have hle : (tangentSpace P N).toSubmodule ≤ (tangentSpace P N').toSubmodule :=
    ClosedSubmodule.toSubmodule_le_toSubmodule.mp (tangentSpace_mono h)
  simpa only [efficientInformationMatrix_def, efficientScore_def] using
    Matrix.gram_starProjection_orthogonal_sub_of_le hle ℓ

/-- Enlarging the nuisance scores can only lower the efficient information matrix in the Loewner
order. -/
theorem posSemidef_efficientInformationMatrix_sub_of_subset {P : Measure X} {ι : Type*}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ).PosSemidef := by
  rw [efficientInformationMatrix_sub_eq_gram_of_subset h]
  exact Matrix.posSemidef_gram ℝ _

/-- Information loss: `Matrix.gram ℝ ℓ - I_eff` is the Gram matrix of the projections of the scores
onto the nuisance tangent space. -/
theorem gram_sub_efficientInformationMatrix_eq_gram {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    Matrix.gram ℝ ℓ - efficientInformationMatrix P N ℓ =
      Matrix.gram ℝ (fun i ↦ (tangentSpace P N).toSubmodule.starProjection (ℓ i)) := by
  have h := efficientInformationMatrix_sub_eq_gram_of_subset (Set.empty_subset N) ℓ
  simpa only [efficientInformationMatrix_empty, tangentSpace_empty,
    ClosedSubmodule.toSubmodule_bot, Submodule.starProjection_bot, zero_apply, sub_zero] using h

/-- Information loss is positive semidefinite: `Matrix.gram ℝ ℓ - I_eff ≥ 0`. -/
theorem posSemidef_gram_sub_efficientInformationMatrix {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    (Matrix.gram ℝ ℓ - efficientInformationMatrix P N ℓ).PosSemidef := by
  rw [gram_sub_efficientInformationMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℝ _

/-- Adaptation criterion: the efficient information matrix equals the full Gram matrix if and only
if every score coordinate is orthogonal to the nuisance set `N`. -/
theorem efficientInformationMatrix_eq_gram_iff {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = Matrix.gram ℝ ℓ ↔
      ∀ i, ∀ g ∈ N, ⟪g, ℓ i⟫_ℝ = 0 := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hzero :
        Matrix.gram ℝ (fun i ↦ (tangentSpace P N).toSubmodule.starProjection (ℓ i)) i i = 0 := by
      rw [← gram_sub_efficientInformationMatrix_eq_gram, h, sub_self, Matrix.zero_apply]
    rw [← efficientScore_eq_self_iff, efficientScore_eq_sub_starProjection, sub_eq_self]
    simpa [Matrix.gram_apply] using hzero
  · ext i j
    simp only [efficientInformationMatrix_def, Matrix.gram_apply,
      (efficientScore_eq_self_iff N (ℓ i)).mpr (h i),
      (efficientScore_eq_self_iff N (ℓ j)).mpr (h j)]

end EfficientScore

/-! ### Score operators -/

section ScoreOperators

variable {X : Type*} [MeasurableSpace X]

/-- The tangent space of the range of a score operator `A` with closed range equals `A.range`. -/
theorem tangentSpace_range_eq_range {H : Type*} [AddCommMonoid H] [Module ℝ H] [TopologicalSpace H]
    {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P) (hA : IsClosed (A.range : Set (Lp ℝ 2 P))) :
    (tangentSpace P (Set.range A)).toSubmodule = A.range := by
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    toSubmodule_tangentSpace_coe hA

/-- The orthogonal projection onto the tangent space of the range of a score operator `A` with
continuously invertible information operator `A† A` is `A (A† A)⁻¹ A†`, specializing
`ContinuousLinearMap.starProjection_range_eq`. -/
theorem starProjection_tangentSpace_range_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule.starProjection =
      A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  have hclosed : IsClosed (A.range : Set (Lp ℝ 2 P)) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
      ContinuousLinearMap.isClosed_range_of_isUnit_adjoint_comp hA
  let := ContinuousLinearMap.hasOrthogonalProjection_range_of_isUnit_adjoint_comp hA
  rw [← ContinuousLinearMap.gramLeftInverse_def A,
    ← ContinuousLinearMap.starProjection_range_eq hA]
  -- `Submodule.HasOrthogonalProjection` is a `Prop`, so `simp_rw` unifies the projection instances.
  simp_rw [tangentSpace_range_eq_range A hclosed]

end ScoreOperators

end MeasureTheory.Measure
