/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.Analysis.InnerProductSpace.RangeProjection

/-!
# Hilbert geometry of score spaces

This file develops the Hilbert-space geometry of score functions in `Lp ℝ 2 P` underlying
semiparametric efficiency theory. The generic `L²` background lives in its measure-theoretic homes:
`TauCeti.MeasureTheory.Function.L2Space.MeanZero` for the mean-zero subspace `L²₀(P)`
(`MeasureTheory.Measure.meanZeroL2`) and its projection/density properties, and
`TauCeti.MeasureTheory.Function.ConditionalExpectation.Pullback` for the `L²` pullback isometry
(`MeasureTheory.Measure.pullbackL2`) and its conditional-expectation adjoint
(`MeasureTheory.Measure.condExpOperator`).

* **Tangent spaces:** `MeasureTheory.Measure.tangentSpace P T` is the closed linear span of a
  tangent set `T ⊆ Lp ℝ 2 P` as a `ClosedSubmodule`. It satisfies the universal property of the
  smallest closed submodule containing `T`, sends unions to joins in `ClosedSubmodule`, and reduces
  to an algebraic orthogonal sum with additive orthogonal projections when the two tangent spaces
  are orthogonal.
* **Efficient scores and information matrices:** `MeasureTheory.Measure.efficientScore P N ℓ` is the
  residual of a score `ℓ` after orthogonal projection onto the nuisance tangent space
  `P.tangentSpace N`. `MeasureTheory.Measure.informationMatrix P ℓ` and
  `MeasureTheory.Measure.efficientInformationMatrix P N ℓ` are the Gram matrices of the scores and
  of the efficient scores. Enlarging the nuisance set decreases the efficient information matrix in
  the Loewner order, yielding the information-loss inequality `I - I_eff ≥ 0`, the adaptation
  criterion `I_eff = I` iff every score is orthogonal to `N`, and positive definiteness iff the
  efficient scores are linearly independent.
* **Score operators:** For a continuous linear score operator `A : H →L[ℝ] Lp ℝ 2 P` with
  invertible Gram operator `A† A`, the tangent space of `Set.range A` equals `A.range`, and the
  orthogonal projection onto it is `A (A† A)⁻¹ A†`.

## Main definitions

* `MeasureTheory.Measure.tangentSpace`: the closed linear span of a set of scores in `Lp ℝ 2 P`.
* `MeasureTheory.Measure.efficientScore`: the residual of a score after projection onto a nuisance
  tangent space.
* `MeasureTheory.Measure.informationMatrix`, `MeasureTheory.Measure.efficientInformationMatrix`:
  the Gram matrices of a family of scores and of their efficient scores.

## Main results

* `MeasureTheory.Measure.tangentSpace_union`,
  `MeasureTheory.Measure.toSubmodule_tangentSpace_union_of_isOrtho`,
  `MeasureTheory.Measure.starProjection_tangentSpace_union_of_isOrtho`: tangent space of a union,
  orthogonal sum decomposition, and additivity of projections.
* `MeasureTheory.Measure.posSemidef_efficientInformationMatrix_sub_of_subset`,
  `MeasureTheory.Measure.posSemidef_informationMatrix_sub_efficientInformationMatrix`,
  `MeasureTheory.Measure.efficientInformationMatrix_eq_informationMatrix_iff`,
  `MeasureTheory.Measure.posDef_efficientInformationMatrix_iff`: information-loss inequalities,
  adaptation criterion, and nonsingularity criterion.
* `MeasureTheory.Measure.tangentSpace_range_eq_range`,
  `MeasureTheory.Measure.starProjection_tangentSpace_range_eq`: closed range and projection formula
  `A (A† A)⁻¹ A†` for a score operator with invertible `A† A`.

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

/-- Every tangent set is contained in its tangent space. -/
theorem subset_tangentSpace {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    T ⊆ (tangentSpace P T : Set (Lp ℝ 2 P)) :=
  tangentSpace_le_iff.mp le_rfl

/-- Every element of a tangent set belongs to its tangent space. -/
theorem mem_tangentSpace_of_mem {P : Measure X} {T : Set (Lp ℝ 2 P)} {g : Lp ℝ 2 P} (hg : g ∈ T) :
    g ∈ tangentSpace P T :=
  subset_tangentSpace T hg

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
    tangentSpace P (K : Set (Lp ℝ 2 P)) = K :=
  le_antisymm (tangentSpace_le_iff.mpr Set.Subset.rfl) (subset_tangentSpace _)

/-- The underlying submodule of the tangent space of a closed submodule is that submodule. -/
theorem toSubmodule_tangentSpace_coe {P : Measure X} {K : Submodule ℝ (Lp ℝ 2 P)}
    (hK : IsClosed (K : Set (Lp ℝ 2 P))) :
    (tangentSpace P (K : Set (Lp ℝ 2 P))).toSubmodule = K :=
  congrArg ClosedSubmodule.toSubmodule (tangentSpace_coe ⟨K, hK⟩)

/-- The tangent space of a singleton is its linear span. -/
theorem toSubmodule_tangentSpace_singleton {P : Measure X} (g : Lp ℝ 2 P) :
    (tangentSpace P {g}).toSubmodule = Submodule.span ℝ {g} := by
  rw [toSubmodule_tangentSpace]
  exact (Submodule.span ℝ {g}).isClosed_of_finiteDimensional.submodule_topologicalClosure_eq

/-- If every score in `T` has mean zero, then `tangentSpace P T` is contained in `L²₀(P)`. -/
theorem tangentSpace_le_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {T : Set (Lp ℝ 2 P)}
    (hT : T ⊆ meanZeroL2 P) : (tangentSpace P T).toSubmodule ≤ meanZeroL2 P :=
  (tangentSpace_le_iff (K := ⟨meanZeroL2 P, isClosed_meanZeroL2 P⟩)).mpr hT

/-- A vector is orthogonal to `tangentSpace P T` if and only if it is orthogonal to every element
of `T`. -/
theorem mem_orthogonal_tangentSpace_iff {P : Measure X} {T : Set (Lp ℝ 2 P)} {f : Lp ℝ 2 P} :
    f ∈ (tangentSpace P T).toSubmoduleᗮ ↔ ∀ g ∈ T, ⟪g, f⟫_ℝ = 0 := by
  rw [toSubmodule_tangentSpace, Submodule.orthogonal_closure,
    ← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, Submodule.isOrtho_comm,
    Submodule.isOrtho_span]
  simp

/-- Two tangent spaces are orthogonal if and only if every element of the first tangent set is
orthogonal to every element of the second. -/
theorem isOrtho_tangentSpace_iff {P : Measure X} {T T' : Set (Lp ℝ 2 P)} :
    (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule ↔
      ∀ g ∈ T, ∀ g' ∈ T', ⟪g, g'⟫_ℝ = 0 := by
  rw [Submodule.isOrtho_iff_le]
  refine (tangentSpace_le_iff (K := ⟨_, Submodule.isClosed_orthogonal _⟩)).trans ?_
  simp only [Set.subset_def, SetLike.mem_coe, ClosedSubmodule.mem_mk,
    mem_orthogonal_tangentSpace_iff, real_inner_comm]

/-- The tangent space of a union is the join of the two tangent spaces in `ClosedSubmodule` (the
closure of their sum). -/
@[simp]
theorem tangentSpace_union {P : Measure X} (T T' : Set (Lp ℝ 2 P)) :
    tangentSpace P (T ∪ T') = tangentSpace P T ⊔ tangentSpace P T' := by
  refine le_antisymm ?_ (sup_le (tangentSpace_mono Set.subset_union_left)
    (tangentSpace_mono Set.subset_union_right))
  rw [tangentSpace_le_iff]
  exact Set.union_subset
    ((subset_tangentSpace T).trans (SetLike.coe_subset_coe.mpr le_sup_left))
    ((subset_tangentSpace T').trans (SetLike.coe_subset_coe.mpr le_sup_right))

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
  have := h.hasOrthogonalProjection_sup
  rw [← h.starProjection_sup]
  simp_rw [toSubmodule_tangentSpace_union_of_isOrtho h]

end TangentSpace

/-! ### Efficient scores and information matrices -/

section EfficientScore

variable {X : Type*} [MeasurableSpace X]

/-- The efficient score: the residual of `ℓ` after orthogonal projection onto the nuisance tangent
space generated by `N`. -/
def efficientScore (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) : Lp ℝ 2 P :=
  ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ

theorem efficientScore_def {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ :=
  (rfl)

/-- The efficient score is the orthogonal projection of `ℓ` onto the orthogonal complement of the
nuisance tangent space. -/
theorem efficientScore_eq_starProjection_orthogonal {P : Measure X} (N : Set (Lp ℝ 2 P))
    (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = (tangentSpace P N).toSubmoduleᗮ.starProjection ℓ :=
  (Submodule.starProjection_orthogonal_val ℓ).symm

/-- The efficient score is orthogonal to the nuisance tangent space. -/
theorem efficientScore_mem_orthogonal {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ ∈ (tangentSpace P N).toSubmoduleᗮ :=
  Submodule.sub_starProjection_mem_orthogonal ℓ

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
  rw [efficientScore_def, sub_eq_self, Submodule.starProjection_apply_eq_zero_iff,
    mem_orthogonal_tangentSpace_iff]

/-- The efficient score vanishes if and only if `ℓ` lies in the nuisance tangent space. -/
theorem efficientScore_eq_zero_iff {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = 0 ↔ ℓ ∈ tangentSpace P N := by
  rw [efficientScore_def, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff,
    ClosedSubmodule.mem_toSubmodule_iff]

/-- Taking the efficient score is idempotent. -/
@[simp]
theorem efficientScore_efficientScore {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (efficientScore P N ℓ) = efficientScore P N ℓ :=
  (efficientScore_eq_self_iff N _).mpr fun _ hg ↦ inner_efficientScore_eq_zero_of_mem N ℓ hg

/-- The efficient score of `0` is `0`. -/
@[simp]
theorem efficientScore_zero {P : Measure X} (N : Set (Lp ℝ 2 P)) : efficientScore P N 0 = 0 := by
  simp [efficientScore_def]

/-- `efficientScore P N` is additive in the score. -/
theorem efficientScore_add {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ₁ ℓ₂ : Lp ℝ 2 P) :
    efficientScore P N (ℓ₁ + ℓ₂) = efficientScore P N ℓ₁ + efficientScore P N ℓ₂ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_add]

/-- `efficientScore P N` is homogeneous in the score. -/
theorem efficientScore_smul {P : Measure X} (N : Set (Lp ℝ 2 P)) (c : ℝ) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (c • ℓ) = c • efficientScore P N ℓ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_smul]

/-- With no nuisance scores, the efficient score is the score itself. -/
@[simp]
theorem efficientScore_empty {P : Measure X} (ℓ : Lp ℝ 2 P) : efficientScore P ∅ ℓ = ℓ :=
  (efficientScore_eq_self_iff ∅ ℓ).mpr fun _ h ↦ h.elim

/-- For a single nuisance score `n`, the efficient score is `ℓ - (⟪n, ℓ⟫ / ‖n‖²) n`. -/
theorem efficientScore_singleton {P : Measure X} (n ℓ : Lp ℝ 2 P) :
    efficientScore P {n} ℓ = ℓ - (⟪n, ℓ⟫_ℝ / ‖n‖ ^ 2) • n := by
  rw [efficientScore_def]
  simp_rw [toSubmodule_tangentSpace_singleton n]
  simp [Submodule.starProjection_singleton ℝ ℓ]

/-- If `ℓ` and every nuisance score in `N` have mean zero, then so does the efficient score. -/
theorem efficientScore_mem_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {N : Set (Lp ℝ 2 P)}
    {ℓ : Lp ℝ 2 P} (hN : N ⊆ meanZeroL2 P) (hℓ : ℓ ∈ meanZeroL2 P) :
    efficientScore P N ℓ ∈ meanZeroL2 P :=
  Submodule.sub_mem _ hℓ
    (tangentSpace_le_meanZeroL2 hN (Submodule.starProjection_apply_mem _ ℓ))

/-- The information matrix `Iᵢⱼ = ⟪ℓᵢ, ℓⱼ⟫` of a family of scores in `Lp ℝ 2 P`. -/
def informationMatrix (P : Measure X) {ι : Type*} (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  Matrix.gram ℝ ℓ

theorem informationMatrix_eq_gram {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ = Matrix.gram ℝ ℓ :=
  (rfl)

@[simp]
theorem informationMatrix_apply {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    informationMatrix P ℓ i j = ⟪ℓ i, ℓ j⟫_ℝ :=
  (rfl)

/-- Every information matrix is positive semidefinite. -/
theorem posSemidef_informationMatrix {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ ℓ

/-- The information matrix is positive definite if and only if the scores are linearly
independent. -/
theorem posDef_informationMatrix_iff {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosDef ↔ LinearIndependent ℝ ℓ :=
  Matrix.posDef_gram_iff_linearIndependent

/-- The efficient information matrix of a family of scores relative to a nuisance set `N`: the
Gram matrix of the efficient scores `efficientScore P N (ℓ i)`. -/
def efficientInformationMatrix (P : Measure X) {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  informationMatrix P (fun i ↦ efficientScore P N (ℓ i))

theorem efficientInformationMatrix_def {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = informationMatrix P (fun i ↦ efficientScore P N (ℓ i)) :=
  (rfl)

@[simp]
theorem efficientInformationMatrix_apply {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    efficientInformationMatrix P N ℓ i j = ⟪efficientScore P N (ℓ i), efficientScore P N (ℓ j)⟫_ℝ :=
  (rfl)

/-- With no nuisance scores, the efficient information matrix equals the information matrix. -/
@[simp]
theorem efficientInformationMatrix_empty {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P ∅ ℓ = informationMatrix P ℓ := by
  simp [efficientInformationMatrix_def]

/-- Every efficient information matrix is positive semidefinite. -/
theorem posSemidef_efficientInformationMatrix {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : (efficientInformationMatrix P N ℓ).PosSemidef :=
  posSemidef_informationMatrix _

/-- The efficient information matrix is positive definite if and only if the efficient scores are
linearly independent in `Lp ℝ 2 P`. -/
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
  ext i j
  set K := (tangentSpace P N).toSubmodule
  set K' := (tangentSpace P N').toSubmodule
  have hle : K ≤ K' := tangentSpace_mono h
  have hdiff (k : ι) : K'.starProjection (ℓ k) - K.starProjection (ℓ k) ∈ K' :=
    K'.sub_mem (K'.starProjection_apply_mem _) (hle (K.starProjection_apply_mem _))
  have hsplit (k : ι) : efficientScore P N (ℓ k) =
      efficientScore P N' (ℓ k) + (K'.starProjection (ℓ k) - K.starProjection (ℓ k)) := by
    simp only [efficientScore_def, K, K']
    abel
  have h₁ : ⟪efficientScore P N' (ℓ i),
      K'.starProjection (ℓ j) - K.starProjection (ℓ j)⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (hdiff j) (efficientScore_mem_orthogonal N' (ℓ i))
  have h₂ : ⟪K'.starProjection (ℓ i) - K.starProjection (ℓ i),
      efficientScore P N' (ℓ j)⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hdiff i) (efficientScore_mem_orthogonal N' (ℓ j))
  simp only [Matrix.sub_apply, efficientInformationMatrix_apply, Matrix.gram_apply]
  conv_lhs => rw [hsplit i, hsplit j]
  rw [inner_add_left, inner_add_right, inner_add_right, h₁, h₂]
  ring

/-- Enlarging the nuisance scores can only lower the efficient information matrix in the Loewner
order. -/
theorem posSemidef_efficientInformationMatrix_sub_of_subset {P : Measure X} {ι : Type*}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ).PosSemidef := by
  rw [efficientInformationMatrix_sub_eq_gram_of_subset h]
  exact Matrix.posSemidef_gram ℝ _

/-- Information loss: `I - I_eff` is the Gram matrix of the projections of the scores onto the
nuisance tangent space. -/
theorem informationMatrix_sub_efficientInformationMatrix_eq_gram {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ - efficientInformationMatrix P N ℓ =
      Matrix.gram ℝ (fun i ↦ (tangentSpace P N).toSubmodule.starProjection (ℓ i)) := by
  have h := efficientInformationMatrix_sub_eq_gram_of_subset (Set.empty_subset N) ℓ
  simpa only [efficientInformationMatrix_empty, tangentSpace_empty,
    ClosedSubmodule.toSubmodule_bot, Submodule.starProjection_bot, zero_apply, sub_zero] using h

/-- Information loss is positive semidefinite: `I - I_eff ≥ 0`. -/
theorem posSemidef_informationMatrix_sub_efficientInformationMatrix {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ - efficientInformationMatrix P N ℓ).PosSemidef := by
  rw [informationMatrix_sub_efficientInformationMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℝ _

/-- Adaptation criterion: the efficient information matrix equals the full information matrix if
and only if every score coordinate is orthogonal to the nuisance set `N`. -/
theorem efficientInformationMatrix_eq_informationMatrix_iff {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = informationMatrix P ℓ ↔
      ∀ i, ∀ g ∈ N, ⟪g, ℓ i⟫_ℝ = 0 := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hzero : (informationMatrix P ℓ - efficientInformationMatrix P N ℓ) i i = 0 := by
      rw [h, sub_self, Matrix.zero_apply]
    rw [informationMatrix_sub_efficientInformationMatrix_eq_gram, Matrix.gram_apply,
      inner_self_eq_zero, Submodule.starProjection_apply_eq_zero_iff,
      mem_orthogonal_tangentSpace_iff] at hzero
    exact hzero
  · ext i j
    simp only [efficientInformationMatrix_apply, informationMatrix_apply,
      (efficientScore_eq_self_iff N (ℓ i)).mpr (h i),
      (efficientScore_eq_self_iff N (ℓ j)).mpr (h j)]

end EfficientScore

/-! ### Score operators -/

section ScoreOperators

variable {X : Type*} [MeasurableSpace X]

/-- The tangent space of the range of a score operator `A` with invertible Gram operator `A† A`
equals the range of `A`. -/
theorem tangentSpace_range_eq_range {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule = A.range := by
  have hclosed : IsClosed (A.range : Set (Lp ℝ 2 P)) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
      ContinuousLinearMap.isClosed_range_of_isUnit_adjoint_comp hA
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    toSubmodule_tangentSpace_coe hclosed

/-- The orthogonal projection onto the tangent space of the range of a score operator `A` with
continuously invertible information operator `A† A` is `A (A† A)⁻¹ A†`. -/
theorem starProjection_tangentSpace_range_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule.starProjection =
      A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  have := ContinuousLinearMap.hasOrthogonalProjection_range_of_isUnit_adjoint_comp hA
  rw [← ContinuousLinearMap.gramLeftInverse_def A,
    ← ContinuousLinearMap.starProjection_range_eq hA]
  simp_rw [tangentSpace_range_eq_range A hA]

end ScoreOperators

end MeasureTheory.Measure
