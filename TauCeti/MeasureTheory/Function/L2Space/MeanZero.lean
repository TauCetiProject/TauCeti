/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Const

/-!
# Mean-zero subspace of `L²`

On a finite measure space `(X, P)` and for a Hilbert space `E` over `𝕜`, the closed subspace
`L²₀(P)` (`MeasureTheory.Measure.meanZeroL2 P 𝕜`) consists of square-integrable `E`-valued functions
with vanishing integral, defined as the orthogonal complement of the constant functions
`LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P)` in `Lp E 2 P`.

`L²₀(P)` complements the subspace of constant functions and is complete, so it admits an orthogonal
projection. On a finite measure space, the orthogonal projection onto `L²₀(P)` subtracts the
`P`-average; on a probability space it subtracts the integral. Transferring `Lp.simpleFunc.dense`
by centering along this projection shows that bounded mean-zero functions are dense in `L²₀(P)`
(`MeasureTheory.Measure.meanZeroL2_subset_closure_bounded`); see
`TauCeti.MeasureTheory.Function.L2Space.MeanZero.Density` for bounded continuous density.

## Main definitions

* `MeasureTheory.Measure.meanZeroL2`: the closed subspace `L²₀(P)` of mean-zero elements of
  `Lp E 2 P`.

## Main results

* `MeasureTheory.Measure.mem_meanZeroL2_iff`: `f ∈ P.meanZeroL2 𝕜 ↔ ∫ x, f x ∂P = 0`.
* `MeasureTheory.Measure.isClosed_meanZeroL2`, `MeasureTheory.Measure.completeSpace_meanZeroL2`:
  `L²₀(P)` is closed and complete.
* `MeasureTheory.Measure.hasOrthogonalProjection_range_constₗ`,
  `MeasureTheory.Measure.starProjection_range_constₗ`: the constant functions admit an
  orthogonal projection equal to the `P`-average.
* `MeasureTheory.Measure.isCompl_range_constₗ_meanZeroL2`: `Lp E 2 P` splits into the constant
  functions and `L²₀(P)`.
* `MeasureTheory.Measure.starProjection_meanZeroL2_eq_sub_const_average`,
  `MeasureTheory.Measure.starProjection_meanZeroL2`: the orthogonal projection onto `L²₀(P)`
  subtracts the average (the mean on a probability space).
* `MeasureTheory.Measure.meanZeroL2_subset_closure_bounded`: density of bounded mean-zero elements
  in `L²₀(P)`, obtained by centering `Lp.simpleFunc.dense`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.2,
  pp. 360–362, for the orthogonal decomposition into constants and `L²₀(P)` and the centering
  projection on probability spaces.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The closed subspace `L²₀(P)` of mean-zero elements of `Lp E 2 P`, defined as the orthogonal
complement of the constant functions `LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P)`. -/
def meanZeroL2 (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : Submodule 𝕜 (Lp E 2 P) :=
  (LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P))ᗮ

theorem meanZeroL2_def (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    meanZeroL2 P 𝕜 (E := E) = (LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P))ᗮ :=
  (rfl)

/-- An element of `Lp E 2 P` lies in `meanZeroL2 P 𝕜` if and only if its integral vanishes. -/
@[simp]
theorem mem_meanZeroL2_iff {P : Measure X} [IsFiniteMeasure P] {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    {f : Lp E 2 P} :
    f ∈ meanZeroL2 P 𝕜 ↔ ∫ x, f x ∂P = 0 := by
  rw [meanZeroL2_def, Submodule.mem_orthogonal]
  simp only [LinearMap.mem_range, Lp.constₗ_apply, forall_exists_index, forall_apply_eq_imp_iff,
    L2.inner_const_left]
  exact ⟨fun h ↦ inner_self_eq_zero.mp (h _), fun h c ↦ by rw [h, inner_zero_right]⟩

/-- The mean-zero subspace `L²₀(P)` is closed in `Lp E 2 P`. -/
theorem isClosed_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    IsClosed (meanZeroL2 P 𝕜 (E := E) : Set (Lp E 2 P)) :=
  Submodule.isClosed_orthogonal _

/-- The mean-zero subspace `L²₀(P)` is complete, and hence admits orthogonal projections. -/
instance completeSpace_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*) {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    CompleteSpace (meanZeroL2 P 𝕜 (E := E)) :=
  (isClosed_meanZeroL2 P 𝕜).isComplete.completeSpace_coe

/-- Subtracting the `P`-average yields an element of `L²₀(P)`. -/
theorem sub_const_average_mem_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {𝕜 E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    (f : Lp E 2 P) :
    f - Lp.const 2 P (⨍ x, f x ∂P) ∈ meanZeroL2 P 𝕜 := by
  rw [mem_meanZeroL2_iff, integral_congr_ae (Lp.coeFn_sub_const f (⨍ x, f x ∂P))]
  exact integral_sub_average P (f : X → E)

/-- The subspace of constant functions in `Lp E 2 P` admits an orthogonal projection. -/
instance hasOrthogonalProjection_range_constₗ (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*)
    {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] :
    (LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P)).HasOrthogonalProjection :=
  ⟨fun f ↦ ⟨Lp.const 2 P (⨍ x, f x ∂P), ⟨_, rfl⟩, sub_const_average_mem_meanZeroL2 f⟩⟩

/-- On a finite measure space, the orthogonal projection onto the constant functions is the
`P`-average. -/
theorem starProjection_range_constₗ {P : Measure X} [IsFiniteMeasure P]
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] (f : Lp E 2 P) :
    (LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P)).starProjection f =
      Lp.const 2 P (⨍ x, f x ∂P) :=
  Submodule.eq_starProjection_of_mem_orthogonal ⟨_, rfl⟩ (sub_const_average_mem_meanZeroL2 f)

/-- `Lp E 2 P` decomposes as the direct sum of the constant functions and `L²₀(P)`. -/
theorem isCompl_range_constₗ_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*)
    {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] :
    IsCompl (LinearMap.range (Lp.constₗ 2 P 𝕜 : E →ₗ[𝕜] Lp E 2 P)) (meanZeroL2 P 𝕜) := by
  rw [meanZeroL2_def]
  exact Submodule.isCompl_orthogonal _

/-- For a Dirac measure, every mean-zero element of `L²` vanishes. -/
@[simp]
theorem meanZeroL2_dirac (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] (x : X) :
    meanZeroL2 (dirac x) 𝕜 (E := E) = ⊥ := by
  borelize E
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [mem_meanZeroL2_iff] at hf
  obtain ⟨g, hg, hfg⟩ := Lp.aestronglyMeasurable f
  have hgx : g x = 0 := by
    rw [← integral_dirac' g x hg, ← integral_congr_ae hfg]
    exact hf
  have hg0 : g =ᵐ[dirac x] (0 : X → E) :=
    (ae_eq_dirac' (a := x) hg.measurable).mono fun _ h ↦ h.trans hgx
  exact Lp.ext (hfg.trans (hg0.trans (Lp.coeFn_zero E 2 (dirac x)).symm))

/-- On a finite measure space, the orthogonal projection onto `L²₀(P)` subtracts the `P`-average. -/
theorem starProjection_meanZeroL2_eq_sub_const_average {P : Measure X} [IsFiniteMeasure P]
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] (f : Lp E 2 P) :
    (meanZeroL2 P 𝕜).starProjection f = f - Lp.const 2 P (⨍ x, f x ∂P) := by
  -- `Submodule.HasOrthogonalProjection` is a `Prop`, so `simp_rw` unifies the projection instances.
  simp_rw [meanZeroL2_def]
  rw [Submodule.starProjection_orthogonal_val, starProjection_range_constₗ]

/-- On a probability space, subtracting the mean yields an element of `L²₀(P)`. -/
theorem sub_const_integral_mem_meanZeroL2 {P : Measure X} [IsProbabilityMeasure P] {𝕜 E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    (f : Lp E 2 P) :
    f - Lp.const 2 P (∫ x, f x ∂P) ∈ meanZeroL2 P 𝕜 := by
  rw [← average_eq_integral]
  exact sub_const_average_mem_meanZeroL2 f

/-- On a probability space, the orthogonal projection onto `L²₀(P)` subtracts the mean. -/
theorem starProjection_meanZeroL2 {P : Measure X} [IsProbabilityMeasure P] {𝕜 E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    (f : Lp E 2 P) :
    (meanZeroL2 P 𝕜).starProjection f = f - Lp.const 2 P (∫ x, f x ∂P) := by
  rw [starProjection_meanZeroL2_eq_sub_const_average, average_eq_integral]

/-- Bounded mean-zero elements are dense in `L²₀(P)`, obtained by centering
`Lp.simpleFunc.dense`. -/
theorem meanZeroL2_subset_closure_bounded (P : Measure X) [IsFiniteMeasure P] (𝕜 : Type*)
    {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] :
    (meanZeroL2 P 𝕜 (E := E) : Set (Lp E 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P 𝕜 ∧ ∃ C, ∀ᵐ x ∂P, ‖u x‖ ≤ C} := by
  rw [← (meanZeroL2 P 𝕜 (E := E)).closure_image_starProjection_of_dense
    (Lp.simpleFunc.dense (by norm_num))]
  refine closure_mono ?_
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  let s : SimpleFunc X E := Lp.simpleFunc.toSimpleFunc ⟨v, hv⟩
  have hvs : (v : X → E) =ᵐ[P] s := (Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨v, hv⟩).symm
  obtain ⟨C, hC⟩ := s.exists_forall_norm_le
  refine ⟨C + ‖⨍ x, v x ∂P‖, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_const_average]
  filter_upwards [Lp.coeFn_sub_const v (⨍ x, v x ∂P), hvs] with x hsub hxs
  rw [hsub, hxs]
  exact (norm_sub_le (s x) _).trans (add_le_add (hC x) le_rfl)

end MeasureTheory.Measure
