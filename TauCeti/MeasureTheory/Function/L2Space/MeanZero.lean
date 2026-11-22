/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.MeasureTheory.Function.L2Space.Basic

/-!
# Mean-zero subspace of `L²`

On a finite measure space `(X, P)`, the closed subspace `L²₀(P)`
(`MeasureTheory.Measure.meanZeroL2 P`) consists of square-integrable real functions with vanishing
integral, defined as the orthogonal complement of the constant functions in `Lp ℝ 2 P`.

`L²₀(P)` complements the subspace spanned by the constant function `1` (which is one-dimensional
when `P ≠ 0`) and is complete, so it admits an orthogonal projection. On a finite measure space,
the orthogonal projection onto `L²₀(P)` subtracts the `P`-average; on a probability space it
subtracts the integral. Both bounded measurable and (on a normal Borel space with a weakly regular
measure) bounded continuous mean-zero functions are dense in `L²₀(P)`.

## Main definitions

* `MeasureTheory.Measure.meanZeroL2`: the closed subspace `L²₀(P)` of mean-zero elements of
  `Lp ℝ 2 P`.

## Main results

* `MeasureTheory.Measure.mem_meanZeroL2_iff`: `f ∈ P.meanZeroL2 ↔ ∫ x, f x ∂P = 0`.
* `MeasureTheory.Measure.isClosed_meanZeroL2`, `MeasureTheory.Measure.completeSpace_meanZeroL2`:
  `L²₀(P)` is closed and complete.
* `MeasureTheory.Measure.isCompl_span_const_meanZeroL2`: `Lp ℝ 2 P` splits into the constants and
  `L²₀(P)`.
* `MeasureTheory.Measure.starProjection_meanZeroL2_eq_sub_const_average`,
  `MeasureTheory.Measure.starProjection_meanZeroL2`: the orthogonal projection onto `L²₀(P)`
  subtracts the average (the mean on a probability space).
* `MeasureTheory.Measure.meanZeroL2_subset_closure_bounded`,
  `MeasureTheory.Measure.meanZeroL2_subset_closure_boundedContinuous`: density of bounded and
  bounded continuous mean-zero elements in `L²₀(P)`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.2,
  pp. 360–362, for the orthogonal decomposition into constants and `L²₀(P)` and the centering
  projection on probability spaces.
-/

public section

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The closed subspace `L²₀(P)` of mean-zero elements of `Lp ℝ 2 P`, defined as the orthogonal
complement of the constant functions. -/
def meanZeroL2 (P : Measure X) [IsFiniteMeasure P] : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ

theorem meanZeroL2_def (P : Measure X) [IsFiniteMeasure P] :
    meanZeroL2 P = (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ :=
  (rfl)

/-- An element of `Lp ℝ 2 P` lies in `meanZeroL2 P` if and only if its integral vanishes. -/
@[simp]
theorem mem_meanZeroL2_iff {P : Measure X} [IsFiniteMeasure P] {f : Lp ℝ 2 P} :
    f ∈ meanZeroL2 P ↔ ∫ x, f x ∂P = 0 := by
  rw [meanZeroL2_def, Submodule.mem_orthogonal_singleton_iff_inner_right, L2.inner_const_one]

/-- The mean-zero subspace `L²₀(P)` is closed in `Lp ℝ 2 P`. -/
theorem isClosed_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    IsClosed (meanZeroL2 P : Set (Lp ℝ 2 P)) :=
  Submodule.isClosed_orthogonal _

/-- The mean-zero subspace `L²₀(P)` is complete, and hence admits orthogonal projections. -/
instance completeSpace_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    CompleteSpace (meanZeroL2 P) :=
  (isClosed_meanZeroL2 P).isComplete.completeSpace_coe

/-- `Lp ℝ 2 P` decomposes as the direct sum of the constant functions and `L²₀(P)`. -/
theorem isCompl_span_const_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    IsCompl (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)}) (meanZeroL2 P) := by
  rw [meanZeroL2_def]
  exact Submodule.isCompl_orthogonal _

/-- For a Dirac measure, every mean-zero element of `L²` vanishes. -/
@[simp]
theorem meanZeroL2_dirac (x : X) : meanZeroL2 (dirac x) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [mem_meanZeroL2_iff] at hf
  obtain ⟨g, hg, hfg⟩ := Lp.aestronglyMeasurable f
  have hgx : g x = 0 := by
    rw [← integral_dirac' g x hg, ← integral_congr_ae hfg]
    exact hf
  have hg0 : g =ᵐ[dirac x] (0 : X → ℝ) :=
    (ae_eq_dirac' (a := x) hg.measurable).mono fun _ h ↦ h.trans hgx
  exact Lp.ext (hfg.trans (hg0.trans (Lp.coeFn_zero ℝ 2 (dirac x)).symm))

/-- On a finite measure space, the orthogonal projection onto `L²₀(P)` subtracts the `P`-average. -/
theorem starProjection_meanZeroL2_eq_sub_const_average {P : Measure X} [IsFiniteMeasure P]
    (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (⨍ x, f x ∂P) := by
  have hnorm : ‖Lp.const 2 P (1 : ℝ)‖ ^ 2 = P.real Set.univ := by
    rw [← real_inner_self_eq_norm_sq, ← indicatorConstLp_univ,
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, Set.inter_self]
  have hsmul (c : ℝ) : c • Lp.const 2 P (1 : ℝ) = Lp.const 2 P c := by
    simpa [mul_one] using ((Lp.constₗ 2 P ℝ).map_smul c (1 : ℝ)).symm
  dsimp only [meanZeroL2]
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton ℝ f, L2.inner_const_one, hnorm, average_eq, smul_eq_mul,
    ← div_eq_inv_mul, hsmul]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-- On a probability space, subtracting the mean yields an element of `L²₀(P)`. -/
theorem sub_const_integral_mem_meanZeroL2 {P : Measure X} [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    f - Lp.const 2 P (∫ x, f x ∂P) ∈ meanZeroL2 P := by
  rw [← average_eq_integral, ← starProjection_meanZeroL2_eq_sub_const_average]
  exact Submodule.starProjection_apply_mem _ _

/-- On a probability space, the orthogonal projection onto `L²₀(P)` subtracts the mean. -/
theorem starProjection_meanZeroL2 {P : Measure X} [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (∫ x, f x ∂P) := by
  rw [starProjection_meanZeroL2_eq_sub_const_average, average_eq_integral]

/-- Bounded mean-zero elements are dense in `L²₀(P)`. -/
theorem meanZeroL2_subset_closure_bounded (P : Measure X) [IsFiniteMeasure P] :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P ∧ ∃ C, ∀ᵐ x ∂P, |u x| ≤ C} := by
  rw [← (meanZeroL2 P).closure_image_starProjection_of_dense (Lp.simpleFunc.dense (by norm_num))]
  refine closure_mono ?_
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  let s : SimpleFunc X ℝ := Lp.simpleFunc.toSimpleFunc ⟨v, hv⟩
  have hvs : (v : X → ℝ) =ᵐ[P] s := (Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨v, hv⟩).symm
  obtain ⟨C, hC⟩ := s.exists_forall_norm_le
  refine ⟨C + |⨍ x, v x ∂P|, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_const_average]
  filter_upwards [Lp.coeFn_sub_const v (⨍ x, v x ∂P), hvs] with x hsub hxs
  rw [hsub, hxs]
  exact (abs_sub (s x) _).trans (add_le_add (Real.norm_eq_abs _ ▸ hC x) le_rfl)

/-- On a normal space with its Borel σ-algebra and a weakly regular finite measure `P`, bounded
continuous mean-zero functions are dense in `L²₀(P)`. -/
theorem meanZeroL2_subset_closure_boundedContinuous (P : Measure X) [IsFiniteMeasure P]
    [TopologicalSpace X] [NormalSpace X] [BorelSpace X] [P.WeaklyRegular] :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P ∧ ∃ g : X →ᵇ ℝ, (u : X → ℝ) =ᵐ[P] g} := by
  rw [← (meanZeroL2 P).closure_image_starProjection_of_dense
    (BoundedContinuousFunction.toLp_denseRange ℝ ℝ (p := 2) (μ := P) (by norm_num))]
  refine closure_mono ?_
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  set c := ⨍ x, (BoundedContinuousFunction.toLp 2 P ℝ g : X → ℝ) x ∂P
  refine ⟨g - BoundedContinuousFunction.const X c, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_const_average]
  filter_upwards [Lp.coeFn_sub_const (BoundedContinuousFunction.toLp 2 P ℝ g) c,
    BoundedContinuousFunction.coeFn_toLp 2 P ℝ g] with x hsub hg
  rw [hsub, hg]
  simp only [FunLike.coe_sub, BoundedContinuousFunction.const_apply, Pi.sub_apply]

end MeasureTheory.Measure
