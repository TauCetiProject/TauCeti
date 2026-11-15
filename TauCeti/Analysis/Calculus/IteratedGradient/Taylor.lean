/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction

/-!
# Directional Taylor remainders in iterated-gradient form

Evaluating every slot of `TauCeti.iteratedGradientChain f k x` along a repeated direction `h` via
`TauCeti.IteratedGradient.fullContractL` recovers the diagonal multilinear derivative
`iteratedFDeriv ℝ (k + 1) f x (fun _ ↦ h)` without any smoothness hypothesis on `f`: each step in
the iterated-gradient recursion adds a left Fréchet-derivative slot, and the base step pairs the
gradient with `h` through the Riesz isometry.

Combined with Taylor's theorem with integral remainder
(`map_add_eq_sum_add_integral_iteratedFDeriv`) under the parameter reversal `s = 1 - t` along the
segment from `x` to `y`, this expresses the order-`m` Taylor remainder of `f` at `x` expanded about
`y` as an integral over `s ∈ (0, 1)` at `x + s • (y - x)` weighted by `s ^ m`: the basepoint `x` of
the homothety `y ↦ x + s • (y - x)` is fixed as `y` varies, preparing the spatial ray change of
variables used in potential and averaged Taylor estimates.

## Main declarations

* `TauCeti.IteratedGradient.continuous_contractL`,
  `TauCeti.IteratedGradient.continuous_fullContractL`: continuity of partial and full contractions
  in the direction vector.
* `TauCeti.fullContractL_iteratedGradientChain`: unconditional identification of full contraction
  of `iteratedGradientChain f k x` with `iteratedFDeriv ℝ (k + 1) f x` on a constant tuple.
* `TauCeti.continuousOn_sum_iteratedFDeriv`: continuity of the degree-`m` Taylor sum in the center
  point on an open set.
* `TauCeti.sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv`: Taylor's integral remainder
  parametrized from `x` towards `y` over `s ∈ (0, 1)`.
* `TauCeti.sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL`: the scalar inner-product version
  in terms of `IteratedGradient.fullContractL` and `iteratedGradientChain`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Nat ContDiff

namespace TauCeti.IteratedGradient

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial contraction of `i` outer slots is continuous in the direction vector. -/
@[fun_prop]
theorem continuous_contractL (j i : ℕ) : Continuous (contractL (E := E) j i) := by
  induction i with
  | zero => exact continuous_const.congr fun h ↦ (contractL_zero j h).symm
  | succ i ih =>
      exact (ih.clm_comp
        (ContinuousLinearMap.id ℝ (E →L[ℝ] IteratedGradient E (j + i))).flip.continuous).congr
        fun h ↦ (contractL_succ j i h).symm

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Full contraction of `IteratedGradient E j` is continuous in the direction vector. -/
@[fun_prop]
theorem continuous_fullContractL (j : ℕ) : Continuous (fullContractL (E := E) j) := by
  induction j with
  | zero => exact (innerSL ℝ (E := E)).continuous.congr fun h ↦ (fullContractL_zero h).symm
  | succ j ih =>
      exact (ih.clm_comp
        (ContinuousLinearMap.id ℝ (E →L[ℝ] IteratedGradient E j)).flip.continuous).congr
        fun h ↦ (fullContractL_succ j h).symm

end InnerProductSpace

end TauCeti.IteratedGradient

namespace TauCeti

section ContractionBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Contracting all `k + 1` slots of the `i`th multilinear derivative of `iteratedGradientChain f k`
along a constant tuple `(h, …, h)` recovers the `(k + 1 + i)`th multilinear derivative of `f` on
`(h, …, h)`. No differentiability assumption on `f` is needed. -/
theorem fullContractL_iteratedFDeriv_iteratedGradientChain_const (f : E → ℝ) (i k : ℕ)
    (x h : E) :
    IteratedGradient.fullContractL k h
        (iteratedFDeriv ℝ i (iteratedGradientChain f k) x (fun _ ↦ h)) =
      iteratedFDeriv ℝ (k + 1 + i) f x (fun _ ↦ h) := by
  induction k generalizing i with
  | zero =>
      rw [iteratedGradientChain_zero, IteratedGradient.fullContractL_zero]
      have hgrad : gradient f =
          ⇑(InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv ∘ fderiv ℝ f := rfl
      rw [hgrad, ContinuousLinearEquiv.iteratedFDeriv_comp_left,
        ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        innerSL_apply_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]
      exact (iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := f) (x := x)
        (fun _ : Fin (i + 1) ↦ h)).symm.trans
        (congrArg (fun n ↦ iteratedFDeriv ℝ n f x (fun _ ↦ h)) (by omega))
  | succ k ih =>
      rw [iteratedGradientChain_succ, IteratedGradient.fullContractL_succ,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
      have hstep :
          iteratedFDeriv ℝ i (fderiv ℝ (iteratedGradientChain f k)) x (fun _ ↦ h) h =
            iteratedFDeriv ℝ (i + 1) (iteratedGradientChain f k) x (fun _ ↦ h) :=
        (iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := iteratedGradientChain f k) (x := x)
          (fun _ : Fin (i + 1) ↦ h)).symm
      rw [hstep, ih (i + 1)]
      exact congrArg (fun n ↦ iteratedFDeriv ℝ n f x (fun _ ↦ h)) (by omega)

/-- Full contraction of `iteratedGradientChain f k x` in direction `h` agrees unconditionally with
the `(k + 1)`st multilinear Fréchet derivative of `f` at `x` evaluated on the constant tuple `h`. -/
@[simp]
theorem fullContractL_iteratedGradientChain (f : E → ℝ) (k : ℕ) (x h : E) :
    IteratedGradient.fullContractL k h (iteratedGradientChain f k x) =
      iteratedFDeriv ℝ (k + 1) f x (fun _ ↦ h) := by
  simpa only [iteratedFDeriv_zero_apply] using
    fullContractL_iteratedFDeriv_iteratedGradientChain_const f 0 k x h

end ContractionBridge

section SegmentRemainder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- For a `C^m` map `f : E → F` on an open set `Ω` and a fixed point `x : E`, the degree-`m` Taylor
sum `y ↦ ∑ j ∈ range (m + 1), (j !)⁻¹ • D^j f(y)(x - y, …, x - y)` is continuous on `Ω`. -/
theorem continuousOn_sum_iteratedFDeriv {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} {m : ℕ}
    (hf : ContDiffOn ℝ m f Ω) (x : E) :
    ContinuousOn (fun y ↦ ∑ j ∈ Finset.range (m + 1),
      (j ! : ℝ)⁻¹ • iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) Ω := by
  induction m with
  | zero =>
    simp_rw [zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_zero_apply]
    exact hf.continuousOn
  | succ m ih =>
    simp_rw [Finset.sum_range_succ _ (m + 1)]
    refine (ih (hf.of_le (by simp))).add (continuousOn_const.smul ?_)
    exact continuous_eval.comp_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv (k := m + 1) hf hΩ (by simp)).prodMk
        (continuous_pi fun _ ↦ continuous_const.sub continuous_id).continuousOn)

/-- **Taylor's integral remainder parametrized from the evaluation point.** If `f` is `C^{m+1}` at
every point of the segment `s ↦ x + s • (y - x)` (`s ∈ [0, 1]`), then the remainder of `f x` modulo
its degree-`m` Taylor sum at `y` equals `(m !)⁻¹` times the integral over `s ∈ (0, 1)` of
`s ^ m • D^{m+1} f (x + s • (y - x)) (x - y, …, x - y)`. -/
theorem sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv (f : E → F) (m : ℕ) (x y : E)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + s • (y - x))) :
    f x - ∑ j ∈ Finset.range (m + 1),
        (j ! : ℝ)⁻¹ • iteratedFDeriv ℝ j f y (fun _ ↦ x - y) =
      (m ! : ℝ)⁻¹ • ∫ s in Ioo (0 : ℝ) 1,
        s ^ m • iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ ↦ x - y) := by
  have hseg : ∀ t : ℝ, y + t • (x - y) = x + (1 - t) • (y - x) := fun t ↦ by
    rw [sub_smul, one_smul]
    abel_nf
    module
  have hft : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (y + t • (x - y)) := fun t ht ↦ by
    rw [hseg t]
    exact hf (1 - t) ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := m) hft
  rw [add_sub_cancel, ← sub_eq_iff_eq_add'] at htaylor
  rw [htaylor]
  congr 1
  set g : ℝ → F := fun s ↦ s ^ m • iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ ↦ x - y)
  have hflip : (∫ t in (0 : ℝ)..1,
      (1 - t) ^ m • iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ ↦ x - y)) =
        ∫ t in (0 : ℝ)..1, g (1 - t) :=
    intervalIntegral.integral_congr fun t _ ↦ by simp only [g, hseg t]
  rw [hflip, intervalIntegral.integral_comp_sub_left g 1, sub_self, sub_zero,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

end SegmentRemainder

section InnerProductRemainder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Taylor's integral remainder in iterated-gradient form.** For a real-valued function `f` on a
complete real inner product space that is `C^{m+1}` along the segment between `x` and `y`, the
degree-`m` Taylor remainder of `f x` about `y` is `(m !)⁻¹` times the integral over `s ∈ (0, 1)` of
`s ^ m` against the full contraction of `iteratedGradientChain f m (x + s • (y - x))` in direction
`x - y`. -/
theorem sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL (f : E → ℝ) (m : ℕ) (x y : E)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + s • (y - x))) :
    f x - ∑ j ∈ Finset.range (m + 1),
        (j ! : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y) =
      (m ! : ℝ)⁻¹ * ∫ s in Ioo (0 : ℝ) 1,
        s ^ m * IteratedGradient.fullContractL m (x - y)
          (iteratedGradientChain f m (x + s • (y - x))) := by
  simpa only [smul_eq_mul, fullContractL_iteratedGradientChain] using
    sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv f m x y hf

end InnerProductRemainder

-- Concrete checks: degree-2 expansion of a linear map `t ↦ 2 * t` leaves zero remainder, while
-- degree-0 expansion from `y = 1` to `x = 4` leaves `8 - 2 = 6 = ∫₀¹ 2 * 3 ds`.
example :
    (2 * (4 : ℝ)) - ∑ j ∈ Finset.range 3,
        (j ! : ℝ)⁻¹ * iteratedFDeriv ℝ j (fun t : ℝ ↦ 2 * t) 1 (fun _ ↦ (4 : ℝ) - 1) = 0 := by
  let L : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hclm : (fun t : ℝ ↦ 2 * t) = ⇑L := by ext t; simp [L]
  rw [sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL (fun t : ℝ ↦ 2 * t) 2 4 1
    (fun s _ ↦ by rw [hclm]; exact L.contDiff.contDiffAt)]
  have hgrad : gradient (fun t : ℝ ↦ 2 * t) = Function.const ℝ (2 : ℝ) := by
    ext t
    apply ext_inner_right ℝ fun v ↦ ?_
    rw [gradient, InnerProductSpace.toDual_symm_apply, hclm, L.fderiv]
    simp [L, RCLike.inner_apply, mul_comm]
  have hzero : ∀ z : ℝ, iteratedGradientChain (fun t : ℝ ↦ 2 * t) 2 z = 0 := fun z ↦ by
    rw [iteratedGradientChain_succ, iteratedGradientChain_succ, iteratedGradientChain_zero,
      hgrad, fderiv_const, Pi.zero_def, fderiv_const_apply]
  simp only [hzero, map_zero, mul_zero, integral_zero]

example :
    (2 * (4 : ℝ)) - ∑ j ∈ Finset.range 1,
        (j ! : ℝ)⁻¹ * iteratedFDeriv ℝ j (fun t : ℝ ↦ 2 * t) 1 (fun _ ↦ (4 : ℝ) - 1) = 6 := by
  rw [Finset.sum_range_one, iteratedFDeriv_zero_apply]
  norm_num

end TauCeti
