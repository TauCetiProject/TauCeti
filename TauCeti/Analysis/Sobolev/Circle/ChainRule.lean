/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Sobolev.Circle.Precomp

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.Deriv.AddCircle

/-!
# Circle diffeomorphisms act on `H¹`: the chain rule

A fixed diffeomorphism `φ` of the circle should induce a bounded isomorphism `u ↦ u ∘ φ` of every
Sobolev space `H^s` of boundary maps. `TauCeti/Analysis/Sobolev/Circle/Precomp.lean` treats the
order `s = 0`. This file treats the order `s = 1`, where the new ingredient is the chain rule
`(u ∘ φ)' = φ' · (u' ∘ φ)`.

Let `φ` have the lift `F : ℝ → ℝ`, `F (x + T) = F x + T`, with continuous derivative
`0 < c ≤ F' ≤ M`. For `u ∈ H¹`, the function `u ∘ φ ∈ H⁰` has the weak derivative
`F' · (u' ∘ φ) ∈ H⁰`: its Fourier coefficients are `2πin/T` times those of `u ∘ φ`. For a Fourier
monomial `u` this is integration by parts over a period, and it extends to all of `H¹` because
both sides are continuous in `u`. Hence `u ∘ φ ∈ H¹`, with
`‖u ∘ φ‖_{H¹} ≤ √(2 (1 + M²) / c) ‖u‖_{H¹}`. The inverse of `φ` has the lift `F⁻¹`, whose
derivative lies between `M⁻¹` and `c⁻¹` (`AddCircle.exists_lift_inverse`), so precomposition is a
continuous linear automorphism of `H¹`.

## Main definitions

* `TauCeti.CircleSobolev.precompOneEquivOfLift`: for `φ` with lift `F` and continuous derivative
  `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H¹`.

## Main statements

* `TauCeti.CircleSobolev.inclusion_precompOneEquivOfLift`: in `H⁰` it is the precomposition
  `TauCeti.CircleSobolev.precompEquivOfLift`; similarly for its inverse
  (`TauCeti.CircleSobolev.inclusion_precompOneEquivOfLift_symm`).
* `TauCeti.CircleSobolev.toLpₗᵢ_derivative_precompOneEquivOfLift`: the chain rule
  `(u ∘ φ)' = F' · (u' ∘ φ)` almost everywhere.
* `TauCeti.CircleSobolev.norm_precompOneEquivOfLift_le`: `‖u ∘ φ‖ ≤ √(2 (1 + M²) / c) ‖u‖`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the Sobolev spaces of boundary maps on which
  the Hardy decompositions of cut Riemann surfaces are carried out.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6 (change of variables in Sobolev spaces under diffeomorphisms).
-/

public section

noncomputable section

open MeasureTheory AddCircle Complex Real
open scoped ENNReal

namespace TauCeti

namespace CircleSobolev

variable {T : ℝ} [hT : Fact (0 < T)] {φ : AddCircle T → AddCircle T}

omit hT in
/-- **Integration by parts against a reparametrized monomial.** For a `C¹` lift `F`,
`∫₀ᵀ e_{-n}(y) F'(y) (2πim/T) e_m(F y) dy = (2πin/T) ∫₀ᵀ e_{-n}(y) e_m(F y) dy`, since the
integrand of the difference is the derivative of the `T`-periodic function
`y ↦ e_{-n}(y) e_m(F y)`. -/
private theorem integral_fourier_mul_deriv_fourier_comp {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hper : ∀ x, F (x + T) = F x + T) (hF'c : Continuous F')
    (m n : ℤ) :
    ∫ y in (0 : ℝ)..T, fourier (-n) (y : AddCircle T) *
        ((F' y : ℂ) * (2 * π * I * m / T * fourier m (F y : AddCircle T))) =
      2 * π * I * n / T * ∫ y in (0 : ℝ)..T, fourier (-n) (y : AddCircle T) *
        fourier m (F y : AddCircle T) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  have he (k : ℤ) : Continuous fun y : ℝ ↦ fourier k (y : AddCircle T) :=
    (fourier k).continuous.comp continuous_quotient_mk'
  have hA : Continuous fun y : ℝ ↦ fourier (-n) (y : AddCircle T) *
      fourier m (F y : AddCircle T) := (he _).mul ((he m).comp hFc)
  have hB : Continuous fun y : ℝ ↦ fourier (-n) (y : AddCircle T) *
      ((F' y : ℂ) * (2 * π * I * m / T * fourier m (F y : AddCircle T))) :=
    (he _).mul ((continuous_ofReal.comp hF'c).mul (continuous_const.mul ((he m).comp hFc)))
  -- The derivative of `y ↦ e_{-n}(y) e_m(F y)`.
  have hderiv (y : ℝ) : HasDerivAt
      (fun y : ℝ ↦ fourier (-n) (y : AddCircle T) * fourier m (F y : AddCircle T))
      (2 * π * I * ↑(-n) / T * (fourier (-n) (y : AddCircle T) * fourier m (F y : AddCircle T)) +
        fourier (-n) (y : AddCircle T) *
          ((F' y : ℂ) * (2 * π * I * m / T * fourier m (F y : AddCircle T)))) y := by
    have h : HasDerivAt (fun y : ℝ ↦ fourier m (F y : AddCircle T))
        ((F' y : ℂ) * (2 * π * I * m / T * fourier m (F y : AddCircle T))) y := by
      rw [← real_smul]
      exact (hasDerivAt_fourier T m (F y)).scomp y (hF y)
    convert (hasDerivAt_fourier T (-n) y).mul h using 1
    ring
  have hcA : Continuous fun y : ℝ ↦ 2 * π * I * ↑(-n) / T *
      (fourier (-n) (y : AddCircle T) * fourier m (F y : AddCircle T)) :=
    continuous_const.mul hA
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hderiv y)
    ((hcA.add hB).intervalIntegrable 0 T)
  have hend : fourier (-n) ((T : ℝ) : AddCircle T) * fourier m (F T : AddCircle T) =
      fourier (-n) ((0 : ℝ) : AddCircle T) * fourier m (F 0 : AddCircle T) := by
    rw [show F T = F 0 + T by simpa using hper 0, coe_add, coe_period, add_zero, coe_zero]
  rw [hend, sub_self, intervalIntegral.integral_add
    (hcA.intervalIntegrable 0 T) (hB.intervalIntegrable 0 T),
    intervalIntegral.integral_const_mul] at hFTC
  push_cast at hFTC
  linear_combination hFTC

section Lift

variable {F F' : ℝ → ℝ} {c M : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
  (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (hc : 0 < c)
  (hcF : ∀ x, c ≤ F' x) (hMF : ∀ x, F' x ≤ M) (hF'c : Continuous F')

omit hT in
/-- The derivative `F'` of the lift, as a continuous function on the circle. -/
private def derivOfLift : C(AddCircle T, ℂ) where
  toFun z := ((periodic_deriv_of_lift hF hper).lift z : ℂ)
  continuous_toFun :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ofReal.comp hF'c)

omit hT in
private theorem derivOfLift_coe (x : ℝ) : derivOfLift hF hper hF'c x = F' x :=
  (rfl)

/-- Multiplication by the derivative `F'` of the lift, on `H⁰ = L²`. -/
private def mulDerivOfLift : CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ :=
  (toLpₗᵢ T).symm.toLinearIsometry.toContinuousLinearMap.comp
    (((ContinuousLinearMap.mul ℂ ℂ).holderL haarAddCircle ∞ 2 2
      (ContinuousMap.toLp ∞ haarAddCircle ℂ (derivOfLift hF hper hF'c))).comp
      (toLpₗᵢ T).toLinearIsometry.toContinuousLinearMap)

private theorem toLpₗᵢ_mulDerivOfLift (a : CircleSobolev 0 ℂ) :
    toLpₗᵢ T (mulDerivOfLift hF hper hF'c a) =ᵐ[haarAddCircle]
      fun x ↦ derivOfLift hF hper hF'c x * toLpₗᵢ T a x := by
  simp only [mulDerivOfLift, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.holderL_apply_apply]
  filter_upwards [ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ) (r := 2)
    (ContinuousMap.toLp ∞ haarAddCircle ℂ (derivOfLift hF hper hF'c)) (toLpₗᵢ T a),
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) haarAddCircle (derivOfLift hF hper hF'c)]
    with x h₁ h₂
  rw [h₁, ContinuousLinearMap.mul_apply', h₂]

include hc hcF hMF in
private theorem norm_mulDerivOfLift_le (a : CircleSobolev 0 ℂ) :
    ‖mulDerivOfLift hF hper hF'c a‖ ≤ M * ‖a‖ := by
  rw [← (toLpₗᵢ T).norm_map, ← (toLpₗᵢ T).norm_map a]
  refine Lp.norm_le_mul_norm_of_ae_le_mul
    ((toLpₗᵢ_mulDerivOfLift hF hper hF'c a).mono fun x hx ↦ ?_)
  rw [hx, norm_mul]
  gcongr
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [derivOfLift_coe, norm_real, Real.norm_of_nonneg (hc.le.trans (hcF y))]
  exact hMF y

/-- For `u ∈ H¹`, the coefficients of `u ∘ φ` are the Fourier coefficients of the continuous
function `x ↦ u (φ x)`. -/
private theorem coeff_precompEquivOfLift_inclusion (a : CircleSobolev 1 ℂ) (n : ℤ) :
    (precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a)).coeff n =
      fourierCoeff (fun x ↦ toContinuousMap T (by norm_num) a (φ x)) n := by
  have hφc := continuous_of_lift (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hφ
  rw [precompEquivOfLift_apply, ← fourierCoeff_toLpₗᵢ T,
    toLpₗᵢ_precomp_inclusion (by norm_num) hφc, fourierCoeff_toLp]
  rfl

/-- For `u ∈ H¹`, the coefficients of `F' · (u ∘ φ)` are the Fourier coefficients of the
continuous function `x ↦ F' x u (φ x)`. -/
private theorem coeff_mulDerivOfLift_precompEquivOfLift_inclusion (a : CircleSobolev 1 ℂ)
    (n : ℤ) :
    (mulDerivOfLift hF hper hF'c
        (precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a))).coeff n =
      fourierCoeff (fun x ↦ derivOfLift hF hper hF'c x * toContinuousMap T (by norm_num) a (φ x))
        n := by
  have hφc := continuous_of_lift (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hφ
  rw [← fourierCoeff_toLpₗᵢ T, fourierCoeff, fourierCoeff]
  refine integral_congr_ae ?_
  have h := toLpₗᵢ_precomp_inclusion (s := 1) (by norm_num) hφc
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')
    (map_haarAddCircle_le_of_lift hF hper hφ hc hcF) a
  filter_upwards [toLpₗᵢ_mulDerivOfLift hF hper hF'c
    (precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle
      ((toContinuousMap T (show (1 : ℝ) / 2 < 1 by norm_num) a).comp ⟨φ, hφc⟩)] with x h₁ h₂
  rw [h₁, precompEquivOfLift_apply, h, h₂]
  rfl

/-- **The weak chain rule.** For `u ∈ H¹`, the Fourier coefficients of `F' · (u' ∘ φ)` are
`2πin/T` times those of `u ∘ φ`. Both sides are continuous in `u ∈ H¹`, so it suffices to check
this on Fourier monomials, where it is integration by parts over one period. -/
private theorem coeff_mulDerivOfLift_precompEquivOfLift_derivative (a : CircleSobolev 1 ℂ)
    (n : ℤ) :
    (mulDerivOfLift hF hper hF'c (precompEquivOfLift hF hper hφ hc hcF hMF
        (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a))).coeff n =
      (2 * π * I * n / T : ℂ) •
        (precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a)).coeff n := by
  set P := (precompEquivOfLift hF hper hφ hc hcF hMF :
    CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ)
  have h := congr($(continuousLinearMap_ext_single
    (f := (coeffCLM n).comp ((mulDerivOfLift hF hper hF'c).comp
      (P.comp (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num)))))
    (g := (2 * π * I * n / T : ℂ) • (coeffCLM n).comp (P.comp (inclusion zero_le_one)))
    fun m x ↦ ?_) a)
  · simpa [P] using h
  have key := integral_fourier_mul_deriv_fourier_comp hF hper hF'c m n
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, coeffCLM_apply,
    derivative_single, P, ContinuousLinearEquiv.coe_coe]
  rw [← inclusion_single (zero_le_one' ℝ), coeff_mulDerivOfLift_precompEquivOfLift_inclusion,
    coeff_precompEquivOfLift_inclusion, fourierCoeff_eq_intervalIntegral _ n 0,
    fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
  have h₁ : ∫ y in (0 : ℝ)..T, fourier (-n) (y : AddCircle T) • (derivOfLift hF hper hF'c y *
        toContinuousMap T (by norm_num) (single m ((2 * π * I * m / T : ℂ) • x) :
          CircleSobolev 1 ℂ) (φ y)) =
      (∫ y in (0 : ℝ)..T, fourier (-n) (y : AddCircle T) *
        ((F' y : ℂ) * (2 * π * I * m / T * fourier m (F y : AddCircle T)))) * x := by
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [toContinuousMap_single, smul_eq_mul, ContinuousMap.mul_apply,
      ContinuousMap.const_apply, derivOfLift_coe, hφ]
    ring
  have h₂ : ∫ y in (0 : ℝ)..T, fourier (-n) (y : AddCircle T) •
        toContinuousMap T (by norm_num) (single m x : CircleSobolev 1 ℂ) (φ y) =
      (∫ y in (0 : ℝ)..T, fourier (-n) (y : AddCircle T) * fourier m (F y : AddCircle T)) * x := by
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [toContinuousMap_single, smul_eq_mul, ContinuousMap.mul_apply,
      ContinuousMap.const_apply, hφ]
    ring
  rw [h₁, h₂, key]
  simp only [real_smul, smul_eq_mul]
  ring

include hF'c in
/-- For `u ∈ H¹`, the coefficients of `u ∘ φ ∈ H⁰` are those of an element of `H¹`. -/
private theorem memℓp_precompEquivOfLift_inclusion (a : CircleSobolev 1 ℂ) :
    Memℓp (fun n ↦ weight 1 n •
      (precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a)).coeff n) 2 := by
  obtain ⟨b, hb, -⟩ := exists_inclusion_eq_and_derivative_eq T _ _
    (coeff_mulDerivOfLift_precompEquivOfLift_derivative hF hper hφ hc hcF hMF hF'c a)
  have h := b.memℓp_weight_smul_coeff
  simp only [zero_add] at h
  simpa only [← hb, coeff_inclusion] using h

/-- Precomposition with `φ` on `H¹`. -/
private def precompOne : CircleSobolev 1 ℂ →ₗ[ℂ] CircleSobolev 1 ℂ where
  toFun a := ⟨_, memℓp_precompEquivOfLift_inclusion hF hper hφ hc hcF hMF hF'c a⟩
  map_add' a b := CircleSobolev.ext (by simp)
  map_smul' z a := CircleSobolev.ext (by simp)

private theorem inclusion_precompOne (a : CircleSobolev 1 ℂ) :
    inclusion zero_le_one (precompOne hF hper hφ hc hcF hMF hF'c a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a) :=
  CircleSobolev.ext (by simp [precompOne])

private theorem derivative_precompOne (a : CircleSobolev 1 ℂ) :
    derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) (precompOne hF hper hφ hc hcF hMF hF'c a) =
      mulDerivOfLift hF hper hF'c (precompEquivOfLift hF hper hφ hc hcF hMF
        (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)) :=
  CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_mulDerivOfLift_precompEquivOfLift_derivative, coeff_derivative]
    simp [precompOne])

/-- The norm bound `‖u ∘ φ‖ ≤ √(2 (1 + M²) / c) ‖u‖` on `H¹`. -/
private theorem norm_precompOne_le (a : CircleSobolev 1 ℂ) :
    ‖precompOne hF hper hφ hc hcF hMF hF'c a‖ ≤ √(2 * (1 + M ^ 2) / c) * ‖a‖ := by
  have hT₀ : T / (2 * π) * (2 * π / T) = 1 := by field_simp [hT.out.ne']
  have hM : 0 ≤ M := hc.le.trans ((hcF 0).trans (hMF 0))
  have h := norm_sq_le_of_derivative T (show (0 : ℝ) + 1 = 1 by norm_num)
    (precompOne hF hper hφ hc hcF hMF hF'c a)
  rw [inclusion_precompOne, derivative_precompOne] at h
  -- `‖u ∘ φ‖_{H⁰} ≤ c^(-1/2) ‖u‖_{H¹}` and `‖F' · (u' ∘ φ)‖_{H⁰} ≤ M c^(-1/2) 2π/T ‖u‖_{H¹}`.
  have h₀ : ‖precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a)‖ ≤
      (√c)⁻¹ * ‖a‖ :=
    (norm_precompEquivOfLift_le hF hper hφ hc hcF hMF _).trans
      (mul_le_mul_of_nonneg_left (norm_inclusion_le _ a) (by positivity))
  have h₁ : ‖mulDerivOfLift hF hper hF'c (precompEquivOfLift hF hper hφ hc hcF hMF
      (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a))‖ ≤
      M * ((√c)⁻¹ * (2 * π / T * ‖a‖)) :=
    (norm_mulDerivOfLift_le hF hper hc hcF hMF hF'c _).trans (mul_le_mul_of_nonneg_left
      ((norm_precompEquivOfLift_le hF hper hφ hc hcF hMF _).trans (mul_le_mul_of_nonneg_left
        (norm_derivative_le T _ a) (by positivity))) hM)
  have hc' : ((√c)⁻¹) ^ 2 = c⁻¹ := by rw [inv_pow, Real.sq_sqrt hc.le]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg a),
    ← Real.sqrt_mul' _ (sq_nonneg _)]
  refine Real.sqrt_le_sqrt (h.trans ?_)
  calc 2 * ‖precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a)‖ ^ 2 +
        2 * (T / (2 * π)) ^ 2 * ‖mulDerivOfLift hF hper hF'c (precompEquivOfLift hF hper hφ hc
          hcF hMF (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a))‖ ^ 2
      ≤ 2 * ((√c)⁻¹ * ‖a‖) ^ 2 +
          2 * (T / (2 * π)) ^ 2 * (M * ((√c)⁻¹ * (2 * π / T * ‖a‖))) ^ 2 := by
        gcongr
    _ = 2 * (1 + M ^ 2 * (T / (2 * π) * (2 * π / T)) ^ 2) * ((√c)⁻¹) ^ 2 * ‖a‖ ^ 2 := by ring
    _ = 2 * (1 + M ^ 2) / c * ‖a‖ ^ 2 := by rw [hT₀, hc']; ring

/-- Precomposition with `φ` on `H¹`, as a continuous linear map. -/
private def precompOneCLM : CircleSobolev 1 ℂ →L[ℂ] CircleSobolev 1 ℂ :=
  (precompOne hF hper hφ hc hcF hMF hF'c).mkContinuous √(2 * (1 + M ^ 2) / c)
    (norm_precompOne_le hF hper hφ hc hcF hMF hF'c)

private theorem precompOneCLM_apply (a : CircleSobolev 1 ℂ) :
    precompOneCLM hF hper hφ hc hcF hMF hF'c a = precompOne hF hper hφ hc hcF hMF hF'c a :=
  (rfl)


private theorem inclusion_precompOneCLM (a : CircleSobolev 1 ℂ) :
    inclusion zero_le_one (precompOneCLM hF hper hφ hc hcF hMF hF'c a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a) := by
  rw [precompOneCLM_apply, inclusion_precompOne]

/-- The inverse `G` of the lift `F`: a lift of the inverse map of the circle, with derivative
`(F' ∘ G)⁻¹` (`AddCircle.exists_lift_inverse`). -/
private def invLift : ℝ → ℝ :=
  (exists_lift_inverse hF hper fun x ↦ hc.trans_le (hcF x)).choose

private theorem invLift_spec :
    Function.LeftInverse (invLift hF hper hc hcF) F ∧
      Function.RightInverse (invLift hF hper hc hcF) F ∧
      (∀ y, invLift hF hper hc hcF (y + T) = invLift hF hper hc hcF y + T) ∧
      ∀ y, HasDerivAt (invLift hF hper hc hcF) (F' (invLift hF hper hc hcF y))⁻¹ y :=
  (exists_lift_inverse hF hper fun x ↦ hc.trans_le (hcF x)).choose_spec

/-- The inverse map of the circle. -/
private def invMap : AddCircle T → AddCircle T :=
  (homeomorphOfLift φ (strictMono_of_hasDerivAt_pos hF fun x ↦ hc.trans_le (hcF x))
    (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hper hφ).symm

private theorem invMap_leftInverse : Function.LeftInverse (invMap hF hper hφ hc hcF) φ :=
  homeomorphOfLift_symm_apply_apply _ _ _ _

private theorem invMap_coe (y : ℝ) : invMap hF hper hφ hc hcF y = invLift hF hper hc hcF y := by
  have h : ((y : ℝ) : AddCircle T) = φ (invLift hF hper hc hcF y) := by
    rw [hφ, (invLift_spec hF hper hc hcF).2.1 y]
  rw [h, invMap_leftInverse]

private theorem hasDerivAt_invLift (y : ℝ) :
    HasDerivAt (invLift hF hper hc hcF) (F' (invLift hF hper hc hcF y))⁻¹ y :=
  (invLift_spec hF hper hc hcF).2.2.2 y

private theorem invLift_add_period (y : ℝ) :
    invLift hF hper hc hcF (y + T) = invLift hF hper hc hcF y + T :=
  (invLift_spec hF hper hc hcF).2.2.1 y

include hMF in
private theorem inv_le_inv_deriv_invLift (y : ℝ) : M⁻¹ ≤ (F' (invLift hF hper hc hcF y))⁻¹ :=
  inv_anti₀ (hc.trans_le (hcF _)) (hMF _)

private theorem inv_deriv_invLift_le (y : ℝ) : (F' (invLift hF hper hc hcF y))⁻¹ ≤ c⁻¹ :=
  inv_anti₀ hc (hcF _)

include hc hcF hMF in
private theorem inv_pos_of_lift : 0 < M⁻¹ :=
  inv_pos.2 (hc.trans_le ((hcF 0).trans (hMF 0)))

include hF'c in
private theorem continuous_inv_deriv_invLift :
    Continuous fun y ↦ (F' (invLift hF hper hc hcF y))⁻¹ :=
  (hF'c.comp (continuous_iff_continuousAt.2 fun y ↦
    (hasDerivAt_invLift hF hper hc hcF y).continuousAt)).inv₀ fun _ ↦ (hc.trans_le (hcF _)).ne'

/-- Precomposition with the inverse map of the circle on `H¹`. -/
private def precompOneInvCLM : CircleSobolev 1 ℂ →L[ℂ] CircleSobolev 1 ℂ :=
  precompOneCLM (hasDerivAt_invLift hF hper hc hcF)
    (invLift_add_period hF hper hc hcF) (invMap_coe hF hper hφ hc hcF) (inv_pos_of_lift hc hcF hMF)
    (inv_le_inv_deriv_invLift hF hper hc hcF hMF) (inv_deriv_invLift_le hF hper hc hcF)
    (continuous_inv_deriv_invLift hF hper hc hcF hF'c)

private theorem precompOneInvCLM_apply (a : CircleSobolev 1 ℂ) :
    precompOneInvCLM hF hper hφ hc hcF hMF hF'c a =
      precompOne (hasDerivAt_invLift hF hper hc hcF) (invLift_add_period hF hper hc hcF)
        (invMap_coe hF hper hφ hc hcF) (inv_pos_of_lift hc hcF hMF)
        (inv_le_inv_deriv_invLift hF hper hc hcF hMF) (inv_deriv_invLift_le hF hper hc hcF)
        (continuous_inv_deriv_invLift hF hper hc hcF hF'c) a :=
  (rfl)

private theorem inclusion_precompOneInvCLM (a : CircleSobolev 1 ℂ) :
    inclusion zero_le_one (precompOneInvCLM hF hper hφ hc hcF hMF hF'c a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion zero_le_one a) := by
  rw [precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF (hasDerivAt_invLift hF hper hc hcF)
      (invLift_add_period hF hper hc hcF) (invMap_coe hF hper hφ hc hcF)
      (inv_pos_of_lift hc hcF hMF) (inv_le_inv_deriv_invLift hF hper hc hcF hMF)
      (inv_deriv_invLift_le hF hper hc hcF)
      (invMap_leftInverse hF hper hφ hc hcF), precompOneInvCLM_apply, inclusion_precompOne]

/-- **Circle diffeomorphisms act on `H¹`.** Let `φ` be the map of the circle with lift `F`, so
that `F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` has a continuous derivative with
`0 < c ≤ F' ≤ M`. Then `u ↦ u ∘ φ` is a continuous linear automorphism of `H¹`, whose inverse is
precomposition with the inverse map of the circle. -/
def precompOneEquivOfLift : CircleSobolev 1 ℂ ≃L[ℂ] CircleSobolev 1 ℂ :=
  ContinuousLinearEquiv.equivOfInverse (precompOneCLM hF hper hφ hc hcF hMF hF'c)
    (precompOneInvCLM hF hper hφ hc hcF hMF hF'c)
    (fun a ↦ inclusion_injective zero_le_one (by
      rw [inclusion_precompOneInvCLM, inclusion_precompOneCLM]
      exact (precompEquivOfLift hF hper hφ hc hcF hMF).symm_apply_apply _))
    (fun a ↦ inclusion_injective zero_le_one (by
      rw [inclusion_precompOneCLM, inclusion_precompOneInvCLM]
      exact (precompEquivOfLift hF hper hφ hc hcF hMF).apply_symm_apply _))

/-- In `H⁰`, precomposition on `H¹` is the precomposition `precompEquivOfLift`: the inclusion of
`u ∘ φ` into `H⁰` is the precomposition of the inclusion of `u`. -/
@[simp]
theorem inclusion_precompOneEquivOfLift (a : CircleSobolev 1 ℂ) :
    inclusion zero_le_one (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion zero_le_one a) :=
  inclusion_precompOneCLM hF hper hφ hc hcF hMF hF'c a

/-- In `H⁰`, the inverse of precomposition on `H¹` is the inverse of `precompEquivOfLift`. -/
@[simp]
theorem inclusion_precompOneEquivOfLift_symm (a : CircleSobolev 1 ℂ) :
    inclusion zero_le_one ((precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c).symm a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion zero_le_one a) :=
  inclusion_precompOneInvCLM hF hper hφ hc hcF hMF hF'c a

private theorem precompOneEquivOfLift_apply (a : CircleSobolev 1 ℂ) :
    precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c a = precompOne hF hper hφ hc hcF hMF hF'c a :=
  (rfl)

private theorem precompOneEquivOfLift_symm_apply (a : CircleSobolev 1 ℂ) :
    (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c).symm a =
      precompOneInvCLM hF hper hφ hc hcF hMF hF'c a :=
  (rfl)

/-- **The chain rule.** For `u ∈ H¹`, the derivative of `u ∘ φ` is `F' · (u' ∘ φ)` almost
everywhere, where `f'` is the function `F'` regarded on the circle. -/
theorem toLpₗᵢ_derivative_precompOneEquivOfLift {f' : AddCircle T → ℝ}
    (hf' : ∀ x : ℝ, f' x = F' x) (a : CircleSobolev 1 ℂ) :
    toLpₗᵢ T (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num)
        (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c a)) =ᵐ[haarAddCircle]
      fun x ↦ (f' x : ℂ) * toLpₗᵢ T (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a) (φ x) := by
  rw [precompOneEquivOfLift_apply, derivative_precompOne]
  filter_upwards [toLpₗᵢ_mulDerivOfLift hF hper hF'c (precompEquivOfLift hF hper hφ hc hcF hMF
    (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)),
    toLpₗᵢ_precompEquivOfLift hF hper hφ hc hcF hMF
      (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)] with x h₁ h₂
  rw [h₁, h₂]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [Function.comp_apply, derivOfLift_coe, ← hf']

/-- The norm of precomposition with a circle diffeomorphism on `H¹`:
`‖u ∘ φ‖ ≤ √(2 (1 + M²) / c) ‖u‖`. -/
theorem norm_precompOneEquivOfLift_le (a : CircleSobolev 1 ℂ) :
    ‖precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c a‖ ≤ √(2 * (1 + M ^ 2) / c) * ‖a‖ := by
  rw [precompOneEquivOfLift_apply]
  exact norm_precompOne_le hF hper hφ hc hcF hMF hF'c a

/-- The norm of the inverse of precomposition with a circle diffeomorphism on `H¹`:
`‖u ∘ φ⁻¹‖ ≤ √(2 (1 + c⁻²) M) ‖u‖`. -/
theorem norm_precompOneEquivOfLift_symm_le (a : CircleSobolev 1 ℂ) :
    ‖(precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c).symm a‖ ≤
      √(2 * (1 + c⁻¹ ^ 2) * M) * ‖a‖ := by
  rw [precompOneEquivOfLift_symm_apply, precompOneInvCLM_apply,
    show 2 * (1 + c⁻¹ ^ 2) * M = 2 * (1 + c⁻¹ ^ 2) / M⁻¹ by rw [div_inv_eq_mul]]
  exact norm_precompOne_le (hasDerivAt_invLift hF hper hc hcF)
    (invLift_add_period hF hper hc hcF) (invMap_coe hF hper hφ hc hcF) (inv_pos_of_lift hc hcF hMF)
    (inv_le_inv_deriv_invLift hF hper hc hcF hMF) (inv_deriv_invLift_le hF hper hc hcF)
    (continuous_inv_deriv_invLift hF hper hc hcF hF'c) a

end Lift

end CircleSobolev

end TauCeti
