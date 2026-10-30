/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Sobolev.Circle.Multiplier
public import TauCeti.Analysis.Sobolev.Circle.Precomp

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.Deriv.AddCircle
import TauCeti.Analysis.Fourier.Monomial

/-!
# Circle diffeomorphisms act on `H^k`: the chain rule

A fixed diffeomorphism `φ` of the circle should induce a bounded isomorphism `u ↦ u ∘ φ` of every
Sobolev space `H^s` of boundary maps. `TauCeti/Analysis/Sobolev/Circle/Precomp.lean` treats the
order `s = 0`. This file treats the order `s = 1`, where the new ingredient is the chain rule
`(u ∘ φ)' = φ' · (u' ∘ φ)`, and then every integer order `s = k ≥ 0` for smooth `φ`.

Let `φ` have the lift `F : ℝ → ℝ`, `F (x + T) = F x + T`, with continuous derivative
`0 < c ≤ F' ≤ M`. For `u ∈ H¹`, the function `u ∘ φ ∈ H⁰` has the weak derivative
`F' · (u' ∘ φ) ∈ H⁰`: its Fourier coefficients are `2πin/T` times those of `u ∘ φ`. For a Fourier
monomial `u` this is integration by parts over a period, and it extends to all of `H¹` because
both sides are continuous in `u`. Hence `u ∘ φ ∈ H¹`, with
`‖u ∘ φ‖_{H¹} ≤ √(2 (1 + M²) / c) ‖u‖_{H¹}`. The inverse of `φ` has the lift `F⁻¹`, whose
derivative lies between `M⁻¹` and `c⁻¹` (`AddCircle.exists_lift_inverse`), so precomposition is a
continuous linear automorphism of `H¹`.

If `F'` is smooth, the chain rule is the inductive step for the orders `k : ℕ`. Suppose that
precomposition preserves `H^k` and let `u ∈ H^(k + 1)`. Then `u ∘ φ` and `u' ∘ φ` lie in `H^k`.
Multiplication by the smooth function `F'` preserves `H^k`
(`TauCeti.CircleSobolev.mulFourierSeries`), so the derivative `F' · (u' ∘ φ)` of `u ∘ φ` lies in
`H^k`, and hence `u ∘ φ ∈ H^(k + 1)`. Precomposition is continuous on `H^k` by the closed graph
theorem, since the inclusion `H^k → H⁰` is injective. The inverse lift `F⁻¹` is smooth by the
inverse function theorem, so precomposition is a continuous linear automorphism of `H^k`.

## Main definitions

* `TauCeti.CircleSobolev.precompOneEquivOfLift`: for `φ` with lift `F` and continuous derivative
  `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H¹`.
* `TauCeti.CircleSobolev.precompNatEquivOfLift k`: for `φ` with lift `F` and smooth derivative
  `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H^k`, for `k : ℕ`.

## Main statements

* `TauCeti.CircleSobolev.inclusion_precompOneEquivOfLift`: in `H⁰` it is the precomposition
  `TauCeti.CircleSobolev.precompEquivOfLift`; similarly for its inverse
  (`TauCeti.CircleSobolev.inclusion_precompOneEquivOfLift_symm`), and for every order `k`
  (`TauCeti.CircleSobolev.inclusion_precompNatEquivOfLift`,
  `TauCeti.CircleSobolev.inclusion_precompNatEquivOfLift_symm`).
* `TauCeti.CircleSobolev.toLpₗᵢ_derivative_precompOneEquivOfLift`: the chain rule
  `(u ∘ φ)' = F' · (u' ∘ φ)` almost everywhere.
* `TauCeti.CircleSobolev.norm_precompOneEquivOfLift_le`: `‖u ∘ φ‖ ≤ √(2 (1 + M²) / c) ‖u‖`.
* `TauCeti.CircleSobolev.precompOneEquivOfLift_symm_eq` and
  `TauCeti.CircleSobolev.precompNatEquivOfLift_symm_eq`: the inverse is precomposition with the
  inverse map of the circle, presented by any of its lifts.
* `TauCeti.CircleSobolev.inclusion_precompNatEquivOfLift_of_le`: the automorphisms of the
  different `H^k` commute with the inclusions `H^l → H^k`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the Sobolev spaces of boundary maps on which
  the Hardy decompositions of cut Riemann surfaces are carried out.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6 (change of variables in Sobolev spaces under diffeomorphisms).
-/

public section

noncomputable section

open MeasureTheory AddCircle Complex Real Filter Topology
open scoped ENNReal

namespace TauCeti

namespace CircleSobolev

variable {T : ℝ} [hT : Fact (0 < T)] {φ : AddCircle T → AddCircle T}

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
  multiplicationOperator (ContinuousMap.toLp ∞ haarAddCircle ℂ (derivOfLift hF hper hF'c))

private theorem toLpₗᵢ_mulDerivOfLift (a : CircleSobolev 0 ℂ) :
    toLpₗᵢ T (mulDerivOfLift hF hper hF'c a) =ᵐ[haarAddCircle]
      fun x ↦ derivOfLift hF hper hF'c x * toLpₗᵢ T a x := by
  filter_upwards [toLpₗᵢ_multiplicationOperator_ae
    (ContinuousMap.toLp ∞ haarAddCircle ℂ (derivOfLift hF hper hF'c)) a,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) haarAddCircle (derivOfLift hF hper hF'c)]
    with x h₁ h₂
  rw [mulDerivOfLift, h₁, h₂]

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

/-- The inverse of `precompOneEquivOfLift` is `precompOneEquivOfLift` for the inverse map `ψ` of
the circle, presented by any lift `G` of `ψ` with continuous derivative between two positive
constants. -/
theorem precompOneEquivOfLift_symm_eq {ψ : AddCircle T → AddCircle T} {G G' : ℝ → ℝ}
    {c' M' : ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hperG : ∀ x, G (x + T) = G x + T)
    (hψ : ∀ x : ℝ, ψ x = G x) (hc' : 0 < c') (hcG : ∀ x, c' ≤ G' x) (hMG : ∀ x, G' x ≤ M')
    (hG'c : Continuous G') (hψφ : Function.LeftInverse ψ φ) :
    (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'c).symm =
      precompOneEquivOfLift hG hperG hψ hc' hcG hMG hG'c :=
  ContinuousLinearEquiv.ext <| funext fun a ↦ inclusion_injective zero_le_one (by
    rw [inclusion_precompOneEquivOfLift_symm, inclusion_precompOneEquivOfLift,
      precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hc' hcG hMG hψφ])

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

/-! ### Smooth circle diffeomorphisms act on `H^k` -/

section Smooth

open scoped ContDiff

variable {F F' : ℝ → ℝ} {c M : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
  (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (hc : 0 < c)
  (hcF : ∀ x, c ≤ F' x) (hMF : ∀ x, F' x ≤ M) (hF' : ContDiff ℝ ∞ F')

omit hT in
private theorem contDiff_derivOfLift :
    ContDiff ℝ ∞ fun x : ℝ ↦ derivOfLift hF hper hF'.continuous x := by
  simp only [derivOfLift_coe]
  exact ofRealCLM.contDiff.comp hF'

/-- Multiplication by the smooth function `F'` preserves `H^k`. -/
private theorem mulDerivOfLift_inclusion (k : ℕ) (w : CircleSobolev k ℂ) :
    mulDerivOfLift hF hper hF'.continuous (inclusion (Nat.cast_nonneg k) w) =
      inclusion (Nat.cast_nonneg k)
        (mulFourierSeries (fourierCoeff (derivOfLift hF hper hF'.continuous)) w) := by
  rw [inclusion_mulFourierSeries _
      (summable_weight_mul_norm_fourierCoeff_of_contDiff (contDiff_derivOfLift hF hper hF') _)
      (summable_weight_mul_norm_fourierCoeff_of_contDiff (contDiff_derivOfLift hF hper hF') _),
    mulDerivOfLift,
    mulFourierSeries_fourierCoeff_eq_multiplicationOperator _ (contDiff_derivOfLift hF hper hF')]

include hF' in
/-- Precomposition with `φ` maps `H^k` into `H^k`: the image in `H⁰` of an element of `H^k` is the
image of an element of `H^k`. The proof is by induction on `k`, with the chain rule as the
inductive step. -/
private theorem exists_inclusion_eq_precompEquivOfLift (k : ℕ) (a : CircleSobolev k ℂ) :
    ∃ b : CircleSobolev k ℂ, inclusion (Nat.cast_nonneg k) b =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a) := by
  induction k with
  | zero =>
    refine ⟨inclusion (by simp) (precompEquivOfLift hF hper hφ hc hcF hMF
      (inclusion (Nat.cast_nonneg 0) a)), ?_⟩
    rw [inclusion_inclusion, inclusion_refl]
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : ℝ) = k + 1 := Nat.cast_succ k
    have hk₁ : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by simp
    have hkk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by simp
    -- `u ∘ φ ∈ H^k`, represented by `uₖ`, and `u' ∘ φ ∈ H^k`, represented by `w`.
    obtain ⟨uₖ, huₖ⟩ := ih (inclusion hkk a)
    rw [inclusion_inclusion] at huₖ
    obtain ⟨w, hw⟩ := ih (derivative T hk.ge a)
    -- In `H¹`, `u ∘ φ` has derivative `F' · (u' ∘ φ)`, the image of `F' · w ∈ H^k`.
    set u := precompOne hF hper hφ hc hcF hMF hF'.continuous (inclusion hk₁ a)
    have hu : inclusion zero_le_one u = inclusion (Nat.cast_nonneg k) uₖ := by
      rw [inclusion_precompOne, inclusion_inclusion, huₖ]
    have hdu : derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) u = inclusion (Nat.cast_nonneg k)
        (mulFourierSeries (fourierCoeff (derivOfLift hF hper hF'.continuous)) w) := by
      rw [derivative_precompOne, derivative_inclusion,
        ← inclusion_derivative T (Nat.cast_nonneg k) hk.ge, ← hw,
        mulDerivOfLift_inclusion hF hper hF']
    -- Hence `u ∘ φ ∈ H^(k + 1)`.
    obtain ⟨b, hb, -⟩ := exists_inclusion_eq_and_derivative_eq T uₖ _ fun n ↦ by
      have h₁ := congr(($hdu).coeff n)
      have h₂ := congr(($hu).coeff n)
      simp only [coeff_derivative, coeff_inclusion] at h₁ h₂
      rw [← h₁, h₂]
    refine ⟨inclusion hk.le b, ?_⟩
    rw [inclusion_inclusion, ← huₖ, ← hb, inclusion_inclusion]

include hF' in
private theorem memℓp_precompEquivOfLift_inclusion_nat (k : ℕ) (a : CircleSobolev k ℂ) :
    Memℓp (fun n ↦ weight k n •
      (precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a)).coeff n) 2 := by
  obtain ⟨b, hb⟩ := exists_inclusion_eq_precompEquivOfLift hF hper hφ hc hcF hMF hF' k a
  simpa only [← hb, coeff_inclusion] using b.memℓp_weight_smul_coeff

/-- Precomposition with `φ` on `H^k`. -/
private def precompNat (k : ℕ) : CircleSobolev k ℂ →ₗ[ℂ] CircleSobolev k ℂ where
  toFun a := ⟨_, memℓp_precompEquivOfLift_inclusion_nat hF hper hφ hc hcF hMF hF' k a⟩
  map_add' a b := CircleSobolev.ext (by simp)
  map_smul' z a := CircleSobolev.ext (by simp)

private theorem inclusion_precompNat (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) (precompNat hF hper hφ hc hcF hMF hF' k a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a) :=
  CircleSobolev.ext (by simp [precompNat])

/-- Precomposition with `φ` on `H^k`, as a continuous linear map. It is continuous by the closed
graph theorem: its composite with the injective inclusion `H^k → H⁰` is continuous. -/
private def precompNatCLM (k : ℕ) : CircleSobolev k ℂ →L[ℂ] CircleSobolev k ℂ where
  toLinearMap := precompNat hF hper hφ hc hcF hMF hF' k
  cont := (precompNat hF hper hφ hc hcF hMF hF' k).continuous_of_seq_closed_graph
    fun u x y hu hy ↦ inclusion_injective (Nat.cast_nonneg k) <| tendsto_nhds_unique
      (((inclusion (Nat.cast_nonneg k)).continuous.tendsto y).comp hy) <| by
        simp only [Function.comp_def, inclusion_precompNat]
        exact ((precompEquivOfLift hF hper hφ hc hcF hMF).continuous.tendsto _).comp
          (((inclusion (Nat.cast_nonneg k)).continuous.tendsto x).comp hu)

private theorem inclusion_precompNatCLM (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) (precompNatCLM hF hper hφ hc hcF hMF hF' k a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a) :=
  inclusion_precompNat hF hper hφ hc hcF hMF hF' k a

include hF' in
/-- The derivative `(F' ∘ G)⁻¹` of the inverse lift `G` is smooth, by the inverse function
theorem. -/
private theorem contDiff_inv_deriv_invLift :
    ContDiff ℝ ∞ fun y ↦ (F' (invLift hF hper hc hcF y))⁻¹ := by
  let e : ℝ ≃ₜ ℝ :=
    { toFun := F
      invFun := invLift hF hper hc hcF
      left_inv := (invLift_spec hF hper hc hcF).1
      right_inv := (invLift_spec hF hper hc hcF).2.1
      continuous_toFun := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
      continuous_invFun := continuous_iff_continuousAt.2 fun y ↦
        (hasDerivAt_invLift hF hper hc hcF y).continuousAt }
  have hFs : ContDiff ℝ ∞ F := contDiff_infty_iff_deriv.2
    ⟨fun x ↦ (hF x).differentiableAt, by rwa [show deriv F = F' from funext fun x ↦ (hF x).deriv]⟩
  have hG : ContDiff ℝ ∞ (invLift hF hper hc hcF) :=
    e.contDiff_symm_deriv (fun x ↦ (hc.trans_le (hcF x)).ne') hF hFs
  exact (hF'.comp hG).inv fun y ↦ (hc.trans_le (hcF _)).ne'

/-- Precomposition with the inverse map of the circle on `H^k`. -/
private def precompNatInvCLM (k : ℕ) : CircleSobolev k ℂ →L[ℂ] CircleSobolev k ℂ :=
  precompNatCLM (hasDerivAt_invLift hF hper hc hcF) (invLift_add_period hF hper hc hcF)
    (invMap_coe hF hper hφ hc hcF) (inv_pos_of_lift hc hcF hMF)
    (inv_le_inv_deriv_invLift hF hper hc hcF hMF) (inv_deriv_invLift_le hF hper hc hcF)
    (contDiff_inv_deriv_invLift hF hper hc hcF hF') k

private theorem inclusion_precompNatInvCLM (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) (precompNatInvCLM hF hper hφ hc hcF hMF hF' k a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion (Nat.cast_nonneg k) a) := by
  rw [precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF (hasDerivAt_invLift hF hper hc hcF)
      (invLift_add_period hF hper hc hcF) (invMap_coe hF hper hφ hc hcF)
      (inv_pos_of_lift hc hcF hMF) (inv_le_inv_deriv_invLift hF hper hc hcF hMF)
      (inv_deriv_invLift_le hF hper hc hcF) (invMap_leftInverse hF hper hφ hc hcF)]
  exact inclusion_precompNatCLM _ _ _ _ _ _ _ k a

/-- **Smooth circle diffeomorphisms act on `H^k`.** Let `φ` be the map of the circle with lift `F`,
so that `F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` has a smooth derivative with
`0 < c ≤ F' ≤ M`. Then for every `k : ℕ`, `u ↦ u ∘ φ` is a continuous linear automorphism of
`H^k`, whose inverse is precomposition with the inverse map of the circle. -/
def precompNatEquivOfLift (k : ℕ) : CircleSobolev k ℂ ≃L[ℂ] CircleSobolev k ℂ :=
  ContinuousLinearEquiv.equivOfInverse (precompNatCLM hF hper hφ hc hcF hMF hF' k)
    (precompNatInvCLM hF hper hφ hc hcF hMF hF' k)
    (fun a ↦ inclusion_injective (Nat.cast_nonneg k) (by
      rw [inclusion_precompNatInvCLM, inclusion_precompNatCLM]
      exact (precompEquivOfLift hF hper hφ hc hcF hMF).symm_apply_apply _))
    (fun a ↦ inclusion_injective (Nat.cast_nonneg k) (by
      rw [inclusion_precompNatCLM, inclusion_precompNatInvCLM]
      exact (precompEquivOfLift hF hper hφ hc hcF hMF).apply_symm_apply _))

/-- In `H⁰`, precomposition on `H^k` is the precomposition `precompEquivOfLift`: the inclusion of
`u ∘ φ` into `H⁰` is the precomposition of the inclusion of `u`. -/
@[simp]
theorem inclusion_precompNatEquivOfLift (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a) :=
  inclusion_precompNatCLM hF hper hφ hc hcF hMF hF' k a

/-- In `H⁰`, the inverse of precomposition on `H^k` is the inverse of `precompEquivOfLift`. -/
@[simp]
theorem inclusion_precompNatEquivOfLift_symm (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) ((precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k).symm a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion (Nat.cast_nonneg k) a) :=
  inclusion_precompNatInvCLM hF hper hφ hc hcF hMF hF' k a

/-- Precomposition commutes with the inclusions `H^l → H^k` for `k ≤ l`. -/
theorem inclusion_precompNatEquivOfLift_of_le {k l : ℕ} (h : k ≤ l) (a : CircleSobolev l ℂ) :
    inclusion (Nat.cast_le.2 h) (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' l a) =
      precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k (inclusion (Nat.cast_le.2 h) a) :=
  inclusion_injective (Nat.cast_nonneg k) (by simp)

/-- The inverse of `precompNatEquivOfLift` is `precompNatEquivOfLift` for the inverse map `ψ` of
the circle, presented by any lift `G` of `ψ` with smooth derivative between two positive
constants. -/
theorem precompNatEquivOfLift_symm_eq {ψ : AddCircle T → AddCircle T} {G G' : ℝ → ℝ}
    {c' M' : ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hperG : ∀ x, G (x + T) = G x + T)
    (hψ : ∀ x : ℝ, ψ x = G x) (hc' : 0 < c') (hcG : ∀ x, c' ≤ G' x) (hMG : ∀ x, G' x ≤ M')
    (hG' : ContDiff ℝ ∞ G') (hψφ : Function.LeftInverse ψ φ) (k : ℕ) :
    (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k).symm =
      precompNatEquivOfLift hG hperG hψ hc' hcG hMG hG' k :=
  ContinuousLinearEquiv.ext <| funext fun a ↦ inclusion_injective (Nat.cast_nonneg k) (by
    rw [inclusion_precompNatEquivOfLift_symm, inclusion_precompNatEquivOfLift,
      precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hc' hcG hMG hψφ])

end Smooth

end CircleSobolev

end TauCeti
