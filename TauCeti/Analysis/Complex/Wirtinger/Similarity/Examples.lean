/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported
public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Analytic.Order
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Complex.Wirtinger.Radial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Examples for the similarity principle

Four examples calibrating the similarity principle for `∂_s ξ + J ∂_t ξ + C ξ = 0`. With the
convention `bar∂ξ = (∂_s ξ + i ∂_t ξ) / 2` of `TauCeti.conjWirtingerDeriv`, the case `J = i`
reads `2 bar∂ξ + C ξ = 0`.

* The factor `Φ` need not be holomorphic. `ξ z = z e^{-conj z}` solves `bar∂ξ = -ξ`, that is
  `∂_s ξ + i ∂_t ξ + 2 ξ = 0`, and factors as `ξ = Φ σ` with `Φ z = e^{-conj z}` smooth, nowhere
  zero and commuting with `i` (it acts by a complex scalar), and `σ z = z` with a simple zero
  (Mathlib's `analyticOrderAt_id`). `Φ` is not holomorphic anywhere, and `ξ` admits no
  factorization near `0` into two holomorphic factors at all, since `ξ` is not holomorphic at any
  nonzero point.
* The coefficient hypothesis is used. `ξ z = exp (-1 / ‖z‖²)`, with `ξ 0 = 0`, is smooth,
  is `o(‖z‖ⁿ)` at `0` for every `n`, and vanishes nowhere else. Away from the origin it solves
  `2 bar∂ξ + C ξ = 0` exactly for `C z = -2 z / ‖z‖⁴`; at the origin both `ξ` and `bar∂ξ` vanish,
  and the chosen extension is `C 0 = 0`. This coefficient has size `2 ‖z‖⁻³` and is not locally
  `Lᵖ` near `0` for any `p ≥ 1`. So unique continuation fails without a coefficient in
  `L^p_loc`.
* `J` need not be constant. For a family `Φ` of real-linear automorphisms, every `Φ σ` with `σ`
  holomorphic solves the equation for `J = Φ i Φ⁻¹` and `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`. This
  construction lives in `TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported`, which this
  file imports.
* Orders of zeros. `z²` has an isolated zero of order `2` at `0`, and by
  `TauCeti.eq_of_eventually_mul_eq_sub_pow_mul` the exponent of every local factorization
  `e^{-conj z} z² = zᵐ v`, with `v` continuous and nonzero at `0`, is `2`.

## Main declarations

* `TauCeti.fderiv_mul_cexp_neg_conj_add_eq_zero`: `z e^{-conj z}` solves
  `∂_s ξ + i ∂_t ξ + 2 ξ = 0`.
* `TauCeti.not_differentiableAt_cexp_neg_conj`,
  `TauCeti.not_exists_eventually_differentiableAt_mul_cexp_neg_conj_eq`: the factor `e^{-conj z}` is
  nowhere holomorphic, and no holomorphic factorization of `z e^{-conj z}` exists near `0`.
* `TauCeti.expNegInvNormSq_isLittleO_pow`, `TauCeti.expNegInvNormSq_ne_zero`: the flat function
  vanishes to infinite order at `0` and nowhere else.
* `TauCeti.two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero_iff`: the coefficient is forced
  away from the origin.
* `TauCeti.not_memLpLoc_expNegInvNormSqCoeff`: it is locally `Lᵖ` near `0` for no `p ≥ 1`.
* `TauCeti.eq_two_of_eventually_cexp_neg_conj_mul_sq_eq`: `e^{-conj z} z²` has a zero of order
  `2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (Theorem 2.3.5, the Carleman similarity principle).
-/

public noncomputable section

open Complex ComplexConjugate Filter Metric Set Topology MeasureTheory ContinuousLinearMap
open scoped ContDiff

namespace TauCeti

/-! ### A similarity factor that is not holomorphic -/

/-- The real derivative of `z ↦ e^{-conj z}` is `v ↦ -e^{-conj z} conj v`. -/
theorem hasFDerivAt_cexp_neg_conj (z : ℂ) :
    HasFDerivAt (fun w : ℂ ↦ cexp (-conj w))
      (cexp (-conj z) • -conjCLE.toContinuousLinearMap) z :=
  (conjCLE.hasFDerivAt.neg).cexp

/-- `bar∂ e^{-conj z} = -e^{-conj z}`. -/
theorem conjWirtingerDeriv_cexp_neg_conj (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ cexp (-conj w)) z 1 = -cexp (-conj z) := by
  rw [conjWirtingerDeriv_apply, (hasFDerivAt_cexp_neg_conj z).fderiv]
  simp only [smul_apply, neg_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one,
    smul_eq_mul, mul_one, conj_I]
  linear_combination cexp (-conj z) / 2 * I_sq

/-- `ξ z = z e^{-conj z}` solves `bar∂ξ = -ξ`. -/
theorem conjWirtingerDeriv_mul_cexp_neg_conj (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ w * cexp (-conj w)) z 1 = -(z * cexp (-conj z)) := by
  rw [conjWirtingerDeriv_fun_mul (f := fun w ↦ w)
    ((differentiableAt_fun_id (𝕜 := ℂ) (x := z)).restrictScalars ℝ)
    (hasFDerivAt_cexp_neg_conj z).differentiableAt]
  simp [conjWirtingerDeriv_cexp_neg_conj]

/-- `ξ = z e^{-conj z}` solves `∂_s ξ + i ∂_t ξ + 2 ξ = 0`. -/
theorem fderiv_mul_cexp_neg_conj_add_eq_zero (z : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ w * cexp (-conj w)) z 1 +
        I * fderiv ℝ (fun w : ℂ ↦ w * cexp (-conj w)) z I + 2 * (z * cexp (-conj z)) = 0 := by
  have h := conjWirtingerDeriv_mul_cexp_neg_conj z
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at h
  linear_combination 2 * h

/-- The factor `e^{-conj z}` is holomorphic at no point. -/
theorem not_differentiableAt_cexp_neg_conj (z : ℂ) :
    ¬ DifferentiableAt ℂ (fun w : ℂ ↦ cexp (-conj w)) z := fun h ↦ by
  have := conjWirtingerDeriv_cexp_neg_conj z
  rw [h.conjWirtingerDeriv_eq_zero, zero_apply, eq_comm, neg_eq_zero] at this
  exact exp_ne_zero _ this

/-- `z e^{-conj z}` is not holomorphic at any nonzero point. -/
theorem not_differentiableAt_mul_cexp_neg_conj {z : ℂ} (hz : z ≠ 0) :
    ¬ DifferentiableAt ℂ (fun w : ℂ ↦ w * cexp (-conj w)) z := fun h ↦ by
  have := conjWirtingerDeriv_mul_cexp_neg_conj z
  rw [h.conjWirtingerDeriv_eq_zero, zero_apply, eq_comm, neg_eq_zero] at this
  exact mul_ne_zero hz (exp_ne_zero _) this

/-- A similarity principle demanding a holomorphic factor fails for `z e^{-conj z}`: it has no
factorization near `0` into two holomorphic factors. -/
theorem not_exists_eventually_differentiableAt_mul_cexp_neg_conj_eq :
    ¬ ∃ Φ σ : ℂ → ℂ, ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ Φ w ∧ DifferentiableAt ℂ σ w ∧
      w * cexp (-conj w) = Φ w * σ w := by
  rintro ⟨Φ, σ, h⟩
  obtain ⟨w, hw, hw0⟩ := ((h.eventually_nhds.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {w : ℂ | w ≠ 0} ∈ 𝓝[≠] 0)).exists
  refine not_differentiableAt_mul_cexp_neg_conj hw0 ?_
  exact (hw.self_of_nhds.1.mul hw.self_of_nhds.2.1).congr_of_eventuallyEq
    (hw.mono fun y hy ↦ hy.2.2)

/-- The factor `e^{-conj z}` is locally `W^{k,p}` on every set, for every `k` and `p`. -/
theorem memWkpLoc_cexp_neg_conj (p : ENNReal) (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (fun w : ℂ ↦ cexp (-conj w)) :=
  ContDiffOn.memWkpLoc (Ω := ⊤)
    ((contDiff_neg.comp conjCLE.contDiff).cexp.contDiffOn) (subset_univ U)

/-! ### Order of zeros -/

/-- `z²` has an isolated zero of order `2` at `0`. -/
example : analyticOrderAt (fun w : ℂ ↦ w ^ 2) 0 = 2 ∧ ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ^ 2 ≠ 0 :=
  ⟨by simpa [Pi.pow_def] using analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := 2),
    eventually_mem_nhdsWithin.mono fun _ hw ↦ pow_ne_zero 2 hw⟩

/-- `e^{-conj z} z²` has a zero of order `2` at `0`: the exponent of every local factorization
`wᵐ v w`, with `v` continuous and nonzero at `0`, is `2`. -/
theorem eq_two_of_eventually_cexp_neg_conj_mul_sq_eq {v : ℂ → ℂ} {m : ℕ} (hv : ContinuousAt v 0)
    (hv₀ : v 0 ≠ 0) (h : ∀ᶠ w in 𝓝 0, cexp (-conj w) * w ^ 2 = w ^ m * v w) : m = 2 :=
  eq_of_eventually_mul_eq_sub_pow_mul (Φ := fun w ↦ cexp (-conj w)) (σ := fun w ↦ w ^ 2)
    (by fun_prop) (exp_ne_zero _)
    (analyticAt_id.pow 2)
    (by simpa [Pi.pow_def] using analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := 2))
    hv hv₀ (by simpa using h)

/-! ### A flat solution with a non-integrable coefficient -/

/-- `exp (-1 / ‖z‖²)`, extended by `0` at the origin. -/
def expNegInvNormSq (z : ℂ) : ℂ := expNegInvGlue (‖z‖ ^ 2)

/-- `expNegInvNormSq` is Mathlib's `expNegInvGlue` evaluated at `‖z‖²`. -/
theorem expNegInvNormSq_def (z : ℂ) : expNegInvNormSq z = expNegInvGlue (‖z‖ ^ 2) := (rfl)

/-- Away from the origin, `expNegInvNormSq z = exp (-1 / ‖z‖²)`. -/
theorem expNegInvNormSq_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    expNegInvNormSq z = cexp (-1 / (‖z‖ : ℂ) ^ 2) := by
  rw [expNegInvNormSq_def, expNegInvGlue,
    ite_eq_right (not_le.mpr (pow_pos (norm_pos_iff.mpr hz) 2)), ofReal_exp]
  push_cast
  ring_nf

/-- `exp (-1 / ‖z‖²)` is smooth, across the origin. -/
theorem contDiff_expNegInvNormSq : ContDiff ℝ ∞ expNegInvNormSq :=
  ofRealCLM.contDiff.comp (expNegInvGlue.contDiff.comp (contDiff_norm_sq ℝ))

/-- `exp (-1 / ‖z‖²)` vanishes exactly at the origin. -/
@[simp]
theorem expNegInvNormSq_eq_zero_iff {z : ℂ} : expNegInvNormSq z = 0 ↔ z = 0 := by
  simp [expNegInvNormSq_def]

/-- `exp (-1 / ‖z‖²)` vanishes at the origin. -/
theorem expNegInvNormSq_zero : expNegInvNormSq 0 = 0 :=
  expNegInvNormSq_eq_zero_iff.mpr rfl

/-- `exp (-1 / ‖z‖²)` vanishes nowhere except at the origin. -/
theorem expNegInvNormSq_ne_zero {z : ℂ} (hz : z ≠ 0) : expNegInvNormSq z ≠ 0 :=
  mt expNegInvNormSq_eq_zero_iff.mp hz

/-- `exp (-1 / ‖z‖²)` vanishes to infinite order at the origin. -/
theorem expNegInvNormSq_isLittleO_pow (n : ℕ) :
    expNegInvNormSq =o[𝓝 0] fun z ↦ ‖z‖ ^ n := by
  have hN : Tendsto (fun z : ℂ ↦ ‖z‖ ^ 2) (𝓝 0) (𝓝 0) := by
    exact (show Continuous fun z : ℂ ↦ ‖z‖ ^ 2 by fun_prop).tendsto' 0 0 (by simp)
  have hlim : Tendsto (fun z : ℂ ↦ ((‖z‖ ^ 2) ^ n)⁻¹ * expNegInvGlue (‖z‖ ^ 2)) (𝓝 0) (𝓝 0) := by
    simpa [Function.comp_def] using
      (expNegInvGlue.tendsto_polynomial_inv_mul_zero (Polynomial.X ^ n)).comp hN
  refine Asymptotics.isLittleO_iff.mpr fun c hc ↦ ?_
  filter_upwards [hlim (ge_mem_nhds hc), closedBall_mem_nhds (0 : ℂ) one_pos] with z hz hz1
  rw [mem_closedBall_zero_iff] at hz1
  rw [expNegInvNormSq_def, norm_real, Real.norm_of_nonneg (expNegInvGlue.nonneg _), norm_pow,
    norm_norm]
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa [expNegInvGlue.zero] using mul_nonneg hc.le (pow_nonneg le_rfl n)
  have hpos : 0 < (‖z‖ ^ 2) ^ n := by positivity
  rw [mem_preimage, mem_ofPred_eq, inv_mul_le_iff₀ hpos] at hz
  calc expNegInvGlue (‖z‖ ^ 2) ≤ (‖z‖ ^ 2) ^ n * c := hz
    _ ≤ ‖z‖ ^ n * c := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg z) hz1 (by omega)) hc.le
    _ = c * ‖z‖ ^ n := mul_comm _ _

/-- `bar∂ exp (-1 / ‖z‖²) = z / ‖z‖⁴ · exp (-1 / ‖z‖²)`, both sides vanishing at `0`. -/
theorem conjWirtingerDeriv_expNegInvNormSq (z : ℂ) :
    conjWirtingerDeriv expNegInvNormSq z 1 = z / (‖z‖ : ℂ) ^ 4 * expNegInvNormSq z := by
  rw [funext expNegInvNormSq_def,
    conjWirtingerDeriv_ofReal_comp_norm_sq_apply_one (expNegInvGlue.hasDerivAt _)]
  push_cast
  field_simp

/-- The coefficient `C z = -2 z / ‖z‖⁴` forced away from the origin by `2 bar∂ξ + C ξ = 0` for
`ξ = exp (-1 / ‖z‖²)`. Any value at the origin solves the equation there; the chosen extension
is `C 0 = 0`. -/
def expNegInvNormSqCoeff (z : ℂ) : ℂ := -2 * z / (‖z‖ : ℂ) ^ 4

/-- The defining formula `C z = -2 z / ‖z‖⁴`; division by zero gives `C 0 = 0`. -/
theorem expNegInvNormSqCoeff_def (z : ℂ) : expNegInvNormSqCoeff z = -2 * z / (‖z‖ : ℂ) ^ 4 :=
  (rfl)

/-- The coefficient vanishes at the origin. -/
@[simp]
theorem expNegInvNormSqCoeff_zero : expNegInvNormSqCoeff 0 = 0 := by
  simp [expNegInvNormSqCoeff_def]

/-- `ξ = exp (-1 / ‖z‖²)` solves `2 bar∂ξ + C ξ = 0` for `C z = -2 z / ‖z‖⁴`. -/
theorem two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero (z : ℂ) :
    2 * conjWirtingerDeriv expNegInvNormSq z 1 + expNegInvNormSqCoeff z * expNegInvNormSq z =
      0 := by
  rw [conjWirtingerDeriv_expNegInvNormSq, expNegInvNormSqCoeff_def]
  ring

/-- Away from the origin, `-2 z / ‖z‖⁴` is the only value of the coefficient for which
`ξ = exp (-1 / ‖z‖²)` solves `2 bar∂ξ + C ξ = 0`. -/
theorem two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero_iff {z : ℂ} (hz : z ≠ 0) {c : ℂ} :
    2 * conjWirtingerDeriv expNegInvNormSq z 1 + c * expNegInvNormSq z = 0 ↔
      c = expNegInvNormSqCoeff z := by
  have h := two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero z
  refine ⟨fun hc ↦ mul_right_cancel₀ (expNegInvNormSq_ne_zero hz) ?_, fun hc ↦ hc ▸ h⟩
  linear_combination hc - h

/-- The coefficient `-2 z / ‖z‖⁴` has size `2 ‖z‖⁻³`; both sides vanish at `0`. -/
theorem norm_expNegInvNormSqCoeff (z : ℂ) : ‖expNegInvNormSqCoeff z‖ = 2 * ‖z‖ ^ (-3 : ℝ) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have h : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [expNegInvNormSqCoeff_def, norm_div, norm_mul, norm_neg, norm_pow, norm_real, norm_norm,
    Real.rpow_neg h.le, Real.rpow_ofNat, Complex.norm_two]
  field_simp

/-- The coefficient `-2 z / ‖z‖⁴` is not locally `Lᵖ` on any neighbourhood of `0`, for any
`p ≥ 1`. -/
theorem not_memLpLoc_expNegInvNormSqCoeff {p : ENNReal} (hp : 1 ≤ p) {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ¬ MemLpLoc p U expNegInvNormSqCoeff := by
  intro h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp hU
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) r)) :=
    ⟨by simpa using (isCompact_closedBall (0 : ℂ) r).measure_lt_top⟩
  have h0 : IntegrableOn expNegInvNormSqCoeff (closedBall 0 r) :=
    memLp_one_iff_integrable.mp
      ((memLpLoc_iff.mp h _ hrU (isCompact_closedBall 0 r)).mono_exponent hp)
  have h1 : IntegrableOn expNegInvNormSqCoeff (ball 0 r) := h0.mono_set ball_subset_closedBall
  have h3 : IntegrableOn (fun z ↦ 1 / 2 * ‖expNegInvNormSqCoeff z‖) (ball 0 r) :=
    h1.norm.const_mul (1 / 2)
  have h2 : IntegrableOn (fun z : ℂ ↦ ‖z‖ ^ (-3 : ℝ)) (ball 0 r) :=
    h3.congr_fun (fun z _ ↦ by simp only [norm_expNegInvNormSqCoeff]; ring)
      measurableSet_ball
  have := (integrableOn_norm_rpow_ball_iff (mu := volume) hr).mp h2
  rw [Complex.finrank_real_complex] at this
  norm_num at this

end TauCeti
