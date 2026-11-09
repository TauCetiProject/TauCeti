/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Similarity
public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Analytic.Order
import TauCeti.MeasureTheory.Integral.NormRpow
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Examples for the similarity principle

Four examples calibrating the similarity principle for `∂_s ξ + J ∂_t ξ + C ξ = 0`. With the
convention `bar∂ξ = (∂_s ξ + i ∂_t ξ) / 2` of `TauCeti.conjWirtingerDeriv`, the case `J = i`
reads `2 bar∂ξ + C ξ = 0`.

* The factor `Φ` need not be holomorphic. `ξ z = z e^{-conj z}` solves `bar∂ξ = -ξ`, that is
  `∂_s ξ + i ∂_t ξ + 2 ξ = 0`, and factors as `ξ = Φ σ` with `Φ z = e^{-conj z}` smooth, nowhere
  zero and commuting with `i` (it acts by a complex scalar), and `σ z = z` with a simple zero.
  `Φ` is not holomorphic anywhere, and `ξ` admits no factorization near `0` into two
  holomorphic factors at all, since `ξ` is not holomorphic at any nonzero point.
* The coefficient hypothesis is used. `ξ z = exp (-1 / ‖z‖²)`, with `ξ 0 = 0`, is smooth,
  is `o(‖z‖ⁿ)` at `0` for every `n`, and vanishes nowhere else. It solves `2 bar∂ξ + C ξ = 0`
  exactly for `C z = -2 z / ‖z‖⁴`, of size `2 ‖z‖⁻³`, which is not locally `Lᵖ` near `0` for any
  `p ≥ 1`. So unique continuation fails without a coefficient in `L^p_loc`.
* `J` need not be constant. For a differentiable family `Φ` of real-linear automorphisms of a
  complex normed space, `J = Φ i Φ⁻¹` is a complex structure with `J Φ = Φ i`, and with
  `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹` every `ξ = Φ σ` with `σ` holomorphic solves the equation.
  For `C¹` families with continuous inverse, `C` is continuous, hence locally `Lᵖ`. The
  opposite normalization is excluded: if `J' Φ = -Φ i` at `z₀`, then `ξ w = Φ w ((w - z₀) v)`,
  `v ≠ 0`, fails `∂_s ξ + J' ∂_t ξ + C' ξ = 0` at `z₀` for every `C'`.
* Orders of zeros. `z²` has an isolated zero of order `2` at `0`, and for `Φ` continuous and
  nonzero at a point and `σ` holomorphic, the exponent of every local factorization
  `Φ σ = (w - z)ᵐ v`, with `v` continuous and nonzero at `z`, is the order of `σ`.

## Main declarations

* `TauCeti.fderiv_mul_cexp_neg_conj_add_eq_zero`: `z e^{-conj z}` solves
  `∂_s ξ + i ∂_t ξ + 2 ξ = 0`.
* `TauCeti.not_differentiableAt_cexp_neg_conj`,
  `TauCeti.not_exists_eventually_differentiableAt_mul_cexp_neg_conj_eq`: the factor `e^{-conj z}` is
  nowhere holomorphic, and no holomorphic factorization of `z e^{-conj z}` exists near `0`.
* `TauCeti.expNegInvNormSq_isLittleO_pow`, `TauCeti.expNegInvNormSq_ne_zero`: the flat function
  vanishes to infinite order at `0` and nowhere else.
* `TauCeti.two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero_iff`: the coefficient is forced.
* `TauCeti.not_memLpLoc_expNegInvNormSqCoeff`: it is locally `Lᵖ` near `0` for no `p ≥ 1`.
* `TauCeti.fderiv_apply_add_transportedComplexStructure_add_eq_zero`: `Φ σ` solves the equation
  for `J = Φ i Φ⁻¹`.
* `TauCeti.fderiv_apply_smul_add_ne_zero`: the normalization `J' Φ = -Φ i` fails.
* `TauCeti.eq_of_eventually_mul_eq_sub_pow_mul`: zero orders of `Φ σ` are those of `σ`.

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

/-- The factor `σ z = z` of `z e^{-conj z}` has a simple zero at `0`. -/
theorem analyticOrderAt_id_zero : analyticOrderAt (fun w : ℂ ↦ w) 0 = 1 := by
  simpa using analyticOrderAt_id_sub_const_self (c := (0 : ℂ))

/-! ### Order of zeros -/

/-- If `Φ` is continuous and nonzero at `z` and `σ` is analytic with a zero of order `n` at `z`,
then `Φ σ` factors near `z` as `(w - z) ^ n` times a function continuous and nonzero at `z`. -/
theorem exists_eventually_mul_eq_sub_pow_mul {Φ σ : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΦ : ContinuousAt Φ z) (hΦ₀ : Φ z ≠ 0) (hσ : AnalyticAt ℂ σ z)
    (hn : analyticOrderAt σ z = n) :
    ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, Φ w * σ w = (w - z) ^ n * v w := by
  obtain ⟨g, hg, hg₀, hgσ⟩ := hσ.analyticOrderAt_eq_natCast.mp hn
  refine ⟨fun w ↦ Φ w * g w, hΦ.mul hg.continuousAt, mul_ne_zero hΦ₀ hg₀, ?_⟩
  filter_upwards [hgσ] with w hw
  rw [hw, smul_eq_mul]
  ring

/-- The zero orders of `Φ σ` are those of `σ`: for `Φ` continuous and nonzero at `z` and `σ`
analytic with a zero of order `n` at `z`, every local factorization `Φ σ = (w - z) ^ m v`, with `v`
continuous and nonzero at `z`, has `m = n`. -/
theorem eq_of_eventually_mul_eq_sub_pow_mul {Φ σ v : ℂ → ℂ} {z : ℂ} {m n : ℕ}
    (hΦ : ContinuousAt Φ z) (hΦ₀ : Φ z ≠ 0) (hσ : AnalyticAt ℂ σ z)
    (hn : analyticOrderAt σ z = n) (hv : ContinuousAt v z) (hv₀ : v z ≠ 0)
    (h : ∀ᶠ w in 𝓝 z, Φ w * σ w = (w - z) ^ m * v w) : m = n := by
  obtain ⟨u, hu, hu₀, hσu⟩ := exists_eventually_mul_eq_sub_pow_mul hΦ hΦ₀ hσ hn
  exact eq_of_eventually_sub_pow_mul_eq hv hv₀ hu hu₀ <| by
    filter_upwards [h, hσu] with w hw hw'
    rw [← hw, hw']

/-- `z²` has a zero of order `2` at `0`. -/
theorem analyticOrderAt_sq_zero : analyticOrderAt (fun w : ℂ ↦ w ^ 2) 0 = 2 := by
  change analyticOrderAt ((fun w : ℂ ↦ w) ^ 2) 0 = 2
  rw [analyticOrderAt_pow (f := fun w : ℂ ↦ w) analyticAt_id, analyticOrderAt_id_zero]
  rfl

/-- The zero of `z²` at `0` is isolated. -/
theorem eventually_sq_ne_zero : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ^ 2 ≠ 0 :=
  eventually_mem_nhdsWithin.mono fun _ hw ↦ pow_ne_zero 2 hw

/-- `e^{-conj z} z²` has a zero of order `2` at `0`: the exponent of every local factorization
`wᵐ v w`, with `v` continuous and nonzero at `0`, is `2`. -/
theorem eq_two_of_eventually_cexp_neg_conj_mul_sq_eq {v : ℂ → ℂ} {m : ℕ} (hv : ContinuousAt v 0)
    (hv₀ : v 0 ≠ 0) (h : ∀ᶠ w in 𝓝 0, cexp (-conj w) * w ^ 2 = w ^ m * v w) : m = 2 :=
  eq_of_eventually_mul_eq_sub_pow_mul (Φ := fun w ↦ cexp (-conj w)) (σ := fun w ↦ w ^ 2)
    (by fun_prop) (exp_ne_zero _)
    (analyticAt_id.pow 2) analyticOrderAt_sq_zero hv hv₀ (by simpa using h)

/-! ### A flat solution with a non-integrable coefficient -/

/-- `exp (-1 / ‖z‖²)`, extended by `0` at the origin. -/
def expNegInvNormSq (z : ℂ) : ℂ := expNegInvGlue (‖z‖ ^ 2)

/-- `exp (-1 / ‖z‖²)` is smooth, across the origin. -/
theorem contDiff_expNegInvNormSq : ContDiff ℝ ∞ expNegInvNormSq :=
  ofRealCLM.contDiff.comp (expNegInvGlue.contDiff.comp (contDiff_norm_sq ℝ))

/-- `exp (-1 / ‖z‖²)` vanishes at the origin. -/
@[simp]
theorem expNegInvNormSq_zero : expNegInvNormSq 0 = 0 := by
  simp [expNegInvNormSq, expNegInvGlue.zero]

/-- `exp (-1 / ‖z‖²)` vanishes nowhere except at the origin. -/
theorem expNegInvNormSq_ne_zero {z : ℂ} (hz : z ≠ 0) : expNegInvNormSq z ≠ 0 := by
  rw [expNegInvNormSq, ofReal_ne_zero]
  exact (expNegInvGlue.pos_of_pos (by positivity)).ne'

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
  rw [expNegInvNormSq, norm_real, Real.norm_of_nonneg (expNegInvGlue.nonneg _), norm_pow,
    norm_norm]
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa [expNegInvGlue.zero] using mul_nonneg hc.le (pow_nonneg le_rfl n)
  have hpos : 0 < (‖z‖ ^ 2) ^ n := by positivity
  replace hz : ((‖z‖ ^ 2) ^ n)⁻¹ * expNegInvGlue (‖z‖ ^ 2) ≤ c := hz
  rw [inv_mul_le_iff₀ hpos] at hz
  calc expNegInvGlue (‖z‖ ^ 2) ≤ (‖z‖ ^ 2) ^ n * c := hz
    _ ≤ ‖z‖ ^ n * c := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg z) hz1 (by omega)) hc.le
    _ = c * ‖z‖ ^ n := mul_comm _ _

/-- The real derivative of `z ↦ exp (-1 / ‖z‖²)`, as a real function, including at `0`. -/
theorem hasFDerivAt_expNegInvGlue_norm_sq (z : ℂ) :
    HasFDerivAt (fun w : ℂ ↦ expNegInvGlue (‖w‖ ^ 2))
      ((((‖z‖ ^ 2)⁻¹ ^ 2 * expNegInvGlue (‖z‖ ^ 2)) • (2 • innerSL ℝ z))) z := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 (‖z‖ ^ 2)
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero, mul_one,
    Polynomial.eval_pow, Polynomial.eval_X] at h
  exact h.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt

/-- `bar∂ exp (-1 / ‖z‖²) = z / ‖z‖⁴ · exp (-1 / ‖z‖²)`, both sides vanishing at `0`. -/
theorem conjWirtingerDeriv_expNegInvNormSq (z : ℂ) :
    conjWirtingerDeriv expNegInvNormSq z 1 = z / (‖z‖ : ℂ) ^ 4 * expNegInvNormSq z := by
  have hf : expNegInvNormSq = fun w : ℂ ↦ ((expNegInvGlue (‖w‖ ^ 2) : ℝ) : ℂ) := rfl
  rw [conjWirtingerDeriv_apply, hf]
  simp only [fderiv_ofReal_comp_apply, (hasFDerivAt_expNegInvGlue_norm_sq z).fderiv,
    smul_apply, innerSL_apply_apply, Complex.inner, smul_eq_mul, mul_one]
  simp only [one_mul, conj_re, mul_re, I_re, I_im, conj_im, zero_mul, one_mul, neg_neg,
    zero_sub, nsmul_eq_mul]
  push_cast
  generalize ((expNegInvGlue (‖z‖ ^ 2) : ℝ) : ℂ) = g
  generalize ((‖z‖ : ℝ) : ℂ) = n
  conv_rhs => rw [← re_add_im z]
  ring

/-- The coefficient `C z = -2 z / ‖z‖⁴` forced by `2 bar∂ξ + C ξ = 0` for
`ξ = exp (-1 / ‖z‖²)`, with value `0` at the origin. -/
def expNegInvNormSqCoeff (z : ℂ) : ℂ := -2 * z / (‖z‖ : ℂ) ^ 4

/-- `ξ = exp (-1 / ‖z‖²)` solves `2 bar∂ξ + C ξ = 0` for `C z = -2 z / ‖z‖⁴`. -/
theorem two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero (z : ℂ) :
    2 * conjWirtingerDeriv expNegInvNormSq z 1 + expNegInvNormSqCoeff z * expNegInvNormSq z =
      0 := by
  rw [conjWirtingerDeriv_expNegInvNormSq, expNegInvNormSqCoeff]
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
  · simp [expNegInvNormSqCoeff]
  have h : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [expNegInvNormSqCoeff, norm_div, norm_mul, norm_neg, norm_pow, norm_real, norm_norm,
    Real.rpow_neg h.le]
  norm_num
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

/-! ### A non-constant structure `J = Φ i Φ⁻¹` -/

section Transported

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The complex structure `J = Φ i Φ⁻¹` transported from multiplication by `i` along
real-linear automorphisms `Φ z`. -/
def transportedComplexStructure (Φ : ℂ → V ≃L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  (Φ z : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V) ∘L ((Φ z).symm : V →L[ℝ] V)

/-- The coefficient `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹` that absorbs the derivative of `Φ`. -/
def transportedCoeff (Φ : ℂ → V ≃L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  -((fderiv ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z 1 +
      transportedComplexStructure Φ z ∘L fderiv ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z I) ∘L
    ((Φ z).symm : V →L[ℝ] V))

variable {Φ : ℂ → V ≃L[ℝ] V}

/-- The transported structure acts by `v ↦ Φ (i Φ⁻¹ v)`. -/
theorem transportedComplexStructure_apply (z : ℂ) (v : V) :
    transportedComplexStructure Φ z v = Φ z (I • (Φ z).symm v) := by
  simp [transportedComplexStructure]

/-- `J Φ = Φ i`. -/
theorem transportedComplexStructure_apply_apply (z : ℂ) (v : V) :
    transportedComplexStructure Φ z (Φ z v) = Φ z (I • v) := by
  simp [transportedComplexStructure_apply]

/-- `J² = -1`. -/
theorem transportedComplexStructure_comp_self (z : ℂ) :
    transportedComplexStructure Φ z ∘L transportedComplexStructure Φ z =
      -ContinuousLinearMap.id ℝ V := by
  ext v
  simp [transportedComplexStructure_apply, smul_smul]

/-- For `J = Φ i Φ⁻¹` and `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`, every `ξ = Φ σ` with `σ` holomorphic
solves `∂_s ξ + J ∂_t ξ + C ξ = 0`. -/
theorem fderiv_apply_add_transportedComplexStructure_add_eq_zero {σ : ℂ → V} {z : ℂ}
    (hΦ : DifferentiableAt ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z) (hσ : DifferentiableAt ℂ σ z) :
    fderiv ℝ (fun w ↦ Φ w (σ w)) z 1 +
        transportedComplexStructure Φ z (fderiv ℝ (fun w ↦ Φ w (σ w)) z I) +
      transportedCoeff Φ z (Φ z (σ z)) = 0 := by
  have hD := hΦ.hasFDerivAt.clm_apply (hσ.restrictScalars ℝ).hasFDerivAt
  rw [show (fun w ↦ Φ w (σ w)) = fun w ↦ (Φ w : V →L[ℝ] V) (σ w) from rfl, hD.fderiv]
  have hI : fderiv ℝ σ z I = I • fderiv ℝ σ z 1 := by
    rw [hσ.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars', ← map_smul,
      smul_eq_mul, mul_one]
  simp [transportedCoeff, transportedComplexStructure_apply, hI, smul_smul]
  abel

/-- The normalization `Φ⁻¹ J' Φ = -i` is wrong: if `J' Φ = -Φ i` at `z₀` and `v ≠ 0`, then
`ξ w = Φ w ((w - z₀) v)` fails `∂_s ξ + J' ∂_t ξ + C' ξ = 0` at its zero `z₀`, whatever `C'`. -/
theorem fderiv_apply_smul_add_ne_zero {z₀ : ℂ}
    (hΦ : DifferentiableAt ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z₀) {J' C' : V →L[ℝ] V}
    (hJ' : ∀ v, J' (Φ z₀ v) = -Φ z₀ (I • v)) {v : V} (hv : v ≠ 0) :
    fderiv ℝ (fun w ↦ Φ w ((w - z₀) • v)) z₀ 1 +
        J' (fderiv ℝ (fun w ↦ Φ w ((w - z₀) • v)) z₀ I) +
      C' (Φ z₀ ((z₀ - z₀) • v)) ≠ 0 := by
  have hσ : HasFDerivAt (fun w : ℂ ↦ (w - z₀) • v) ((ContinuousLinearMap.id ℝ ℂ).smulRight v) z₀ :=
    ((hasFDerivAt_id z₀).sub_const z₀).smul_const v
  have hD := hΦ.hasFDerivAt.clm_apply hσ
  rw [show (fun w ↦ Φ w ((w - z₀) • v)) = fun w ↦ (Φ w : V →L[ℝ] V) ((w - z₀) • v) from rfl,
    hD.fderiv]
  simp only [sub_self, zero_smul, map_zero, add_zero, comp_apply, smulRight_apply, id_apply,
    one_smul, ContinuousLinearEquiv.coe_coe, hJ', smul_smul, I_mul_I, neg_smul, map_neg, neg_neg,
    ne_eq]
  rw [← two_smul ℝ]
  exact smul_ne_zero two_ne_zero ((Φ z₀).map_ne_zero_iff.mpr hv)

/-- For a `C¹` family with continuous inverse, the coefficient `C` is continuous. -/
theorem continuous_transportedCoeff (hΦ : ContDiff ℝ 1 fun w ↦ (Φ w : V →L[ℝ] V))
    (hΨ : Continuous fun w ↦ ((Φ w).symm : V →L[ℝ] V)) : Continuous (transportedCoeff Φ) := by
  have hD := hΦ.continuous_fderiv one_ne_zero
  have hJ : Continuous (transportedComplexStructure Φ) :=
    hΦ.continuous.clm_comp (continuous_const.clm_comp hΨ)
  exact ((hD.clm_apply continuous_const).add (hJ.clm_comp (hD.clm_apply continuous_const))).clm_comp
    hΨ |>.neg

/-- For a `C¹` family with continuous inverse, the coefficient `C` is locally `Lᵖ` everywhere. -/
theorem memLpLoc_transportedCoeff (hΦ : ContDiff ℝ 1 fun w ↦ (Φ w : V →L[ℝ] V))
    (hΨ : Continuous fun w ↦ ((Φ w).symm : V →L[ℝ] V)) (p : ENNReal) (U : Set ℂ) :
    MemLpLoc p U (transportedCoeff Φ) :=
  (continuous_transportedCoeff hΦ hΨ).continuousOn.memLpLoc

end Transported

end TauCeti
