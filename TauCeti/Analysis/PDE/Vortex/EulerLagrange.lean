/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Functional
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.PDE.Vortex.Variational

/-!
# The Euler–Lagrange equation of the minimizer of Taubes's functional

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)` and
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`. Taubes's functional `I` on `H¹(ℂ) = W^{1,2}(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional`) attains its minimum
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`). This file shows that a minimizer `u`
is a weak solution of the reduced vortex equation `Δu = (exp (2u) h - 1) / 8 + g`:

`∫ ⟪∇u, ∇φ⟫ + ∫ ((exp (2u) h - 1) / 8 + g) φ = 0`

for every compactly supported `C¹` function `φ`.

The potential `(1 / 16) ∫ h (exp (2u) - 1 - 2u)` of an element of `H¹(ℂ)` can be infinite, so `I`
is not differentiable on all of `H¹(ℂ)`. At a point where `I` is finite, however, `h exp (2u)` is
integrable on every set of finite measure
(`TauCeti.Vortex.integrableOn_mul_exp_of_sobolevReducedFunctional_ne_top`): it differs from the
integrable potential by `h (1 + 2u)`, and `h ≤ 1`. For a direction `v ∈ H¹(ℂ)` whose value is
bounded and vanishes outside a set of finite measure, the expansion
`φ(s + r) = φ(s) + φ'(s) r + exp (2s) φ(r)` of Taubes's potential `φ` and the bound
`φ(r) ≤ r² / 4` for `|r| ≤ 1 / 2` then give

`I(u + t v) ≤ I(u) + t L + t² C`    for small `|t|`,

where `L` is the first variation of `I` at `u` in the direction `v`. At a minimizer the right side
has a local minimum at `t = 0`, so `L = 0`. No exponential integrability of `H¹` functions
(Trudinger–Moser) is needed.

## Main results

* `TauCeti.Vortex.integrableOn_mul_exp_of_sobolevReducedFunctional_ne_top`: where `I(u)` is
  finite, `h exp (2u)` is integrable on sets of finite measure.
* `TauCeti.Vortex.integral_inner_gradient_add_integral_mul_value_eq_zero`: the weak
  Euler–Lagrange equation at a minimizer, tested against directions `v ∈ H¹(ℂ)` with bounded value
  vanishing outside a set of finite measure.
* `TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`: the weak Euler–Lagrange
  equation at a minimizer, tested against compactly supported `C¹` functions.

The regularity of the minimizer, which turns it into a classical solution, is not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Set
open scoped ENNReal Gradient RealInnerProductSpace

variable {P : Polynomial ℂ}

/-- **Local integrability of `h exp (2u)`.** If Taubes's functional is finite at `u ∈ H¹(ℂ)`, then
`h exp (2u)`, with `h = ‖P‖² / (1 + ‖P‖²)`, is integrable on every set of finite measure. -/
theorem integrableOn_mul_exp_of_sobolevReducedFunctional_ne_top
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) {K : Set ℂ}
    (hK : volume K ≠ ∞) :
    IntegrableOn (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      Real.exp (2 * W1p.value u z)) K := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK
  have ha : IntegrableOn (W1p.value u : ℂ → ℝ) K :=
    ((W1p.memLp_value u).restrict K).integrable one_le_two
  have hlin : IntegrableOn (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (1 + 2 * W1p.value u z)) K :=
    ((integrable_const 1).add (ha.const_mul 2)).bdd_mul
      ((continuous_backgroundWeight P.continuous).congr
        (backgroundWeight_def _)).aestronglyMeasurable
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs, ← backgroundWeight_def (P.eval ·),
          abs_of_nonneg (backgroundWeight_nonneg _ z)]
        exact (backgroundWeight_lt_one _ z).le)
  refine ((sobolevReducedFunctional_ne_top_iff.1 hu).integrableOn.add hlin).congr
    (ae_of_all _ fun z ↦ ?_)
  simp only [Pi.add_apply]
  ring

/-- Let `x` be a weight with values in `[0, 1]` and `x exp (2a)` be integrable on a measurable set
`K` of finite measure. If `|b| ≤ M 1_K`, then the first variation
`2 x (exp (2a) - 1) b` of the potential `x (exp (2a) - 1 - 2a)` in the direction `b` is
integrable. -/
private theorem integrable_mul_exp_sub_one_mul {x a b : ℂ → ℝ} {K : Set ℂ} {M : ℝ}
    (hx : Continuous x) (hx01 : ∀ z, x z ∈ Icc (0 : ℝ) 1) (ha : AEStronglyMeasurable a)
    (hb : AEStronglyMeasurable b) (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (he : IntegrableOn (fun z ↦ x z * Real.exp (2 * a z)) K)
    (hbI : ∀ᵐ z, |b z| ≤ M * K.indicator (fun _ ↦ (1 : ℝ)) z) :
    Integrable fun z ↦ 2 * (x z * (Real.exp (2 * a z) - 1)) * b z := by
  have hie : Integrable (K.indicator fun z ↦ x z * Real.exp (2 * a z)) :=
    (integrable_indicator_iff hK).2 he
  have hiK : Integrable (K.indicator fun _ ↦ (1 : ℝ)) :=
    (integrable_indicator_iff hK).2 (integrableOn_const hKfin)
  refine ((hie.const_mul (2 * M)).add (hiK.const_mul (2 * M))).mono' (by fun_prop) ?_
  filter_upwards [hbI] with z hz
  have hx0 := (hx01 z).1
  have hx1 := (hx01 z).2
  have hexp := Real.exp_pos (2 * a z)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
  by_cases hzK : z ∈ K
  · simp only [Pi.add_apply, indicator_of_mem hzK, mul_one] at hz ⊢
    have h1 : |x z * (Real.exp (2 * a z) - 1)| ≤ x z * Real.exp (2 * a z) + 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    have h2 := mul_le_mul h1 hz (abs_nonneg _) (by positivity)
    nlinarith
  · simp only [Pi.add_apply, indicator_of_notMem hzK, mul_zero, add_zero] at hz ⊢
    have : b z = 0 := abs_nonpos_iff.mp hz
    simp [this]

/-- **Second-order upper bound for the potential.** Let `x` be a weight with values in `[0, 1]`,
let `x (exp (2a) - 1 - 2a)` be integrable and `x exp (2a)` be integrable on a measurable set `K` of
finite measure, and let `|b| ≤ M 1_K`. If `|t| M ≤ 1 / 2`, then
`x (exp (2(a + t b)) - 1 - 2(a + t b))` is integrable, and its integral exceeds that of
`x (exp (2a) - 1 - 2a)` by at most `t ∫ 2 x (exp (2a) - 1) b + 4 t² M² ∫_K x exp (2a)`. -/
private theorem integral_mul_exp_sub_one_sub_add_le {x a b : ℂ → ℝ} {K : Set ℂ} {M t : ℝ}
    (hx : Continuous x) (hx01 : ∀ z, x z ∈ Icc (0 : ℝ) 1) (ha : AEStronglyMeasurable a)
    (hb : AEStronglyMeasurable b) (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (hpot : Integrable fun z ↦ x z * (Real.exp (2 * a z) - 1 - 2 * a z))
    (he : IntegrableOn (fun z ↦ x z * Real.exp (2 * a z)) K)
    (hbI : ∀ᵐ z, |b z| ≤ M * K.indicator (fun _ ↦ (1 : ℝ)) z) (ht : |t| * M ≤ 1 / 2) :
    Integrable (fun z ↦ x z * (Real.exp (2 * (a z + t * b z)) - 1 - 2 * (a z + t * b z))) ∧
      ∫ z, x z * (Real.exp (2 * (a z + t * b z)) - 1 - 2 * (a z + t * b z)) ≤
        (∫ z, x z * (Real.exp (2 * a z) - 1 - 2 * a z)) +
          t * (∫ z, 2 * (x z * (Real.exp (2 * a z) - 1)) * b z) +
          t ^ 2 * (4 * M ^ 2 * ∫ z in K, x z * Real.exp (2 * a z)) := by
  have hxe : AEStronglyMeasurable fun z ↦ x z * Real.exp (2 * a z) :=
    hx.aestronglyMeasurable.mul (Real.continuous_exp.comp_aestronglyMeasurable
      (ha.const_mul 2))
  have hie : Integrable (K.indicator fun z ↦ x z * Real.exp (2 * a z)) :=
    (integrable_indicator_iff hK).2 he
  have hvar := integrable_mul_exp_sub_one_mul hx hx01 ha hb hK hKfin he hbI
  -- The second-order remainder is nonnegative and bounded by `4 t² M² 1_K x exp (2a)`.
  set r : ℂ → ℝ := fun z ↦ 16 * (x z * Real.exp (2 * a z)) * taubesPotential (t * b z) with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z ↦ by
    have := (hx01 z).1
    have := taubesPotential_nonneg (t * b z)
    positivity
  have hrle : ∀ᵐ z, r z ≤ 4 * t ^ 2 * M ^ 2 *
      K.indicator (fun z ↦ x z * Real.exp (2 * a z)) z := by
    filter_upwards [hbI] with z hz
    have hxe0 : 0 ≤ x z * Real.exp (2 * a z) := mul_nonneg (hx01 z).1 (Real.exp_pos _).le
    by_cases hzK : z ∈ K
    · simp only [indicator_of_mem hzK, mul_one] at hz ⊢
      have htb : |t * b z| ≤ 1 / 2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hz (abs_nonneg t)).trans ht
      have hφ := taubesPotential_le_sq htb
      have hsq : (t * b z) ^ 2 ≤ t ^ 2 * M ^ 2 := by
        rw [mul_pow, ← sq_abs (b z)]
        gcongr
      calc r z ≤ 16 * (x z * Real.exp (2 * a z)) * ((t * b z) ^ 2 / 4) := by
            simp only [hr]
            gcongr
        _ ≤ 16 * (x z * Real.exp (2 * a z)) * (t ^ 2 * M ^ 2 / 4) := by gcongr
        _ = 4 * t ^ 2 * M ^ 2 * (x z * Real.exp (2 * a z)) := by ring
    · simp only [indicator_of_notMem hzK, mul_zero] at hz ⊢
      have : b z = 0 := abs_nonpos_iff.mp hz
      simp [hr, this]
  have hrm : AEStronglyMeasurable r :=
    (hxe.const_mul 16).mul (continuous_taubesPotential.comp_aestronglyMeasurable
      (hb.const_mul t))
  have hri : Integrable r :=
    (hie.const_mul (4 * t ^ 2 * M ^ 2)).mono' hrm
      (hrle.mono fun z hz ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg (hr0 z)])
  -- The expansion of the potential along `t b`.
  have hexp : (fun z ↦ x z * (Real.exp (2 * (a z + t * b z)) - 1 - 2 * (a z + t * b z))) =
      fun z ↦ (x z * (Real.exp (2 * a z) - 1 - 2 * a z) +
        t * (2 * (x z * (Real.exp (2 * a z) - 1)) * b z)) + r z := by
    funext z
    have h := taubesPotential_add (a z) (t * b z)
    rw [taubesPotential_def (a z + t * b z), taubesPotential_def (a z)] at h
    simp only [hr]
    linear_combination 16 * x z * h
  have hsum : Integrable fun z ↦ x z * (Real.exp (2 * a z) - 1 - 2 * a z) +
      t * (2 * (x z * (Real.exp (2 * a z) - 1)) * b z) :=
    hpot.add (hvar.const_mul t)
  refine ⟨hexp ▸ hsum.add hri, ?_⟩
  rw [hexp, integral_add hsum hri, integral_add hpot (hvar.const_mul t), integral_const_mul]
  have hrint : ∫ z, r z ≤ t ^ 2 * (4 * M ^ 2 * ∫ z in K, x z * Real.exp (2 * a z)) := by
    calc ∫ z, r z ≤ ∫ z, 4 * t ^ 2 * M ^ 2 *
          K.indicator (fun z ↦ x z * Real.exp (2 * a z)) z :=
          integral_mono_ae hri (hie.const_mul _) hrle
      _ = t ^ 2 * (4 * M ^ 2 * ∫ z in K, x z * Real.exp (2 * a z)) := by
          rw [integral_const_mul, integral_indicator hK]
          ring
  linarith

/-- **Taubes's functional along a line.** Let `I(u)` be finite and let `v ∈ H¹(ℂ)` have value
bounded by `M 1_K` for a measurable set `K` of finite measure. Then there is `C` such that
`I(u + t v) ≤ I(u) + t L + t² C` whenever `|t| M ≤ 1 / 2`, where `L` is the first variation
`⟪∇u, ∇v⟫ + (1 / 16) ∫ 2 h (exp (2u) - 1) v + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) v`. One can take
`C = ‖∇v‖² / 2 + (M² / 4) ∫_K h exp (2u)`. -/
private theorem sobolevReducedFunctional_add_smul_le (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) {K : Set ℂ}
    (hK : MeasurableSet K) (hKfin : volume K ≠ ∞) {M : ℝ}
    (hvI : ∀ᵐ z, |W1p.value v z| ≤ M * K.indicator (fun _ ↦ (1 : ℝ)) z) :
    ∃ L C : ℝ, L = ⟪W1p.gradient u, W1p.gradient v⟫ +
          (∫ z, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
            (Real.exp (2 * W1p.value u z) - 1)) * W1p.value v z) / 16 +
          ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
            (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z ∧
      ∀ t : ℝ, |t| * M ≤ 1 / 2 → sobolevReducedFunctional P (u + t • v) ≤
        sobolevReducedFunctional P u + ((t * L + t ^ 2 * C : ℝ) : EReal) := by
  refine ⟨_, ‖W1p.gradient v‖ ^ 2 / 2 + 4 * M ^ 2 * (∫ z in K,
    ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u z)) / 16, rfl,
    fun t htM ↦ ?_⟩
  have hua := W1p.memLp_value u
  have hva := W1p.memLp_value v
  have hpot := sobolevReducedFunctional_ne_top_iff.1 hu
  have hc := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  have hca : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := hc.integrable_mul hua
  have hcb : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z := hc.integrable_mul hva
  -- The value and the weak gradient of `u + t v`.
  have hval : (W1p.value (u + t • v) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ W1p.value u z + t * W1p.value v z := by
    have h1 := W1p.value_add_ae u (t • v)
    have h2 := W1p.value_smul_ae t v
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h1 h2
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, Pi.add_apply, hz2, Pi.smul_apply, smul_eq_mul]
  have hgrad : W1p.gradient (u + t • v) = W1p.gradient u + t • W1p.gradient v := by
    rw [← W1p.gradientL_apply, map_add, map_smul, W1p.gradientL_apply, W1p.gradientL_apply]
  -- The potential, the linear term and the Dirichlet energy along the line.
  obtain ⟨hint, hle⟩ := integral_mul_exp_sub_one_sub_add_le
    ((continuous_backgroundWeight P.continuous).congr (backgroundWeight_def _))
    (fun z ↦ backgroundWeight_def (P.eval ·) z ▸
      ⟨backgroundWeight_nonneg _ z, (backgroundWeight_lt_one _ z).le⟩) hua.aestronglyMeasurable
    hva.aestronglyMeasurable hK hKfin hpot
    (integrableOn_mul_exp_of_sobolevReducedFunctional_ne_top hu hKfin) hvI htM
  have hpot' : (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value (u + t • v) z) - 1 - 2 * W1p.value (u + t • v) z)) =ᵐ[volume]
      fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * (W1p.value u z + t * W1p.value v z)) - 1 -
          2 * (W1p.value u z + t * W1p.value v z)) :=
    hval.mono fun z hz ↦ by simp only [hz]
  have hlin : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value (u + t • v) z =
      (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) +
      t * ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z := by
    rw [← integral_const_mul, ← integral_add hca (hcb.const_mul t)]
    exact integral_congr_ae (hval.mono fun z hz ↦ by simp only [hz]; ring)
  have hnorm : ‖W1p.gradient u + t • W1p.gradient v‖ ^ 2 =
      ‖W1p.gradient u‖ ^ 2 + 2 * t * ⟪W1p.gradient u, W1p.gradient v⟫ +
        t ^ 2 * ‖W1p.gradient v‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [sobolevReducedFunctional_eq_coe hpot,
    sobolevReducedFunctional_eq_coe ((integrable_congr hpot').2 hint), ← EReal.coe_add,
    EReal.coe_le_coe_iff, integral_congr_ae hpot', hlin, hgrad, hnorm]
  nlinarith

/-- **The weak Euler–Lagrange equation of Taubes's functional, `H¹` directions.** Let
`u ∈ H¹(ℂ)` minimize Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P`, and let
`v ∈ H¹(ℂ)` have bounded value vanishing outside a set of finite measure. Then, with
`h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`,

`∫ ⟪∇u, ∇v⟫ + ∫ ((exp (2u) h - 1) / 8 + g) v = 0`.

The second integrand is integrable by
`TauCeti.Vortex.integrableOn_mul_exp_of_sobolevReducedFunctional_ne_top`. -/
theorem integral_inner_gradient_add_integral_mul_value_eq_zero (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w)
    {v : W1p (volume : Measure ℂ) ⊤ 2} {K : Set ℂ} (hK : volume K ≠ ∞) {M : ℝ}
    (hvM : ∀ᵐ z, |W1p.value v z| ≤ M) (hvK : ∀ᵐ z, z ∉ K → W1p.value v z = 0) :
    (∫ z, ⟪W1p.gradient u z, W1p.gradient v z⟫) +
      ∫ z, ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * W1p.value v z = 0 := by
  -- `I(u) ≤ I(0) = 0` is finite.
  have hu0 : sobolevReducedFunctional P u ≠ ⊤ :=
    ((hu 0).trans_lt (by rw [sobolevReducedFunctional_zero]; exact EReal.zero_lt_top)).ne
  -- Replace `K` by a measurable superset of the same measure, so that `|v| ≤ M 1_K`.
  have hK' : MeasurableSet (toMeasurable volume K) := measurableSet_toMeasurable _ _
  have hK'fin : volume (toMeasurable volume K) ≠ ∞ := by rwa [measure_toMeasurable]
  have hvI : ∀ᵐ z, |W1p.value v z| ≤ M * (toMeasurable volume K).indicator (fun _ ↦ 1) z := by
    filter_upwards [hvM, hvK] with z hzM hzK
    by_cases hz : z ∈ toMeasurable volume K
    · simpa [indicator_of_mem hz] using hzM
    · simp [indicator_of_notMem hz, hzK fun h ↦ hz (subset_toMeasurable _ _ h)]
  have hM : 0 ≤ M := (abs_nonneg _).trans hvM.exists.choose_spec
  obtain ⟨L, C, hLdef, hLC⟩ := sobolevReducedFunctional_add_smul_le hm hu0 hK' hK'fin hvI
  -- By minimality, the quadratic `t L + t² C` has a local minimum at `0`.
  have hmin : IsLocalMin (fun t : ℝ ↦ t * L + t ^ 2 * C) 0 := by
    have hδ : (0 : ℝ) < 1 / (2 * (M + 1)) := by positivity
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with t ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    have htM : |t| * M ≤ 1 / 2 := by
      calc |t| * M ≤ 1 / (2 * (M + 1)) * (M + 1) := by gcongr; linarith
        _ = 1 / 2 := by field_simp
    have hle := (hu (u + t • v)).trans (hLC t htM)
    rw [sobolevReducedFunctional_eq_coe (sobolevReducedFunctional_ne_top_iff.1 hu0),
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    linarith
  -- Its derivative at `0`, the first variation `L`, therefore vanishes.
  have hquad (L C : ℝ) : HasDerivAt (fun t : ℝ ↦ t * L + t ^ 2 * C) L 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ t * L) L 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).mul_const L
    have h2 : HasDerivAt (fun t : ℝ ↦ t ^ 2 * C) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const C
    have := h1.add h2
    rwa [add_zero] at this
  have hL := hmin.hasDerivAt_eq_zero (hquad L C)
  rw [hLdef] at hL
  -- Rewrite the first variation as the weak form of the reduced equation.
  have hinner : ⟪W1p.gradient u, W1p.gradient v⟫ =
      ∫ z, ⟪W1p.gradient u z, W1p.gradient v z⟫ := by
    rw [L2.inner_def]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  have hvar := integrable_mul_exp_sub_one_mul
    ((continuous_backgroundWeight P.continuous).congr (backgroundWeight_def _))
    (fun z ↦ backgroundWeight_def (P.eval ·) z ▸
      ⟨backgroundWeight_nonneg _ z, (backgroundWeight_lt_one _ z).le⟩)
    (W1p.memLp_value u).aestronglyMeasurable (W1p.memLp_value v).aestronglyMeasurable hK' hK'fin
    (integrableOn_mul_exp_of_sobolevReducedFunctional_ne_top hu0 hK'fin) hvI
  have hcb : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z :=
    (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).integrable_mul
      (W1p.memLp_value v)
  rw [hinner, ← integral_div, add_assoc, ← integral_add (hvar.div_const 16) hcb] at hL
  rw [← hL]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  have h1 : (1 + ‖P.eval z‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **The weak Euler–Lagrange equation of Taubes's functional.** Let `P` have degree at least one
and let `u ∈ H¹(ℂ)` minimize Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P`.
Then `u` is a weak solution of the reduced vortex equation `Δu = (exp (2u) h - 1) / 8 + g`, with
`h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`: for every compactly supported `C¹`
function `φ`,

`∫ ⟪∇u, ∇φ⟫ + ∫ ((exp (2u) h - 1) / 8 + g) φ = 0`. -/
theorem integral_inner_gradient_add_integral_mul_eq_zero (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
      ∫ z, ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z = 0 := by
  obtain ⟨v, hv, hg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn
    (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2) hφ.contDiffOn
    (hφ.continuous.memLp_of_hasCompactSupport hφc) (hφc.memLp_gradient hφ)
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hv hg
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have h := integral_inner_gradient_add_integral_mul_value_eq_zero hm hu
    hφc.isCompact.measure_ne_top (M := M) (hv.mono fun z hz ↦ by rw [hz]; exact hM z)
    (hv.mono fun z hz hzK ↦ by rw [hz]; exact image_eq_zero_of_notMem_tsupport hzK)
  rw [← h]
  congr 1
  · exact integral_congr_ae (hg.mono fun z hz ↦ by simp only [hz])
  · exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

end TauCeti.Vortex
