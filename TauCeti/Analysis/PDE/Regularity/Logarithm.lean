/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Power
public import TauCeti.Analysis.Sobolev.W1p.ChainRule
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# The logarithm of a positive weak supersolution

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, which is bounded below by a constant
`ε > 0`. Then `log u` is a Sobolev function with weak gradient `∇u / u`
(`TauCeti.W1p.exists_value_gradient_ae_eq_comp_of_le`), and this file shows that this gradient is
controlled by the ellipticity constants alone:

* the **logarithmic Caccioppoli inequality**: for every smooth `ψ` compactly supported in `Ω`,

  `∫_Ω ψ² ‖∇u‖² / u² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖²`.

  Unlike the Caccioppoli inequality for `u` itself, the right side does not involve `u` at all;
* on every ball with `B(x₀, 2r) ⊆ Ω`, the scale-invariant bound
  `∫_{B(x₀, r)} ‖∇u‖² / u² ≤ C (Λ/λ)² |B(x₀, r)| / r²`;
* consequently, by the Poincaré–Wirtinger inequality on balls, **`log u` has bounded mean
  oscillation**: `⨍_{B(x₀, r)} |log u - (log u)_{B(x₀, r)}| ≤ C Λ/λ` on every such ball.

The constants `C` depend only on the dimension; nothing depends on `u` or on the lower bound `ε`,
which serves only to make `u⁻¹` and `log u` Sobolev functions. No regularity of the coefficients
beyond measurability is used.

The mean oscillation bound is the hypothesis of the John–Nirenberg inequality. In Moser's proof of
the weak Harnack inequality, John–Nirenberg turns it into the crossover estimate
`⨍_B u^p · ⨍_B u^{-p} ≤ C` for a small `p > 0`, which links bounds on negative powers of a
supersolution to bounds on positive ones.

The logarithmic Caccioppoli inequality is the case `p = 0` of the Caccioppoli inequality for
powers of `u`
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le`), which tests
the supersolution inequality against `ψ² u^{p-1}`, here `ψ² u⁻¹`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le`: the
  logarithmic Caccioppoli inequality.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_div_value_sq_le`: the bound for
  `∫ ‖∇ log u‖²` on balls.
* `TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le`: `log u` has bounded mean
  oscillation.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6 (the proof of Theorem 8.18).
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- **The logarithmic Caccioppoli inequality.** Let `a` be measurable and uniformly elliptic on
`Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ ε`
almost everywhere for some `ε > 0`. Then for every smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² (‖∇u‖ / u)² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖²`.

The integrand on the left is `ψ² ‖∇ log u‖²`, and the right side depends on neither `u` nor
`ε`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu := by
  -- This is the case `p = 0` of the Caccioppoli inequality for powers.
  have hc := h.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le ha hu hε hεu zero_lt_one hψ hcpt hts
  rw [sub_zero, one_mul] at hc
  convert hc using 1
  · refine integral_congr_ae ?_
    filter_upwards [hεu] with x hx
    rw [zero_sub, Real.rpow_neg (hε.le.trans hx), div_pow, Real.rpow_two]
    ring
  · simp only [Real.rpow_zero, mul_one]

/-- **The gradient of `log u` on balls.** There is a constant `C ≥ 0`, depending only on the
dimension, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` with
`u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball with `B(x₀, 2r) ⊆ Ω`,

`∫_{B(x₀, r)} (‖∇u‖ / u)² ≤ C (Λ/λ)² |B(x₀, r)| / r²`.

So the average of `‖∇ log u‖²` over `B(x₀, r)` is at most `C (Λ/λ)² r⁻²`, the power of `r`
dictated by scaling. -/
theorem exists_setIntegral_ball_norm_gradient_div_value_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < r → Metric.ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
        C * (Lam / lam) ^ 2 * mu.real (Metric.ball x₀ r) / r ^ 2 := by
  obtain ⟨c, hc0, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨16 * c ^ 2 * (3 / 2) ^ Fintype.card ι, by positivity, ?_⟩
  intro mu _ Omega a lam Lam u ε x₀ r h ha hu hε hεu hr hball
  have hlam := h.pos
  -- A cutoff equal to `1` on `B(x₀, r)`, supported in `closedBall x₀ (3r/2)`, with `‖∇ψ‖ ≤ 2c/r`.
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg⟩ := hcut x₀ hr (by linarith : r < 3 * r / 2)
  have hR : 3 * r / 2 - r = r / 2 := by ring
  rw [hR] at hψg
  have hclosed : Metric.closedBall x₀ (3 * r / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hcpt : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ (3 * r / 2))
      (subset_tsupport ψ |>.trans hψts)
  have hcacc := h.setIntegral_sq_mul_norm_gradient_div_value_sq_le ha hu hε hεu hψ hcpt
    (hψts.trans hclosed)
  have hmeasB : MeasurableSet (Metric.closedBall x₀ (3 * r / 2)) := measurableSet_closedBall
  -- The gradient of the cutoff is supported in `closedBall x₀ (3r/2)`, where it is at most `2c/r`.
  have hgrad : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu ≤
      (2 * c / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2)) := by
    calc ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu
        ≤ ∫ x in Omega, (Metric.closedBall x₀ (3 * r / 2)).indicator
            (fun _ => (2 * c / r) ^ 2) x ∂mu := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
              hmeasB).restrict
            (Filter.Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ Metric.closedBall x₀ (3 * r / 2)
          · rw [indicator_of_mem hx]
            have := hψg x
            rw [div_div_eq_mul_div, mul_comm c 2] at this
            exact pow_le_pow_left₀ (norm_nonneg _) this 2
          · have hfd : fderiv ℝ ψ x = 0 := Function.notMem_support.1 fun hx' =>
              hx (hψts (support_fderiv_subset ℝ hx'))
            simp [indicator_of_notMem hx, _root_.gradient, hfd]
      _ ≤ (2 * c / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2)) := by
          rw [integral_indicator_const _ hmeasB, smul_eq_mul, mul_comm]
          gcongr
          rw [measureReal_restrict_apply hmeasB]
          exact measureReal_mono inter_subset_left measure_closedBall_lt_top.ne
  -- On `B(x₀, r)` the cutoff is `1`, so the integral there is dominated by the weighted one.
  have hweighted : Integrable (fun x => ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2)
      (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_div_value_sq hε hεu).bdd_mul
      (hψ.continuous.pow 2).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall
        fun x => by
          obtain ⟨h0, h1⟩ := hψr (mem_range_self x)
          rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
          exact pow_le_one₀ h0 h1)
  have hleft : ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu := by
    calc ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu
        = ∫ x in Metric.ball x₀ r, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu :=
          setIntegral_congr_fun measurableSet_ball fun x hx => by
            rw [hψ1 (Metric.ball_subset_closedBall hx)]
            simp
      _ ≤ ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu :=
          setIntegral_mono_set hweighted (Filter.Eventually.of_forall fun x => by positivity)
            ((Metric.ball_subset_ball (by linarith)).trans hball).eventuallyLE
  -- Both balls have measure proportional to the `n`-th power of the radius.
  have hvol : mu.real (Metric.closedBall x₀ (3 * r / 2)) =
      (3 / 2) ^ Fintype.card ι * mu.real (Metric.ball x₀ r) := by
    have hb : mu.real (Metric.ball x₀ r) = r ^ Fintype.card ι * mu.real (Metric.ball 0 1) := by
      rw [measureReal_def, Measure.addHaar_ball_of_pos mu x₀ hr, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), measureReal_def, finrank_euclideanSpace]
    rw [Measure.addHaar_real_closedBall mu x₀ (by positivity), hb, finrank_euclideanSpace]
    ring
  calc ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu
      ≤ (2 * Lam / lam) ^ 2 * ((2 * c / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2))) :=
        hleft.trans (hcacc.trans (by gcongr))
    _ = 16 * c ^ 2 * (3 / 2) ^ Fintype.card ι * (Lam / lam) ^ 2 * mu.real (Metric.ball x₀ r) /
          r ^ 2 := by
        rw [hvol]
        field_simp
        ring

/-- **The logarithm of a positive supersolution has bounded mean oscillation.** There is a
constant `C ≥ 0`, depending only on the dimension, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a
weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` with `u ≥ ε` almost everywhere for some `ε > 0`. Then on
every ball with `B(x₀, 2r) ⊆ Ω`,

`⨍_{B(x₀, r)} |log u - ⨍_{B(x₀, r)} log u| ≤ C Λ/λ`.

The bound is uniform over all such balls, and independent of `u` and `ε`: this is the hypothesis
of the John–Nirenberg inequality for `log u`. -/
theorem exists_setAverage_abs_log_sub_setAverage_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < r → Metric.ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍ x in Metric.ball x₀ r, |Real.log (W1p.value u x) -
          ⨍ y in Metric.ball x₀ r, Real.log (W1p.value u y) ∂mu| ∂mu ≤ C * (Lam / lam) := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_div_value_sq_le (ι := ι)
  refine ⟨2 ^ (Fintype.card ι + 1) * √C, by positivity, ?_⟩
  intro mu _ Omega a lam Lam u ε x₀ r h ha hu hε hεu hr hball
  have hBsub : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  set f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (W1p.value u x)
  set m := ⨍ y in Metric.ball x₀ r, f y ∂mu
  have hB0 : mu (Metric.ball x₀ r) ≠ 0 := (Metric.measure_ball_pos mu x₀ hr).ne'
  have hBtop : mu (Metric.ball x₀ r) ≠ (⊤ : ℝ≥0∞) := (measure_ball_lt_top (μ := mu)).ne
  have hBpos : 0 < mu.real (Metric.ball x₀ r) := ENNReal.toReal_pos hB0 hBtop
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ r)) := isFiniteMeasure_restrict.2 hBtop
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_log (by simp) hε hεu
  have hwvB : W1p.value w =ᵐ[mu.restrict (Metric.ball x₀ r)] f :=
    ae_restrict_of_ae_restrict_of_subset hBsub hwv
  have hmem : MemLp (fun x => f x - m) 2 (mu.restrict (Metric.ball x₀ r)) :=
    (((Lp.memLp (W1p.value w)).ae_eq hwv).mono_measure
      (Measure.restrict_mono hBsub le_rfl)).sub (memLp_const m)
  -- The Poincaré–Wirtinger inequality on the ball, for `log u`.
  have hP : ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu ≤ (2 ^ (Fintype.card ι + 1) * r) ^ 2 *
      ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu := by
    have hP := W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset hr hBsub w
    rw [average_congr hwvB, finrank_euclideanSpace] at hP
    calc ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu
        = ∫ x in Metric.ball x₀ r, (W1p.value w x - m) ^ 2 ∂mu :=
          integral_congr_ae (hwvB.mono fun x hx => by simp only [hx])
      _ ≤ _ := hP
      _ = _ := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hBsub hwg,
            ae_restrict_of_ae_restrict_of_subset hBsub hεu] with x h1 h2
          rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le h2),
            inv_mul_eq_div]
  -- Jensen's inequality bounds the `L¹` mean oscillation by the `L²` one.
  have hgi : Integrable (fun x => |f x - m| ^ 2) (mu.restrict (Metric.ball x₀ r)) := by
    simpa only [sq_abs] using hmem.integrable_sq
  have hJ : (⨍ x in Metric.ball x₀ r, |f x - m| ∂mu) ^ 2 ≤
      ⨍ x in Metric.ball x₀ r, |f x - m| ^ 2 ∂mu :=
    ConvexOn.map_set_average_le (convexOn_pow 2) (continuous_pow 2).continuousOn isClosed_Ici
      hB0 hBtop (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hmem.integrable one_le_two).abs hgi
  have hJ' : ⨍ x in Metric.ball x₀ r, |f x - m| ^ 2 ∂mu =
      (mu.real (Metric.ball x₀ r))⁻¹ * ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu := by
    simp [setAverage_eq, sq_abs]
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (by positivity) (div_nonneg h.upper_nonneg h.pos.le)) (hJ.trans ?_)
  rw [hJ']
  -- Poincaré–Wirtinger for `log u`, then the gradient bound for `log u` on the ball.
  calc (mu.real (Metric.ball x₀ r))⁻¹ * ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu
      ≤ (mu.real (Metric.ball x₀ r))⁻¹ * ((2 ^ (Fintype.card ι + 1) * r) ^ 2 *
          (C * (Lam / lam) ^ 2 * mu.real (Metric.ball x₀ r) / r ^ 2)) := by
        gcongr
        exact hP.trans (by gcongr; exact hC mu h ha hu hε hεu hr hball)
    _ = (2 ^ (Fintype.card ι + 1) * √C * (Lam / lam)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC0]
        field_simp

end PDE

end TauCeti
