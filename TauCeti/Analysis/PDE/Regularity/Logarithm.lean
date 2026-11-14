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
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The logarithm of a positive weak supersolution

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` in `Ω`,

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

All three statements extend to supersolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with measurable
`‖b‖ ≤ β` and `|c| ≤ γ`, with no sign condition on `c`. The logarithmic Caccioppoli inequality
acquires the term `(2/λ)² (β² + λγ) ∫_Ω ψ²`, and on a ball of radius `r` the coefficients enter
only through the dimensionless quantities `βr/λ` and `γr²/λ`:

`⨍_{B(x₀, r)} |log u - (log u)_{B(x₀, r)}| ≤ C √((Λ/λ)² + (βr/λ)² + γr²/λ)`.

So `log u` again has bounded mean oscillation on balls of bounded radius. The statements without
lower-order terms on balls are the case `b = 0`, `c = 0`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le`: the
  logarithmic Caccioppoli inequality.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_div_value_sq_le`: the bound for
  `∫ ‖∇ log u‖²` on balls.
* `TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le`: `log u` has bounded mean
  oscillation.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le_lowerOrder`,
  `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_div_value_sq_le_lowerOrder` and
  `TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le_lowerOrder`: the same three results
  for supersolutions of the equation with lower-order terms.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6 (the proofs of Theorems 8.18 and 8.20, where the lower-order terms are included).
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
`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ ε`
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

/-- **The logarithmic Caccioppoli inequality with lower-order terms.** Let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let `b` and `c` be measurable with
`‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`. Let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with
`u ≥ ε` almost everywhere for some `ε > 0`. Then for every smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² (‖∇u‖ / u)² ≤ (2/λ)² (2Λ² ∫_Ω ‖∇ψ‖² + (β² + λγ) ∫_Ω ψ²)`.

As without lower-order terms, the right side depends on neither `u` nor `ε`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
      (2 / lam) ^ 2 * (2 * Lam ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu +
        (beta ^ 2 + lam * gamma) * ∫ x in Omega, ψ x ^ 2 ∂mu) := by
  -- This is the case `p = 0` of the Caccioppoli inequality for powers with lower-order terms.
  have hcacc := h.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le_lowerOrder ha hb hc hb_bound
    hc_bound hu hε hεu zero_lt_one hψ hcpt hts
  rw [sub_zero, one_mul] at hcacc
  convert hcacc using 1
  · refine integral_congr_ae ?_
    filter_upwards [hεu] with x hx
    rw [zero_sub, Real.rpow_neg (hε.le.trans hx), div_pow, Real.rpow_two]
    ring
  · simp only [Real.rpow_zero, mul_one]

omit [DecidableEq ι] in
/-- Poincaré–Wirtinger for `log u` on a ball inside `Ω`, given `w ∈ H¹(Ω)` representing `log u`
with gradient `u⁻¹ ∇u`: the mean oscillation of `log u` is controlled by `‖∇u‖ / u`. -/
private lemma setIntegral_log_sub_setAverage_sq_le {u w : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε)
    (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {x₀ : EuclideanSpace ℝ ι} {r : ℝ}
    (hBsub : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hwv : W1p.value w =ᵐ[mu.restrict Omega] fun x => Real.log (W1p.value u x))
    (hwg : W1p.gradient w =ᵐ[mu.restrict Omega] fun x => (W1p.value u x)⁻¹ • W1p.gradient u x) :
    ∫ x in Metric.ball x₀ r, (Real.log (W1p.value u x) -
        ⨍ y in Metric.ball x₀ r, Real.log (W1p.value u y) ∂mu) ^ 2 ∂mu ≤
      (2 ^ (Fintype.card ι + 1) * r) ^ 2 *
        ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu := by
  have hwvB : W1p.value w =ᵐ[mu.restrict (Metric.ball x₀ r)] fun x => Real.log (W1p.value u x) :=
    ae_restrict_of_ae_restrict_of_subset hBsub hwv
  have hP := W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset hBsub w
  rw [average_congr hwvB, finrank_euclideanSpace] at hP
  calc _ = ∫ x in Metric.ball x₀ r, (W1p.value w x -
          ⨍ y in Metric.ball x₀ r, Real.log (W1p.value u y) ∂mu) ^ 2 ∂mu :=
        integral_congr_ae (hwvB.mono fun x hx => by simp only [hx])
    _ ≤ _ := hP
    _ = _ := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hBsub hwg,
          ae_restrict_of_ae_restrict_of_subset hBsub hεu] with x h1 h2
        rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le h2),
          inv_mul_eq_div]

/-- **The gradient of `log u` on balls, with lower-order terms.** There is a constant `C ≥ 0`,
depending only on the dimension, with the following property. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and
`|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `u ≥ ε` almost everywhere for some `ε > 0`. Then on every
ball with `B(x₀, 2r) ⊆ Ω`,

`∫_{B(x₀, r)} (‖∇u‖ / u)² ≤ C ((Λ/λ)² + (βr/λ)² + γr²/λ) |B(x₀, r)| / r²`.

The lower-order terms enter only through the dimensionless quantities `βr/λ` and `γr²/λ`, which
are small on small balls. -/
theorem exists_setIntegral_ball_norm_gradient_div_value_sq_le_lowerOrder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < r → Metric.ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
        C * ((Lam / lam) ^ 2 + (beta * r / lam) ^ 2 + gamma * r ^ 2 / lam) *
          mu.real (Metric.ball x₀ r) / r ^ 2 := by
  obtain ⟨c₀, -, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨4 * (8 * c₀ ^ 2 + 1) * (3 / 2) ^ Fintype.card ι, by positivity, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma u ε x₀ r h ha hb hc hb_bound hc_bound hu hε hεu hr
    hball
  have hlam := h.pos
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball (Metric.mem_ball_self (by linarith))
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ hx₀)
  -- A cutoff equal to `1` on `B(x₀, r)`, supported in `closedBall x₀ (3r/2)`, with `‖∇ψ‖ ≤ 2c₀/r`.
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg, -⟩ := hcut x₀ hr.le (by linarith : r < 3 * r / 2)
  have hR : 3 * r / 2 - r = r / 2 := by ring
  rw [hR] at hψg
  have hclosed : Metric.closedBall x₀ (3 * r / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hcpt : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ (3 * r / 2))
      (subset_tsupport ψ |>.trans hψts)
  have hcacc := h.setIntegral_sq_mul_norm_gradient_div_value_sq_le_lowerOrder ha hb hc hb_bound
    hc_bound hu hε hεu hψ hcpt (hψts.trans hclosed)
  -- The gradient of the cutoff is supported in `closedBall x₀ (3r/2)`, where it is at most `2c₀/r`.
  have hgrad : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu ≤
      (2 * c₀ / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2)) :=
    setIntegral_norm_gradient_sq_le_of_tsupport_subset_closedBall hψts fun x _ => by
      have := hψg x
      rwa [div_div_eq_mul_div, mul_comm c₀ 2] at this
  -- The cutoff itself takes values in `[0, 1]` and is supported in `closedBall x₀ (3r/2)`.
  have hsq : ∫ x in Omega, ψ x ^ 2 ∂mu ≤ mu.real (Metric.closedBall x₀ (3 * r / 2)) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Omega.isOpen.measurableSet hclosed
      fun x hx => by rw [image_eq_zero_of_notMem_tsupport fun hx' => hx.2 (hψts hx'), sq,
        mul_zero]]
    calc ∫ x in Metric.closedBall x₀ (3 * r / 2), ψ x ^ 2 ∂mu
        ≤ ‖∫ x in Metric.closedBall x₀ (3 * r / 2), ψ x ^ 2 ∂mu‖ := Real.le_norm_self _
      _ ≤ 1 * mu.real (Metric.closedBall x₀ (3 * r / 2)) :=
          norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun x _ => by
            obtain ⟨h0, h1⟩ := hψr (mem_range_self x)
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact pow_le_one₀ h0 h1
      _ = _ := one_mul _
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
            ((Metric.ball_subset_ball (by linarith)).trans hball).eventuallySubset
  have hvol : mu.real (Metric.closedBall x₀ (3 * r / 2)) =
      (3 / 2) ^ Fintype.card ι * mu.real (Metric.ball x₀ r) := by
    rw [show 3 * r / 2 = 3 / 2 * r by ring,
      mu.addHaar_real_closedBall_mul_eq_pow_mul_addHaar_real_ball x₀ (by norm_num) hr,
      finrank_euclideanSpace]
  set V := mu.real (Metric.ball x₀ r)
  set Q := (Lam / lam) ^ 2 + (beta * r / lam) ^ 2 + gamma * r ^ 2 / lam
  have hQ1 : (Lam / lam) ^ 2 ≤ Q := by
    simp only [Q]
    have : 0 ≤ gamma * r ^ 2 / lam := by positivity
    nlinarith [sq_nonneg (beta * r / lam)]
  calc ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu
      ≤ (2 / lam) ^ 2 * (2 * Lam ^ 2 * ((2 * c₀ / r) ^ 2 *
            mu.real (Metric.closedBall x₀ (3 * r / 2))) +
          (beta ^ 2 + lam * gamma) * mu.real (Metric.closedBall x₀ (3 * r / 2))) :=
        hleft.trans (hcacc.trans (by gcongr))
    _ = 4 * (8 * c₀ ^ 2 * (Lam / lam) ^ 2 + ((beta * r / lam) ^ 2 + gamma * r ^ 2 / lam)) *
          (3 / 2) ^ Fintype.card ι * V / r ^ 2 := by
        rw [hvol]
        field_simp
        ring
    _ ≤ 4 * (8 * c₀ ^ 2 + 1) * (3 / 2) ^ Fintype.card ι * Q * V / r ^ 2 := by
        have hle : 8 * c₀ ^ 2 * (Lam / lam) ^ 2 + ((beta * r / lam) ^ 2 + gamma * r ^ 2 / lam) ≤
            (8 * c₀ ^ 2 + 1) * Q := by
          simp only [Q] at hQ1 ⊢
          nlinarith [mul_le_mul_of_nonneg_left hQ1 (by positivity : (0 : ℝ) ≤ 8 * c₀ ^ 2)]
        calc 4 * (8 * c₀ ^ 2 * (Lam / lam) ^ 2 + ((beta * r / lam) ^ 2 + gamma * r ^ 2 / lam)) *
              (3 / 2) ^ Fintype.card ι * V / r ^ 2
            = 4 * (3 / 2) ^ Fintype.card ι * V / r ^ 2 *
                (8 * c₀ ^ 2 * (Lam / lam) ^ 2 + ((beta * r / lam) ^ 2 + gamma * r ^ 2 / lam)) := by
              ring
          _ ≤ 4 * (3 / 2) ^ Fintype.card ι * V / r ^ 2 * ((8 * c₀ ^ 2 + 1) * Q) := by gcongr
          _ = _ := by ring

/-- **The gradient of `log u` on balls.** There is a constant `C ≥ 0`, depending only on the
dimension, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` with
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
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_div_value_sq_le_lowerOrder (ι := ι)
  refine ⟨C, hC0, fun mu _ Omega a lam Lam u ε x₀ r h ha hu hε hεu hr hball => ?_⟩
  -- The case `b = 0`, `c = 0` of the estimate with lower-order terms.
  simpa using hC mu (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _ _ => by rw [Pi.zero_apply, norm_zero])
    (fun _ _ => by rw [Pi.zero_apply, norm_zero]) hu hε hεu hr hball

/-- **The logarithm of a positive supersolution has bounded mean oscillation, with lower-order
terms.** There is a constant `C ≥ 0`, depending only on the dimension, with the following
property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b`
and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `u ≥ ε` almost everywhere for some
`ε > 0`. Then on every ball with `B(x₀, 2r) ⊆ Ω`,

`⨍_{B(x₀, r)} |log u - ⨍_{B(x₀, r)} log u| ≤ C √((Λ/λ)² + (βr/λ)² + γr²/λ)`.

On balls of radius at most `R`, the right side is bounded uniformly in terms of `Λ/λ`, `βR/λ` and
`γR²/λ`, and independently of `u` and `ε`: this is the hypothesis of the John–Nirenberg inequality
for `log u` on such balls. -/
theorem exists_setAverage_abs_log_sub_setAverage_le_lowerOrder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < r → Metric.ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍ x in Metric.ball x₀ r, |Real.log (W1p.value u x) -
          ⨍ y in Metric.ball x₀ r, Real.log (W1p.value u y) ∂mu| ∂mu ≤
        C * √((Lam / lam) ^ 2 + (beta * r / lam) ^ 2 + gamma * r ^ 2 / lam) := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_div_value_sq_le_lowerOrder (ι := ι)
  refine ⟨2 ^ (Fintype.card ι + 1) * √C, by positivity, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma u ε x₀ r h ha hb hc hb_bound hc_bound hu hε hεu hr
    hball
  have hBsub : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hBsub (Metric.mem_ball_self hr)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ hx₀)
  set Q := (Lam / lam) ^ 2 + (beta * r / lam) ^ 2 + gamma * r ^ 2 / lam
  have hQ : 0 ≤ Q := by
    have : 0 ≤ gamma * r ^ 2 / lam := div_nonneg (by positivity) h.pos.le
    positivity
  set f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (W1p.value u x)
  set m := ⨍ y in Metric.ball x₀ r, f y ∂mu
  have hB0 : mu (Metric.ball x₀ r) ≠ 0 := (Metric.measure_ball_pos mu x₀ hr).ne'
  have hBtop : mu (Metric.ball x₀ r) ≠ (⊤ : ℝ≥0∞) := (measure_ball_lt_top (μ := mu)).ne
  have hBpos : 0 < mu.real (Metric.ball x₀ r) := ENNReal.toReal_pos hB0 hBtop
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ r)) := isFiniteMeasure_restrict.2 hBtop
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_log (by simp) hε hεu
  have hmem : MemLp (fun x => f x - m) 2 (mu.restrict (Metric.ball x₀ r)) :=
    (W1p.memLp_log_value (by simp) hε hεu hBsub).sub (memLp_const m)
  -- The Poincaré–Wirtinger inequality on the ball, for `log u`.
  have hP := setIntegral_log_sub_setAverage_sq_le hε hεu hBsub hwv hwg
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
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (hJ.trans ?_)
  rw [hJ']
  -- Poincaré–Wirtinger for `log u`, then the gradient bound for `log u` on the ball.
  calc (mu.real (Metric.ball x₀ r))⁻¹ * ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu
      ≤ (mu.real (Metric.ball x₀ r))⁻¹ * ((2 ^ (Fintype.card ι + 1) * r) ^ 2 *
          (C * Q * mu.real (Metric.ball x₀ r) / r ^ 2)) := by
        gcongr
        exact hP.trans (by
          gcongr
          exact hC mu h ha hb hc hb_bound hc_bound hu hε hεu hr hball)
    _ = (2 ^ (Fintype.card ι + 1) * √C * √Q) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt hQ]
        field_simp

/-- **The logarithm of a positive supersolution has bounded mean oscillation.** There is a
constant `C ≥ 0`, depending only on the dimension, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a
weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` with `u ≥ ε` almost everywhere for some `ε > 0`. Then on
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
  obtain ⟨C, hC0, hC⟩ := exists_setAverage_abs_log_sub_setAverage_le_lowerOrder (ι := ι)
  refine ⟨C, hC0, fun mu _ Omega a lam Lam u ε x₀ r h ha hu hε hεu hr hball => ?_⟩
  -- The case `b = 0`, `c = 0` of the estimate with lower-order terms.
  have hb := hC mu (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _ _ => by rw [Pi.zero_apply, norm_zero])
    (fun _ _ => by rw [Pi.zero_apply, norm_zero]) hu hε hεu hr hball
  have hz : (Lam / lam) ^ 2 + (0 * r / lam) ^ 2 + 0 * r ^ 2 / lam = (Lam / lam) ^ 2 := by ring
  rwa [hz, Real.sqrt_sq (div_nonneg h.upper_nonneg h.pos.le)] at hb

end PDE

end TauCeti
