/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Analysis.Convex.StrictConvexSpace

/-!
# Strict convexity of `Lᵖ` spaces

For `1 < p < ∞` and a strictly convex real normed space `E`, the space `Lᵖ(μ; E)` is strictly
convex. The proof integrates the pointwise strict convexity of `v ↦ ‖v‖ ^ p` on `E`
(`TauCeti.strictConvexOn_norm_rpow`): if `‖f‖ = ‖g‖ = 1` and `‖(f + g) / 2‖ = 1`, the integrand
`(‖f‖ ^ p + ‖g‖ ^ p) / 2 - ‖(f + g) / 2‖ ^ p` is nonnegative with integral zero, so it vanishes
almost everywhere, which forces `f = g` almost everywhere.

Both endpoint exponents are genuinely excluded: `L¹` and `L^∞` of a measure space with two disjoint
sets of positive finite measure contain nontrivial segments in their unit spheres.

Strict convexity is what makes geodesics unique in a metric space that embeds isometrically in
`Lᵖ`: the only geodesic segment of a strictly convex normed space is the affine one. This is how
the one-dimensional Wasserstein space `P_p(ℝ)`, `1 < p < ∞`, is seen to be uniquely geodesic.

## Main statements

* `MeasureTheory.Lp.strictConvexSpace` — `Lᵖ(μ; E)` is strictly convex for `1 < p < ∞` when `E`
  is.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {p : ℝ≥0∞}

/-- The midpoint inequality for `v ↦ ‖v‖ ^ q`, read in `ℝ≥0∞`, as a non-strict inequality together
with its equality case. -/
private theorem enorm_midpoint_rpow_le {q : ℝ} (hq : 1 < q) (a b : E) :
    ‖(2⁻¹ : ℝ) • (a + b)‖ₑ ^ q ≤ 2⁻¹ * ‖a‖ₑ ^ q + 2⁻¹ * ‖b‖ₑ ^ q ∧
      (‖(2⁻¹ : ℝ) • (a + b)‖ₑ ^ q = 2⁻¹ * ‖a‖ₑ ^ q + 2⁻¹ * ‖b‖ₑ ^ q → a = b) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq.le
  have henorm (v : E) : ‖v‖ₑ ^ q = ENNReal.ofReal (‖v‖ ^ q) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg v) hq0]
  have hrhs : 2⁻¹ * ‖a‖ₑ ^ q + 2⁻¹ * ‖b‖ₑ ^ q =
      ENNReal.ofReal (2⁻¹ * ‖a‖ ^ q + 2⁻¹ * ‖b‖ ^ q) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num), henorm, henorm, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hconv := TauCeti.strictConvexOn_norm_rpow (E := E) hq
  rw [henorm, hrhs]
  refine ⟨ENNReal.ofReal_le_ofReal ?_, fun h ↦ ?_⟩
  · simpa only [smul_eq_mul, smul_add] using
      hconv.convexOn.2 (mem_univ a) (mem_univ b) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
  · by_contra hab
    have hlt := hconv.2 (mem_univ a) (mem_univ b) hab (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
    simp only [smul_eq_mul, ← smul_add] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hlt |>.ne h

/-- **`Lᵖ` is strictly convex.** For `1 < p < ∞` and a strictly convex real normed space `E`, the
space `Lᵖ(μ; E)` is strictly convex. -/
theorem strictConvexSpace [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    StrictConvexSpace ℝ (Lp E p μ) := by
  refine StrictConvexSpace.of_norm_add_ne_two fun f g hf hg hfg h2 ↦ hfg ?_
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hq : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp_top hp
  -- The integral of the `q`-th power of the pointwise norm is the `q`-th power of the norm.
  have hint (h : Lp E p μ) : ∫⁻ x, ‖h x‖ₑ ^ p.toReal ∂μ = ‖h‖ₑ ^ p.toReal := by
    rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' hp0 hp_top (Lp.aestronglyMeasurable h),
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (zero_lt_one.trans hq)]
  have hone {h : Lp E p μ} (hh : ‖h‖ = 1) : ‖h‖ₑ = 1 := by
    rw [← ofReal_norm, hh, ENNReal.ofReal_one]
  have hmid : ‖(2⁻¹ : ℝ) • (f + g)‖ = 1 := by
    rw [norm_smul, h2]
    norm_num
  set F : α → ℝ≥0∞ := fun x ↦ ‖(2⁻¹ : ℝ) • (f x + g x)‖ₑ ^ p.toReal
  set G : α → ℝ≥0∞ := fun x ↦ 2⁻¹ * ‖f x‖ₑ ^ p.toReal + 2⁻¹ * ‖g x‖ₑ ^ p.toReal
  -- The midpoint integrand integrates to `1`, as does the average of the two integrands.
  have hF : ∫⁻ x, F x ∂μ = 1 := by
    have hcoe : (fun x ↦ ‖((2⁻¹ : ℝ) • (f + g) : Lp E p μ) x‖ₑ ^ p.toReal) =ᵐ[μ] F := by
      filter_upwards [Lp.coeFn_smul (2⁻¹ : ℝ) (f + g), Lp.coeFn_add f g] with x hs ha
      simp only [F, hs, Pi.smul_apply, ha, Pi.add_apply]
    rw [← lintegral_congr_ae hcoe, hint, hone hmid, ENNReal.one_rpow]
  have hmeas (h : Lp E p μ) : AEMeasurable (fun x ↦ ‖h x‖ₑ ^ p.toReal) μ :=
    (Lp.aestronglyMeasurable h).enorm.pow_const _
  have hG : ∫⁻ x, G x ∂μ = 1 := by
    rw [lintegral_add_left' ((hmeas f).const_mul _), lintegral_const_mul'' _ (hmeas f),
      lintegral_const_mul'' _ (hmeas g), hint, hint, hone hf, hone hg, ENNReal.one_rpow,
      mul_one, ENNReal.inv_two_add_inv_two]
  -- So the pointwise midpoint inequality is an equality almost everywhere, which forces `f = g`.
  have hFG : F =ᵐ[μ] G :=
    ae_eq_of_ae_le_of_lintegral_le (.of_forall fun x ↦ (enorm_midpoint_rpow_le hq _ _).1)
      (by rw [hF]; exact ENNReal.one_ne_top) (((hmeas f).const_mul _).add ((hmeas g).const_mul _))
      (by rw [hF, hG])
  refine Lp.ext ?_
  filter_upwards [hFG] with x hx
  exact (enorm_midpoint_rpow_le hq _ _).2 hx

end MeasureTheory.Lp
