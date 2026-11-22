/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# Branches through a power substitution and their `Lᵖ` margin

Near a point `x` where `d` sheets of a curve over the complex plane come together, the curve is
parametrized after the substitution `y = x + zᵈ`: its sheets are the values of a single function
`u` of `z`, and a branch over a region of `y` is a function `V` with `V (x + zᵈ) = u z` for `z` in
a sheet `s` of the substitution. Such a branch is no more regular than `y ↦ (y - x) ^ (1 / d)`: its
derivative blows up like `‖y - x‖ ^ (1 / d - 1)` at `x`. This file computes that singularity and
the resulting integrability of the derivative.

* **The branch derivative.** If `s` is open and `u` is real differentiable at `z ∈ s`, `z ≠ 0`,
  then `V` is real differentiable at `x + zᵈ`, and its derivative is the derivative of `u`
  composed with multiplication by `(d z ^ (d - 1))⁻¹`, the inverse of the derivative of the
  substitution (`TauCeti.hasFDerivAt_of_forall_add_pow_eq`). Multiplication by a complex number
  is a similarity (`ContinuousLinearMap.norm_comp_restrictScalars_smulRight_one`), so
  `‖dV‖ = ‖du‖ / ‖d z ^ (d - 1)‖ = (‖du‖ / d) ‖y - x‖ ^ (1 / d - 1)` exactly
  (`TauCeti.norm_fderiv_add_pow_eq_mul_rpow`).
* **Change of variables.** If the substitution is injective on `s`,
  `∫_{x + sᵈ} ‖dV‖ᵖ = ∫_s ‖du‖ᵖ ‖d z ^ (d - 1)‖^(2 - p)`
  (`TauCeti.lintegral_image_add_pow_enorm_fderiv_rpow`): the factor `‖d z ^ (d - 1)‖²` is the
  Jacobian of the substitution.
* **The margin.** If `‖du‖` is bounded on `s` and the image of `s` is bounded, `‖dV‖` is `Lʳ` on
  that image whenever `r (1 - 1 / d) < 2` (`TauCeti.memLp_norm_fderiv_image_add_pow`).
  Conversely, if `‖du‖` is bounded below by a positive constant and the image covers a disc about
  `x` up to a null set, then `‖dV‖ ∈ Lʳ` forces `r (1 - 1 / d) < 2`
  (`TauCeti.toReal_mul_one_sub_inv_lt_two_of_memLp_norm_fderiv_image_add_pow`); together they give
  `TauCeti.memLp_norm_fderiv_image_add_pow_iff`.

The exponent `p_m = 2 + 2 / m` of the coefficient estimates for `m` sheets has
`p_m (1 - 1 / m) = 2 - 2 / m² < 2` (`TauCeti.two_add_two_div_mul_one_sub_inv`), so the derivative
of a branch through a degree-`m` substitution lies in `L^{p_m}`
(`TauCeti.memLp_norm_fderiv_image_add_pow_two_add_two_div`). If a distortion factor `K`
multiplies the exponent, the margin survives exactly when `K (m² - 1) < m²`
(`TauCeti.mul_two_add_two_div_mul_one_sub_inv_lt_two_iff`).

The branch `u` is only assumed real differentiable, so the statements apply to holomorphic
branches and equally to the root branches of real Cauchy–Riemann equations parametrized after a
power substitution, as in `TauCeti.exists_root_branches_hasWeakConjWirtingerDerivOn`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter Bornology
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d : ℕ} {x : ℂ} {s : Set ℂ} {u V : ℂ → E}

/-! ### The margin exponent -/

/-- The exponent `p_m = 2 + 2 / m` of the coefficient estimates for `m` sheets satisfies
`p_m (1 - 1 / m) = 2 - 2 / m²`. -/
theorem two_add_two_div_mul_one_sub_inv {m : ℝ} (hm : m ≠ 0) :
    (2 + 2 / m) * (1 - m⁻¹) = 2 - 2 / m ^ 2 := by
  field_simp
  ring

/-- The margin of the exponent `p_m = 2 + 2 / m`: `p_m (1 - 1 / m) < 2`. -/
theorem two_add_two_div_mul_one_sub_inv_lt_two {m : ℝ} (hm : m ≠ 0) :
    (2 + 2 / m) * (1 - m⁻¹) < 2 := by
  rw [two_add_two_div_mul_one_sub_inv hm]
  have : 0 < 2 / m ^ 2 := by positivity
  linarith

/-- A factor `K` multiplying the exponent `p_m (1 - 1 / m)` keeps it below `2` exactly when
`K (m² - 1) < m²`, that is, when `K < m² / (m² - 1)` for `m² > 1`. -/
theorem mul_two_add_two_div_mul_one_sub_inv_lt_two_iff {m : ℝ} (hm : m ≠ 0) (K : ℝ) :
    K * ((2 + 2 / m) * (1 - m⁻¹)) < 2 ↔ K * (m ^ 2 - 1) < m ^ 2 := by
  have hm2 : 0 < m ^ 2 := by positivity
  rw [two_add_two_div_mul_one_sub_inv hm, ← mul_lt_mul_iff_of_pos_right hm2]
  constructor <;> intro h
  · have : K * (2 - 2 / m ^ 2) * m ^ 2 = 2 * (K * (m ^ 2 - 1)) := by field_simp
    nlinarith
  · have : K * (2 - 2 / m ^ 2) * m ^ 2 = 2 * (K * (m ^ 2 - 1)) := by field_simp
    nlinarith

/-! ### The branch derivative -/

/-- The derivative of the substitution `z ↦ x + zᵈ`. -/
private theorem hasStrictDerivAt_add_pow (x z : ℂ) (d : ℕ) :
    HasStrictDerivAt (fun z ↦ x + z ^ d) ((d : ℂ) * z ^ (d - 1)) z :=
  (hasStrictDerivAt_pow d z).const_add x

private theorem natCast_mul_pow_sub_one_ne_zero (hd : d ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    (d : ℂ) * z ^ (d - 1) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.2 hd) (pow_ne_zero _ hz)

/-- **The derivative of a branch through a power substitution.** Let `V (x + zᵈ) = u z` for all
`z` in an open set `s`. At a point `z ∈ s` other than `0` where `u` has derivative `u'`, the
branch `V` has derivative `u'` composed with multiplication by `(d z ^ (d - 1))⁻¹`, the inverse
of the derivative of the substitution. -/
theorem hasFDerivAt_of_forall_add_pow_eq (hd : d ≠ 0) (hs : IsOpen s)
    (hV : ∀ z ∈ s, V (x + z ^ d) = u z) {z : ℂ} (hz : z ∈ s) (hz0 : z ≠ 0) {u' : ℂ →L[ℝ] E}
    (hu : HasFDerivAt u u' z) :
    HasFDerivAt V (u'.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      ((d : ℂ) * z ^ (d - 1))⁻¹).restrictScalars ℝ)) (x + z ^ d) := by
  have hf := hasStrictDerivAt_add_pow x z d
  have hf' := natCast_mul_pow_sub_one_ne_zero hd hz0
  -- The substitution has a local inverse `g` near `z`, through which `V = u ∘ g`.
  set g := hf.localInverse _ _ _ hf'
  have hg : HasDerivAt g ((d : ℂ) * z ^ (d - 1))⁻¹ (x + z ^ d) :=
    (hf.to_localInverse hf').hasDerivAt
  have hgz : g (x + z ^ d) = z := (hf.eventually_left_inverse hf').self_of_nhds
  have hcont : Tendsto g (𝓝 (x + z ^ d)) (𝓝 z) := by
    simpa only [hgz] using hg.continuousAt.tendsto
  have heq : V =ᶠ[𝓝 (x + z ^ d)] u ∘ g := by
    filter_upwards [hf.eventually_right_inverse hf', hcont (hs.mem_nhds hz)] with y hy hys
    rw [Function.comp_apply, ← hV _ hys, hy]
  have hu' : HasFDerivAt u u' (g (x + z ^ d)) := by rwa [hgz]
  exact (hu'.comp (x + z ^ d) (hg.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq heq

/-- **The size of the branch derivative.** If `V (x + zᵈ) = u z` on an open set `s` and `u` is
differentiable at `z ∈ s`, `z ≠ 0`, then `‖dV‖ = ‖du‖ / ‖d z ^ (d - 1)‖` at `x + zᵈ`. -/
theorem norm_fderiv_add_pow_eq (hd : d ≠ 0) (hs : IsOpen s)
    (hV : ∀ z ∈ s, V (x + z ^ d) = u z) {z : ℂ} (hz : z ∈ s) (hz0 : z ≠ 0)
    (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ V (x + z ^ d)‖ = ‖fderiv ℝ u z‖ / ‖(d : ℂ) * z ^ (d - 1)‖ := by
  rw [(hasFDerivAt_of_forall_add_pow_eq hd hs hV hz hz0 hu.hasFDerivAt).fderiv,
    ContinuousLinearMap.norm_comp_restrictScalars_smulRight_one, norm_inv, div_eq_mul_inv]

/-- The inverse of the stretching factor `‖d z ^ (d - 1)‖` of the substitution, as a power of the
distance `‖zᵈ‖` from the branch point in the target. This holds for every `d` and `z`, including
`z = 0`, where both sides vanish when `d ≥ 2`. -/
private theorem inv_norm_natCast_mul_pow_sub_one (d : ℕ) (z : ℂ) :
    ‖(d : ℂ) * z ^ (d - 1)‖⁻¹ = (d : ℝ)⁻¹ * ‖z ^ d‖ ^ ((d : ℝ)⁻¹ - 1) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hexp : (d : ℝ) * ((d : ℝ)⁻¹ - 1) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hd), Nat.cast_one, mul_sub, mul_inv_cancel₀ hd']
    ring
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, mul_inv, ← Real.rpow_natCast ‖z‖ d,
    ← Real.rpow_mul (norm_nonneg z), hexp, Real.rpow_neg (norm_nonneg z), Real.rpow_natCast]

/-- **The singularity of the branch derivative.** If `V (x + zᵈ) = u z` on an open set `s` and
`u` is differentiable at `z ∈ s`, `z ≠ 0`, then at `y = x + zᵈ`,
`‖dV(y)‖ = (‖du(z)‖ / d) ‖y - x‖ ^ (1 / d - 1)`, with `‖y - x‖ = ‖zᵈ‖`. -/
theorem norm_fderiv_add_pow_eq_mul_rpow (hd : d ≠ 0) (hs : IsOpen s)
    (hV : ∀ z ∈ s, V (x + z ^ d) = u z) {z : ℂ} (hz : z ∈ s) (hz0 : z ≠ 0)
    (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ V (x + z ^ d)‖ = ‖fderiv ℝ u z‖ / d * ‖z ^ d‖ ^ ((d : ℝ)⁻¹ - 1) := by
  rw [norm_fderiv_add_pow_eq hd hs hV hz hz0 hu, div_eq_mul_inv,
    inv_norm_natCast_mul_pow_sub_one, div_eq_mul_inv, mul_assoc]

/-! ### Change of variables -/

/-- **Change of variables for a branch.** Let `V (x + zᵈ) = u z` on an open set `s` on which the
substitution `z ↦ x + zᵈ` is injective, with `u` differentiable on `s`. Then for every real `p`
the `p`-th power of `‖dV‖` integrates over the image of `s` to the integral of
`‖du‖ᵖ ‖d z ^ (d - 1)‖^(2 - p)` over `s`; the factor `‖d z ^ (d - 1)‖²` is the Jacobian of
the substitution. -/
theorem lintegral_image_add_pow_enorm_fderiv_rpow (hs : IsOpen s)
    (hinj : InjOn (fun z ↦ x + z ^ d) s) (hu : ∀ z ∈ s, DifferentiableAt ℝ u z)
    (hV : ∀ z ∈ s, V (x + z ^ d) = u z) (p : ℝ) :
    ∫⁻ y in (fun z ↦ x + z ^ d) '' s, ‖fderiv ℝ V y‖ₑ ^ p =
      ∫⁻ z in s, ‖fderiv ℝ u z‖ₑ ^ p * ‖(d : ℂ) * z ^ (d - 1)‖ₑ ^ (2 - p) := by
  rcases eq_or_ne d 0 with rfl | hd
  · -- For `d = 0` the substitution is constant, so injectivity leaves at most one point of `s`.
    have hsub : s.Subsingleton := fun a ha b hb ↦ hinj ha hb (by simp)
    rw [setLIntegral_measure_zero _ _ (hsub.measure_zero _),
      setLIntegral_measure_zero _ _ ((hsub.image _).measure_zero _)]
  rw [lintegral_image_eq_lintegral_enorm_deriv_sq_mul
    (fun z _ ↦ (hasStrictDerivAt_add_pow x z d).hasDerivAt.differentiableAt) hs.measurableSet
    hinj]
  refine setLIntegral_congr_fun_ae hs.measurableSet ?_
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h0] with z hz0 hz
  have hc := natCast_mul_pow_sub_one_ne_zero hd hz0
  have hc0 : ‖(d : ℂ) * z ^ (d - 1)‖ₑ ≠ 0 := eNorm_ne_zero.2 hc
  have hcV : ‖fderiv ℝ V (x + z ^ d)‖ₑ = ‖fderiv ℝ u z‖ₑ / ‖(d : ℂ) * z ^ (d - 1)‖ₑ := by
    rw [← ofReal_norm, norm_fderiv_add_pow_eq hd hs hV hz hz0 (hu z hz),
      ENNReal.ofReal_div_of_pos (norm_pos_iff.2 hc), ofReal_norm, ofReal_norm]
  rw [(hasStrictDerivAt_add_pow x z d).hasDerivAt.deriv, hcV, div_eq_mul_inv,
    ENNReal.mul_rpow_of_ne_top eNorm_ne_top (ENNReal.inv_ne_top.2 hc0), ENNReal.inv_rpow,
    ENNReal.rpow_sub _ _ hc0 eNorm_ne_top, ← ENNReal.rpow_natCast, Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-! ### The `Lᵖ` margin -/

/-- For `d = 0` the substitution is constant, so the image of any set is at most a point. -/
private theorem subsingleton_image_add_pow_zero (x : ℂ) (s : Set ℂ) :
    ((fun z ↦ x + z ^ 0) '' s).Subsingleton := by
  rintro _ ⟨_, -, rfl⟩ _ ⟨_, -, rfl⟩
  simp

/-- The image of an open set under the substitution `z ↦ x + zᵈ` is measurable: off the origin the
substitution is open, and the origin contributes at most the point `x`. -/
private theorem measurableSet_image_add_pow (hs : IsOpen s) :
    MeasurableSet ((fun z ↦ x + z ^ d) '' s) := by
  have hsub : ((fun z ↦ x + z ^ d) '' (s ∩ {0})).Subsingleton :=
    (subsingleton_singleton.anti inter_subset_right).image _
  rcases eq_or_ne d 0 with rfl | hd
  · exact (subsingleton_image_add_pow_zero x s).measurableSet
  rw [← sdiff_union_inter s {0}, image_union]
  refine (IsOpen.measurableSet ?_).union hsub.measurableSet
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩
  rw [← (hasStrictDerivAt_add_pow x z d).map_nhds_eq
    (natCast_mul_pow_sub_one_ne_zero hd hz0)]
  exact image_mem_map ((hs.sdiff isClosed_singleton).mem_nhds ⟨hz, hz0⟩)

/-- Almost every point `y` of the image of `s` is `x + zᵈ` for some `z ∈ s` other than `0`. -/
private theorem ae_restrict_image_add_pow (hd : d ≠ 0) (hs : IsOpen s) :
    ∀ᵐ y ∂volume.restrict ((fun z ↦ x + z ^ d) '' s), ∃ z ∈ s, z ≠ 0 ∧ x + z ^ d = y := by
  have hx : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem (measurableSet_image_add_pow hs), ae_restrict_of_ae hx]
    with y ⟨z, hz, hzy⟩ hyx
  refine ⟨z, hz, fun hz0 ↦ hyx ?_, hzy⟩
  simp only [← hzy, hz0, zero_pow hd, add_zero]

/-- **The `Lᵖ` margin of a branch derivative.** Let `V (x + zᵈ) = u z` on an open set `s`, with
`u` differentiable on `s` and `‖du‖ ≤ M` there, and let the image of `s` be bounded. Then
`‖dV‖` is `Lʳ` on the image of `s` for every finite `r` with `r (1 - 1 / d) < 2`. -/
theorem memLp_norm_fderiv_image_add_pow [CompleteSpace E] (hs : IsOpen s)
    (hu : ∀ z ∈ s, DifferentiableAt ℝ u z) (hV : ∀ z ∈ s, V (x + z ^ d) = u z) {M : ℝ}
    (hM : ∀ z ∈ s, ‖fderiv ℝ u z‖ ≤ M) (hb : IsBounded ((fun z ↦ x + z ^ d) '' s))
    {r : ℝ≥0∞} (hr : r ≠ ∞) (hmargin : r.toReal * (1 - (d : ℝ)⁻¹) < 2) :
    MemLp (fun y ↦ ‖fderiv ℝ V y‖) r (volume.restrict ((fun z ↦ x + z ^ d) '' s)) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [Measure.restrict_eq_zero.2 ((subsingleton_image_add_pow_zero x s).measure_zero _)]
    exact memLp_measure_zero
  refine hb.memLp_of_ae_norm_le_mul_norm_sub_rpow hr (s := (d : ℝ)⁻¹ - 1) (C := M / d) ?_ x
    (measurable_fderiv ℝ V).norm.aestronglyMeasurable ?_
  · rw [Complex.finrank_real_complex]
    push_cast
    linarith
  filter_upwards [ae_restrict_image_add_pow hd hs] with y ⟨z, hz, hz0, hzy⟩
  subst hzy
  rw [norm_norm, norm_fderiv_add_pow_eq_mul_rpow hd hs hV hz hz0 (hu z hz), sub_add_cancel_left,
    norm_neg]
  gcongr
  exact hM z hz

/-- **Sharpness of the `Lᵖ` margin.** Let `V (x + zᵈ) = u z` on an open set `s`, with `u`
differentiable on `s` and `c ≤ ‖du‖` there for some `c > 0`, and let the image of `s` contain a
disc about `x` up to a null set. If `‖dV‖` is `Lʳ` on the image of `s`, then
`r (1 - 1 / d) < 2`; this is automatic for `r = 0` and `r = ∞`, where `r.toReal = 0`. -/
theorem toReal_mul_one_sub_inv_lt_two_of_memLp_norm_fderiv_image_add_pow (hs : IsOpen s)
    (hu : ∀ z ∈ s, DifferentiableAt ℝ u z) (hV : ∀ z ∈ s, V (x + z ^ d) = u z) {c : ℝ}
    (hc : 0 < c) (hcu : ∀ z ∈ s, c ≤ ‖fderiv ℝ u z‖) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball x ρ ≤ᵐ[volume] (fun z ↦ x + z ^ d) '' s) {r : ℝ≥0∞}
    (hdV : MemLp (fun y ↦ ‖fderiv ℝ V y‖) r (volume.restrict ((fun z ↦ x + z ^ d) '' s))) :
    r.toReal * (1 - (d : ℝ)⁻¹) < 2 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  rcases eq_or_ne d 0 with rfl | hd
  · -- For `d = 0` the image is at most a point, which cannot contain a disc up to a null set.
    have := measure_mono_ae hball
    rw [(subsingleton_image_add_pow_zero x s).measure_zero, nonpos_iff_eq_zero] at this
    exact absurd this (measure_ball_pos volume x hρ).ne'
  set q := ((d : ℝ)⁻¹ - 1) * r.toReal
  have hcd : 0 < (c / d) ^ r.toReal := Real.rpow_pos_of_pos (div_pos hc (by positivity)) _
  have hint := (integrable_norm_rpow_iff hdV.aestronglyMeasurable hr0 hr).2 hdV
  -- On the image, `(c / d)ʳ ‖x - y‖^q ≤ ‖dV(y)‖ʳ`.
  have hlow : IntegrableOn (fun y ↦ (c / d) ^ r.toReal * ‖x - y‖ ^ q)
      ((fun z ↦ x + z ^ d) '' s) := by
    refine hint.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_image_add_pow hd hs] with y ⟨z, hz, hz0, hzy⟩
    subst hzy
    have hpow : 0 ≤ ‖z ^ d‖ ^ ((d : ℝ)⁻¹ - 1) := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_of_nonneg (by positivity), sub_add_cancel_left, norm_neg, norm_norm,
      norm_fderiv_add_pow_eq_mul_rpow hd hs hV hz hz0 (hu z hz), Real.rpow_mul (norm_nonneg _),
      ← Real.mul_rpow (div_nonneg hc.le (Nat.cast_nonneg d)) hpow]
    gcongr
    exact hcu z hz
  have hball' : IntegrableOn (fun y ↦ ‖x - y‖ ^ q) (ball x ρ) :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.2 hcd.ne') _).1 (hlow.mono_set_ae hball)
  rw [integrableOn_norm_sub_rpow_ball_iff_integrableOn_norm_rpow_ball,
    integrableOn_norm_rpow_ball_iff hρ, Complex.finrank_real_complex] at hball'
  push_cast at hball'
  linarith

/-- **The `Lᵖ` margin of a branch derivative, both directions.** Let `V (x + zᵈ) = u z` on an open
set `s`, with `u` differentiable on `s` and `c ≤ ‖du‖ ≤ M` there for some `c > 0`, and let the
image of `s` be bounded and contain a disc about `x` up to a null set. Then for a finite `r`,
`‖dV‖` is `Lʳ` on the image of `s` exactly when `r (1 - 1 / d) < 2`. -/
theorem memLp_norm_fderiv_image_add_pow_iff [CompleteSpace E] (hs : IsOpen s)
    (hu : ∀ z ∈ s, DifferentiableAt ℝ u z) (hV : ∀ z ∈ s, V (x + z ^ d) = u z) {c M : ℝ}
    (hc : 0 < c) (hcu : ∀ z ∈ s, c ≤ ‖fderiv ℝ u z‖) (hM : ∀ z ∈ s, ‖fderiv ℝ u z‖ ≤ M)
    (hb : IsBounded ((fun z ↦ x + z ^ d) '' s)) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball x ρ ≤ᵐ[volume] (fun z ↦ x + z ^ d) '' s) {r : ℝ≥0∞} (hr : r ≠ ∞) :
    MemLp (fun y ↦ ‖fderiv ℝ V y‖) r (volume.restrict ((fun z ↦ x + z ^ d) '' s)) ↔
      r.toReal * (1 - (d : ℝ)⁻¹) < 2 :=
  ⟨toReal_mul_one_sub_inv_lt_two_of_memLp_norm_fderiv_image_add_pow hs hu hV hc hcu hρ hball,
    memLp_norm_fderiv_image_add_pow hs hu hV hM hb hr⟩

/-- **Branch derivatives lie in `L^{p_d}`.** Let `V (x + zᵈ) = u z` on an open set `s`, with `u`
differentiable on `s` and `‖du‖ ≤ M` there, and let the image of `s` be bounded. Then `‖dV‖` is
`L^{p_d}` on the image of `s` for the exponent `p_d = 2 + 2 / d` of `d` sheets, by the margin
`p_d (1 - 1 / d) = 2 - 2 / d² < 2`. -/
theorem memLp_norm_fderiv_image_add_pow_two_add_two_div [CompleteSpace E] (hs : IsOpen s)
    (hu : ∀ z ∈ s, DifferentiableAt ℝ u z) (hV : ∀ z ∈ s, V (x + z ^ d) = u z)
    {M : ℝ} (hM : ∀ z ∈ s, ‖fderiv ℝ u z‖ ≤ M) (hb : IsBounded ((fun z ↦ x + z ^ d) '' s)) :
    MemLp (fun y ↦ ‖fderiv ℝ V y‖) (ENNReal.ofReal (2 + 2 / d))
      (volume.restrict ((fun z ↦ x + z ^ d) '' s)) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [Measure.restrict_eq_zero.2 ((subsingleton_image_add_pow_zero x s).measure_zero _)]
    exact memLp_measure_zero
  refine memLp_norm_fderiv_image_add_pow hs hu hV hM hb ENNReal.ofReal_ne_top ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact two_add_two_div_mul_one_sub_inv_lt_two (Nat.cast_ne_zero.2 hd)

end TauCeti
