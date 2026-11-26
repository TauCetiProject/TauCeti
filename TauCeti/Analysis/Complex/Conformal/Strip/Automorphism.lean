/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.Strip.Basic
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
import TauCeti.Analysis.Complex.UpperHalfPlane.Log
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Order.Filter.Tendsto

/-!
# Holomorphic automorphisms of the strip fixing its two ends

The real translations `z ↦ z + c` are holomorphic automorphisms of the strip
`ℝ × (0, 1) = {z | 0 < z.im < 1}` which fix its two ends: they send `re z → -∞` to `re z → -∞`
and `re z → ∞` to `re z → ∞`. This file proves that they are the only ones
(`TauCeti.exists_eqOn_add_of_bijOn_strip`). In particular a holomorphic automorphism of the strip
fixing both ends maps each of the two boundary lines to itself: it cannot exchange them, as the
antiholomorphic reflection `z ↦ conj z + i` does.

This is the rigidity behind the translation action of `ℝ` on holomorphic strips in Lagrangian and
Heegaard Floer theory: two holomorphic parametrizations of the same strip-like domain by
`ℝ × [0, 1]`, with the same ends, differ by a translation in the `ℝ` direction.

The proof transports the question to the unit disc. The coordinate
`z ↦ (exp (π z) - i) / (exp (π z) + i)`, the Cayley transform of the exponential coordinate
`z ↦ exp (π z)` of `TauCeti.bijOn_exp_pi_mul_add_strip`, is a holomorphic bijection of the strip
onto the disc with inverse `ζ ↦ log (i (1 + ζ) / (1 - ζ)) / π`. It sends the negative end of the
strip to `-1` and the positive end to `1`. Conjugated by it, an automorphism `φ` of the strip
fixing both ends becomes a holomorphic automorphism of the disc, of the form
`ζ ↦ u (ζ - a) / (1 - conj a ζ)` by
`TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv`, which extends continuously
to `±1` and fixes these two boundary points. Fixing `1` and `-1` forces `u = 1` and `a` real
(`TauCeti.coe_eq_one_and_conj_eq_of_tendsto`), and the automorphism `ζ ↦ (ζ - a) / (1 - a ζ)` of
the disc with real `a` is the conjugate of the translation of the strip by
`log ((1 - a) / (1 + a)) / π` (`TauCeti.sub_ofReal_div_one_sub_ofReal_mul_sub_I_div_add_I`).

Consequently two holomorphic parametrizations `u` and `v` of the same domain by the strip, with
the same limits `x ≠ y` at the two ends, differ by a real translation as soon as `v` extends
continuously to the closed strip without taking the values `x` and `y`
(`TauCeti.exists_eqOn_add_of_bijOn_of_notMem_image`): then `v⁻¹ ∘ u` is an automorphism of the
strip fixing both ends, because a compactness argument shows that `v z` can only approach `x`
(respectively `y`) as `z` runs to the negative (respectively positive) end. This holds for the
strip maps of a Jordan bigon of `TauCeti.exists_continuousOn_bijOn_strip_of_isJordanCurve_frontier`,
which map the closed strip bijectively onto the closure of the bigon with its two corners removed.

## Main results

* `TauCeti.exists_eqOn_add_of_bijOn_strip`: a holomorphic bijection of the strip onto itself
  which fixes both ends is a real translation.
* `TauCeti.exists_eqOn_add_of_bijOn_of_notMem_image`: two holomorphic parametrizations of a domain
  by the strip with the same ends differ by a real translation, provided one of them extends
  continuously to the closed strip without taking the end values there.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill, 1979, Ch. 4, Section 3 (the
  automorphisms of the disc) and Ch. 3, Section 4 (elementary conformal mappings, among them the
  maps of the strip).
-/

public section

open Bornology Complex Filter Function Metric Set Topology
open UpperHalfPlane (upperHalfPlaneSet)
open scoped ComplexConjugate Real

namespace TauCeti

/-! ### A coordinate identifying the strip with the disc -/

/-- The holomorphic bijection `z ↦ (exp (π z) - i) / (exp (π z) + i)` of the strip onto the unit
disc, the Cayley transform of the exponential coordinate of the strip. -/
private noncomputable def stripToDisc (z : ℂ) : ℂ :=
  (cexp (π * z) - I) / (cexp (π * z) + I)

/-- Its inverse `ζ ↦ log (i (1 + ζ) / (1 - ζ)) / π`. -/
private noncomputable def discToStrip (ζ : ℂ) : ℂ :=
  log (I * (1 + ζ) / (1 - ζ)) / π

/-- The exponential coordinate `z ↦ exp (π z)` maps the strip onto the upper half-plane. -/
private theorem bijOn_exp_pi_mul_strip :
    BijOn (fun z : ℂ => cexp (π * z)) {z : ℂ | z.im ∈ Ioo 0 1} upperHalfPlaneSet := by
  simpa using bijOn_exp_pi_mul_add_strip 0

/-- The logarithmic coordinate `w ↦ log w / π` inverts it. -/
private theorem invOn_log_div_pi_exp_pi_mul_strip :
    InvOn (fun w : ℂ => log w / π) (fun z : ℂ => cexp (π * z))
      {z : ℂ | z.im ∈ Ioo 0 1} upperHalfPlaneSet := by
  simpa using invOn_log_sub_div_pi_exp_pi_mul_add_strip 0

private theorem stripToDisc_mem_ball {z : ℂ} (hz : z ∈ {z : ℂ | z.im ∈ Ioo 0 1}) :
    stripToDisc z ∈ ball (0 : ℂ) 1 :=
  bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo (bijOn_exp_pi_mul_strip.mapsTo hz)

private theorem discToStrip_mem_strip {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    discToStrip ζ ∈ {z : ℂ | z.im ∈ Ioo 0 1} :=
  (bijOn_exp_pi_mul_strip.symm invOn_log_div_pi_exp_pi_mul_strip.symm).mapsTo
    (bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hζ)

private theorem discToStrip_stripToDisc {z : ℂ} (hz : z ∈ {z : ℂ | z.im ∈ Ioo 0 1}) :
    discToStrip (stripToDisc z) = z := by
  have him : 0 < (cexp (π * z)).im := bijOn_exp_pi_mul_strip.mapsTo hz
  have hI : cexp (π * z) + I ≠ 0 := add_I_ne_zero_of_im_nonneg him.le
  rw [discToStrip, stripToDisc, I_mul_one_add_sub_I_div_add_I_div_one_sub hI]
  exact invOn_log_div_pi_exp_pi_mul_strip.1 hz

private theorem stripToDisc_discToStrip {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    stripToDisc (discToStrip ζ) = ζ := by
  have h := invOn_log_div_pi_exp_pi_mul_strip.2 (bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hζ)
  simp only at h
  rw [stripToDisc, discToStrip, h]
  exact sub_I_div_add_I_I_mul_one_add_div_one_sub
    (sub_ne_zero.mp (one_sub_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp hζ))).symm

private theorem differentiableOn_stripToDisc :
    DifferentiableOn ℂ stripToDisc {z : ℂ | z.im ∈ Ioo 0 1} := by
  intro z hz
  have him : 0 < (cexp (π * z)).im := bijOn_exp_pi_mul_strip.mapsTo hz
  have hI : cexp (π * z) + I ≠ 0 := add_I_ne_zero_of_im_nonneg him.le
  have he : DifferentiableAt ℂ (fun z : ℂ => cexp (π * z)) z :=
    ((differentiableAt_const _).mul differentiableAt_id).cexp
  exact ((he.sub_const I).div (he.add_const I) hI).differentiableWithinAt

private theorem differentiableOn_discToStrip :
    DifferentiableOn ℂ discToStrip (ball (0 : ℂ) 1) := by
  intro ζ hζ
  have him : 0 < (I * (1 + ζ) / (1 - ζ)).im := bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hζ
  have hw : I * (1 + ζ) / (1 - ζ) ∈ slitPlane := mem_slitPlane_iff.mpr (.inr him.ne')
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => I * (1 + ζ) / (1 - ζ)) ζ :=
    ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id)
      (one_sub_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp hζ))
  exact ((hd.clog hw).div_const _).differentiableWithinAt

/-! ### The two ends -/

/-- The coordinate sends the negative end of the strip to `-1`. -/
private theorem tendsto_stripToDisc_atBot :
    Tendsto stripToDisc (comap re atBot ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1}) (𝓝 (-1)) := by
  have h : Tendsto (fun z : ℂ => (cexp (π * z) + ((0 : ℝ) : ℂ) - I) /
      (cexp (π * z) + ((0 : ℝ) : ℂ) + I))
      (comap re atBot ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1})
      (𝓝 ((((0 : ℝ) : ℂ) - I) / (((0 : ℝ) : ℂ) + I))) :=
    (continuousAt_sub_I_div_add_I 0).tendsto.comp
      ((tendsto_exp_pi_mul_add_comap_re_atBot 0).mono_left inf_le_left)
  have hI : (((0 : ℝ) : ℂ) - I) / (((0 : ℝ) : ℂ) + I) = -1 := by simp [I_ne_zero]
  rw [hI] at h
  exact h.congr fun z => by simp [stripToDisc]

/-- The coordinate sends the positive end of the strip to `1`. -/
private theorem tendsto_stripToDisc_atTop :
    Tendsto stripToDisc (comap re atTop ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1}) (𝓝 1) :=
  (tendsto_sub_I_div_add_I_cobounded.comp
    ((tendsto_exp_pi_mul_add_comap_re_atTop 0).mono_left inf_le_left)).congr fun z => by
      simp [stripToDisc]

/-- The real part of the inverse coordinate is `log (|1 + ζ| / |1 - ζ|) / π`. -/
private theorem re_discToStrip (ζ : ℂ) :
    (discToStrip ζ).re = Real.log (‖1 + ζ‖ / ‖1 - ζ‖) / π := by
  rw [discToStrip, div_ofReal_re, log_re, norm_div, norm_mul, norm_I, one_mul]

/-- `|1 + ζ|` tends to `|1 + ζ₀|` as `ζ` tends to `ζ₀` in the disc. -/
private theorem tendsto_norm_one_add (ζ₀ : ℂ) :
    Tendsto (fun ζ : ℂ => ‖1 + ζ‖) (𝓝[ball 0 1] ζ₀) (𝓝 ‖1 + ζ₀‖) :=
  ((continuous_const.add continuous_id).norm.tendsto ζ₀).mono_left nhdsWithin_le_nhds

/-- `|1 - ζ|` tends to `|1 - ζ₀|` as `ζ` tends to `ζ₀` in the disc. -/
private theorem tendsto_norm_one_sub (ζ₀ : ℂ) :
    Tendsto (fun ζ : ℂ => ‖1 - ζ‖) (𝓝[ball 0 1] ζ₀) (𝓝 ‖1 - ζ₀‖) :=
  ((continuous_const.sub continuous_id).norm.tendsto ζ₀).mono_left nhdsWithin_le_nhds

/-- The inverse coordinate sends `-1` to the negative end of the strip. -/
private theorem tendsto_discToStrip_neg_one :
    Tendsto discToStrip (𝓝[ball 0 1] (-1)) (comap re atBot ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1}) := by
  refine (tendsto_comap_iff.mpr ?_).inf_principal_of_mapsTo
    fun ζ hζ => discToStrip_mem_strip hζ
  have hq : Tendsto (fun ζ : ℂ => ‖1 + ζ‖ / ‖1 - ζ‖) (𝓝[ball 0 1] (-1)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
    · have h := (tendsto_norm_one_add (-1)).div (tendsto_norm_one_sub (-1)) (by norm_num)
      norm_num at h
      exact h
    have hζ' : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    have h₁ : 1 + ζ ≠ 0 := by
      simpa using one_sub_ne_zero_of_norm_lt_one (x := -ζ) (by simpa using hζ')
    exact div_ne_zero (norm_ne_zero_iff.mpr h₁)
      (norm_ne_zero_iff.mpr (one_sub_ne_zero_of_norm_lt_one hζ'))
  exact ((Real.tendsto_log_nhdsNE_zero.comp hq).atBot_div_const Real.pi_pos).congr fun ζ => by
    simp [re_discToStrip]

/-- The inverse coordinate sends `1` to the positive end of the strip. -/
private theorem tendsto_discToStrip_one :
    Tendsto discToStrip (𝓝[ball 0 1] 1) (comap re atTop ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1}) := by
  refine (tendsto_comap_iff.mpr ?_).inf_principal_of_mapsTo
    fun ζ hζ => discToStrip_mem_strip hζ
  have hnum := tendsto_norm_one_add 1
  have hden : Tendsto (fun ζ : ℂ => ‖1 - ζ‖) (𝓝[ball 0 1] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using tendsto_norm_one_sub 1,
      eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
    exact norm_pos_iff.mpr (one_sub_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp hζ))
  have h2 : ‖(1 : ℂ) + 1‖ = 2 := by norm_num
  rw [h2] at hnum
  have hq : Tendsto (fun ζ : ℂ => ‖1 + ζ‖ / ‖1 - ζ‖) (𝓝[ball 0 1] 1) atTop := by
    simpa only [div_eq_mul_inv, comp_def] using
      hnum.pos_mul_atTop two_pos (tendsto_inv_nhdsGT_zero.comp hden)
  exact ((Real.tendsto_log_atTop.comp hq).atTop_div_const Real.pi_pos).congr fun ζ => by
    simp [re_discToStrip]

/-! ### Automorphisms of the strip -/

/-- Conjugated to the disc by the coordinate `stripToDisc`, a holomorphic automorphism of the strip
becomes a standard disc automorphism `ζ ↦ u (ζ - a) / (1 - conj a ζ)`. -/
private theorem exists_eqOn_stripToDisc_comp {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ {z | z.im ∈ Ioo 0 1})
    (hφS : BijOn φ {z | z.im ∈ Ioo 0 1} {z | z.im ∈ Ioo 0 1}) :
    ∃ (u : Circle) (a : Complex.UnitDisc), EqOn (stripToDisc ∘ φ ∘ discToStrip)
      (fun ζ => (u : ℂ) * ((ζ - a) / (1 - conj (a : ℂ) * ζ))) (ball 0 1) := by
  set S := {z : ℂ | z.im ∈ Ioo 0 1}
  have hSo : IsOpen S := isOpen_Ioo.preimage continuous_im
  -- The inverse `ψ` of `φ` is holomorphic.
  set ψ := invFunOn φ S
  have hinv : InvOn ψ φ S S := hφS.invOn_invFunOn
  have hψ : DifferentiableOn ℂ ψ S := by
    simpa [hφS.image_eq] using hφ.invFunOn hSo hφS.injOn
  have hψS : MapsTo ψ S S := (hφS.symm hinv.symm).mapsTo
  -- Conjugate `φ` and `ψ` to holomorphic self-maps `f` and `g` of the disc, inverse to each other.
  set f : ℂ → ℂ := stripToDisc ∘ φ ∘ discToStrip
  set g : ℂ → ℂ := stripToDisc ∘ ψ ∘ discToStrip
  have hfd : DifferentiableOn ℂ f (ball 0 1) :=
    differentiableOn_stripToDisc.comp (hφ.comp differentiableOn_discToStrip
      fun ζ hζ => discToStrip_mem_strip hζ) fun ζ hζ => hφS.mapsTo (discToStrip_mem_strip hζ)
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    differentiableOn_stripToDisc.comp (hψ.comp differentiableOn_discToStrip
      fun ζ hζ => discToStrip_mem_strip hζ) fun ζ hζ => hψS (discToStrip_mem_strip hζ)
  have hfm : MapsTo f (ball 0 1) (ball 0 1) := fun ζ hζ =>
    stripToDisc_mem_ball (hφS.mapsTo (discToStrip_mem_strip hζ))
  have hgm : MapsTo g (ball 0 1) (ball 0 1) := fun ζ hζ =>
    stripToDisc_mem_ball (hψS (discToStrip_mem_strip hζ))
  have hgf : LeftInvOn g f (ball 0 1) := fun ζ hζ => by
    simp only [f, g, comp_apply]
    rw [discToStrip_stripToDisc (hφS.mapsTo (discToStrip_mem_strip hζ)),
      hinv.1 (discToStrip_mem_strip hζ), stripToDisc_discToStrip hζ]
  have hfg : RightInvOn g f (ball 0 1) := fun ζ hζ => by
    simp only [f, g, comp_apply]
    rw [discToStrip_stripToDisc (hψS (discToStrip_mem_strip hζ)),
      hinv.2 (discToStrip_mem_strip hζ), stripToDisc_discToStrip hζ]
  obtain ⟨u, a, -, hua⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv hfd hgd hfm hgm hgf hfg
  refine ⟨u, a, fun ζ hζ => ?_⟩
  have h := hua (Complex.UnitDisc.mk ζ (by simpa using hζ))
  rwa [coe_unitDiscStandardAutomorphismEquiv_apply, Complex.UnitDisc.coe_mk] at h

/-- **Automorphisms of the strip fixing both ends are translations.** Let `φ` be a holomorphic
bijection of the strip `0 < z.im < 1` onto itself which sends the negative end `re z → -∞` of the
strip to the negative end and the positive end `re z → ∞` to the positive end. Then `φ` is a real
translation: `φ z = z + c` on the strip for some real `c`. -/
theorem exists_eqOn_add_of_bijOn_strip {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ {z | z.im ∈ Ioo 0 1})
    (hφS : BijOn φ {z | z.im ∈ Ioo 0 1} {z | z.im ∈ Ioo 0 1})
    (hbot : Tendsto φ (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (comap re atBot))
    (htop : Tendsto φ (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (comap re atTop)) :
    ∃ c : ℝ, EqOn φ (fun z => z + c) {z | z.im ∈ Ioo 0 1} := by
  set S := {z : ℂ | z.im ∈ Ioo 0 1}
  -- Conjugated to the disc, `φ` is `ζ ↦ u (ζ - a) / (1 - conj a ζ)`, which fixes `1` and `-1`
  -- since `φ` fixes the two ends; hence `u = 1` and `a` is real.
  obtain ⟨u, a, hfM⟩ := exists_eqOn_stripToDisc_comp hφ hφS
  have hend {l : Filter ℝ} (hl : Tendsto φ (comap re l ⊓ 𝓟 S) (comap re l)) :
      Tendsto φ (comap re l ⊓ 𝓟 S) (comap re l ⊓ 𝓟 S) :=
    hl.inf_principal_of_mapsTo hφS.mapsTo
  obtain ⟨hu, ha⟩ := coe_eq_one_and_conj_eq_of_tendsto hfM
    (tendsto_stripToDisc_atTop.comp ((hend htop).comp tendsto_discToStrip_one))
    (tendsto_stripToDisc_atBot.comp ((hend hbot).comp tendsto_discToStrip_neg_one))
  set r : ℝ := (a : ℂ).re
  have hr : ((r : ℝ) : ℂ) = a := conj_eq_iff_re.mp ha
  obtain ⟨hr₀, hr₁⟩ := abs_lt.mp ((abs_re_le_norm _).trans_lt a.norm_lt_one)
  -- `ζ ↦ (ζ - r) / (1 - r ζ)` is the conjugate of the translation by `log l / π`.
  set l : ℝ := (1 - r) / (1 + r)
  have hl : 0 < l := div_pos (by linarith) (by linarith)
  refine ⟨Real.log l / π, fun z hz => ?_⟩
  have hφz := hfM (stripToDisc_mem_ball hz)
  simp only [comp_apply, discToStrip_stripToDisc hz, hu, one_mul, ← hr, conj_ofReal] at hφz
  have hzc : z + ((Real.log l / π : ℝ) : ℂ) ∈ S := by simpa [S] using hz
  beta_reduce
  rw [← discToStrip_stripToDisc (hφS.mapsTo hz), hφz, ← discToStrip_stripToDisc hzc]
  congr 1
  have hexp : cexp (π * (z + ((Real.log l / π : ℝ) : ℂ))) = cexp (π * z) * l := by
    rw [mul_add, Complex.exp_add, ← ofReal_mul, mul_div_cancel₀ _ Real.pi_ne_zero,
      ← ofReal_exp, Real.exp_log hl]
  have him : 0 < (cexp (π * z)).im := bijOn_exp_pi_mul_strip.mapsTo hz
  rw [stripToDisc, stripToDisc, hexp]
  exact sub_ofReal_div_one_sub_ofReal_mul_sub_I_div_add_I him hr₀ hr₁

/-! ### Strip parametrizations of a domain -/

/-- If `v` is continuous on the closed strip, tends to `y` at the positive end and does not take
the value `x ≠ y` on the closed strip, then `v z` can only approach `x` as `z` runs to the
negative end of the strip. -/
private theorem tendsto_re_comap_inf_closedStrip_atBot {v : ℂ → ℂ} {x y : ℂ} (hxy : x ≠ y)
    (hvc : ContinuousOn v {z | z.im ∈ Icc 0 1})
    (hvy : Tendsto v (comap re atTop ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) (𝓝 y))
    (hx : x ∉ v '' {z | z.im ∈ Icc 0 1}) :
    Tendsto re (comap v (𝓝 x) ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) atBot := by
  set C := {z : ℂ | z.im ∈ Icc 0 1}
  have hδ : 0 < dist x y / 2 := half_pos (dist_pos.mpr hxy)
  -- Far out at the positive end, `v` is close to `y`, hence away from `x`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ C, M ≤ z.re → v z ∈ ball y (dist x y / 2) := by
    have h : v ⁻¹' ball y (dist x y / 2) ∈ comap re atTop ⊓ 𝓟 C := hvy (ball_mem_nhds y hδ)
    rw [mem_inf_principal] at h
    obtain ⟨t, ht, hts⟩ := mem_comap.mp h
    obtain ⟨M, hM⟩ := mem_atTop_sets.mp ht
    exact ⟨M, fun z hz hMz => hts (hM _ hMz) hz⟩
  refine tendsto_atBot.mpr fun R => ?_
  -- On the compact part `R ≤ re z ≤ M` of the closed strip, `v` stays away from `x`.
  have hK : IsCompact (Icc R M ×ℂ Icc 0 1) := isCompact_Icc.reProdIm isCompact_Icc
  have hKC : Icc R M ×ℂ Icc 0 1 ⊆ C := fun z hz => (mem_reProdIm.mp hz).2
  have hN : (v '' (Icc R M ×ℂ Icc 0 1))ᶜ ∩ ball x (dist x y / 2) ∈ 𝓝 x :=
    inter_mem ((hK.image_of_continuousOn (hvc.mono hKC)).isClosed.isOpen_compl.mem_nhds
      fun h => hx (image_mono hKC h)) (ball_mem_nhds x hδ)
  filter_upwards [mem_inf_of_left (preimage_mem_comap hN),
    mem_inf_of_right (mem_principal_self C)] with z hzN hzC
  by_contra hRz
  rw [not_le] at hRz
  rcases le_or_gt z.re M with hzM | hzM
  · exact hzN.1 ⟨z, mem_reProdIm.mpr ⟨⟨hRz.le, hzM⟩, hzC⟩, rfl⟩
  · have h₁ := hM z hzC hzM.le
    have h₂ := hzN.2
    rw [mem_ball] at h₁ h₂
    linarith [dist_triangle_left x y (v z)]

/-- The mirror image of `tendsto_re_comap_inf_closedStrip_atBot`: if `v` is continuous on the
closed strip, tends to `x` at the negative end and does not take the value `y ≠ x` on the closed
strip, then `v z` can only approach `y` as `z` runs to the positive end of the strip. -/
private theorem tendsto_re_comap_inf_closedStrip_atTop {v : ℂ → ℂ} {x y : ℂ} (hxy : x ≠ y)
    (hvc : ContinuousOn v {z | z.im ∈ Icc 0 1})
    (hvx : Tendsto v (comap re atBot ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) (𝓝 x))
    (hy : y ∉ v '' {z | z.im ∈ Icc 0 1}) :
    Tendsto re (comap v (𝓝 y) ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) atTop := by
  set C := {z : ℂ | z.im ∈ Icc 0 1}
  -- Reflect the strip in the imaginary axis, exchanging its two ends.
  set ρ : ℂ → ℂ := fun z => -conj z
  have hρC : MapsTo ρ C C := fun z hz => by simpa [ρ, C] using hz
  have hρρ (z : ℂ) : ρ (ρ z) = z := by simp [ρ]
  have hρre (z : ℂ) : (ρ z).re = -z.re := by simp [ρ]
  have hρend : Tendsto ρ (comap re atTop ⊓ 𝓟 C) (comap re atBot ⊓ 𝓟 C) :=
    Tendsto.inf_principal_of_mapsTo (tendsto_comap_iff.mpr (by
        simpa [comp_def, hρre] using (tendsto_neg_atTop_atBot (G := ℝ)).comp
          (tendsto_comap.mono_left inf_le_left))) hρC
  have h := tendsto_re_comap_inf_closedStrip_atBot hxy.symm
    (hvc.comp (continuous_conj.neg.continuousOn) hρC) (hvx.comp hρend)
    fun ⟨z, hz, hvz⟩ => hy ⟨ρ z, hρC hz, hvz⟩
  have hmap : Tendsto ρ (comap v (𝓝 y) ⊓ 𝓟 C) (comap (v ∘ ρ) (𝓝 y) ⊓ 𝓟 C) :=
    Tendsto.inf_principal_of_mapsTo (tendsto_comap_iff.mpr (by
        simpa [comp_def, hρρ] using
          (tendsto_comap (f := v) (x := 𝓝 y)).mono_left inf_le_left)) hρC
  simpa [comp_def, hρre] using tendsto_neg_atBot_atTop.comp (h.comp hmap)

/-- **Strip parametrizations of a domain are unique up to translation.** Let `u` and `v` be
holomorphic bijections of the open strip `0 < z.im < 1` onto a set `Ω`, continuous on the closed
strip, which both tend to `x` as `re z → -∞` and to `y ≠ x` as `re z → ∞`, the limits of `v` being
taken along the closed strip. If `v` does not take the values `x` and `y` on the closed strip,
then `u` and `v` differ by a real translation on the closed strip. -/
theorem exists_eqOn_add_of_bijOn_of_notMem_image {Ω : Set ℂ} {u v : ℂ → ℂ}
    (huc : ContinuousOn u {z | z.im ∈ Icc 0 1}) (hvc : ContinuousOn v {z | z.im ∈ Icc 0 1})
    (hu : DifferentiableOn ℂ u {z | z.im ∈ Ioo 0 1})
    (hv : DifferentiableOn ℂ v {z | z.im ∈ Ioo 0 1}) (huΩ : BijOn u {z | z.im ∈ Ioo 0 1} Ω)
    (hvΩ : BijOn v {z | z.im ∈ Ioo 0 1} Ω) {x y : ℂ} (hxy : x ≠ y)
    (hux : Tendsto u (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (huy : Tendsto u (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y))
    (hvx : Tendsto v (comap re atBot ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) (𝓝 x))
    (hvy : Tendsto v (comap re atTop ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) (𝓝 y))
    (hx : x ∉ v '' {z | z.im ∈ Icc 0 1}) (hy : y ∉ v '' {z | z.im ∈ Icc 0 1}) :
    ∃ c : ℝ, EqOn u (fun z => v (z + c)) {z | z.im ∈ Icc 0 1} := by
  set S := {z : ℂ | z.im ∈ Ioo 0 1}
  set C := {z : ℂ | z.im ∈ Icc 0 1}
  have hSC : S ⊆ C := fun z hz => Ioo_subset_Icc_self hz
  have hSo : IsOpen S := isOpen_Ioo.preimage continuous_im
  -- `φ = v⁻¹ ∘ u` is a holomorphic automorphism of the strip.
  set w := invFunOn v S
  have hvinv : InvOn w v S Ω := hvΩ.invOn_invFunOn
  have hw : DifferentiableOn ℂ w Ω := by simpa [hvΩ.image_eq] using hv.invFunOn hSo hvΩ.injOn
  set φ := w ∘ u
  have hφ : DifferentiableOn ℂ φ S := hw.comp hu huΩ.mapsTo
  have hφS : BijOn φ S S := (hvΩ.symm hvinv.symm).comp huΩ
  have hvφ (z : ℂ) (hz : z ∈ S) : v (φ z) = u z := hvinv.2 (huΩ.mapsTo hz)
  -- It fixes both ends, since `v (φ z) = u z` tends to `x` or `y` there.
  have hend (l : Filter ℝ) (p : ℂ) (hup : Tendsto u (comap re l ⊓ 𝓟 S) (𝓝 p)) :
      Tendsto φ (comap re l ⊓ 𝓟 S) (comap v (𝓝 p) ⊓ 𝓟 C) :=
    Tendsto.inf_principal_of_mapsTo (tendsto_comap_iff.mpr (hup.congr'
      (eventually_inf_principal.mpr (Eventually.of_forall fun z hz => (hvφ z hz).symm))))
      fun z hz => hSC (hφS.mapsTo hz)
  obtain ⟨c, hc⟩ := exists_eqOn_add_of_bijOn_strip hφ hφS
    (tendsto_comap_iff.mpr ((tendsto_re_comap_inf_closedStrip_atBot hxy hvc hvy hx).comp
      (hend atBot x hux)))
    (tendsto_comap_iff.mpr ((tendsto_re_comap_inf_closedStrip_atTop hxy hvc hvx hy).comp
      (hend atTop y huy)))
  -- Both sides are continuous on the closed strip, the closure of the open strip.
  exact ⟨c, eqOn_add_closedStrip_of_eqOn_strip huc hvc fun z hz => by rw [← hvφ z hz, hc hz]⟩

end TauCeti
