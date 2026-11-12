/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.Analysis.Distribution.DuBoisReymond

/-!
# Hopf's boundary-point lemma for weak supersolutions on an interval

On an interval `(x₀, x₁)` consider the one-dimensional operator in divergence form

`L u = (a u' + b u)' + c u' + d u`

with measurable coefficients, `a` bounded between two positive constants, `b` and `c` bounded and
`d` integrable. A function `u`, absolutely continuous on `[x₀, x₁]` (the continuous representative
of a `W^{1,1}(x₀, x₁)` class), is a **weak supersolution**, `L u ≤ 0`, if

`∫ φ (c u' + d u) ≤ ∫ φ' (a u' + b u)`

for every nonnegative smooth `φ` compactly supported in `(x₀, x₁)`. This file proves **Hopf's
boundary-point lemma** for such `u`: if `u` vanishes at the boundary point `x₀` and is positive
inside, then it leaves `x₀` at a positive linear rate, `ε t ≤ u (x₀ + t)` for some `ε > 0` and all
small `t > 0`. In particular a right derivative of `u` at `x₀`, if it exists, is positive.

Since `u (x₀) = 0`, no sign condition on the zeroth-order coefficients `b` and `d` is needed, and
in one dimension the principal coefficient needs no continuity. In higher dimensions bounded
measurable principal coefficients do not suffice: there the divergence-form Hopf lemma assumes
Hölder continuous principal coefficients.

## The proof

The flux `F = a u' + b u` satisfies `F' + g ≤ 0` in the sense of distributions, where
`g = c u' + d u` is integrable. Hence the corrected flux
`H x = F x + ∫ t in x₀..x, g t` is antitone on a subset `S` of full measure
(`MeasureTheory.LocallyIntegrableOn.exists_antitoneOn_add_intervalIntegral_of_integral_mul_le`).

* If `H x₂ > 0` at some `x₂ ∈ S`, then `H ≥ H x₂` on `S` to the left of `x₂`. Near `x₀` both `u`
  and `∫ g` are small, so `a u' = H - b u - ∫ g ≥ H x₂ / 2` there, and `u' ≥ H x₂ / (2 Λ)` almost
  everywhere near `x₀`. Integrating gives the linear lower bound.
* Otherwise `a u' ≤ -b u - ∫ g` almost everywhere. With `Q x = ∫ t in x₀..x, |u'|`, both `|u|` and
  `|∫ g|` are at most constant multiples of `Q`, so `u' ≤ K Q` almost everywhere. Integrating
  `|u'| ≤ 2 K Q x - u'` over `(x₀, x)` gives `Q x + u x ≤ 2 K (x - x₀) Q x`, so `u x ≤ 0` for `x`
  close to `x₀`, contradicting the positivity of `u`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_of_integral_mul_le_integral_deriv_mul`: **Hopf's lemma** for
  one-dimensional weak supersolutions, the difference quotients `u (x₀ + t) / t` are bounded below
  by a positive constant.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_integral_mul_le_integral_deriv_mul`: the derivative
  form, a right derivative at `x₀` is positive.

## References

* C. Rosales, *Generalizing Hopf's boundary point lemma*, arXiv:1806.07003.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4, for the classical lemma.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace TauCeti

namespace PDE

variable {x₀ x₁ : ℝ} {u : ℝ → ℝ}

/-- An absolutely continuous function vanishing at `x₀` is the primitive of its derivative. -/
private lemma eq_intervalIntegral_deriv (hu : AbsolutelyContinuousOnInterval u x₀ x₁)
    (hu₀ : u x₀ = 0) {x : ℝ} (hx : x ∈ uIcc x₀ x₁) : u x = ∫ t in x₀..x, deriv u t := by
  rw [(hu.mono (uIcc_subset_uIcc left_mem_uIcc hx)).integral_deriv_eq_sub, hu₀, sub_zero]

/-- An absolutely continuous function vanishing at `x₀` is bounded by the integral of `|u'|`. -/
private lemma abs_le_intervalIntegral_abs_deriv (hu : AbsolutelyContinuousOnInterval u x₀ x₁)
    (hu₀ : u x₀ = 0) {x : ℝ} (hx : x ∈ Icc x₀ x₁) : |u x| ≤ ∫ t in x₀..x, |deriv u t| := by
  rw [eq_intervalIntegral_deriv hu hu₀ (Icc_subset_uIcc hx)]
  exact intervalIntegral.abs_integral_le_integral_abs hx.1

/-- The bound `|∫ t in x₀..x, (c u' + d u)| ≤ (γ + ∫ |d|) ∫ t in x₀..x, |u'|` for `|c| ≤ γ`. -/
private lemma abs_intervalIntegral_mul_deriv_add_mul_le {c d : ℝ → ℝ} {γ : ℝ}
    (hu : AbsolutelyContinuousOnInterval u x₀ x₁) (hu₀ : u x₀ = 0)
    (hc : ∀ x ∈ Ioo x₀ x₁, |c x| ≤ γ) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hg : IntegrableOn (fun x ↦ c x * deriv u x + d x * u x) (Ioo x₀ x₁)) {x : ℝ}
    (hx : x ∈ Ioo x₀ x₁) :
    |∫ t in x₀..x, (c t * deriv u t + d t * u t)| ≤
      (γ + ∫ t in x₀..x₁, |d t|) * ∫ t in x₀..x, |deriv u t| := by
  have hx₀x : x₀ ≤ x := hx.1.le
  have hx₀x₁ : x₀ ≤ x₁ := hx.1.le.trans hx.2.le
  have hint {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo x₀ x₁)) : IntervalIntegrable f volume x₀ x :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀x).2
      (hf.mono_set (Ioo_subset_Ioo_right hx.2.le))
  have hw : IntervalIntegrable (deriv u) volume x₀ x :=
    (hu.mono (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc (Ioo_subset_Icc_self hx))))
      |>.intervalIntegrable_deriv
  set Q := ∫ t in x₀..x, |deriv u t|
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hx₀x fun _ _ ↦ abs_nonneg _
  -- `|u| ≤ Q` on `[x₀, x]`.
  have hu_le (s : ℝ) (hs : s ∈ Ioc x₀ x) : |u s| ≤ Q :=
    (abs_le_intervalIntegral_abs_deriv hu hu₀ ⟨hs.1.le, hs.2.trans hx.2.le⟩).trans
      (intervalIntegral.integral_mono_interval le_rfl hs.1.le hs.2
        (Eventually.of_forall fun _ ↦ abs_nonneg _) hw.abs)
  have hdx : ∫ t in x₀..x, |d t| ≤ ∫ t in x₀..x₁, |d t| :=
    intervalIntegral.integral_mono_interval le_rfl hx₀x hx.2.le
      (Eventually.of_forall fun _ ↦ abs_nonneg _)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀x₁).2 hd).abs
  calc |∫ t in x₀..x, (c t * deriv u t + d t * u t)|
      ≤ ∫ t in x₀..x, |c t * deriv u t + d t * u t| :=
        intervalIntegral.abs_integral_le_integral_abs hx₀x
    _ ≤ ∫ t in x₀..x, (γ * |deriv u t| + |d t| * Q) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hx₀x (hint hg).abs
          ((hw.abs.const_mul γ).add ((hint hd).abs.mul_const Q)) fun s hs ↦ ?_
        have hs₁ := hs.1
        have hsI : s ∈ Ioo x₀ x₁ := ⟨hs₁, hs.2.trans hx.2⟩
        calc |c s * deriv u s + d s * u s| ≤ |c s| * |deriv u s| + |d s| * |u s| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ γ * |deriv u s| + |d s| * Q := by
              gcongr
              · exact hc s hsI
              · exact hu_le s ⟨hs₁, hs.2.le⟩
    _ = γ * Q + (∫ t in x₀..x, |d t|) * Q := by
        rw [intervalIntegral.integral_add (hw.abs.const_mul γ) ((hint hd).abs.mul_const Q),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    _ ≤ (γ + ∫ t in x₀..x₁, |d t|) * Q := by nlinarith

/-- The case of a positive corrected flux: if `H = a u' + b u + G` is antitone on a subset `S` of
full measure and positive at a point of `S`, and `u` and `G` vanish at `x₀` and are continuous
there, then `u` grows at least linearly from `x₀`. -/
private lemma exists_pos_mul_le_of_antitoneOn {a b G : ℝ → ℝ} {S : Set ℝ} {Λ β : ℝ}
    (hu : AbsolutelyContinuousOnInterval u x₀ x₁) (hx : x₀ < x₁) (hu₀ : u x₀ = 0)
    (ha : ∀ x ∈ Ioo x₀ x₁, 0 < a x) (ha' : ∀ x ∈ Ioo x₀ x₁, a x ≤ Λ)
    (hb : ∀ x ∈ Ioo x₀ x₁, |b x| ≤ β) (hG : ContinuousWithinAt G (Icc x₀ x₁) x₀) (hG₀ : G x₀ = 0)
    (hS : S ⊆ Ioo x₀ x₁) (hSnull : volume (Ioo x₀ x₁ \ S) = 0)
    (hanti : AntitoneOn (fun x ↦ a x * deriv u x + b x * u x + G x) S) {x₂ : ℝ} (hx₂ : x₂ ∈ S)
    (hpos : 0 < a x₂ * deriv u x₂ + b x₂ * u x₂ + G x₂) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (x₀ + t) := by
  set m := (a x₂ * deriv u x₂ + b x₂ * u x₂ + G x₂) / 2 with hm_def
  have hm : 0 < m := half_pos hpos
  have hx₂I := hS hx₂
  have hΛ : 0 < Λ := (ha x₂ hx₂I).trans_le (ha' x₂ hx₂I)
  -- Near `x₀`, `β |u| + |G| < m`.
  have hcont : ContinuousWithinAt (fun x ↦ β * |u x| + |G x|) (Icc x₀ x₁) x₀ := by
    have huc : ContinuousWithinAt u (Icc x₀ x₁) x₀ :=
      (uIcc_of_le hx.le ▸ hu.continuousOn) x₀ (left_mem_Icc.2 hx.le)
    exact (huc.abs.const_mul β).add hG.abs
  obtain ⟨δ₀, hδ₀, hsmall⟩ := Metric.continuousWithinAt_iff.1 hcont m hm
  set δ := min (δ₀ / 2) (x₂ - x₀)
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (sub_pos.2 hx₂I.1)
  -- Almost every point of `(x₀, x₀ + δ]` lies in `S`, where `u' ≥ m / Λ`.
  have hae : ∀ᵐ t, t ∈ Ioo x₀ x₁ → t ∈ S := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hSnull] with t ht htI
    by_contra htS
    exact ht ⟨htI, htS⟩
  have hderiv : ∀ᵐ t, t ∈ Ioc x₀ (x₀ + δ) → m / Λ ≤ deriv u t := by
    filter_upwards [hae] with t ht htmem
    have hδx₂ : δ ≤ x₂ - x₀ := min_le_right _ _
    have htI : t ∈ Ioo x₀ x₁ := ⟨htmem.1, by linarith [htmem.2, hx₂I.2]⟩
    have htS := ht htI
    have hH := hanti htS hx₂ (by linarith [htmem.2])
    simp only at hH
    have hdist : dist t x₀ < δ₀ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 htmem.1)]
      linarith [min_le_left (δ₀ / 2) (x₂ - x₀), htmem.2]
    have hlt := hsmall (Ioo_subset_Icc_self htI) hdist
    simp only [Real.dist_eq, hu₀, hG₀, abs_zero, mul_zero, add_zero, sub_zero] at hlt
    replace hlt := (abs_lt.1 hlt).2
    have hbu : |b t * u t| ≤ β * |u t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb t htI) (abs_nonneg _)
    have hau : m < a t * deriv u t := by
      linarith [le_abs_self (b t * u t), le_abs_self (G t)]
    have hat := ha t htI
    have hw : 0 < deriv u t := pos_of_mul_pos_right (hm.trans hau) hat.le
    rw [div_le_iff₀ hΛ]
    nlinarith [ha' t htI, hw]
  refine ⟨m / Λ, div_pos hm hΛ, δ, hδ, fun t ht ↦ ?_⟩
  have hxt : x₀ + t ∈ Icc x₀ x₁ :=
    ⟨by linarith [ht.1], by linarith [ht.2, min_le_right (δ₀ / 2) (x₂ - x₀), hx₂I.2]⟩
  rw [eq_intervalIntegral_deriv hu hu₀ (Icc_subset_uIcc hxt)]
  have hle : ∫ _ in x₀..x₀ + t, m / Λ ≤ ∫ s in x₀..x₀ + t, deriv u s := by
    refine intervalIntegral.integral_mono_ae_restrict (by linarith [ht.1]) intervalIntegrable_const
      (hu.mono (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hxt))).intervalIntegrable_deriv
      ((ae_restrict_iff' measurableSet_Icc).2 ?_)
    filter_upwards [hderiv, Measure.ae_ne volume x₀] with s hs hs₀ hsmem
    exact hs ⟨lt_of_le_of_ne hsmem.1 hs₀.symm, by linarith [hsmem.2, ht.2]⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hle
  linarith

/-- The case of a nonpositive corrected flux: if `u' ≤ K ∫ t in x₀..x, |u'|` almost everywhere,
then `u x ≤ 0` as long as `2 K (x - x₀) ≤ 1`. -/
private lemma le_zero_of_deriv_le_mul_intervalIntegral_abs_deriv {K : ℝ}
    (hu : AbsolutelyContinuousOnInterval u x₀ x₁) (hu₀ : u x₀ = 0) (hK : 0 ≤ K)
    (h : ∀ᵐ t, t ∈ Ioo x₀ x₁ → deriv u t ≤ K * ∫ s in x₀..t, |deriv u s|) {x : ℝ}
    (hx : x ∈ Ioo x₀ x₁) (hsmall : 2 * K * (x - x₀) ≤ 1) : u x ≤ 0 := by
  have hx₀x : x₀ ≤ x := hx.1.le
  have hw : IntervalIntegrable (deriv u) volume x₀ x :=
    (hu.mono (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc (Ioo_subset_Icc_self hx))))
      |>.intervalIntegrable_deriv
  set Q := ∫ t in x₀..x, |deriv u t| with hQ_def
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hx₀x fun _ _ ↦ abs_nonneg _
  -- Pointwise, `|u'| ≤ 2 K Q - u'` almost everywhere on `(x₀, x]`.
  have hpt : ∀ᵐ t, t ∈ Ioc x₀ x → |deriv u t| ≤ 2 * K * Q - deriv u t := by
    filter_upwards [h] with t ht htmem
    have hQt : ∫ s in x₀..t, |deriv u s| ≤ Q :=
      intervalIntegral.integral_mono_interval le_rfl htmem.1.le htmem.2
        (Eventually.of_forall fun _ ↦ abs_nonneg _) hw.abs
    have hdt := ht ⟨htmem.1, htmem.2.trans_lt hx.2⟩
    rcases le_or_gt 0 (deriv u t) with hnn | hneg
    · rw [abs_of_nonneg hnn]
      nlinarith [mul_le_mul_of_nonneg_left hQt hK]
    · rw [abs_of_neg hneg]
      nlinarith [mul_nonneg hK hQ]
  have hint := intervalIntegral.integral_mono_ae_restrict hx₀x hw.abs
    (intervalIntegrable_const.sub hw) <| (ae_restrict_iff' measurableSet_Icc).2 <| by
      filter_upwards [hpt, Measure.ae_ne volume x₀] with t ht ht₀ htmem
      exact ht ⟨lt_of_le_of_ne htmem.1 ht₀.symm, htmem.2⟩
  rw [intervalIntegral.integral_sub intervalIntegrable_const hw, intervalIntegral.integral_const,
    smul_eq_mul, ← eq_intervalIntegral_deriv hu hu₀ (Icc_subset_uIcc (Ioo_subset_Icc_self hx)),
    ← hQ_def] at hint
  nlinarith [mul_le_mul_of_nonneg_right hsmall hQ]

/-- **Hopf's boundary-point lemma for one-dimensional weak supersolutions.** Let `u` be absolutely
continuous on `[x₀, x₁]` and a weak supersolution of `(a u' + b u)' + c u' + d u ≤ 0` on
`(x₀, x₁)`:

`∫ φ (c u' + d u) ≤ ∫ φ' (a u' + b u)`

for every nonnegative smooth `φ` with `tsupport φ ⊆ (x₀, x₁)`, where `a`, `b`, `c` are measurable
with `0 < λ ≤ a ≤ Λ`, `|b| ≤ β` and `|c| ≤ γ`, and `d` is integrable. If `u x₀ = 0` and `u > 0`
on `(x₀, x₁)`, then `ε t ≤ u (x₀ + t)` for some `ε > 0` and all small `t > 0`. -/
theorem exists_pos_mul_le_of_integral_mul_le_integral_deriv_mul {a b c d : ℝ → ℝ}
    {lam Λ β γ : ℝ} (hx : x₀ < x₁) (hu : AbsolutelyContinuousOnInterval u x₀ x₁)
    (ha_meas : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb_meas : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc_meas : AEStronglyMeasurable c (volume.restrict (Ioo x₀ x₁)))
    (hlam : 0 < lam) (ha : ∀ x ∈ Ioo x₀ x₁, lam ≤ a x) (ha' : ∀ x ∈ Ioo x₀ x₁, a x ≤ Λ)
    (hb : ∀ x ∈ Ioo x₀ x₁, |b x| ≤ β) (hc : ∀ x ∈ Ioo x₀ x₁, |c x| ≤ γ)
    (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ φ x) →
      ∫ x, φ x * (c x * deriv u x + d x * u x) ≤ ∫ x, deriv φ x * (a x * deriv u x + b x * u x))
    (hu₀ : u x₀ = 0) (hpos : ∀ x ∈ Ioo x₀ x₁, 0 < u x) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (x₀ + t) := by
  -- Integrability of `u'`, `u`, the flux `F = a u' + b u` and `g = c u' + d u`.
  have hwi : IntervalIntegrable (deriv u) volume x₀ x₁ := hu.intervalIntegrable_deriv
  have hwI : IntegrableOn (deriv u) (Ioo x₀ x₁) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).1 hwi
  have huc : ContinuousOn u (Icc x₀ x₁) := uIcc_of_le hx.le ▸ hu.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  have huI : IntegrableOn u (Ioo x₀ x₁) :=
    (huc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hbound {f : ℝ → ℝ} {C : ℝ} (h : ∀ x ∈ Ioo x₀ x₁, |f x| ≤ C) :
      ∀ᵐ x ∂(volume.restrict (Ioo x₀ x₁)), ‖f x‖ ≤ C :=
    ae_restrict_of_forall_mem measurableSet_Ioo h
  have hapos (x : ℝ) (hx : x ∈ Ioo x₀ x₁) : 0 < a x := hlam.trans_le (ha x hx)
  have hFI : IntegrableOn (fun x ↦ a x * deriv u x + b x * u x) (Ioo x₀ x₁) :=
    (hwI.bdd_mul ha_meas (hbound fun x hx ↦ (abs_of_pos (hapos x hx)).trans_le (ha' x hx))).add
      (huI.bdd_mul hb_meas (hbound hb))
  have hgI : IntegrableOn (fun x ↦ c x * deriv u x + d x * u x) (Ioo x₀ x₁) :=
    (hwI.bdd_mul hc_meas (hbound hc)).add
      (hd.mul_bdd huI.aestronglyMeasurable (hbound fun x hx ↦ hM x (Ioo_subset_Icc_self hx)))
  -- The corrected flux `H = F + ∫ g` is antitone on a subset `S` of full measure.
  obtain ⟨S, hS, hSnull, hanti⟩ :=
    LocallyIntegrableOn.exists_antitoneOn_add_intervalIntegral_of_integral_mul_le
      hFI.locallyIntegrableOn hgI hsuper
  set G : ℝ → ℝ := fun x ↦ ∫ t in x₀..x, (c t * deriv u t + d t * u t)
  have hmid : (x₀ + x₁) / 2 ∈ Ioo x₀ x₁ := ⟨by linarith, by linarith⟩
  by_cases hcase : ∃ x₂ ∈ S, 0 < a x₂ * deriv u x₂ + b x₂ * u x₂ + G x₂
  · obtain ⟨x₂, hx₂, hpos₂⟩ := hcase
    have hG : ContinuousWithinAt G (Icc x₀ x₁) x₀ := by
      have hgi : IntervalIntegrable (fun x ↦ c x * deriv u x + d x * u x) volume x₀ x₁ :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 hgI
      exact (uIcc_of_le hx.le ▸ intervalIntegral.continuousOn_primitive_interval' hgi
        left_mem_uIcc) x₀ (left_mem_Icc.2 hx.le)
    exact exists_pos_mul_le_of_antitoneOn hu hx hu₀ hapos ha' hb hG
      intervalIntegral.integral_same hS hSnull hanti hx₂ hpos₂
  -- Otherwise `a u' ≤ -b u - ∫ g` almost everywhere, which forces `u` to vanish near `x₀`.
  push Not at hcase
  exfalso
  set D := ∫ t in x₀..x₁, |d t|
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg hx.le fun _ _ ↦ abs_nonneg _
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb _ hmid)
  have hγ : 0 ≤ γ := (abs_nonneg _).trans (hc _ hmid)
  set K := (β + γ + D) / lam with hK_def
  have hK : 0 ≤ K := by positivity
  have hderiv : ∀ᵐ t, t ∈ Ioo x₀ x₁ → deriv u t ≤ K * ∫ s in x₀..t, |deriv u s| := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hSnull] with t ht htI
    have htS : t ∈ S := by
      by_contra htS
      exact ht ⟨htI, htS⟩
    have hH := hcase t htS
    set Q := ∫ s in x₀..t, |deriv u s|
    have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg htI.1.le fun _ _ ↦ abs_nonneg _
    have hut : |u t| ≤ Q := abs_le_intervalIntegral_abs_deriv hu hu₀ (Ioo_subset_Icc_self htI)
    have hGt : |G t| ≤ (γ + D) * Q :=
      abs_intervalIntegral_mul_deriv_add_mul_le hu hu₀ hc hd hgI htI
    have hbu : |b t * u t| ≤ β * Q := by
      rw [abs_mul]; exact mul_le_mul (hb t htI) hut (abs_nonneg _) hβ
    have hau : a t * deriv u t ≤ (β + γ + D) * Q := by
      linarith [le_abs_self (b t * u t), le_abs_self (G t), neg_abs_le (b t * u t),
        neg_abs_le (G t)]
    rcases le_or_gt (deriv u t) 0 with hnp | hpos'
    · exact hnp.trans (mul_nonneg hK hQ)
    · rw [hK_def, div_mul_eq_mul_div, le_div_iff₀ hlam]
      nlinarith [ha t htI]
  -- Take `x` so close to `x₀` that `2 K (x - x₀) ≤ 1`.
  set ρ := min ((x₁ - x₀) / 2) (1 / (2 * K + 2))
  have hρ : 0 < ρ := lt_min (by linarith) (by positivity)
  have hxI : x₀ + ρ ∈ Ioo x₀ x₁ :=
    ⟨by linarith, by linarith [min_le_left ((x₁ - x₀) / 2) (1 / (2 * K + 2))]⟩
  have hsmall : 2 * K * (x₀ + ρ - x₀) ≤ 1 := by
    rw [add_sub_cancel_left]
    have h1 : ρ ≤ 1 / (2 * K + 2) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  linarith [le_zero_of_deriv_le_mul_intervalIntegral_abs_deriv hu hu₀ hK hderiv hxI hsmall,
    hpos _ hxI]

/-- **Hopf's boundary-point lemma for one-dimensional weak supersolutions, derivative form.** Under
the hypotheses of `TauCeti.PDE.exists_pos_mul_le_of_integral_mul_le_integral_deriv_mul`, a right
derivative of `u` at the boundary point `x₀`, if it exists, is positive. -/
theorem pos_of_hasDerivWithinAt_of_integral_mul_le_integral_deriv_mul {a b c d : ℝ → ℝ}
    {lam Λ β γ : ℝ} (hx : x₀ < x₁) (hu : AbsolutelyContinuousOnInterval u x₀ x₁)
    (ha_meas : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb_meas : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc_meas : AEStronglyMeasurable c (volume.restrict (Ioo x₀ x₁)))
    (hlam : 0 < lam) (ha : ∀ x ∈ Ioo x₀ x₁, lam ≤ a x) (ha' : ∀ x ∈ Ioo x₀ x₁, a x ≤ Λ)
    (hb : ∀ x ∈ Ioo x₀ x₁, |b x| ≤ β) (hc : ∀ x ∈ Ioo x₀ x₁, |c x| ≤ γ)
    (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ φ x) →
      ∫ x, φ x * (c x * deriv u x + d x * u x) ≤ ∫ x, deriv φ x * (a x * deriv u x + b x * u x))
    (hu₀ : u x₀ = 0) (hpos : ∀ x ∈ Ioo x₀ x₁, 0 < u x) {u' : ℝ}
    (hderiv : HasDerivWithinAt u u' (Ici x₀) x₀) :
    0 < u' := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_of_integral_mul_le_integral_deriv_mul hx hu
    ha_meas hb_meas hc_meas hlam ha ha' hb hc hd hsuper hu₀ hpos
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  rw [Ici_sdiff_left] at hslope
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  filter_upwards [Ioo_mem_nhdsGT (show x₀ < x₀ + δ by linarith)] with y hy
  have hy' := h (y - x₀) ⟨sub_pos.2 hy.1, by linarith [hy.2]⟩
  rw [add_sub_cancel] at hy'
  rw [slope_def_field, hu₀, sub_zero, le_div_iff₀ (sub_pos.2 hy.1)]
  exact hy'

end PDE

end TauCeti
