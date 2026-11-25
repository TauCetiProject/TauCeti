/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.ODE.Gronwall
import TauCeti.Algebra.Order.GroupWithZero.Basic
import TauCeti.Analysis.SpecialFunctions.Log.TwoAdd
import TauCeti.NumberTheory.LSeries.Moebius
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogUpperBound

/-!
# The zero-free strip of `ζ` with logarithmic bounds

Write `L = log (|Im s| + 2)`. There are `0 < β < 1` and `C > 0` such that on the region
`Z = {s | 1 - β / L ≤ Re s}`, `ζ` has no zero away from `1`, the reciprocal `R = 1/ζ`, extended
by `R(1) = 0`, is analytic on a neighbourhood of `Z`, and both `G = ζ - 1/(s - 1)` and `R` are
at most `C L` in norm. The region has no upper limit on `Re s`, so it contains every strip
`1 - β / L ≤ Re s ≤ σ₁`.

The extensions are Mathlib's entire functions: `riemannZeta₀`, equal to `ζ(s) - 1/(s - 1)` for
`s ≠ 1` (`riemannZeta_eq_inv_sub_add`), and `riemannZeta₁`, equal to `(s - 1) ζ(s)` for `s ≠ 1`
and to `1` at `1`. The extension of `1/ζ` is `R(s) = (s - 1) / riemannZeta₁ s`, which equals
`(ζ s)⁻¹` for `s ≠ 1` (`TauCeti.sub_one_div_riemannZeta₁`) and vanishes at `1`.

## Main results

* `TauCeti.norm_riemannZeta_inv_lt_one_add_one_div_sub_one`: `‖ζ(s)‖⁻¹ < 1 + 1/(Re s - 1)` on
  `1 < Re s`.
* `TauCeti.sub_one_div_riemannZeta₁`: `(s - 1) / riemannZeta₁ s = (ζ s)⁻¹` for `s ≠ 1`.
* `TauCeti.riemannZeta_zeroFreeStrip_bounds`: nonvanishing, analyticity of `R` on a
  neighbourhood of `Z`, and `‖G s‖, ‖R s‖ ≤ C L` on `Z`.

## Implementation notes

The bound for `G` is `TauCeti.exists_norm_riemannZeta₀_le_mul_log`. For `R` put
`s₁ = 1 + 1/L + i Im s`. Right of `Re s = 1 + 1/L` the Möbius series gives `‖R s‖ ≤ 1 + L`.
At height `|Im s| ≥ 1` and left of that line, the bound `‖ζ′/ζ + 1/(s - 1)‖ ≤ C L` of
`TauCeti.riemannZeta_deriv_logDeriv_bound` gives `‖ζ′/ζ‖ = O(L)` on the horizontal segment from `s`
to `s₁`, whose length is at most `2/L`. Grönwall's inequality along the segment bounds
`‖ζ(s₁)‖ / ‖ζ(s)‖` by an absolute constant, so `‖R s‖ ≤ e^O(1) ‖R s₁‖ = O(L)`. This uses the
logarithmic bound for `ζ′/ζ` rather than a bound for `ζ′`, which would only give `log³`. Below
height `1` the remaining part of `Z` is compact and `R` is continuous on it.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 6.7 and its corollaries.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §3.11.
* `ZetaUpperBnd`, `ZetaInvBnd` and `ZetaLowerBnd` in A. Kontorovich, T. Tao et al.,
  *PrimeNumberTheoremAnd*, file `PrimeNumberTheoremAnd/ZetaBounds.lean`, which bound `ζ` and
  `1/ζ` for `3 < |Im s|` on the narrower region `1 - A / log⁹ |Im s| ≤ Re s`, with the weaker
  bound `‖1/ζ‖ ≪ log⁷ |Im s|`.
-/

public section

open Complex

namespace TauCeti

/-- On `1 < Re s`, the Möbius series bounds `1/ζ`: `‖ζ(s)‖⁻¹ < 1 + 1/(Re s - 1)`. -/
theorem norm_riemannZeta_inv_lt_one_add_one_div_sub_one {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖⁻¹ < 1 + 1 / (s.re - 1) := by
  have h := inv_norm_riemannZeta_le_norm_riemannZeta_re_div hs
  have h2 : 1 ≤ ‖riemannZeta (2 * s.re)‖ := by
    have := one_lt_riemannZeta_re (by linarith : 1 < 2 * s.re)
    push_cast at this
    exact this.le.trans (re_le_norm _)
  have hσ := norm_riemannZeta_lt_one_add_one_div_sub_one (s := (s.re : ℂ)) (by simpa using hs)
  rw [ofReal_re] at hσ
  rw [norm_div] at h
  exact h.trans_lt ((div_le_self (norm_nonneg _) h2).trans_lt hσ)

/-- Mathlib's entire `riemannZeta₁`, the completion of `(s - 1) ζ(s)`, gives the extension
`(s - 1) / riemannZeta₁ s` of `1/ζ` across `1`. -/
theorem sub_one_div_riemannZeta₁ {s : ℂ} (hs : s ≠ 1) :
    (s - 1) / riemannZeta₁ s = (riemannZeta s)⁻¹ := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv, inv_inv, div_eq_mul_inv]

/-- **Grönwall along a segment.** If `f` is complex differentiable on the segment `[a, b]` and
`‖f′‖ ≤ K ‖f‖` there, then `‖f b‖ ≤ ‖f a‖ exp (K ‖b - a‖)`. -/
private lemma norm_le_norm_mul_exp_of_norm_deriv_le {f : ℂ → ℂ} {a b : ℂ} {K : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, DifferentiableAt ℂ f z)
    (hK : ∀ z ∈ segment ℝ a b, ‖deriv f z‖ ≤ K * ‖f z‖) :
    ‖f b‖ ≤ ‖f a‖ * Real.exp (K * ‖b - a‖) := by
  set p : ℝ → ℂ := fun θ ↦ a + θ • (b - a)
  have hp : ∀ θ ∈ Set.Icc (0 : ℝ) 1, p θ ∈ segment ℝ a b := fun θ hθ ↦ by
    rw [segment_eq_image']
    exact ⟨θ, hθ, rfl⟩
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (f ∘ p) (deriv f (p θ) * (b - a)) θ := by
    intro θ hθ
    have hpd : HasDerivAt p (b - a) θ := by
      simpa [p] using ((hasDerivAt_id θ).smul_const (b - a)).const_add a
    exact (hf _ (hp θ hθ)).hasDerivAt.comp θ hpd
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := f ∘ p)
    (f' := fun θ ↦ deriv f (p θ) * (b - a)) (δ := ‖f a‖) (K := K * ‖b - a‖) (ε := 0)
    (fun θ hθ ↦ (hderiv θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ ↦ (hderiv θ (Set.Ico_subset_Icc_self hθ)).hasDerivWithinAt)
    (by simp [p]) (fun θ hθ ↦ by
      rw [norm_mul, add_zero, Function.comp_apply]
      have := hK _ (hp θ (Set.Ico_subset_Icc_self hθ))
      calc _ ≤ K * ‖f (p θ)‖ * ‖b - a‖ := by gcongr
        _ = _ := by ring)
    1 ⟨zero_le_one, le_rfl⟩
  simpa [p, gronwallBound_ε0] using h

/-- Right of `Re s = 1 + 1/L`, with `L = log (|Im s| + 2)`, `‖ζ(s)‖⁻¹ ≤ 3 L`. -/
private lemma norm_riemannZeta_inv_le_of_one_add_inv_le {s : ℂ}
    (hs : 1 + (Real.log (|s.im| + 2))⁻¹ ≤ s.re) :
    ‖riemannZeta s‖⁻¹ ≤ 3 * Real.log (|s.im| + 2) := by
  set L := Real.log (|s.im| + 2)
  have hL : 1 / 2 ≤ L := by
    linarith [Real.log_two_le_log_add_two (abs_nonneg s.im), Real.log_two_gt_d9]
  have hpos : 0 < s.re - 1 := by linarith [inv_pos.mpr (by linarith : (0 : ℝ) < L)]
  have h := norm_riemannZeta_inv_lt_one_add_one_div_sub_one (by linarith : 1 < s.re)
  have : 1 / (s.re - 1) ≤ L := by
    calc 1 / (s.re - 1) ≤ 1 / L⁻¹ := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = L := by rw [one_div, inv_inv]
  linarith

/-- At a point `z` with `1 ≤ |Im z|` and `ζ(z) ≠ 0` where `‖ζ′/ζ + 1/(z - 1)‖ ≤ C₄ L`, with
`L = log (|Im z| + 2)`, the pole term is at most `1 ≤ 2L`, so
`‖ζ′(z)‖ ≤ (|C₄| + 2) L ‖ζ(z)‖`. -/
private lemma norm_deriv_riemannZeta_le_of_one_le_abs_im {C₄ : ℝ} {z : ℂ} (ht : 1 ≤ |z.im|)
    (hζ : riemannZeta z ≠ 0)
    (hbd : ‖deriv riemannZeta z / riemannZeta z + 1 / (z - 1)‖ ≤ C₄ * Real.log (|z.im| + 2)) :
    ‖deriv riemannZeta z‖ ≤ (|C₄| + 2) * Real.log (|z.im| + 2) * ‖riemannZeta z‖ := by
  set L := Real.log (|z.im| + 2)
  have hL : 1 / 2 ≤ L := by
    linarith [Real.log_two_le_log_add_two (abs_nonneg z.im), Real.log_two_gt_d9]
  have hpole : ‖1 / (z - 1)‖ ≤ 1 := by simpa [one_div] using norm_inv_sub_one_le_one ht
  have hlog : ‖deriv riemannZeta z / riemannZeta z‖ ≤ (|C₄| + 2) * L := by
    have := norm_sub_le (deriv riemannZeta z / riemannZeta z + 1 / (z - 1)) (1 / (z - 1))
    rw [add_sub_cancel_right] at this
    have : C₄ * L ≤ |C₄| * L := mul_le_mul_of_nonneg_right (le_abs_self C₄) (by linarith)
    nlinarith
  calc ‖deriv riemannZeta z‖ = ‖deriv riemannZeta z / riemannZeta z‖ * ‖riemannZeta z‖ := by
        rw [← norm_mul, div_mul_cancel₀ _ hζ]
    _ ≤ _ := by gcongr

/-- At height `1 ≤ |Im s|`, left of `Re s = 1 + 1/L` and right of the curve of a bound
`‖ζ′/ζ + 1/(s - 1)‖ ≤ C₄ L` with nonvanishing, Grönwall along the segment to
`1 + 1/L + i Im s`, of length at most `(1 + β)/L`, gives
`‖ζ(s)‖⁻¹ ≤ 3 exp ((1 + β)(|C₄| + 2)) L`. -/
private lemma norm_riemannZeta_inv_le_of_one_le_abs_im {β C₄ : ℝ}
    (h4 : ∀ s : ℂ, s ≠ 1 → 1 - β / Real.log (|s.im| + 2) ≤ s.re →
      riemannZeta s ≠ 0 ∧
        ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₄ * Real.log (|s.im| + 2))
    {s : ℂ} (ht : 1 ≤ |s.im|) (hs : 1 - β / Real.log (|s.im| + 2) ≤ s.re)
    (hs' : s.re < 1 + (Real.log (|s.im| + 2))⁻¹) :
    ‖riemannZeta s‖⁻¹ ≤ 3 * Real.exp ((1 + β) * (|C₄| + 2)) * Real.log (|s.im| + 2) := by
  set t := s.im with ht_def
  set L := Real.log (|t| + 2)
  have hL : 1 / 2 ≤ L := by
    linarith [Real.log_two_le_log_add_two (abs_nonneg t), Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  set s₁ : ℂ := ((1 + L⁻¹ : ℝ) : ℂ) + t * I
  obtain ⟨hs₁re, hs₁im⟩ : s₁.re = 1 + L⁻¹ ∧ s₁.im = t := by simp [s₁]
  -- the segment from `s` to `s₁` stays at height `t`, right of `s`
  have hseg : segment ℝ s s₁ ⊆ {z | s.re ≤ z.re} ∩ ({z | z.im ≤ t} ∩ {z | t ≤ z.im}) :=
    (Convex.inter (convex_halfSpace_re_ge s.re)
      (Convex.inter (convex_halfSpace_im_le t) (convex_halfSpace_im_ge t))).segment_subset
      (show s.re ≤ s.re ∧ s.im ≤ t ∧ t ≤ s.im from ⟨le_rfl, ht_def.ge, ht_def.le⟩)
      (show s.re ≤ s₁.re ∧ s₁.im ≤ t ∧ t ≤ s₁.im from
        ⟨by rw [hs₁re]; linarith, hs₁im.le, hs₁im.ge⟩)
  have hmem (z) (hz : z ∈ segment ℝ s s₁) : z.im = t ∧ s.re ≤ z.re :=
    ⟨le_antisymm (hseg hz).2.1 (hseg hz).2.2, (hseg hz).1⟩
  set K := (|C₄| + 2) * L
  have hK : ∀ z ∈ segment ℝ s s₁, ‖deriv riemannZeta z‖ ≤ K * ‖riemannZeta z‖ := by
    intro z hz
    obtain ⟨hzim, hzre⟩ := hmem z hz
    have ht' : 1 ≤ |z.im| := by rwa [hzim]
    obtain ⟨hζ, hbd⟩ := h4 z (ne_one_of_one_le_abs_im ht') (by rw [hzim]; linarith)
    have h := norm_deriv_riemannZeta_le_of_one_le_abs_im ht' hζ hbd
    rwa [hzim] at h
  have hgr := norm_le_norm_mul_exp_of_norm_deriv_le
    (fun z hz ↦ differentiableAt_riemannZeta (ne_one_of_one_le_abs_im (by rwa [(hmem z hz).1]))) hK
  -- the segment has length `1 + 1/L - Re s ≤ (1 + β)/L`
  have hlen : ‖s₁ - s‖ ≤ (1 + β) * L⁻¹ := by
    have hreal : s₁ - s = ((1 + L⁻¹ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s₁, ht_def]
    rw [hreal, norm_real, Real.norm_of_nonneg (by linarith)]
    rw [div_eq_mul_inv] at hs
    linarith
  have hKlen : K * ‖s₁ - s‖ ≤ (1 + β) * (|C₄| + 2) := by
    calc K * ‖s₁ - s‖ ≤ K * ((1 + β) * L⁻¹) := by gcongr
      _ = (1 + β) * (|C₄| + 2) := by simp only [K]; field_simp
  have hζs : riemannZeta s ≠ 0 := (h4 s (ne_one_of_one_le_abs_im ht) hs).1
  have hζ₁ : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by
    rw [hs₁re]; linarith [inv_pos.mpr hL0])
  have hinv₁ : ‖riemannZeta s₁‖⁻¹ ≤ 3 * L := by
    have := norm_riemannZeta_inv_le_of_one_add_inv_le (s := s₁) (by rw [hs₁re, hs₁im])
    rwa [hs₁im] at this
  calc ‖riemannZeta s‖⁻¹ = ‖riemannZeta s₁‖ / ‖riemannZeta s‖ * ‖riemannZeta s₁‖⁻¹ := by
        field_simp
    _ ≤ Real.exp ((1 + β) * (|C₄| + 2)) * (3 * L) := by
        gcongr
        rw [div_le_iff₀ (norm_pos_iff.mpr hζs)]
        exact hgr.trans (by rw [mul_comm]; gcongr)
    _ = _ := by ring

/-- The part of `1 - β / log (|Im s| + 2) ≤ Re s` with `|Im s| ≤ 1` and `Re s ≤ 3` is
compact. -/
private lemma isCompact_strip_of_abs_im_le_one (β : ℝ) :
    IsCompact {s : ℂ | |s.im| ≤ 1 ∧ s.re ≤ 3 ∧ 1 - β / Real.log (|s.im| + 2) ≤ s.re} := by
  have hlog : ∀ z : ℂ, 1 / 2 ≤ Real.log (|z.im| + 2) := fun z ↦ by
    linarith [Real.log_two_le_log_add_two (abs_nonneg z.im), Real.log_two_gt_d9]
  refine (isCompact_closedBall (0 : ℂ) (4 + 2 * |β|)).of_isClosed_subset ?_ ?_
  · have hc : Continuous fun z : ℂ ↦ Real.log (|z.im| + 2) :=
      (continuous_im.abs.add continuous_const : Continuous fun z : ℂ ↦ |z.im| + 2).log
        fun z ↦ (by positivity : (0 : ℝ) < |z.im| + 2).ne'
    exact (isClosed_le continuous_im.abs continuous_const).inter
      ((isClosed_le continuous_re continuous_const).inter
        (isClosed_le (continuous_const.sub (continuous_const.div hc fun z ↦ by linarith [hlog z]))
          continuous_re))
  · rintro z ⟨him, hre, hre'⟩
    rw [mem_closedBall_zero_iff]
    have : β / Real.log (|z.im| + 2) ≤ 2 * |β| := by
      rw [div_le_iff₀ (by linarith [hlog z])]
      nlinarith [hlog z, le_abs_self β, abs_nonneg β]
    calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      _ ≤ 4 + 2 * |β| := by
        have : |z.re| ≤ 3 + 2 * |β| := abs_le.mpr ⟨by linarith, by linarith [abs_nonneg β]⟩
        linarith

/-- **The zero-free strip of `ζ` with logarithmic bounds.** There are `0 < β < 1` and `C > 0`
such that, on the region `Z = {s | 1 - β / log (|Im s| + 2) ≤ Re s}`:
* `ζ(s) ≠ 0` for `s ≠ 1`;
* the extension `R(s) = (s - 1) / riemannZeta₁ s` of `1/ζ` (`TauCeti.sub_one_div_riemannZeta₁`),
  which vanishes at `1`, is analytic on a neighbourhood of `Z`;
* `‖riemannZeta₀ s‖ ≤ C log (|Im s| + 2)`, where `riemannZeta₀` is the entire extension of
  `ζ(s) - 1/(s - 1)`;
* `‖R s‖ ≤ C log (|Im s| + 2)`. -/
theorem riemannZeta_zeroFreeStrip_bounds :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ 0 < C ∧
      AnalyticOnNhd ℂ (fun s ↦ (s - 1) / riemannZeta₁ s)
        {s | 1 - β / Real.log (|s.im| + 2) ≤ s.re} ∧
      ∀ s : ℂ, 1 - β / Real.log (|s.im| + 2) ≤ s.re →
        (s ≠ 1 → riemannZeta s ≠ 0) ∧
          ‖riemannZeta₀ s‖ ≤ C * Real.log (|s.im| + 2) ∧
          ‖(s - 1) / riemannZeta₁ s‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨β, C₄, hβ, hβ1, h4⟩ := riemannZeta_deriv_logDeriv_bound
  obtain ⟨CG, hCG⟩ := exists_norm_riemannZeta₀_le_mul_log β
  have hne : ∀ s : ℂ, 1 - β / Real.log (|s.im| + 2) ≤ s.re → riemannZeta₁ s ≠ 0 := by
    intro s hs h
    rcases eq_or_ne s 1 with rfl | hs1
    · simp [riemannZeta₁_one] at h
    · exact (h4 s hs1 hs).1 (by rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero])
  have hR : AnalyticOnNhd ℂ (fun s ↦ (s - 1) / riemannZeta₁ s)
      {s | 1 - β / Real.log (|s.im| + 2) ≤ s.re} := fun s hs ↦
    (analyticAt_id.sub analyticAt_const).div (differentiable_riemannZeta₁.analyticAt s) (hne s hs)
  obtain ⟨M, hM⟩ := (isCompact_strip_of_abs_im_le_one β).exists_bound_of_continuousOn
    (hR.continuousOn.mono fun s hs ↦ hs.2.2)
  set E := Real.exp ((1 + β) * (|C₄| + 2))
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg (by linarith) (by positivity))
  set C := max (max CG 1) (max (3 * E) (|M| / Real.log 2))
  have hC : 0 < C := lt_max_of_lt_left (lt_max_of_lt_right one_pos)
  refine ⟨β, C, hβ, hβ1, hC, hR, fun s hs ↦ ⟨fun hs1 ↦ (h4 s hs1 hs).1, ?_, ?_⟩⟩
  · exact (hCG s hs).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _))
      ((Real.log_pos one_lt_two).le.trans (Real.log_two_le_log_add_two (abs_nonneg _))))
  set L := Real.log (|s.im| + 2)
  have hL2 : Real.log 2 ≤ L := Real.log_two_le_log_add_two (abs_nonneg _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : 0 < L := hlog2.trans_le hL2
  have h3E : 3 * E * L ≤ C * L :=
    mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hL.le
  rcases le_or_gt (1 + L⁻¹) s.re with hsη | hsη
  · have hs1 : s ≠ 1 := fun h ↦ by
      rw [h, one_re] at hsη
      linarith [inv_pos.mpr hL]
    rw [sub_one_div_riemannZeta₁ hs1, norm_inv]
    refine (norm_riemannZeta_inv_le_of_one_add_inv_le hsη).trans (le_trans ?_ h3E)
    nlinarith
  rcases le_or_gt 1 |s.im| with ht | ht
  · rw [sub_one_div_riemannZeta₁ (ne_one_of_one_le_abs_im ht), norm_inv]
    have h4' := fun z hz1 hz ↦ And.intro (h4 z hz1 hz).1 (h4 z hz1 hz).2.2
    exact (norm_riemannZeta_inv_le_of_one_le_abs_im h4' ht hs hsη).trans h3E
  · have hs3 : s.re ≤ 3 := by
      have : L⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hL two_pos]
        linarith [Real.log_two_gt_d9]
      linarith
    calc _ ≤ M := hM s ⟨ht.le, hs3, hs⟩
      _ ≤ |M| := le_abs_self M
      _ ≤ |M| / Real.log 2 * L := TauCeti.le_div_mul_of_le (abs_nonneg M) hlog2 hL2
      _ ≤ C * L := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) hL.le

end TauCeti
