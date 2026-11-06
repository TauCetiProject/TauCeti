/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Smooth functions are dense in `W^{1,p}(a, b)`

On a bounded open interval `(a, b)` and for `1 ≤ p < ∞`, the restrictions to `(a, b)` of smooth
functions on `ℝ` are dense in the first-order Sobolev space `W^{1,p}(a, b)`. No boundary
condition is imposed, so the approximants are smooth up to the boundary: they are restrictions of
functions smooth on a neighbourhood of `[a, b]`. This is stronger than the interior smoothness of
Meyers–Serrin (`TauCeti.Wkp.dense_contDiffOn_representatives`), and differs from density of test
functions with compact support in `(a, b)`, whose closure is the strictly smaller space
`W^{1,p}_0(a, b)`. At `p = 2` it says that such restrictions are dense in `H¹(a, b)`, the domain of
the derivative `D f = f'` on `L²(a, b)` without boundary condition (`TauCeti.weakGradientPMap`).

An element `u` of `W^{1,p}(a, b)` is almost everywhere a constant `c` plus the primitive of its
weak derivative `g` (`TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral`). If `h` is
a smooth function close to `g` in `Lᵖ(a, b)`, then `c + ∫ h` is a smooth function on `ℝ` whose
derivative is close to `g` and whose value differs from `u` by the primitive of `h - g`, of
`Lᵖ(a, b)` norm at most `(b - a) ‖h - g‖_p`
(`TauCeti.intervalIntegral.eLpNorm_primitive_le_mul_eLpNorm`).

The restriction `p < ∞` cannot be dropped. The absolute value lies in `W^{1,p}(a, b)` for every
`p`, with the sign as weak derivative, and when `a < 0 < b` the sign stays at `L^∞` distance at
least `1` from every continuous derivative.

## Main declarations

* `TauCeti.W1p.dense_contDiff_representatives_Ioo`: for `1 ≤ p < ∞`, the elements of
  `W^{1,p}(a, b)` represented by smooth functions on `ℝ` are dense.
* `TauCeti.W1p.exists_value_gradient_ae_eq_abs`: `|x|` is an element of `W^{1,p}(a, b)` whose
  weak derivative is the sign of `x`.
* `TauCeti.W1p.one_le_dist_of_gradient_ae_eq_sign`: for `a < 0 < b`, such an element of
  `W^{1,∞}(a, b)` is at distance at least `1` from every element with a `C¹` representative.
* `TauCeti.W1p.not_dense_contDiff_representatives_Ioo_top`: hence smooth functions are not dense in
  `W^{1,∞}(a, b)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Theorem 8.7
  (density of the restrictions of `C_c^∞(ℝ)` in `W^{1,p}(I)` for `1 ≤ p < ∞`).
-/

public section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Gradient ContDiff

namespace TauCeti

namespace W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Write `u ∈ W^{1,p}(a, b)` as `c + ∫ s in t₀..t, g s` with `g` its weak derivative. Replacing
`g` by a smooth `h` gives an element `w` represented by the smooth function `c + ∫ h`, whose weak
derivative is `h` and whose value differs from that of `u` by at most `(b - a) ‖g - h‖_p` in
`Lᵖ`. -/
private theorem exists_contDiff_eLpNorm_sub_le (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p)
    {c t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hc : W1p.value u =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ c + ∫ s in t₀..t, W1p.gradient u s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ∃ w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      (∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ W1p.value w =ᵐ[volume.restrict (Ioo a b)] f) ∧
      eLpNorm (⇑(W1p.value w) - ⇑(W1p.value u)) p (volume.restrict (Ioo a b)) ≤
        ENNReal.ofReal (b - a) * eLpNorm (⇑(W1p.gradient u) - h) p (volume.restrict (Ioo a b)) ∧
      eLpNorm (⇑(W1p.gradient w) - ⇑(W1p.gradient u)) p (volume.restrict (Ioo a b)) =
        eLpNorm (⇑(W1p.gradient u) - h) p (volume.restrict (Ioo a b)) := by
  set g : ℝ → ℝ := ⇑(W1p.gradient u)
  set f : ℝ → ℝ := fun t ↦ c + ∫ s in t₀..t, h s
  have hfd (t : ℝ) : HasDerivAt f (h t) t :=
    (hh.continuous.integral_hasStrictDerivAt t₀ t).hasDerivAt.const_add c
  have hderiv : deriv f = h := funext fun t ↦ (hfd t).deriv
  have hf : ContDiff ℝ ∞ f :=
    contDiff_infty_iff_deriv.2 ⟨fun t ↦ (hfd t).differentiableAt, hderiv ▸ hh⟩
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (p := p) isOpen_univ
    (hf.of_le (by exact_mod_cast le_top)).contDiffOn isCompact_Icc Ioo_subset_Icc_self
    (subset_univ _)
  refine ⟨w, ⟨f, hf, hwv⟩, ?_, ?_⟩
  · -- The values differ by the primitive of `h - g`.
    have hg : MemLp g p (volume.restrict (Ioo a b)) := Lp.memLp _
    have hgi : IntegrableOn g (Ioo a b) := hg.integrable Fact.out
    have hhi : IntegrableOn h (Ioo a b) :=
      hh.continuous.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have heq : ⇑(W1p.value w) - ⇑(W1p.value u) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ ∫ s in t₀..t, (h - g) s := by
      filter_upwards [hwv, hc, ae_restrict_mem measurableSet_Ioo] with t hwt hct ht
      have hsub : uIcc t₀ t ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset ht₀ ht
      rw [Pi.sub_apply, hwt, hct]
      simp only [f, Pi.sub_apply]
      rw [intervalIntegral.integral_sub (hh.continuous.intervalIntegrable _ _)
        (hgi.mono_set hsub).intervalIntegrable]
      ring
    rw [eLpNorm_congr_ae heq, eLpNorm_sub_comm]
    exact intervalIntegral.eLpNorm_primitive_le_mul_eLpNorm Fact.out (hhi.sub hgi)
      (Ioo_subset_Icc_self ht₀)
  · rw [eLpNorm_sub_comm]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hwg] with t ht
    simp [g, ht, gradient_eq_deriv', hderiv]

/-- **Smooth functions are dense in `W^{1,p}(a, b)`** for `1 ≤ p < ∞`: every element of the
Sobolev space on the interval `(a, b)` is a `W^{1,p}`-limit of elements represented on `(a, b)` by
functions smooth on all of `ℝ`. No boundary condition is imposed on the approximants. -/
theorem dense_contDiff_representatives_Ioo (hp : p ≠ ⊤) :
    Dense {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p |
      ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ W1p.value u =ᵐ[volume.restrict (Ioo a b)] f} := by
  rcases le_or_gt b a with hba | hab
  · -- On an empty interval every element is represented by the zero function.
    have h0 : volume.restrict (Ioo a b) = 0 := by simp [Ioo_eq_empty_of_le hba]
    exact dense_univ.mono fun u _ ↦ ⟨0, contDiff_const, by simp [h0, EventuallyEq]⟩
  intro u
  -- `u` is a constant plus the primitive of its weak derivative.
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (W1p.value u) (W1p.gradient u) 1 := by
    simpa using (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc⟩ := hw.exists_ae_eq_add_intervalIntegral ht₀
  -- Smooth `hₙ` with `‖g - hₙ‖_p ≤ 1 / (n + 1)`, and the elements `wₙ` they produce.
  have hg : MemLp (W1p.gradient u) p (volume.restrict (Ioo a b)) := Lp.memLp _
  choose h _ hhs hhg using fun n : ℕ ↦
    hg.exist_eLpNorm_sub_le hp Fact.out (Nat.one_div_pos_of_nat (n := n))
  choose w hws hwv hwg using fun n ↦ exists_contDiff_eLpNorm_sub_le u ht₀ hc (hhs n)
  refine mem_closure_of_tendsto (b := atTop) ?_ (Eventually.of_forall hws)
  have hδ : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  rw [W1p.tendsto_iff_value_gradient, Lp.tendsto_Lp_iff_tendsto_eLpNorm',
    Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hδ (Or.inr (ENNReal.ofReal_ne_top (r := b - a))))
    (fun _ ↦ zero_le) fun n ↦ (hwv n).trans (by gcongr; exact hhg n),
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ
    (fun _ ↦ zero_le) fun n ↦ (hwg n).trans_le (hhg n)⟩

/-- The absolute value is an element of `W^{1,p}(a, b)` for every `1 ≤ p ≤ ∞` on every bounded
interval, and its weak derivative is the sign of `x`, normalised to `-1` at `x = 0`. -/
theorem exists_value_gradient_ae_eq_abs (a b : ℝ) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      W1p.value u =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ |x|) ∧
      W1p.gradient u =ᵐ[volume.restrict (Ioo a b)] fun x ↦ if 0 < x then 1 else -1 := by
  set s : ℝ → ℝ := fun x ↦ if 0 < x then 1 else -1 with hs_def
  have hv : MemLp (fun x : ℝ ↦ |x|) p (volume.restrict (Ioo a b)) := by
    refine MemLp.of_bound continuous_abs.aestronglyMeasurable (max |a| |b|) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le_max_abs_abs hx.1.le hx.2.le
  have hg : MemLp s p (volume.restrict (Ioo a b)) := by
    refine MemLp.of_bound (Measurable.ite measurableSet_Ioi measurable_const
      measurable_const).aestronglyMeasurable 1 (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : 0 < x <;> simp [hs_def, hx]
  -- Away from `0` the absolute value is differentiable with derivative `s x`.
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) →
      HasFDerivAt (fun x : ℝ ↦ |x|) (innerSL ℝ (s x)) x := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx _
    have hd : HasDerivAt (fun x : ℝ ↦ |x|) (s x) x := by
      rcases lt_or_gt_of_ne (show x ≠ 0 from hx) with hx | hx
      · simpa [hs_def, hx.not_gt] using hasDerivAt_abs_neg hx
      · simpa [hs_def, hx] using hasDerivAt_abs_pos hx
    convert hd.hasFDerivAt using 1
    ext
    simp
  have hL : LipschitzWith 1 fun x : ℝ ↦ |x| := lipschitzWith_one_norm (E := ℝ)
  have hweak := LocallyLipschitzOn.hasWeakFDerivOn hL.locallyLipschitz.locallyLipschitzOn hderiv
  refine ⟨W1p.mk (hv.toLp _) (hg.toLp _) ((hweak.congr_ae hv.coeFn_toLp.symm).congr_ae_deriv ?_),
    by simpa using hv.coeFn_toLp, by simpa using hg.coeFn_toLp⟩
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

/-- In `W^{1,∞}(a, b)` with `a < 0 < b`, an element whose weak derivative is the sign of `x`,
such as `|x|` (`TauCeti.W1p.exists_value_gradient_ae_eq_abs`), is at distance at least `1` from
every element represented by a `C¹` function: a continuous derivative cannot be uniformly close to
the jump of the sign at `0`. -/
theorem one_le_dist_of_gradient_ae_eq_sign {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤}
    (hu : W1p.gradient u =ᵐ[volume.restrict (Ioo a b)] fun x ↦ if 0 < x then 1 else -1)
    {w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hw : W1p.value w =ᵐ[volume.restrict (Ioo a b)] f) :
    1 ≤ dist u w := by
  set μ := volume.restrict (Ioo a b)
  -- The weak derivative of `w` is the classical derivative of `f`.
  obtain ⟨w', hw'v, hw'g⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (p := ⊤) isOpen_univ hf.contDiffOn
    isCompact_Icc Ioo_subset_Icc_self (subset_univ _)
  obtain rfl : w = w' := W1p.ext_value (Lp.ext (hw.trans hw'v.symm))
  set G := W1p.gradient u - W1p.gradient w
  set r := ‖G‖ with hr_def
  -- Almost everywhere, the two derivatives differ by at most `r = ‖∇u - ∇w‖_∞`.
  have hG : ∀ᵐ t ∂μ, |(if 0 < t then 1 else -1) - deriv f t| ≤ r := by
    filter_upwards [ae_le_eLpNormEssSup (f := G) (μ := μ), Lp.coeFn_sub (W1p.gradient u)
      (W1p.gradient w), hu, hw'g] with t ht hsub hut hwt
    rw [hsub, Pi.sub_apply, hut, hwt, gradient_eq_deriv'] at ht
    have htop := eLpNorm_exponent_top (Lp.aestronglyMeasurable G)
    rw [← Real.norm_eq_abs, ← toReal_enorm, hr_def, Lp.norm_def, htop]
    exact ENNReal.toReal_mono (htop ▸ Lp.eLpNorm_ne_top G) ht
  have hdist : r ≤ dist u w := by
    simpa only [dist_eq_norm, r, G, W1p.gradient_sub] using W1p.norm_gradient_le (u - w)
  by_contra! hlt
  have hr : r < 1 := hdist.trans_lt hlt
  -- Continuity of `f'` at `0` is incompatible with the jump of the sign there.
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 ((hf.continuous_deriv le_rfl).continuousAt
    (x := 0)) ((1 - r) / 2) (by linarith)
  -- Every nonempty subinterval contains a point where this bound holds.
  have hex : ∀ l m, l < m → l ∈ Icc a b → m ∈ Icc a b →
      ∃ t ∈ Ioo l m, |(if 0 < t then 1 else -1) - deriv f t| ≤ r := by
    intro l m hlm hl hm
    have : (ae (volume.restrict (Ioo l m))).NeBot := ae_restrict_neBot.2 (by simp [hlm])
    obtain ⟨t, ht, hPt⟩ := ((ae_restrict_mem (measurableSet_Ioo (a := l) (b := m))).and
      (ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).1 hG))).exists
    exact ⟨t, ht, hPt ⟨hl.1.trans_lt ht.1, ht.2.trans_le hm.2⟩⟩
  -- Such points `0 < t₁ < δ` and `-δ < t₂ < 0` force `f' 0 > (1 - r) / 2` and `f' 0 < (r - 1) / 2`.
  obtain ⟨t₁, ht₁, h₁⟩ := hex 0 (min δ b) (lt_min hδ hb) ⟨ha.le, hb.le⟩
    ⟨by linarith [lt_min hδ hb], min_le_right _ _⟩
  obtain ⟨t₂, ht₂, h₂⟩ := hex (max (-δ) a) 0 (max_lt (by linarith) ha)
    ⟨le_max_right _ _, by linarith [max_lt (neg_lt_zero.2 hδ) ha]⟩ ⟨ha.le, hb.le⟩
  have hc₁ := hcont (show dist t₁ 0 < δ by
    rw [Real.dist_0_eq_abs, abs_of_pos ht₁.1]; exact ht₁.2.trans_le (min_le_left _ _))
  have hc₂ := hcont (show dist t₂ 0 < δ by
    rw [Real.dist_0_eq_abs, abs_of_neg ht₂.2]; linarith [ht₂.1.trans_le' (le_max_left _ _)])
  simp only [ht₁.1, ↓reduceIte] at h₁
  simp only [ht₂.2.not_gt, ↓reduceIte] at h₂
  rw [Real.dist_eq] at hc₁ hc₂
  linarith [(abs_le.1 h₁).2, (abs_le.1 h₂).1, (abs_lt.1 hc₁).2, (abs_lt.1 hc₂).1]

/-- Smooth density fails in `W^{1,∞}(a, b)` whenever `a < 0 < b`: the class of `|x|` is not in the
closure of the elements represented by smooth functions on `ℝ`. -/
theorem not_dense_contDiff_representatives_Ioo_top {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ¬ Dense {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤ |
      ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ W1p.value u =ᵐ[volume.restrict (Ioo a b)] f} := by
  intro hd
  obtain ⟨u, -, hu⟩ := exists_value_gradient_ae_eq_abs (p := ⊤) a b
  obtain ⟨w, hw, f, hf, hwf⟩ := Metric.dense_iff.1 hd u 1 one_pos
  exact (one_le_dist_of_gradient_ae_eq_sign ha hb hu (hf.of_le (by exact_mod_cast le_top))
    hwf).not_gt (by simpa [dist_comm] using hw)

end W1p

end TauCeti
