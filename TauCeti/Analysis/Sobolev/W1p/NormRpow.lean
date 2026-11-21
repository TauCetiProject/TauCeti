/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Norm powers in `W^{1,p}` and the sharpness of the Sobolev exponent

Let `E` be a real inner product space of finite dimension `n ≥ 1` with an additive Haar measure,
and let `Ω` be a bounded open neighbourhood of the origin, such as the unit ball. This file
decides exactly when the norm power `x ↦ ‖x‖ ^ s` lies in `W^{1,p}(Ω)`, `1 ≤ p < ∞`, and uses
it to show that the Sobolev exponent `p⋆ = np / (n - p)` of the embedding
`W^{1,p} ↪ L^{p⋆}` cannot be improved.

For `s ≠ 0`, `‖x‖ ^ s` is in `W^{1,p}(Ω)` exactly when `(s - 1) p > -n`
(`TauCeti.exists_w1p_value_ae_eq_norm_rpow_iff`). Its weak gradient is then the classical one,
`s ‖x‖ ^ (s - 2) x`, of norm `|s| ‖x‖ ^ (s - 1)` (`TauCeti.exists_w1p_value_ae_eq_norm_rpow`);
conversely a weak gradient agrees with the classical one away from the origin, so it cannot be
`p`-integrable when `(s - 1) p ≤ -n` (`TauCeti.not_exists_w1p_value_ae_eq_norm_rpow`). With
`s = -a`, `a > 0`, the condition reads `(a + 1) p < n`.

On the other hand `‖x‖ ^ s` is in `L^{p⋆}(Ω)` exactly when `s p⋆ > -n`
(`TauCeti.memLp_norm_rpow_restrict_iff`). When `1 / p⋆ + 1 / n = 1 / p` the two conditions
agree, so for every real `s` the norm power lies in `W^{1,p}(Ω)` exactly when it lies in
`L^{p⋆}(Ω)` (`TauCeti.exists_w1p_value_ae_eq_norm_rpow_iff_memLp`). Taking `s = -n / r` for
`p⋆ < r` gives a function of `W^{1,p}(Ω)` outside `L^r(Ω)`, and so outside `L^q(Ω)` for every
`q > p⋆`: no Sobolev embedding of `W^{1,p}(Ω)` reaches past `p⋆`
(`TauCeti.exists_w1p_not_memLp_value`).

## Main declarations

* `TauCeti.exists_w1p_value_ae_eq_norm_rpow_iff`: `‖x‖ ^ s ∈ W^{1,p}(Ω)` if and only if
  `(s - 1) p > -n`, for `s ≠ 0`.
* `TauCeti.exists_w1p_value_ae_eq_norm_rpow_iff_memLp`: `‖x‖ ^ s ∈ W^{1,p}(Ω)` if and only if
  `‖x‖ ^ s ∈ L^{p⋆}(Ω)`.
* `TauCeti.exists_w1p_not_memLp_value`: for `q > p⋆` some `u ∈ W^{1,p}(Ω)` is not in `L^q(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, Section 5.2 (the example
  `|x| ^ (-α)` on the unit ball).

The converse direction follows the planar argument of `TauCeti.not_memWkpLoc_one_norm_rpow`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set Topology TopologicalSpace

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The exponent condition `(s - 1) p > -n` forces `s > 1 - n`, since `p ≥ 1`. -/
private theorem one_sub_finrank_lt (hp : p ≠ ∞)
    (hs : -(Module.finrank ℝ E : ℝ) < (s - 1) * p.toReal) :
    1 - (Module.finrank ℝ E : ℝ) < s := by
  have hp1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  rcases le_or_gt 0 (s - 1) with h | h
  · rcases eq_or_lt_of_le hn with hn0 | hn0
    · rw [← hn0] at hs ⊢
      nlinarith
    · linarith
  · nlinarith

/-- For `1 ≤ p < ∞` and a bounded open set `Ω`, the norm power `x ↦ ‖x‖ ^ s` lies in
`W^{1,p}(Ω)` when `(s - 1) p > -n`, and its weak gradient is the classical gradient
`s ‖x‖ ^ (s - 2) x`. -/
theorem exists_w1p_value_ae_eq_norm_rpow (hp : p ≠ ∞) (hb : Bornology.IsBounded (Ω : Set E))
    (hs : -(Module.finrank ℝ E : ℝ) < (s - 1) * p.toReal) :
    ∃ u : W1p μ Ω p, W1p.value u =ᵐ[μ.restrict Ω] (fun x => ‖x‖ ^ s) ∧
      W1p.gradient u =ᵐ[μ.restrict Ω] fun x => (s * ‖x‖ ^ (s - 2)) • x := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp1 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hu : MemLp (fun x : E => ‖x‖ ^ s) p (μ.restrict Ω) :=
    hb.memLp_norm_rpow_restrict (mu := μ) hp (by nlinarith)
  have hD : MemLp (fun x : E => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) p (μ.restrict Ω) := by
    have hm : AEStronglyMeasurable (fun x : E => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x)
        (μ.restrict Ω) :=
      (locallyIntegrable_norm_rpow_smul_innerSL (μ := μ)
        (one_sub_finrank_lt hp hs)).aestronglyMeasurable.restrict
    exact hb.memLp_of_norm_le_mul_norm_rpow (mu := μ) hp hs hm (norm_rpow_smul_innerSL_le s)
  obtain ⟨u, hval, hgrad⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hu hD
    (hasWeakFDerivOn_norm_rpow (one_sub_finrank_lt hp hs) Ω)
  refine ⟨u, hval, hgrad.trans (ae_of_all _ fun x => ?_)⟩
  simp only [map_smul, InnerProductSpace.toDual_symm_innerSL]

/-- For `1 ≤ p` and `s ≠ 0`, if `(s - 1) p ≤ -n` then the norm power `x ↦ ‖x‖ ^ s` is not in
`W^{1,p}(Ω)` for any open neighbourhood `Ω` of the origin: away from the origin a weak gradient
agrees with the classical one, whose norm `|s| ‖x‖ ^ (s - 1)` is not `p`-integrable near the
origin. -/
theorem not_exists_w1p_value_ae_eq_norm_rpow [Nontrivial E]
    (hΩ : (Ω : Set E) ∈ 𝓝 (0 : E)) (hs0 : s ≠ 0)
    (hs : (s - 1) * p.toReal ≤ -(Module.finrank ℝ E : ℝ)) :
    ¬ ∃ u : W1p μ Ω p, W1p.value u =ᵐ[μ.restrict Ω] fun x => ‖x‖ ^ s := by
  rintro ⟨u, hu⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : p ≠ ∞ := by
    rintro rfl
    have hn : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
    simp only [ENNReal.toReal_top, mul_zero] at hs
    linarith
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_ball.mem_iff.1 hΩ
  -- On the punctured ball, the weak derivative of `u` is the classical derivative.
  let W : Opens E := ⟨ball 0 r, isOpen_ball⟩ ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hWΩ : W ≤ Ω := fun x hx => hrΩ hx.1
  have hdiff : ∀ x ∈ (W : Set E), HasFDerivAt (fun x : E => ‖x‖ ^ s)
      ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) x := fun x hx => hasFDerivAt_norm_rpow_of_ne s hx.2
  have hcont : ContinuousOn (fderiv ℝ fun x : E => ‖x‖ ^ s) W := by
    have hc : ContinuousOn (fun x : E => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) W :=
      fun x hx => ((continuousAt_const.mul ((continuous_norm.continuousAt).rpow_const
        (Or.inl (norm_ne_zero_iff.2 hx.2)))).smul
          (innerSL ℝ).continuous.continuousAt).continuousWithinAt
    exact hc.congr fun x hx => (hdiff x hx).fderiv
  have hae := (((W1p.hasWeakFDerivOn u).congr_ae hu).mono hWΩ).ae_eq_fderiv
    (hcont.locallyIntegrableOn W.isOpen.measurableSet)
    fun x hx => (hdiff x hx).differentiableAt
  have hae' := (ae_restrict_iff' W.isOpen.measurableSet).1 hae
  -- So `|s| ‖x‖ ^ (s - 1)` would be `p`-integrable on the ball.
  have hint := ((Lp.memLp (W1p.gradient u)).mono_measure
    (Measure.restrict_mono hrΩ le_rfl)).integrable_norm_rpow hp0 hp
  have hball : IntegrableOn (fun x : E => |s| ^ p.toReal * ‖x‖ ^ ((s - 1) * p.toReal))
      (ball 0 r) μ := by
    refine hint.congr ?_
    filter_upwards [ae_restrict_of_ae hae', ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (Measure.ae_ne μ (0 : E))] with x hx hxb hx0
    have hxW : x ∈ (W : Set E) := ⟨hxb, hx0⟩
    rw [← innerSL_apply_norm ℝ, hx hxW, norm_fderiv_norm_rpow_of_ne s hx0,
      Real.mul_rpow (abs_nonneg s) (Real.rpow_nonneg (norm_nonneg x) _),
      ← Real.rpow_mul (norm_nonneg x)]
  have hpos : (0 : ℝ) < |s| ^ p.toReal := Real.rpow_pos_of_pos (abs_pos.2 hs0) _
  rw [IntegrableOn, integrable_const_mul_iff hpos.ne'.isUnit, ← IntegrableOn,
    integrableOn_norm_rpow_ball_iff hr] at hball
  linarith

/-- **Norm powers in `W^{1,p}`.** For `1 ≤ p < ∞`, `s ≠ 0` and a bounded open neighbourhood `Ω`
of the origin, `x ↦ ‖x‖ ^ s` lies in `W^{1,p}(Ω)` exactly when `(s - 1) p > -n`. For `s = -a`
with `a > 0` this reads `(a + 1) p < n`. -/
theorem exists_w1p_value_ae_eq_norm_rpow_iff [Nontrivial E] (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Ω : Set E)) (hΩ : (Ω : Set E) ∈ 𝓝 (0 : E)) (hs0 : s ≠ 0) :
    (∃ u : W1p μ Ω p, W1p.value u =ᵐ[μ.restrict Ω] fun x => ‖x‖ ^ s) ↔
      -(Module.finrank ℝ E : ℝ) < (s - 1) * p.toReal :=
  ⟨fun h => not_le.1 fun hs => not_exists_w1p_value_ae_eq_norm_rpow hΩ hs0 hs h,
    fun hs => (exists_w1p_value_ae_eq_norm_rpow hp hb hs).imp fun _ h => h.1⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `1 / p⋆ + 1 / n = 1 / p` with `p⋆` finite, the conditions `(s - 1) p > -n` and
`s p⋆ > -n` agree. -/
private theorem neg_finrank_lt_sub_one_mul_iff [Nontrivial E] {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ ∞) (hexp : pstar⁻¹ + (Module.finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    -(Module.finrank ℝ E : ℝ) < (s - 1) * p.toReal ↔
      -(Module.finrank ℝ E : ℝ) < s * pstar.toReal := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := by simp [n, Module.finrank_pos]
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp := ne_top_of_inv_add_inv_eq_inv hexp
  have hpstar0 : pstar ≠ 0 := (zero_lt_one.trans_le (one_le_of_inv_add_eq_inv hexp)).ne'
  have hc : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have ha : 0 < pstar.toReal := ENNReal.toReal_pos hpstar0 hpstar
  -- In real numbers, `1 / p⋆ + 1 / n = 1 / p`, that is `(n + p⋆) p = p⋆ n`.
  have hreal : pstar.toReal⁻¹ + n⁻¹ = p.toReal⁻¹ := toReal_inv_add_inv_eq_inv hp0 hexp
  have hpoly : (n + pstar.toReal) * p.toReal = pstar.toReal * n := by
    field_simp at hreal
    linarith
  -- Hence `p⋆ ((s - 1) p + n) = p (s p⋆ + n)`, and both factors `p⋆` and `p` are positive.
  have key : pstar.toReal * ((s - 1) * p.toReal + n) = p.toReal * (s * pstar.toReal + n) := by
    linear_combination -hpoly
  constructor <;> intro h
  · have : 0 < p.toReal * (s * pstar.toReal + n) := by
      rw [← key]
      exact mul_pos ha (by linarith)
    linarith [pos_of_mul_pos_right this hc.le]
  · have : 0 < pstar.toReal * ((s - 1) * p.toReal + n) := by
      rw [key]
      exact mul_pos hc (by linarith)
    linarith [pos_of_mul_pos_right this ha.le]

variable {pstar : ℝ≥0∞}

/-- **The Sobolev exponent of norm powers.** Let `1 ≤ p` and let `p⋆ < ∞` be the Sobolev
exponent, `1 / p⋆ + 1 / n = 1 / p`, so that `p < n`. On a bounded open neighbourhood `Ω` of the
origin, the norm power `x ↦ ‖x‖ ^ s` lies in `W^{1,p}(Ω)` exactly when it lies in `L^{p⋆}(Ω)`,
for every real `s`. -/
theorem exists_w1p_value_ae_eq_norm_rpow_iff_memLp [Nontrivial E] (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (Module.finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (hb : Bornology.IsBounded (Ω : Set E)) (hΩ : (Ω : Set E) ∈ 𝓝 (0 : E)) (s : ℝ) :
    (∃ u : W1p μ Ω p, W1p.value u =ᵐ[μ.restrict Ω] fun x => ‖x‖ ^ s) ↔
      MemLp (fun x : E => ‖x‖ ^ s) pstar (μ.restrict Ω) := by
  have hp := ne_top_of_inv_add_inv_eq_inv hexp
  have hpstar0 : pstar ≠ 0 := (zero_lt_one.trans_le (one_le_of_inv_add_eq_inv hexp)).ne'
  rw [memLp_norm_rpow_restrict_iff hb hΩ hpstar0 hpstar,
    ← neg_finrank_lt_sub_one_mul_iff hpstar hexp]
  rcases eq_or_ne s 0 with rfl | hs0
  · -- The constant `‖x‖ ^ 0 = 1` lies in both spaces; the exponent condition is `p < n`.
    refine ⟨fun _ => ?_, fun hs => (exists_w1p_value_ae_eq_norm_rpow hp hb hs).imp fun _ h => h.1⟩
    rw [neg_finrank_lt_sub_one_mul_iff hpstar hexp, zero_mul, neg_lt_zero]
    exact_mod_cast Module.finrank_pos
  · exact exists_w1p_value_ae_eq_norm_rpow_iff hp hb hΩ hs0

/-- **The Sobolev exponent is sharp.** Let `1 ≤ p` and let `p⋆ < ∞` be the Sobolev exponent,
`1 / p⋆ + 1 / n = 1 / p`, so that `p < n`. On a bounded open neighbourhood `Ω` of the origin,
for every `q > p⋆` there is `u ∈ W^{1,p}(Ω)` which is not in `L^q(Ω)`: a norm power
`‖x‖ ^ (-n / r)` with `p⋆ < r ≤ q`. -/
theorem exists_w1p_not_memLp_value [Nontrivial E] (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (Module.finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (hb : Bornology.IsBounded (Ω : Set E)) (hΩ : (Ω : Set E) ∈ 𝓝 (0 : E)) {q : ℝ≥0∞}
    (hq : pstar < q) : ∃ u : W1p μ Ω p, ¬ MemLp (W1p.value u) q (μ.restrict Ω) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := by simp [n, Module.finrank_pos]
  have hp := ne_top_of_inv_add_inv_eq_inv hexp
  -- A finite exponent `r` with `p⋆ < r ≤ q`.
  set r : ℝ≥0∞ := min q (pstar + 1)
  have hrq : r ≤ q := min_le_left _ _
  have hr : pstar < r := lt_min hq (ENNReal.lt_add_right hpstar one_ne_zero)
  have hrtop : r ≠ ∞ := ((min_le_right _ _).trans_lt (ENNReal.add_lt_top.2
    ⟨hpstar.lt_top, ENNReal.one_lt_top⟩)).ne
  have hr0 : r ≠ 0 := (pos_of_gt hr).ne'
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0 hrtop
  have hpr : pstar.toReal < r.toReal := (ENNReal.toReal_lt_toReal hpstar hrtop).2 hr
  -- The norm power `‖x‖ ^ (-n / r)` is in `L^{p⋆}`, hence in `W^{1,p}`, but not in `L^r`.
  have hs : -n < -n / r.toReal * pstar.toReal := by
    rw [neg_div, neg_mul, neg_lt_neg_iff, div_mul_eq_mul_div, div_lt_iff₀ hrr]
    exact mul_lt_mul_of_pos_left hpr hn
  obtain ⟨u, hu, -⟩ := exists_w1p_value_ae_eq_norm_rpow (μ := μ) hp hb
    ((neg_finrank_lt_sub_one_mul_iff hpstar hexp).2 hs)
  refine ⟨u, fun hq' => ?_⟩
  have : IsFiniteMeasure (μ.restrict (Ω : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hmem := (hq'.ae_eq hu).mono_exponent hrq
  rw [memLp_norm_rpow_restrict_iff hb hΩ hr0 hrtop, div_mul_cancel₀ _ hrr.ne'] at hmem
  exact lt_irrefl _ hmem

end TauCeti
