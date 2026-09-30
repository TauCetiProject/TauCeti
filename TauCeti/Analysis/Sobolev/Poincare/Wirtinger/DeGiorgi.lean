/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
public import TauCeti.Analysis.Sobolev.W1p.LevelSet

/-!
# De Giorgi's isoperimetric inequality

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n`, and let `μ` be an additive Haar measure.  For `u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, and
levels `k < l`, this file proves **De Giorgi's isoperimetric inequality**

`(l - k) · |{u ≥ l}| · |{u ≤ k}| ≤ μ(B(0, 1)) · (diam Ω) ^ (n + 1) · ∫_{k < u < l} |∇u|`,

all sets being taken inside `Ω`.  On a ball of radius `R` the constant is
`μ(B(0, 1)) · (2R) ^ (n + 1)`; its value depends on the normalization of `μ`.

The inequality quantifies how a Sobolev function passes from low to high values: if both
`{u ≤ k}` and `{u ≥ l}` occupy a fixed proportion of `Ω`, then `∇u` carries a definite amount of
mass on the strip `{k < u < l}` in between.  This is the ingredient of De Giorgi's proof of
Hölder continuity for weak solutions of divergence-form equations with bounded measurable
coefficients that turns a lower bound on the measure of `{u ≤ k}` into a decay of the measure of
`{u ≥ l}` along a sequence of levels.  Only the `L¹` norm of `∇u` on the strip enters, which is
why the inequality is stated for every exponent `p` and proved at `p = 1`.

## Main declarations

* `TauCeti.W1p.sub_mul_measureReal_mul_measureReal_le_of_convex`: the inequality on a bounded
  convex domain.
* `TauCeti.W1p.sub_mul_measureReal_mul_measureReal_le_of_eq_ball`: the inequality on a ball of
  radius `R`, with constant `μ(B(0, 1)) (2R) ^ (n + 1)`.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* L. Caffarelli, A. Vasseur, *The De Giorgi method for regularity of solutions of elliptic
  equations and its applications to fluid dynamics*, Discrete Contin. Dyn. Syst. Ser. S (2010).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The double truncation `w = (u - k)⁺ - (u - l)⁺` of `u ∈ W^{1,p}(Ω)` at levels `k < l`, on a
domain of finite measure, as an element of `W^{1,1}(Ω)`: its weak gradient is `1_{k < u < l} ∇u`,
the level set `{u = l}` contributing nothing. -/
private theorem exists_w1p_one_truncation [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (u : W1p mu Omega p) {k l : ℝ} (hkl : k < l) :
    ∃ w : W1p mu Omega 1,
      (∀ᵐ x ∂mu.restrict Omega,
        W1p.value w x = max (W1p.value u x - k) 0 - max (W1p.value u x - l) 0) ∧
      ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient w x‖ₑ =
        {x | k < W1p.value u x ∧ W1p.value u x < l}.indicator
          (fun x ↦ ‖W1p.gradient u x‖ₑ) x := by
  set nu := mu.restrict (Omega : Set E)
  set v : W1p mu Omega 1 := W1p.ofExponentLE Fact.out u
  have hv : ⇑(W1p.value v) =ᵐ[nu] W1p.value u := W1p.value_ofExponentLE_ae _ u
  have hgv : ⇑(W1p.gradient v) =ᵐ[nu] W1p.gradient u := W1p.gradient_ofExponentLE_ae _ u
  have hmem : ∀ j : ℝ, MemLp (fun x ↦ max (W1p.value v x - j) 0) 1 nu := fun j ↦
    ((Lp.memLp (W1p.value v)).sub (memLp_const j)).pos_part
  set wk : W1p mu Omega 1 := W1p.posPartAboveOfMemLp ENNReal.one_ne_top k v (hmem k)
  set wl : W1p mu Omega 1 := W1p.posPartAboveOfMemLp ENNReal.one_ne_top l v (hmem l)
  refine ⟨wk - wl, ?_, ?_⟩
  · have hsub : ⇑(W1p.value (wk - wl)) =ᵐ[nu] ⇑(W1p.value wk) - ⇑(W1p.value wl) := by
      simpa only [← W1p.valueL_apply, map_sub] using Lp.coeFn_sub _ _
    filter_upwards [hsub, hv,
      W1p.value_posPartAboveOfMemLp_ae ENNReal.one_ne_top k v (hmem k),
      W1p.value_posPartAboveOfMemLp_ae ENNReal.one_ne_top l v (hmem l)] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h3, h4, h2]
  · have hsub : ⇑(W1p.gradient (wk - wl)) =ᵐ[nu]
        ⇑(W1p.gradient wk) - ⇑(W1p.gradient wl) := by
      simpa only [← W1p.gradientL_apply, map_sub] using Lp.coeFn_sub _ _
    filter_upwards [hsub, hv, hgv,
      W1p.gradient_posPartAboveOfMemLp_ae ENNReal.one_ne_top k v (hmem k),
      W1p.gradient_posPartAboveOfMemLp_ae ENNReal.one_ne_top l v (hmem l),
      W1p.gradient_ae_eq_zero_on_level_set ENNReal.one_ne_top v l] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.sub_apply, h4, h5]
    by_cases hk : k < W1p.value u x
    · by_cases hl : l < W1p.value u x
      · have : ¬ W1p.value u x < l := not_lt.2 hl.le
        simp [indicator, h2, hk, hl, this]
      · rcases (not_lt.1 hl).lt_or_eq with hlt | heq
        · simp [indicator, h2, h3, hk, hl, hlt]
        · -- On the level set `{u = l}` the weak gradient vanishes.
          have h0 : W1p.gradient v x = 0 := h6 (h2.trans heq)
          simp [indicator, h2, heq, h0]
    · have hl : ¬ l < W1p.value u x := fun h ↦ hk (hkl.trans h)
      simp [indicator, h2, hk, hl]

/-- **De Giorgi's isoperimetric inequality.**  Let `Ω` be a bounded convex open set in a
finite-dimensional real inner product space of dimension `n`, let `u ∈ W^{1,p}(Ω)` with
`1 ≤ p ≤ ∞`, and let `k < l`.  Then, all sets being taken inside `Ω`,

`(l - k) · |{u ≥ l}| · |{u ≤ k}| ≤ μ(B(0, 1)) · (diam Ω) ^ (n + 1) · ∫_{k < u < l} |∇u|`.

A function that is both `≤ k` and `≥ l` on sets of positive measure must have a weak gradient
of definite `L¹` mass on the strip `{k < u < l}`. -/
theorem W1p.sub_mul_measureReal_mul_measureReal_le_of_convex
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (u : W1p mu Omega p) {k l : ℝ} (hkl : k < l) :
    (l - k) * (mu.restrict Omega).real {x | l ≤ W1p.value u x} *
        (mu.restrict Omega).real {x | W1p.value u x ≤ k} ≤
      mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) *
        ∫ x in {x | k < W1p.value u x ∧ W1p.value u x < l}, ‖W1p.gradient u x‖
          ∂mu.restrict Omega := by
  have hfin : IsFiniteMeasure (mu.restrict (Omega : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  set nu := mu.restrict (Omega : Set E) with hnu
  set K : ℝ := mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) with hK
  set I : ℝ := ∫ x in {x | k < W1p.value u x ∧ W1p.value u x < l}, ‖W1p.gradient u x‖ ∂nu
    with hI
  have hK0 : 0 ≤ K := by positivity
  have hI0 : 0 ≤ I := integral_nonneg fun x ↦ norm_nonneg _
  -- The sets involved are measurable, as `W1p.value u` has a measurable representative.
  have hm : Measurable (W1p.value u) :=
    (W1p.value u : E →ₘ[nu] ℝ).stronglyMeasurable.measurable
  have hA : MeasurableSet {x | l ≤ W1p.value u x} := measurableSet_le measurable_const hm
  have hB : MeasurableSet {x | W1p.value u x ≤ k} := measurableSet_le hm measurable_const
  have hC : MeasurableSet {x | k < W1p.value u x ∧ W1p.value u x < l} :=
    (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  -- The double truncation `w = (u - k)⁺ - (u - l)⁺`, as an element of `W^{1,1}(Ω)`.
  obtain ⟨w, hwval, hwgrad⟩ := exists_w1p_one_truncation u hkl
  -- The mean of `w` over `{u ≤ k}` is zero, since `w` vanishes there.
  set S : Set E := {x | W1p.value u x ≤ k} ∩ (Omega : Set E)
  have hS : mu.real S = nu.real {x | W1p.value u x ≤ k} := by
    rw [measureReal_def, measureReal_def, hnu, Measure.restrict_apply hB]
  have havg : (⨍ y in S, W1p.value w y ∂mu) = 0 := by
    have hzero : ∀ᵐ x ∂mu.restrict S, W1p.value w x = 0 := by
      rw [← Measure.restrict_restrict hB]
      refine (ae_restrict_iff' hB).2 ?_
      filter_upwards [hwval] with x hx hxS
      have hl : W1p.value u x - l ≤ 0 := by linarith [hxS]
      rw [hx, max_eq_right (sub_nonpos.2 hxS), max_eq_right hl, sub_zero]
    rw [average_congr hzero, average_zero]
  rcases eq_or_ne (mu S) 0 with hS0 | hS0
  · -- If `{u ≤ k}` is null, the left side vanishes.
    have : mu.real S = 0 := by simp [measureReal_def, hS0]
    rw [← hS, this, mul_zero]
    exact mul_nonneg hK0 hI0
  -- The Poincaré–Wirtinger inequality for `w`, with the mean over `{u ≤ k}`.
  have hPW : eLpNorm (W1p.value w) 1 nu ≤
      ENNReal.ofReal (K / mu.real S) * ‖W1p.gradient w‖ₑ := by
    have h := W1p.eLpNorm_value_sub_setAverage_le_of_convex (S := S) ENNReal.one_ne_top hconv hb
      (hB.inter Omega.isOpen.measurableSet).nullMeasurableSet inter_subset_right hS0 w
    rw [havg] at h
    simpa only [sub_zero] using h
  -- Its left side is at least `(l - k) |{u ≥ l}|`.
  have hlower : ENNReal.ofReal (l - k) * nu {x | l ≤ W1p.value u x} ≤
      eLpNorm (W1p.value w) 1 nu := by
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
      ← lintegral_indicator_const hA]
    refine lintegral_mono_ae ?_
    filter_upwards [hwval] with x hx
    by_cases hxA : l ≤ W1p.value u x
    · rw [indicator_of_mem (s := {x | l ≤ W1p.value u x}) hxA, hx, max_eq_left (by linarith),
        max_eq_left (by linarith), Real.enorm_eq_ofReal (by linarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [indicator_of_notMem (s := {x | l ≤ W1p.value u x}) hxA]
      exact zero_le
  -- Its right side is `∫_{k < u < l} |∇u|`.
  have hupper : ‖W1p.gradient w‖ₑ = ENNReal.ofReal I := by
    rw [Lp.enorm_def, eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
      lintegral_congr_ae hwgrad,
      lintegral_indicator hC, hI, ofReal_integral_norm_eq_lintegral_enorm]
    exact ((Lp.memLp (W1p.gradient u)).integrable Fact.out).integrableOn
  have hkey := hlower.trans (hPW.trans_eq (by rw [hupper]))
  -- Clear the denominator `|{u ≤ k}|`.
  have hSpos : 0 < mu.real S := ENNReal.toReal_pos hS0 (measure_ne_top_of_subset
    inter_subset_right hb.measure_lt_top.ne)
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hkey
  rw [← hS]
  calc (l - k) * nu.real {x | l ≤ W1p.value u x} * mu.real S
      ≤ K / mu.real S * I * mu.real S := by gcongr
    _ = K * I := by field_simp

/-- **De Giorgi's isoperimetric inequality on a ball.**  For `u ∈ W^{1,p}(B(c, R))`,
`1 ≤ p ≤ ∞`, and levels `k < l`, all sets being taken inside the ball,

`(l - k) · |{u ≥ l}| · |{u ≤ k}| ≤ μ(B(0, 1)) · (2R) ^ (n + 1) · ∫_{k < u < l} |∇u|`.

The power `R ^ (n + 1)` is the one forced by scaling. -/
theorem W1p.sub_mul_measureReal_mul_measureReal_le_of_eq_ball {c : E} {R : ℝ} (hR : 0 ≤ R)
    (hOmega : (Omega : Set E) = ball c R) (u : W1p mu Omega p) {k l : ℝ} (hkl : k < l) :
    (l - k) * (mu.restrict Omega).real {x | l ≤ W1p.value u x} *
        (mu.restrict Omega).real {x | W1p.value u x ≤ k} ≤
      mu.real (ball 0 1) * (2 * R) ^ (finrank ℝ E + 1) *
        ∫ x in {x | k < W1p.value u x ∧ W1p.value u x < l}, ‖W1p.gradient u x‖
          ∂mu.restrict Omega := by
  refine (W1p.sub_mul_measureReal_mul_measureReal_le_of_convex (hOmega ▸ convex_ball c R)
    (hOmega ▸ isBounded_ball) u hkl).trans ?_
  have hI0 : 0 ≤ ∫ x in {x | k < W1p.value u x ∧ W1p.value u x < l}, ‖W1p.gradient u x‖
      ∂mu.restrict Omega := integral_nonneg fun x ↦ norm_nonneg _
  gcongr
  rw [hOmega]
  exact diam_ball hR

end TauCeti
