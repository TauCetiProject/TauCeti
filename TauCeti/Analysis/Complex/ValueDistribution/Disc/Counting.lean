/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Meromorphic.Divisor

/-!
# The disc-local Nevanlinna pole-counting function

Mathlib's `ValueDistribution.logCounting f ⊤` defines the logarithmic pole-counting function via
`(MeromorphicOn.divisor f Set.univ)⁻.logCounting`, which evaluates to zero unless `f` is globally
meromorphic on the entire field (`Meromorphic f`). Functions meromorphic only on an open disc such
as `ball (0 : ℂ) 1`—for instance universal covering maps or functions with accumulating poles or
natural boundaries on `sphere 0 1`—are meromorphic on every compact subdisc `closedBall 0 r`
(`r < 1`) without admitting a global meromorphic extension.

This file defines `TauCeti.discCounting f r` directly from the compact-subdisc pole divisor
`(MeromorphicOn.divisor f (closedBall 0 r))⁻`:
`discCounting f r = (∑ᶠ z, D_r(z) * log (r * ‖z‖⁻¹)) + D_r(0) * log r`,
where `D_r = (MeromorphicOn.divisor f (closedBall 0 r))⁻`. Because `Real.log 0 = 0`, the `finsum`
summand at `z = 0` vanishes and the separate `D_r(0) * log r` term restores the pole weight at the
origin, while poles on the boundary circle `sphere 0 r` (`r > 0`) contribute `log (r * r⁻¹) = 0`.

## Main definitions and results

* `TauCeti.discCounting`: the disc-local Nevanlinna pole-counting function.
* `MeromorphicOn.discCounting_eq_finsum_divisor_ball`: for `0 < r`, `discCounting f r` depends only
  on the open-ball pole divisor `(MeromorphicOn.divisor f (ball 0 r))⁻`; boundary poles on
  `sphere 0 r` have weight zero.
* `Meromorphic.discCounting_eq_logCounting_top`: for globally meromorphic `f` and `0 ≤ r`,
  `discCounting f r = ValueDistribution.logCounting f ⊤ r`.
* `Filter.EventuallyEq.discCounting_eq` and `MeromorphicOn.discCounting_congr_codiscreteWithin`:
  local congruence for functions agreeing near `closedBall 0 r` or away from a discrete subset of
  `ball 0 r`.
* `MeromorphicOn.discCounting_pow` and `MeromorphicOn.discCounting_add_analyticOnNhd`: power scaling
  `discCounting (f ^ n) r = n * discCounting f r` and invariance under adding an analytic function.
* `MeromorphicOn.discCounting_mono`: radial monotonicity of `discCounting f` on `(0, R]`.
* `TauCeti.discCounting_nonneg_of_meromorphicOrderAt_nonneg`: nonnegativity `0 ≤ discCounting f r`
  whenever `0 ≤ meromorphicOrderAt f 0` (including infinite order `⊤`).
* `MeromorphicOn.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg`,
  `MeromorphicOn.discCounting_eq_zero_iff_exists_analyticAt`,
  `MeromorphicOn.discCounting_eq_zero_iff_analyticOnNhd_of_continuousAt`, and
  `MeromorphicNFOn.discCounting_eq_zero_iff_analyticOnNhd`: vanishing criteria for `discCounting`.
* `MeromorphicOn.circleAverage_log_norm_eq_discCounting_inv_sub`: the disc-local Jensen identity
  `circleAverage (log ‖f ·‖) 0 r = discCounting f⁻¹ r - discCounting f r + log ‖c(f, 0)‖`.

## Implementation notes

The definition of `TauCeti.discCounting` and its comparison and monotonicity properties mirror
`Function.locallyFinsuppWithin.logCounting` and `ValueDistribution.logCounting` in
`Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic` by Stefan Kebekus, replacing the
whole-space divisor `MeromorphicOn.divisor f Set.univ` with the compact-subdisc divisor
`MeromorphicOn.divisor f (closedBall 0 r)`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  **38** (2025), 627–702, §6.1.1 and Lemma 6.1.2.
* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.1.
-/

public section

open Filter Function Metric Real Set
open scoped Topology

section NormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace TauCeti

/-- The disc-local Nevanlinna pole-counting function on `closedBall 0 r`:
`(∑ᶠ z, D_r(z) * log (r * ‖z‖⁻¹)) + D_r(0) * log r`, where
`D_r = (MeromorphicOn.divisor f (closedBall 0 r))⁻` is the pole divisor of `f` on `closedBall 0 r`.
Totalization of `Real.log` at `0` makes the `z = 0` summand in `∑ᶠ` vanish, and the explicit centre
term restores the pole multiplicity at `0` weighted by `log r`. -/
noncomputable def discCounting (f : 𝕜 → E) (r : ℝ) : ℝ :=
  (∑ᶠ z, (((MeromorphicOn.divisor f (closedBall 0 r))⁻ z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹)) +
    (((MeromorphicOn.divisor f (closedBall 0 r))⁻ 0 : ℤ) : ℝ) * Real.log r

theorem discCounting_def (f : 𝕜 → E) (r : ℝ) :
    discCounting f r =
      (∑ᶠ z, (((MeromorphicOn.divisor f (closedBall 0 r))⁻ z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹)) +
        (((MeromorphicOn.divisor f (closedBall 0 r))⁻ 0 : ℤ) : ℝ) * Real.log r := by
  rfl

/-- Unfolding `discCounting` in terms of `max 0 (-MeromorphicOn.divisor f (closedBall 0 r) z)`. -/
theorem discCounting_eq_finsum_max (f : 𝕜 → E) (r : ℝ) :
    discCounting f r =
      (∑ᶠ z, ((max 0 (-MeromorphicOn.divisor f (closedBall 0 r) z) : ℤ) : ℝ) *
          Real.log (r * ‖z‖⁻¹)) +
        ((max 0 (-MeromorphicOn.divisor f (closedBall 0 r) 0) : ℤ) : ℝ) * Real.log r := by
  rw [discCounting_def]
  simp_rw [Function.locallyFinsuppWithin.negPart_apply, negPart_def, sup_comm]

/-- If `f` is not meromorphic on `closedBall 0 r`, its local divisor and `discCounting f r` vanish
by totalization. -/
theorem discCounting_of_not_meromorphicOn {f : 𝕜 → E} {r : ℝ}
    (hf : ¬MeromorphicOn f (closedBall 0 r)) :
    discCounting f r = 0 := by
  have hd : MeromorphicOn.divisor f (closedBall 0 r) = 0 := by
    ext z
    exact MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hf
  simp [discCounting_def, hd]

@[simp]
theorem discCounting_eval_zero (f : 𝕜 → E) : discCounting f 0 = 0 := by
  simp [discCounting_def]

/-- For nonpositive radii `r ≤ 0`, `discCounting f r = 0` (`closedBall 0 r` is empty for `r < 0`,
and `Real.log 0 = 0` at `r = 0`). -/
theorem discCounting_of_nonpos (f : 𝕜 → E) {r : ℝ} (hr : r ≤ 0) : discCounting f r = 0 := by
  rcases hr.lt_or_eq with hlt | rfl
  · have hd : MeromorphicOn.divisor f (closedBall 0 r) = 0 := by
      ext z
      simp [closedBall_eq_empty.2 hlt]
    simp [discCounting_def, hd]
  · exact discCounting_eval_zero f

@[simp]
theorem discCounting_const (c : E) : discCounting (fun _ : 𝕜 ↦ c) = 0 := by
  ext r
  simp [discCounting_def]

@[simp]
theorem discCounting_const_zero : discCounting (0 : 𝕜 → E) = 0 :=
  discCounting_const 0

@[to_fun (attr := simp) discCounting_fun_const_smul]
theorem discCounting_const_smul {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    discCounting (s • f) = discCounting f := by
  ext r
  simp [discCounting_def, MeromorphicOn.divisor_const_smul hs]

theorem discCounting_one_div (f : 𝕜 → 𝕜) :
    discCounting (fun z ↦ 1 / f z) = discCounting f⁻¹ := by
  simp only [one_div]
  rfl

/-- For `1 ≤ r`, `discCounting f r` is nonnegative without any centre or meromorphicity
hypothesis. -/
theorem discCounting_nonneg_of_one_le {r : ℝ} (hr : 1 ≤ r) (f : 𝕜 → E) :
    0 ≤ discCounting f r := by
  rw [discCounting_def]
  refine add_nonneg (finsum_nonneg fun z ↦ ?_)
    (mul_nonneg (Int.cast_nonneg (negPart_nonneg _)) (Real.log_nonneg hr))
  by_cases hz0 : z = 0
  · simp [hz0]
  by_cases hzb : z ∈ closedBall (0 : 𝕜) r
  · refine mul_nonneg (Int.cast_nonneg (negPart_nonneg _)) (Real.log_nonneg ?_)
    rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.2 hz0)]
    simpa only [mem_closedBall_zero_iff] using hzb
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb]

/-- Pole-counting positivity at a regular centre (Calegari–Dimitrov–Tang, Lemma 6.1.2): if the
meromorphic germ of `f` at `0` has no pole (`0 ≤ meromorphicOrderAt f 0`, including infinite order
`⊤`), then `0 ≤ discCounting f r` for every `r : ℝ`. The centre value `f 0` itself is immaterial. -/
theorem discCounting_nonneg_of_meromorphicOrderAt_nonneg {f : 𝕜 → E}
    (h0 : 0 ≤ meromorphicOrderAt f 0) (r : ℝ) :
    0 ≤ discCounting f r := by
  by_cases hr : r ≤ 0
  · rw [discCounting_of_nonpos f hr]
  push Not at hr
  by_cases hf : MeromorphicOn f (closedBall 0 r)
  swap
  · rw [discCounting_of_not_meromorphicOn hf]
  have hD0 : (MeromorphicOn.divisor f (closedBall 0 r))⁻ 0 = 0 := by
    rw [Function.locallyFinsuppWithin.negPart_apply, negPart_eq_zero,
      hf.divisor_apply (mem_closedBall_self hr.le)]
    cases ho : meromorphicOrderAt f 0 with
    | top => simp
    | coe n =>
      rw [ho] at h0
      simpa using h0
  rw [discCounting_def, hD0, Int.cast_zero, zero_mul, add_zero]
  refine finsum_nonneg fun z ↦ ?_
  by_cases hz0 : z = 0
  · simp [hz0]
  by_cases hzb : z ∈ closedBall (0 : 𝕜) r
  · refine mul_nonneg (Int.cast_nonneg (negPart_nonneg _)) (Real.log_nonneg ?_)
    rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.2 hz0)]
    simpa only [mem_closedBall_zero_iff] using hzb
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb]

/-- At `f = (·⁻¹)`, the single simple pole at the origin gives `discCounting (·⁻¹) r = log r` for
all `0 < r`. -/
@[simp]
theorem discCounting_inv_id {r : ℝ} (hr : 0 < r) :
    discCounting (fun z : 𝕜 ↦ z⁻¹) r = Real.log r := by
  have hid0 : MeromorphicOn.divisor (fun z : 𝕜 ↦ z) (closedBall 0 r) 0 = 1 := by
    simpa only [sub_zero] using
      MeromorphicOn.divisor_sub_const_self (z₀ := (0 : 𝕜)) (mem_closedBall_self hr.le)
  have h0 : (MeromorphicOn.divisor (fun z : 𝕜 ↦ z⁻¹) (closedBall 0 r))⁻ 0 = 1 := by
    rw [Function.locallyFinsuppWithin.negPart_apply, MeromorphicOn.divisor_fun_inv,
      Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, hid0]
    rfl
  rw [discCounting_def, h0, Int.cast_one, one_mul]
  suffices (∑ᶠ z : 𝕜,
      (((MeromorphicOn.divisor (fun z : 𝕜 ↦ z⁻¹) (closedBall 0 r))⁻ z : ℤ) : ℝ) *
        Real.log (r * ‖z‖⁻¹)) = 0 by
    rw [this, zero_add]
  refine finsum_eq_zero_of_forall_eq_zero fun z ↦ ?_
  by_cases hz0 : z = 0
  · simp [hz0]
  · have ha : AnalyticAt 𝕜 (fun w : 𝕜 ↦ w⁻¹) z := analyticAt_id.inv hz0
    have hdiv : MeromorphicOn.divisor (fun w : 𝕜 ↦ w⁻¹) (closedBall 0 r) z = 0 :=
      ha.divisor_apply_eq_zero (inv_ne_zero hz0)
    simp [Function.locallyFinsuppWithin.negPart_apply, hdiv]

/-- Functions with identical punctured germs at every point of `closedBall 0 r` have equal
`discCounting` at radius `r`. No meromorphicity or global extension hypothesis is required. -/
theorem discCounting_congr_nhdsNE {f g : 𝕜 → E} {r : ℝ}
    (hfg : ∀ z ∈ closedBall 0 r, f =ᶠ[𝓝[≠] z] g) :
    discCounting f r = discCounting g r := by
  simp only [discCounting_def, MeromorphicOn.divisor_congr_nhdsNE hfg]

end TauCeti

open TauCeti

/-- Functions equal on a neighbourhood of `closedBall 0 r` have equal `discCounting` at radius `r`.
No global extension or meromorphicity hypothesis is required. -/
theorem Filter.EventuallyEq.discCounting_eq {f g : 𝕜 → E} {r : ℝ}
    (hfg : f =ᶠ[𝓝ˢ (closedBall 0 r)] g) :
    discCounting f r = discCounting g r := by
  simp only [discCounting_def, hfg.divisor_eq]

namespace MeromorphicOn

variable {f g : 𝕜 → E} {r R : ℝ}

/-- Open-ball support formula for `discCounting`: when `0 < r` and `f` is meromorphic on
`closedBall 0 r`, poles on the boundary circle `sphere 0 r` satisfy `log (r * ‖z‖⁻¹) = log 1 = 0`,
so `discCounting f r` depends only on `(MeromorphicOn.divisor f (ball 0 r))⁻`. -/
theorem discCounting_eq_finsum_divisor_ball (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) :
    discCounting f r =
      (∑ᶠ z, (((divisor f (ball 0 r))⁻ z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹)) +
        (((divisor f (ball 0 r))⁻ 0 : ℤ) : ℝ) * Real.log r := by
  have hball : MeromorphicOn f (ball 0 r) := hf.mono_set ball_subset_closedBall
  rw [discCounting_def]
  congr 1
  · refine finsum_congr fun z ↦ ?_
    by_cases hzb : z ∈ ball (0 : 𝕜) r
    · rw [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.negPart_apply,
        hf.divisor_apply (ball_subset_closedBall hzb), hball.divisor_apply hzb]
    · have h0 : (divisor f (ball 0 r))⁻ z = 0 :=
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb
      rw [h0, Int.cast_zero, zero_mul]
      by_cases hzc : z ∈ closedBall (0 : 𝕜) r
      · have hnorm : ‖z‖ = r := le_antisymm (mem_closedBall_zero_iff.1 hzc)
          (not_lt.1 (mt mem_ball_zero_iff.2 hzb))
        rw [hnorm, mul_inv_cancel₀ hr.ne', Real.log_one, mul_zero]
      · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzc]
  · rw [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.negPart_apply,
      hf.divisor_apply (mem_closedBall_self hr.le), hball.divisor_apply (mem_ball_self hr)]

/-- Explicit open-punctured-disc order sum for `discCounting`: for `0 < r` and `f` meromorphic on
`closedBall 0 r`,
`discCounting f r = ∑ᶠ_{0 < ‖z‖ < r} ord⁻_z(f) * log (r / ‖z‖) + ord⁻_0(f) * log r`. -/
theorem discCounting_eq_finsum_punctured_ball (hf : MeromorphicOn f (closedBall 0 r))
    (hr : 0 < r) :
    discCounting f r =
      (∑ᶠ z ∈ ball (0 : 𝕜) r \ {0},
          (((-(meromorphicOrderAt f z).untop₀) ⊔ 0 : ℤ) : ℝ) * Real.log (r / ‖z‖)) +
        (((-(meromorphicOrderAt f 0).untop₀) ⊔ 0 : ℤ) : ℝ) * Real.log r := by
  have hball : MeromorphicOn f (ball 0 r) := hf.mono_set ball_subset_closedBall
  rw [hf.discCounting_eq_finsum_divisor_ball hr, finsum_mem_def]
  congr 1
  · refine finsum_congr fun z ↦ ?_
    by_cases hz0 : z = 0
    · simp [hz0]
    by_cases hzb : z ∈ ball (0 : 𝕜) r
    · have hmem : z ∈ ball (0 : 𝕜) r \ {0} := ⟨hzb, hz0⟩
      simp [hmem, hball.divisor_apply hzb, negPart_def, div_eq_mul_inv]
    · have hnot : z ∉ ball (0 : 𝕜) r \ {0} := fun h ↦ hzb h.1
      simp [hnot, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb]
  · simp [hball.divisor_apply (mem_ball_self hr), negPart_def]

/-- If `f` is meromorphic on `closedBall 0 r` and analytic on the open disc `ball 0 r`, then
`discCounting f r = 0` even if `f` has poles on `sphere 0 r`. -/
theorem discCounting_eq_zero_of_analyticOnNhd_ball (hf : MeromorphicOn f (closedBall 0 r))
    (ha : AnalyticOnNhd 𝕜 f (ball 0 r)) :
    discCounting f r = 0 := by
  by_cases hr : r ≤ 0
  · exact discCounting_of_nonpos f hr
  push Not at hr
  have hneg : (divisor f (ball 0 r))⁻ = 0 := by
    ext z
    simpa [Function.locallyFinsuppWithin.negPart_apply, negPart_eq_zero] using
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha z
  rw [hf.discCounting_eq_finsum_divisor_ball hr, hneg]
  simp

/-- If `f` and `g` are meromorphic on `closedBall 0 r` and agree away from a discrete subset of
`ball 0 r`, then `discCounting f r = discCounting g r`. -/
theorem discCounting_congr_codiscreteWithin (hf : MeromorphicOn f (closedBall 0 r))
    (hg : MeromorphicOn g (closedBall 0 r)) (hfg : f =ᶠ[codiscreteWithin (ball 0 r)] g) :
    discCounting f r = discCounting g r := by
  by_cases hr : r ≤ 0
  · rw [discCounting_of_nonpos f hr, discCounting_of_nonpos g hr]
  push Not at hr
  rw [hf.discCounting_eq_finsum_divisor_ball hr, hg.discCounting_eq_finsum_divisor_ball hr,
    divisor_congr_codiscreteWithin hfg isOpen_ball]

/-- Adding a function analytic on `closedBall 0 r` does not change `discCounting`. -/
@[to_fun discCounting_fun_add_analyticOnNhd]
theorem discCounting_add_analyticOnNhd (hf : MeromorphicOn f (closedBall 0 r))
    (hg : AnalyticOnNhd 𝕜 g (closedBall 0 r)) :
    discCounting (f + g) r = discCounting f r := by
  simp only [discCounting_def, hf.negPart_divisor_add_of_analyticNhdOn_right hg]

@[simp]
theorem discCounting_add_const (hf : MeromorphicOn f (closedBall 0 r)) (a : E) :
    discCounting (f + fun _ ↦ a) r = discCounting f r :=
  hf.discCounting_add_analyticOnNhd analyticOnNhd_const

@[simp]
theorem discCounting_fun_add_const (hf : MeromorphicOn f (closedBall 0 r)) (a : E) :
    discCounting (fun z ↦ f z + a) r = discCounting f r :=
  hf.discCounting_add_const a

@[simp]
theorem discCounting_sub_const (hf : MeromorphicOn f (closedBall 0 r)) (a : E) :
    discCounting (f - fun _ ↦ a) r = discCounting f r := by
  rw [sub_eq_add_neg]
  exact hf.discCounting_add_analyticOnNhd analyticOnNhd_const.neg

@[simp]
theorem discCounting_fun_sub_const (hf : MeromorphicOn f (closedBall 0 r)) (a : E) :
    discCounting (fun z ↦ f z - a) r = discCounting f r :=
  hf.discCounting_sub_const a

/-- Power scaling of the local pole count: for `f : 𝕜 → 𝕜` meromorphic on `closedBall 0 r` and
`n : ℕ`, `discCounting (f ^ n) r = n * discCounting f r`. -/
@[to_fun discCounting_fun_pow]
theorem discCounting_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f (closedBall 0 r)) (n : ℕ) :
    discCounting (f ^ n) r = n * discCounting f r := by
  rw [discCounting_def, discCounting_def, hf.divisor_pow n,
    Function.locallyFinsuppWithin.nsmul_negPart, mul_add, mul_finsum]
  simp [mul_assoc]

/-- Radial monotonicity of `discCounting`: for `0 < r₁ ≤ r₂` and `f` meromorphic on
`closedBall 0 r₂` over a proper normed field, `discCounting f r₁ ≤ discCounting f r₂`. -/
theorem discCounting_mono [ProperSpace 𝕜] {r₁ r₂ : ℝ} (hf : MeromorphicOn f (closedBall 0 r₂))
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) :
    discCounting f r₁ ≤ discCounting f r₂ := by
  have hsub : closedBall (0 : 𝕜) r₁ ⊆ closedBall 0 r₂ := closedBall_subset_closedBall hr₁₂
  set D₂ := (divisor f (closedBall 0 r₂))⁻
  have hD₁ : (divisor f (closedBall 0 r₁))⁻ = D₂.restrict hsub := by
    rw [← hf.divisor_restrict hsub, Function.locallyFinsuppWithin.restrict_negPart]
  have hs : D₂.support.Finite := D₂.finiteSupport (isCompact_closedBall 0 r₂)
  rw [discCounting_def, discCounting_def, hD₁]
  have hsupp₁ :
      (fun z ↦ (((D₂.restrict hsub) z : ℤ) : ℝ) * Real.log (r₁ * ‖z‖⁻¹)).support ⊆ hs.toFinset := by
    intro z hz
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hz
    by_cases hzb : z ∈ closedBall (0 : 𝕜) r₁
    · simp [Function.locallyFinsuppWithin.restrict_apply, hzb, h0]
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb]
  have hsupp₂ :
      (fun z ↦ ((D₂ z : ℤ) : ℝ) * Real.log (r₂ * ‖z‖⁻¹)).support ⊆ hs.toFinset := by
    intro z hz
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    exact hz (by simp [h0])
  rw [finsum_eq_sum_of_support_subset _ hsupp₁, finsum_eq_sum_of_support_subset _ hsupp₂]
  refine add_le_add (Finset.sum_le_sum fun z hz ↦ ?_) ?_
  · by_cases hz0 : z = 0
    · simp [hz0]
    by_cases hzb : z ∈ closedBall (0 : 𝕜) r₁
    · rw [Function.locallyFinsuppWithin.restrict_apply, ite_eq_left hzb]
      refine mul_le_mul_of_nonneg_left ?_ (Int.cast_nonneg (negPart_nonneg _))
      exact Real.log_le_log (mul_pos hr₁ (inv_pos.2 (norm_pos_iff.2 hz0)))
        (mul_le_mul_of_nonneg_right hr₁₂ (inv_nonneg.2 (norm_nonneg z)))
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb, Int.cast_zero, zero_mul]
      have hzc : z ∈ closedBall (0 : 𝕜) r₂ := D₂.supportWithinDomain (hs.mem_toFinset.1 hz)
      refine mul_nonneg (Int.cast_nonneg (negPart_nonneg _)) (Real.log_nonneg ?_)
      rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.2 hz0)]
      simpa only [mem_closedBall_zero_iff] using hzc
  · rw [Function.locallyFinsuppWithin.restrict_apply, ite_eq_left (mem_closedBall_self hr₁.le)]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hr₁ hr₁₂)
      (Int.cast_nonneg (negPart_nonneg _))

/-- If `f` is meromorphic on `closedBall 0 R`, then `discCounting f` is monotone on `Ioc 0 R`. -/
theorem monotoneOn_discCounting_Ioc [ProperSpace 𝕜] (hf : MeromorphicOn f (closedBall 0 R)) :
    MonotoneOn (discCounting f) (Ioc 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hf.mono_set (closedBall_subset_closedBall hr₂.2)).discCounting_mono hr₁.1 hr₁₂

/-- If `f` is meromorphic on `ball 0 R`, then `discCounting f` is monotone on `Ioo 0 R`. -/
theorem monotoneOn_discCounting_Ioo [ProperSpace 𝕜] (hf : MeromorphicOn f (ball 0 R)) :
    MonotoneOn (discCounting f) (Ioo 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hf.mono_set (closedBall_subset_ball hr₂.2)).discCounting_mono hr₁.1 hr₁₂

/-- Vanishing of the local pole count (Calegari–Dimitrov–Tang, Lemma 6.1.2): for `0 < r` and `f`
meromorphic on `closedBall 0 r` with `0 ≤ meromorphicOrderAt f 0`, `discCounting f r = 0` iff every
point of the open disc `ball 0 r` has nonnegative meromorphic order. Poles on `sphere 0 r` are
permitted and carry zero weight. -/
theorem discCounting_eq_zero_iff_meromorphicOrderAt_nonneg [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔ ∀ z ∈ ball 0 r, 0 ≤ meromorphicOrderAt f z := by
  have hball : MeromorphicOn f (ball 0 r) := hf.mono_set ball_subset_closedBall
  have hD0 : (divisor f (ball 0 r))⁻ 0 = 0 := by
    rw [Function.locallyFinsuppWithin.negPart_apply, negPart_eq_zero,
      hball.divisor_apply (mem_ball_self hr)]
    cases ho : meromorphicOrderAt f 0 with
    | top => simp
    | coe n =>
      rw [ho] at h0
      simpa using h0
  rw [hf.discCounting_eq_finsum_divisor_ball hr, hD0, Int.cast_zero, zero_mul, add_zero]
  set D := (divisor f (ball 0 r))⁻
  have hs : D.support.Finite :=
    hf.divisor_ball_support_finite.subset fun z hz ↦ by
      simp only [Function.mem_support, ne_eq] at hz ⊢
      intro hdiv
      exact hz (by simp [D, hdiv])
  have hsupp :
      (fun z ↦ ((D z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹)).support ⊆ hs.toFinset := by
    intro z hz
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hDz
    exact hz (by simp [hDz])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hterm_nonneg :
      ∀ z ∈ hs.toFinset, 0 ≤ ((D z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹) := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    have hzb : z ∈ ball (0 : 𝕜) r := D.supportWithinDomain (hs.mem_toFinset.1 hz)
    refine mul_nonneg (Int.cast_nonneg (negPart_nonneg _)) (Real.log_nonneg ?_)
    rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.2 hz0)]
    exact (mem_ball_zero_iff.1 hzb).le
  rw [Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg]
  refine ⟨fun hsum z hz ↦ ?_, fun hord z _ ↦ ?_⟩
  · by_cases hz0 : z = 0
    · exact hz0 ▸ h0
    have hlog_pos : 0 < Real.log (r * ‖z‖⁻¹) := by
      refine Real.log_pos ?_
      rw [← div_eq_mul_inv, one_lt_div (norm_pos_iff.2 hz0)]
      exact mem_ball_zero_iff.1 hz
    have hDz : D z = 0 := by
      by_contra hne
      have hzero := hsum z (hs.mem_toFinset.2 hne)
      rcases mul_eq_zero.1 hzero with hD | hL
      · exact hne (Int.cast_eq_zero.1 hD)
      · exact hlog_pos.ne' hL
    have hdiv_nonneg : 0 ≤ divisor f (ball 0 r) z :=
      negPart_eq_zero.1 (by simpa [D] using hDz)
    rw [hball.divisor_apply hz] at hdiv_nonneg
    cases ho : meromorphicOrderAt f z with
    | top => exact le_top
    | coe n =>
      rw [ho] at hdiv_nonneg
      simpa using hdiv_nonneg
  · by_cases hzb : z ∈ ball (0 : 𝕜) r
    · have hDz : D z = 0 := by
        rw [Function.locallyFinsuppWithin.negPart_apply, negPart_eq_zero, hball.divisor_apply hzb]
        cases ho : meromorphicOrderAt f z with
        | top => simp
        | coe n =>
          have hn := hord z hzb
          rw [ho] at hn
          simpa using hn
      simp [hDz]
    · simp [D, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb]

/-- Removable-germ vanishing criterion: under `0 < r`, `MeromorphicOn f (closedBall 0 r)`, and
`0 ≤ meromorphicOrderAt f 0`, `discCounting f r = 0` iff every punctured germ of `f` on `ball 0 r`
admits an analytic extension across the puncture. -/
theorem discCounting_eq_zero_iff_exists_analyticAt [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔
      ∀ z ∈ ball 0 r, ∃ g : 𝕜 → E, AnalyticAt 𝕜 g z ∧ f =ᶠ[𝓝[≠] z] g := by
  rw [hf.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg hr h0]
  exact forall₂_congr fun z hz ↦ (hf z (ball_subset_closedBall hz)).meromorphicOrderAt_nonneg_iff

/-- Pointwise holomorphy criterion on `ball 0 r` when removable singularities have been filled in:
if `f` is continuous at every point of `ball 0 r` where `0 ≤ meromorphicOrderAt f z` (note that
assuming `ContinuousOn f (ball 0 r)` into the normed space `E` outright would already exclude poles
by `MeromorphicAt.analyticAt`), then `discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r)`. -/
theorem discCounting_eq_zero_iff_analyticOnNhd_of_continuousAt [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) (h0 : 0 ≤ meromorphicOrderAt f 0)
    (hrem : ∀ z ∈ ball 0 r, 0 ≤ meromorphicOrderAt f z → ContinuousAt f z) :
    discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r) := by
  rw [hf.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg hr h0]
  exact ⟨fun h z hz ↦ (hf z (ball_subset_closedBall hz)).analyticAt (hrem z hz (h z hz)),
    fun h z hz ↦ (h z hz).meromorphicOrderAt_nonneg⟩

end MeromorphicOn

/-- For a function in meromorphic normal form on `ball 0 r` (so poles take value `0` and removable
singularities match their analytic extensions) that is meromorphic on `closedBall 0 r` with
`0 ≤ meromorphicOrderAt f 0` and `0 < r`, `discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r)`. -/
theorem MeromorphicNFOn.discCounting_eq_zero_iff_analyticOnNhd [ProperSpace 𝕜] {f : 𝕜 → E} {r : ℝ}
    (hnf : MeromorphicNFOn f (ball 0 r)) (hf : MeromorphicOn f (closedBall 0 r))
    (hr : 0 < r) (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r) := by
  rw [hf.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg hr h0]
  exact forall₂_congr fun z hz ↦ (hnf hz).meromorphicOrderAt_nonneg_iff_analyticAt

/-- For globally meromorphic `f` over a proper normed field and `0 ≤ r`, `discCounting f r` agrees
with `ValueDistribution.logCounting f ⊤ r`. -/
theorem Meromorphic.discCounting_eq_logCounting_top [ProperSpace 𝕜] {f : 𝕜 → E} (hf : Meromorphic f)
    {r : ℝ} (hr : 0 ≤ r) :
    discCounting f r = ValueDistribution.logCounting f ⊤ r := by
  have habs : |r| = r := abs_of_nonneg hr
  have heval : ∀ z : 𝕜,
      (MeromorphicOn.divisor f (closedBall 0 r))⁻ z =
        ((Function.locallyFinsuppWithin.toClosedBall r) (MeromorphicOn.divisor f univ)⁻) z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : 𝕜) r
    · have hz' : z ∈ closedBall (0 : 𝕜) |r| := habs.symm ▸ hz
      rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz',
        Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.negPart_apply,
        (hf.meromorphicOn.mono_set (subset_univ _)).divisor_apply hz,
        hf.meromorphicOn.divisor_apply (mem_univ z)]
    · have hz' : z ∉ closedBall (0 : 𝕜) |r| := habs.symm ▸ hz
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz']
  simp only [discCounting_def, ValueDistribution.logCounting_top,
    Function.locallyFinsuppWithin.logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk, heval,
    Function.locallyFinsuppWithin.toClosedBall_eval_within _ (mem_closedBall_self (abs_nonneg r))]

end NormedField

section Complex

open TauCeti

/-- Over `ℂ`, for a function in meromorphic normal form on `ball 0 r` (`[CompleteSpace E]`) that is
meromorphic on `closedBall 0 r` with `0 ≤ meromorphicOrderAt f 0` and `0 < r`,
`discCounting f r = 0 ↔ DifferentiableOn ℂ f (ball 0 r)`. -/
theorem MeromorphicNFOn.discCounting_eq_zero_iff_differentiableOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {r : ℝ}
    (hnf : MeromorphicNFOn f (ball 0 r)) (hf : MeromorphicOn f (closedBall 0 r))
    (hr : 0 < r) (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔ DifferentiableOn ℂ f (ball 0 r) := by
  rw [hnf.discCounting_eq_zero_iff_analyticOnNhd hf hr h0,
    Complex.analyticOnNhd_iff_differentiableOn isOpen_ball]

/-- **Disc-local Jensen identity** (Calegari–Dimitrov–Tang, §6.1, eq. (6.1.4)): for `f : ℂ → ℂ`
meromorphic on `closedBall 0 r` and `0 < r`,
`circleAverage (log ‖f ·‖) 0 r = discCounting f⁻¹ r - discCounting f r + log ‖c(f, 0)‖`,
where `c(f, 0) = meromorphicTrailingCoeffAt f 0` is the leading Laurent coefficient at `0`. Note
that when `meromorphicOrderAt f 0 = ⊤` (`f = 0` away from a discrete set), all four terms vanish by
totalization (`Real.log 0 = 0`). -/
theorem MeromorphicOn.circleAverage_log_norm_eq_discCounting_inv_sub {f : ℂ → ℂ} {r : ℝ}
    (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) :
    circleAverage (fun z ↦ Real.log ‖f z‖) 0 r =
      discCounting f⁻¹ r - discCounting f r + Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have habs : |r| = r := abs_of_pos hr
  have hf' : MeromorphicOn f (closedBall 0 |r|) := habs.symm ▸ hf
  rw [hf'.circleAverage_log_norm hr.ne', habs]
  set D := MeromorphicOn.divisor f (closedBall 0 r)
  have hDinv : (MeromorphicOn.divisor f⁻¹ (closedBall 0 r))⁻ = D⁺ := by
    ext z
    simp [D, MeromorphicOn.divisor_inv, negPart_neg]
  have hDsplit : ∀ z, (D z : ℝ) = ((D⁺ z : ℤ) : ℝ) - ((D⁻ z : ℤ) : ℝ) := fun z ↦ by
    exact_mod_cast (posPart_sub_negPart (D z)).symm
  have hs_pos :
      (fun u ↦ ((D⁺ u : ℤ) : ℝ) * Real.log (r * ‖u‖⁻¹)).HasFiniteSupport :=
    (D⁺.finiteSupport (isCompact_closedBall 0 r)).subset fun u hu h0 ↦
      hu (by simp [h0])
  have hs_neg :
      (fun u ↦ ((D⁻ u : ℤ) : ℝ) * Real.log (r * ‖u‖⁻¹)).HasFiniteSupport :=
    (D⁻.finiteSupport (isCompact_closedBall 0 r)).subset fun u hu h0 ↦
      hu (by simp [h0])
  have hsum :
      (∑ᶠ u, (D u : ℝ) * Real.log (r * ‖(0 : ℂ) - u‖⁻¹)) =
        (∑ᶠ u, ((D⁺ u : ℤ) : ℝ) * Real.log (r * ‖u‖⁻¹)) -
          ∑ᶠ u, ((D⁻ u : ℤ) : ℝ) * Real.log (r * ‖u‖⁻¹) := by
    have hcongr :
        (∑ᶠ u, (D u : ℝ) * Real.log (r * ‖(0 : ℂ) - u‖⁻¹)) =
          ∑ᶠ u, (((D⁺ u : ℤ) : ℝ) * Real.log (r * ‖u‖⁻¹) -
            ((D⁻ u : ℤ) : ℝ) * Real.log (r * ‖u‖⁻¹)) := by
      refine finsum_congr fun u ↦ ?_
      rw [zero_sub, norm_neg, hDsplit u, sub_mul]
    rw [hcongr, finsum_sub_distrib hs_pos hs_neg]
  rw [discCounting_def, discCounting_def, hDinv, hsum, hDsplit 0]
  ring

/-!
### Sanity checks on concrete representatives
-/

-- Check 1: For `0 < r < 1`, `z ↦ 1 / z` has `discCounting = log r < 0`.
example {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    discCounting (fun z : ℂ ↦ 1 / z) r = Real.log r ∧
      discCounting (fun z : ℂ ↦ 1 / z) r < 0 := by
  rw [discCounting_one_div, show ((fun z : ℂ ↦ z)⁻¹) = fun z : ℂ ↦ z⁻¹ from rfl,
    discCounting_inv_id hr]
  exact ⟨rfl, Real.log_neg hr hr1⟩

-- Check 2: Both `1` and `0` have `discCounting = 0` (infinite meromorphic order is not a pole).
example (r : ℝ) :
    discCounting (fun _ : ℂ ↦ (1 : ℂ)) r = 0 ∧ discCounting (0 : ℂ → ℂ) r = 0 :=
  ⟨by simp, by simp⟩

-- Check 3: A simple pole on the boundary circle `sphere 0 ‖a‖` (`a ≠ 0`) has weight zero in
-- `discCounting`, even though `meromorphicOrderAt = -1` at `a`.
example {a : ℂ} (ha : a ≠ 0) :
    meromorphicOrderAt (fun z : ℂ ↦ 1 / (z - a)) a = -1 ∧
      discCounting (fun z : ℂ ↦ 1 / (z - a)) ‖a‖ = 0 := by
  have hmero : MeromorphicOn (fun z : ℂ ↦ 1 / (z - a)) (closedBall 0 ‖a‖) := by
    simp only [one_div]
    exact (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.inv
  have hana : AnalyticOnNhd ℂ (fun z : ℂ ↦ 1 / (z - a)) (ball 0 ‖a‖) := by
    intro z hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 fun h ↦ by
      subst h
      exact lt_irrefl ‖z‖ (mem_ball_zero_iff.1 hz)
    simp only [one_div]
    exact (analyticAt_id.fun_sub analyticAt_const).inv hza
  refine ⟨?_, hmero.discCounting_eq_zero_of_analyticOnNhd_ball hana⟩
  have hsub : meromorphicOrderAt (fun z : ℂ ↦ z - a) a = 1 :=
    (meromorphicOrderAt_eq_int_iff (by fun_prop)).2
      ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, by simp⟩
  simp only [one_div]
  change meromorphicOrderAt (fun z : ℂ ↦ z - a)⁻¹ a = -1
  rw [meromorphicOrderAt_inv, hsub]

-- Check 4: The discontinuous removable representative equal to `2` at `0` and `1` elsewhere has
-- punctured limit `1`, meromorphic order `0` at `0`, and `discCounting = 0`, yet is neither
-- continuous nor analytic at `0`.
example :
    let f : ℂ → ℂ := fun z ↦ if z = 0 then 2 else 1
    f 0 = 2 ∧
      Tendsto f (𝓝[≠] 0) (𝓝 1) ∧
      MeromorphicOn f (ball 0 1) ∧
      meromorphicOrderAt f 0 = 0 ∧
      (∀ r, discCounting f r = 0) ∧
      ¬ContinuousAt f 0 ∧
      ¬AnalyticAt ℂ f 0 := by
  intro f
  have hpunct : f =ᶠ[𝓝[≠] (0 : ℂ)] fun _ ↦ (1 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [f, mem_compl_singleton_iff.1 hz]
  have hf_val : f 0 = 2 := by simp [f]
  have htend : Tendsto f (𝓝[≠] 0) (𝓝 1) := tendsto_const_nhds.congr' hpunct.symm
  have hmero : ∀ U : Set ℂ, MeromorphicOn f U := fun U z _ ↦ by
    by_cases hz : z = 0
    · subst hz
      exact (MeromorphicAt.meromorphicAt_congr hpunct).2 analyticAt_const.meromorphicAt
    · have hnhds : f =ᶠ[𝓝 z] fun _ ↦ (1 : ℂ) := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp [f, (hw : w ≠ 0)]
      exact (analyticAt_congr hnhds.symm).1 analyticAt_const |>.meromorphicAt
  have hord0 : meromorphicOrderAt f 0 = 0 := by
    rw [meromorphicOrderAt_congr hpunct]
    simp [meromorphicOrderAt_const]
  have hnot_cont : ¬ContinuousAt f 0 := by
    intro hc
    have hlim : Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) := hc.continuousWithinAt
    have h12 : (1 : ℂ) = 2 := tendsto_nhds_unique htend (hf_val ▸ hlim)
    norm_num at h12
  refine ⟨hf_val, htend, hmero (ball 0 1), hord0, fun r ↦ ?_, hnot_cont,
    fun ha ↦ hnot_cont ha.continuousAt⟩
  have hcod : f =ᶠ[codiscreteWithin (ball (0 : ℂ) r)] fun _ ↦ (1 : ℂ) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (0 : ℂ)] with z hz
    simp [f, mem_compl_singleton_iff.1 hz]
  rw [(hmero _).discCounting_congr_codiscreteWithin analyticOnNhd_const.meromorphicOn hcod]
  simp

end Complex
