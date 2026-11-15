/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Meromorphic.Divisor
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Analysis.Complex.ValueDistribution.LogCounting.Basic

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
* `MeromorphicOn.discCounting_eq_finsum_divisor_ball_add`: `discCounting f r` depends only on the
  open-ball pole divisor `(MeromorphicOn.divisor f (ball 0 r))⁻`; boundary poles on `sphere 0 r`
  have weight zero.
* `Meromorphic.discCounting_eq_logCounting_top`: for globally meromorphic `f` and `0 ≤ r`,
  `discCounting f r = ValueDistribution.logCounting f ⊤ r`.
* `TauCeti.discCounting_congr_negPart_divisor`,
  `MeromorphicOn.discCounting_congr_negPart_divisor_ball`, `Filter.EventuallyEq.discCounting_eq`,
  and `MeromorphicOn.discCounting_congr_codiscreteWithin`: local congruence from pole-divisor,
  germ, or codiscrete agreement.
* `MeromorphicOn.discCounting_pow`, `AnalyticOnNhd.discCounting_add_right`, and
  `AnalyticOnNhd.discCounting_add_left`: power scaling
  `discCounting (f ^ n) r = n * discCounting f r` and invariance under adding an analytic function.
* `MeromorphicOn.discCounting_mono`, `MeromorphicOn.discCounting_monotoneOn_Ioc`, and
  `MeromorphicOn.discCounting_monotoneOn_Ioo`: radial monotonicity of `discCounting f`.
* `TauCeti.discCounting_nonneg_of_meromorphicOrderAt_nonneg`: nonnegativity `0 ≤ discCounting f r`
  whenever `0 ≤ meromorphicOrderAt f 0` (including infinite order `⊤`).
* `TauCeti.discCounting_eq_zero_of_meromorphicOrderAt_nonneg`, `AnalyticOnNhd.discCounting_eq_zero`,
  `DifferentiableOn.discCounting_eq_zero`,
  `MeromorphicOn.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg`,
  `MeromorphicOn.discCounting_eq_zero_iff_exists_analyticAt`,
  `MeromorphicOn.discCounting_eq_zero_iff_analyticOnNhd_of_continuousAt`, and
  `MeromorphicNFOn.discCounting_eq_zero_iff_analyticOnNhd`: vanishing criteria for `discCounting`.
* `MeromorphicOn.circleAverage_log_norm_eq_discCounting_inv_sub_add`: the disc-local Jensen
  identity `circleAverage (log ‖f ·‖) 0 r = discCounting f⁻¹ r - discCounting f r + log ‖c(f, 0)‖`.

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

/-- Unfolding `discCounting` in terms of `max 0 (-MeromorphicOn.divisor f (closedBall 0 r) z)` plus
the origin pole term. -/
theorem discCounting_eq_finsum_max_add (f : 𝕜 → E) (r : ℝ) :
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

/-- Negating a function leaves `discCounting` unchanged. -/
@[to_fun (attr := simp) discCounting_fun_neg]
theorem discCounting_neg (f : 𝕜 → E) :
    discCounting (-f) = discCounting f := by
  ext r
  simp [discCounting_def]

@[to_fun (attr := simp) discCounting_fun_const_smul]
theorem discCounting_const_smul {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    discCounting (s • f) = discCounting f := by
  ext r
  simp [discCounting_def, MeromorphicOn.divisor_const_smul hs]

@[simp]
theorem discCounting_fun_const_mul {f : 𝕜 → 𝕜} {s : 𝕜} (hs : s ≠ 0) :
    discCounting (fun z ↦ s * f z) = discCounting f := by
  simp_rw [← smul_eq_mul]
  exact discCounting_fun_const_smul hs

/-- Functions with equal pole divisors on `closedBall 0 r` have equal `discCounting` at radius
`r`. -/
theorem discCounting_congr_negPart_divisor {f g : 𝕜 → E} {r : ℝ}
    (h : (MeromorphicOn.divisor f (closedBall 0 r))⁻ =
      (MeromorphicOn.divisor g (closedBall 0 r))⁻) :
    discCounting f r = discCounting g r := by
  simp only [discCounting_def, h]

/-- Functions with identical punctured germs at every point of `closedBall 0 r` have equal
`discCounting` at radius `r`. No meromorphicity or global extension hypothesis is required. -/
theorem discCounting_congr_nhdsNE {f g : 𝕜 → E} {r : ℝ}
    (hfg : ∀ z ∈ closedBall 0 r, f =ᶠ[𝓝[≠] z] g) :
    discCounting f r = discCounting g r :=
  discCounting_congr_negPart_divisor (by rw [MeromorphicOn.divisor_congr_nhdsNE hfg])

/-- For `1 ≤ r`, `discCounting f r` is nonnegative without any centre or meromorphicity
hypothesis. -/
theorem discCounting_nonneg_of_one_le {r : ℝ} (hr : 1 ≤ r) (f : 𝕜 → E) :
    0 ≤ discCounting f r := by
  rw [discCounting_def]
  exact add_nonneg
    (finsum_nonneg (Function.locallyFinsuppWithin.mul_log_nonneg_of_subset_closedBall Subset.rfl
      (negPart_nonneg _)))
    (mul_nonneg (Int.cast_nonneg (negPart_nonneg _)) (Real.log_nonneg hr))

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
  have hD0 : (MeromorphicOn.divisor f (closedBall 0 r))⁻ 0 = 0 :=
    (hf.negPart_divisor_apply_eq_zero_iff (mem_closedBall_self hr.le)).2 h0
  rw [discCounting_def, hD0, Int.cast_zero, zero_mul, add_zero]
  exact finsum_nonneg
    (Function.locallyFinsuppWithin.mul_log_nonneg_of_subset_closedBall Subset.rfl
      (negPart_nonneg _))

/-- At `f = (·⁻¹)`, the single simple pole at the origin gives `discCounting (·⁻¹) r = log r` for
all `0 < r`. -/
@[to_fun (attr := simp) discCounting_fun_inv_id]
theorem discCounting_inv_id {r : ℝ} (hr : 0 < r) :
    discCounting ((fun z : 𝕜 ↦ z)⁻¹) r = Real.log r := by
  have hid0 : MeromorphicOn.divisor (fun z : 𝕜 ↦ z) (closedBall 0 r) 0 = 1 := by
    simpa only [sub_zero] using
      MeromorphicOn.divisor_sub_const_self (z₀ := (0 : 𝕜)) (mem_closedBall_self hr.le)
  have h0 : (MeromorphicOn.divisor ((fun z : 𝕜 ↦ z)⁻¹) (closedBall 0 r))⁻ 0 = 1 := by
    simp [hid0]
  rw [discCounting_def, h0, Int.cast_one, one_mul]
  suffices (∑ᶠ z : 𝕜,
      (((MeromorphicOn.divisor ((fun z : 𝕜 ↦ z)⁻¹) (closedBall 0 r))⁻ z : ℤ) : ℝ) *
        Real.log (r * ‖z‖⁻¹)) = 0 by
    rw [this, zero_add]
  refine finsum_eq_zero_of_forall_eq_zero fun z ↦ ?_
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hdiv : MeromorphicOn.divisor (fun w : 𝕜 ↦ w) (closedBall 0 r) z = 0 :=
      AnalyticAt.divisor_apply_eq_zero analyticAt_id hz0
    simp [hdiv]

@[simp]
theorem discCounting_id_inv {r : ℝ} (hr : 0 < r) :
    discCounting (id : 𝕜 → 𝕜)⁻¹ r = Real.log r :=
  discCounting_inv_id hr

end TauCeti

open TauCeti

/-- Functions equal on a neighbourhood of `closedBall 0 r` have equal `discCounting` at radius `r`.
No global extension or meromorphicity hypothesis is required. -/
theorem Filter.EventuallyEq.discCounting_eq {f g : 𝕜 → E} {r : ℝ}
    (hfg : f =ᶠ[𝓝ˢ (closedBall 0 r)] g) :
    discCounting f r = discCounting g r := by
  simp only [discCounting_def, hfg.divisor_eq]

/-- Adding a function analytic on `closedBall 0 r` on the right leaves `discCounting` unchanged
(with no meromorphicity hypothesis on `f`). -/
@[to_fun AnalyticOnNhd.discCounting_fun_add_right]
theorem AnalyticOnNhd.discCounting_add_right {f g : 𝕜 → E} {r : ℝ}
    (hg : AnalyticOnNhd 𝕜 g (closedBall 0 r)) :
    discCounting (f + g) r = discCounting f r :=
  discCounting_congr_negPart_divisor (hg.negPart_divisor_add_right f)

/-- Adding a function analytic on `closedBall 0 r` on the left leaves `discCounting` unchanged
(with no meromorphicity hypothesis on `g`). -/
@[to_fun AnalyticOnNhd.discCounting_fun_add_left]
theorem AnalyticOnNhd.discCounting_add_left {f g : 𝕜 → E} {r : ℝ}
    (hf : AnalyticOnNhd 𝕜 f (closedBall 0 r)) :
    discCounting (f + g) r = discCounting g r :=
  discCounting_congr_negPart_divisor (hf.negPart_divisor_add_left g)

namespace TauCeti

@[to_fun (attr := simp) discCounting_fun_add_const]
theorem discCounting_add_const (f : 𝕜 → E) (a : E) :
    discCounting (f + fun _ ↦ a) = discCounting f := by
  ext r
  exact analyticOnNhd_const.discCounting_add_right

@[to_fun (attr := simp) discCounting_fun_const_add]
theorem discCounting_const_add (a : E) (f : 𝕜 → E) :
    discCounting ((fun _ ↦ a) + f) = discCounting f := by
  ext r
  exact analyticOnNhd_const.discCounting_add_left

@[to_fun (attr := simp) discCounting_fun_sub_const]
theorem discCounting_sub_const (f : 𝕜 → E) (a : E) :
    discCounting (f - fun _ ↦ a) = discCounting f := by
  rw [sub_eq_add_neg]
  exact discCounting_add_const f (-a)

@[to_fun (attr := simp) discCounting_fun_const_sub]
theorem discCounting_const_sub (a : E) (f : 𝕜 → E) :
    discCounting ((fun _ ↦ a) - f) = discCounting f := by
  rw [sub_eq_add_neg, discCounting_const_add, discCounting_neg]

end TauCeti

namespace MeromorphicOn

variable {f g : 𝕜 → E} {r R : ℝ}

/-- Open-ball support formula for `discCounting`: when `f` is meromorphic on `closedBall 0 r`,
poles on the boundary circle `sphere 0 r` (`r > 0`) satisfy `log (r * ‖z‖⁻¹) = log 1 = 0` (and for
`r ≤ 0` both sides vanish), so `discCounting f r` depends only on
`(MeromorphicOn.divisor f (ball 0 r))⁻`. -/
theorem discCounting_eq_finsum_divisor_ball_add (hf : MeromorphicOn f (closedBall 0 r)) :
    discCounting f r =
      (∑ᶠ z, (((divisor f (ball 0 r))⁻ z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹)) +
        (((divisor f (ball 0 r))⁻ 0 : ℤ) : ℝ) * Real.log r := by
  by_cases hr : r ≤ 0
  · have hempty : ball (0 : 𝕜) r = ∅ := ball_eq_empty.2 hr
    have hzero : ∀ z : 𝕜, (divisor f (ball 0 r))⁻ z = 0 := fun z ↦
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by simp [hempty])
    simp [discCounting_of_nonpos f hr, hzero]
  push Not at hr
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

/-- Functions meromorphic on `closedBall 0 r` with equal open-ball pole divisors
`(divisor · (ball 0 r))⁻` have equal `discCounting` at radius `r`. -/
theorem discCounting_congr_negPart_divisor_ball (hf : MeromorphicOn f (closedBall 0 r))
    (hg : MeromorphicOn g (closedBall 0 r))
    (h : (divisor f (ball 0 r))⁻ = (divisor g (ball 0 r))⁻) :
    discCounting f r = discCounting g r := by
  rw [hf.discCounting_eq_finsum_divisor_ball_add, hg.discCounting_eq_finsum_divisor_ball_add, h]

/-- If `f` and `g` are meromorphic on `closedBall 0 r` and agree away from a discrete subset of
`ball 0 r`, then `discCounting f r = discCounting g r`. -/
theorem discCounting_congr_codiscreteWithin (hf : MeromorphicOn f (closedBall 0 r))
    (hg : MeromorphicOn g (closedBall 0 r)) (hfg : f =ᶠ[codiscreteWithin (ball 0 r)] g) :
    discCounting f r = discCounting g r :=
  hf.discCounting_congr_negPart_divisor_ball hg
    (by rw [divisor_congr_codiscreteWithin hfg isOpen_ball])

/-- Explicit open-punctured-disc order sum for `discCounting`: for `0 < r` and `f` meromorphic on
`closedBall 0 r`,
`discCounting f r = ∑ᶠ_{0 < ‖z‖ < r} ord⁻_z(f) * log (r / ‖z‖) + ord⁻_0(f) * log r`. -/
theorem discCounting_eq_finsum_ball_sdiff_singleton_add (hf : MeromorphicOn f (closedBall 0 r))
    (hr : 0 < r) :
    discCounting f r =
      (∑ᶠ z ∈ ball (0 : 𝕜) r \ {0},
          (((-(meromorphicOrderAt f z).untop₀) ⊔ 0 : ℤ) : ℝ) * Real.log (r / ‖z‖)) +
        (((-(meromorphicOrderAt f 0).untop₀) ⊔ 0 : ℤ) : ℝ) * Real.log r := by
  have hball : MeromorphicOn f (ball 0 r) := hf.mono_set ball_subset_closedBall
  rw [hf.discCounting_eq_finsum_divisor_ball_add, finsum_mem_def]
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

end MeromorphicOn

/-- If every point of the open disc `ball 0 r` has nonnegative meromorphic order (including infinite
order `⊤`), then `discCounting f r = 0`. No closed-ball meromorphicity or `0 < r` hypothesis is
required: if `f` fails to be meromorphic on `closedBall 0 r`, `discCounting f r` vanishes by
totalization, while if `f` is meromorphic on `closedBall 0 r`, boundary poles on `sphere 0 r` have
zero logarithmic weight. -/
theorem TauCeti.discCounting_eq_zero_of_meromorphicOrderAt_nonneg {f : 𝕜 → E} {r : ℝ}
    (h : ∀ z ∈ ball 0 r, 0 ≤ meromorphicOrderAt f z) :
    discCounting f r = 0 := by
  by_cases hf : MeromorphicOn f (closedBall 0 r)
  swap
  · exact discCounting_of_not_meromorphicOn hf
  have hball : MeromorphicOn f (ball 0 r) := hf.mono_set ball_subset_closedBall
  have hneg : (MeromorphicOn.divisor f (ball 0 r))⁻ = 0 := by
    ext z
    by_cases hz : z ∈ ball 0 r
    · exact (hball.negPart_divisor_apply_eq_zero_iff hz).2 (h z hz)
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz
  rw [hf.discCounting_eq_finsum_divisor_ball_add, hneg]
  simp

/-- If `f` is analytic on the open disc `ball 0 r`, then `discCounting f r = 0` (even if `f` has
singularities on `sphere 0 r`). -/
theorem AnalyticOnNhd.discCounting_eq_zero {f : 𝕜 → E} {r : ℝ}
    (hf : AnalyticOnNhd 𝕜 f (ball 0 r)) :
    discCounting f r = 0 :=
  discCounting_eq_zero_of_meromorphicOrderAt_nonneg fun z hz ↦ (hf z hz).meromorphicOrderAt_nonneg

namespace TauCeti

@[simp]
theorem discCounting_id : discCounting (id : 𝕜 → 𝕜) = 0 := by
  ext r
  exact analyticOnNhd_id.discCounting_eq_zero

@[simp]
theorem discCounting_fun_id : discCounting (fun z : 𝕜 ↦ z) = 0 :=
  discCounting_id

end TauCeti

namespace MeromorphicOn

variable {f g : 𝕜 → E} {r R : ℝ}

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
  have hD₁_fin : HasFiniteSupport (D₂.restrict hsub) :=
    (D₂.restrict hsub).finiteSupport (isCompact_closedBall 0 r₁)
  have hD₂_fin : HasFiniteSupport D₂ := D₂.finiteSupport (isCompact_closedBall 0 r₂)
  rw [discCounting_def, discCounting_def, hD₁]
  refine add_le_add (finsum_le_finsum ((hD₁_fin.fun_comp Int.cast_zero).fun_mul_left _)
    ((hD₂_fin.fun_comp Int.cast_zero).fun_mul_left _) fun z ↦ ?_) ?_
  · by_cases hz0 : z = 0
    · simp [hz0]
    by_cases hzb : z ∈ closedBall (0 : 𝕜) r₁
    · rw [Function.locallyFinsuppWithin.restrict_apply, ite_eq_left hzb]
      refine mul_le_mul_of_nonneg_left ?_ (Int.cast_nonneg (negPart_nonneg _))
      exact Real.log_le_log (mul_pos hr₁ (inv_pos.2 (norm_pos_iff.2 hz0)))
        (mul_le_mul_of_nonneg_right hr₁₂ (inv_nonneg.2 (norm_nonneg z)))
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb, Int.cast_zero, zero_mul]
      exact D₂.mul_log_nonneg_of_subset_closedBall Subset.rfl (negPart_nonneg _) z
  · rw [Function.locallyFinsuppWithin.restrict_apply, ite_eq_left (mem_closedBall_self hr₁.le)]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hr₁ hr₁₂)
      (Int.cast_nonneg (negPart_nonneg _))

/-- If `f` is meromorphic on `closedBall 0 R`, then `discCounting f` is monotone on `Ioc 0 R`. -/
theorem discCounting_monotoneOn_Ioc [ProperSpace 𝕜] (hf : MeromorphicOn f (closedBall 0 R)) :
    MonotoneOn (discCounting f) (Ioc 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hf.mono_set (closedBall_subset_closedBall hr₂.2)).discCounting_mono hr₁.1 hr₁₂

/-- If `f` is meromorphic on `ball 0 R`, then `discCounting f` is monotone on `Ioo 0 R`. -/
theorem discCounting_monotoneOn_Ioo [ProperSpace 𝕜] (hf : MeromorphicOn f (ball 0 R)) :
    MonotoneOn (discCounting f) (Ioo 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hf.mono_set (closedBall_subset_ball hr₂.2)).discCounting_mono hr₁.1 hr₁₂

/-- Vanishing of the local pole count (Calegari–Dimitrov–Tang, Lemma 6.1.2): for `f` meromorphic on
`closedBall 0 r` with `0 ≤ meromorphicOrderAt f 0`, `discCounting f r = 0` iff every point of the
open disc `ball 0 r` has nonnegative meromorphic order. Poles on `sphere 0 r` are permitted and
carry zero weight. -/
theorem discCounting_eq_zero_iff_meromorphicOrderAt_nonneg [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall 0 r)) (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔ ∀ z ∈ ball 0 r, 0 ≤ meromorphicOrderAt f z := by
  by_cases hr : r ≤ 0
  · simp [discCounting_of_nonpos f hr, ball_eq_empty.2 hr]
  push Not at hr
  refine ⟨fun hcnt ↦ ?_, discCounting_eq_zero_of_meromorphicOrderAt_nonneg⟩
  set D := (divisor f (closedBall 0 r))⁻
  have hD_fin : HasFiniteSupport D := D.finiteSupport (isCompact_closedBall 0 r)
  have hD0 : D 0 = 0 := (hf.negPart_divisor_apply_eq_zero_iff (mem_closedBall_self hr.le)).2 h0
  rw [discCounting_def, hD0, Int.cast_zero, zero_mul, add_zero] at hcnt
  -- On `ball 0 r \ {0}`, any pole contributes a strictly positive term to the `finsum`.
  intro z hz
  by_cases hz0 : z = 0
  · exact hz0 ▸ h0
  have hlog_pos : 0 < Real.log (r * ‖z‖⁻¹) := by
    refine Real.log_pos ?_
    rw [← div_eq_mul_inv, one_lt_div (norm_pos_iff.2 hz0)]
    exact mem_ball_zero_iff.1 hz
  have hDz : D z = 0 := by
    by_contra hne
    exact (finsum_pos
      (D.mul_log_nonneg_of_subset_closedBall Subset.rfl (negPart_nonneg _))
      ⟨z, mul_pos (Int.cast_pos.2 ((negPart_nonneg _).lt_of_ne' hne)) hlog_pos⟩
      ((hD_fin.fun_comp Int.cast_zero).fun_mul_left _)).ne' hcnt
  exact (hf.negPart_divisor_apply_eq_zero_iff (ball_subset_closedBall hz)).1 hDz

/-- Removable-germ vanishing criterion: under `MeromorphicOn f (closedBall 0 r)` and
`0 ≤ meromorphicOrderAt f 0`, `discCounting f r = 0` iff every punctured germ of `f` on `ball 0 r`
admits an analytic extension across the puncture. -/
theorem discCounting_eq_zero_iff_exists_analyticAt [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall 0 r)) (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔
      ∀ z ∈ ball 0 r, ∃ g : 𝕜 → E, AnalyticAt 𝕜 g z ∧ f =ᶠ[𝓝[≠] z] g := by
  rw [hf.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg h0]
  exact forall₂_congr fun z hz ↦ (hf z (ball_subset_closedBall hz)).meromorphicOrderAt_nonneg_iff

/-- Pointwise analyticity criterion on `ball 0 r` when removable singularities have been filled in:
under `MeromorphicOn f (closedBall 0 r)` and `0 ≤ meromorphicOrderAt f 0`, if `f` is continuous at
every point of `ball 0 r` where `0 ≤ meromorphicOrderAt f z` (note that assuming
`ContinuousOn f (ball 0 r)` into the normed space `E` outright would already exclude poles by
`MeromorphicAt.analyticAt`), then `discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r)`. -/
theorem discCounting_eq_zero_iff_analyticOnNhd_of_continuousAt [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall 0 r)) (h0 : 0 ≤ meromorphicOrderAt f 0)
    (hrem : ∀ z ∈ ball 0 r, 0 ≤ meromorphicOrderAt f z → ContinuousAt f z) :
    discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r) := by
  rw [hf.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg h0]
  exact ⟨fun h z hz ↦ (hf z (ball_subset_closedBall hz)).analyticAt (hrem z hz (h z hz)),
    fun h z hz ↦ (h z hz).meromorphicOrderAt_nonneg⟩

end MeromorphicOn

/-- For a function in meromorphic normal form on `ball 0 r` (so poles take value `0` and removable
singularities match their analytic extensions) that is meromorphic on `closedBall 0 r` with
`0 ≤ meromorphicOrderAt f 0`, `discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r)`. -/
theorem MeromorphicNFOn.discCounting_eq_zero_iff_analyticOnNhd [ProperSpace 𝕜] {f : 𝕜 → E} {r : ℝ}
    (hnf : MeromorphicNFOn f (ball 0 r)) (hf : MeromorphicOn f (closedBall 0 r))
    (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔ AnalyticOnNhd 𝕜 f (ball 0 r) := by
  rw [hf.discCounting_eq_zero_iff_meromorphicOrderAt_nonneg h0]
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

/-- Over `ℂ` (`[CompleteSpace E]`), if `f` is holomorphic on `ball 0 r`, then
`discCounting f r = 0`. -/
theorem DifferentiableOn.discCounting_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 r)) :
    discCounting f r = 0 :=
  ((Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2 hf).discCounting_eq_zero

/-- Over `ℂ`, for a function in meromorphic normal form on `ball 0 r` (`[CompleteSpace E]`) that is
meromorphic on `closedBall 0 r` with `0 ≤ meromorphicOrderAt f 0`,
`discCounting f r = 0 ↔ DifferentiableOn ℂ f (ball 0 r)`. -/
theorem MeromorphicNFOn.discCounting_eq_zero_iff_differentiableOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {r : ℝ}
    (hnf : MeromorphicNFOn f (ball 0 r)) (hf : MeromorphicOn f (closedBall 0 r))
    (h0 : 0 ≤ meromorphicOrderAt f 0) :
    discCounting f r = 0 ↔ DifferentiableOn ℂ f (ball 0 r) := by
  rw [hnf.discCounting_eq_zero_iff_analyticOnNhd hf h0,
    Complex.analyticOnNhd_iff_differentiableOn isOpen_ball]

/-- **Disc-local Jensen identity** (Calegari–Dimitrov–Tang, §6.1, eq. (6.1.4)): for `f : ℂ → ℂ`
meromorphic on `closedBall 0 r` and `0 < r`,
`circleAverage (log ‖f ·‖) 0 r = discCounting f⁻¹ r - discCounting f r + log ‖c(f, 0)‖`,
where `c(f, 0) = meromorphicTrailingCoeffAt f 0` is the leading Laurent coefficient at `0`. Note
that when `meromorphicOrderAt f 0 = ⊤` (`f = 0` away from a discrete set), all four terms vanish by
totalization (`Real.log 0 = 0`). -/
@[to_fun MeromorphicOn.circleAverage_log_norm_eq_discCounting_fun_inv_sub_add]
theorem MeromorphicOn.circleAverage_log_norm_eq_discCounting_inv_sub_add
    {f : ℂ → ℂ} {r : ℝ} (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) :
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
  have hDpos_fin : HasFiniteSupport D⁺ := D⁺.finiteSupport (isCompact_closedBall 0 r)
  have hDneg_fin : HasFiniteSupport D⁻ := D⁻.finiteSupport (isCompact_closedBall 0 r)
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
    rw [hcongr, finsum_sub_distrib ((hDpos_fin.fun_comp Int.cast_zero).fun_mul_left _)
      ((hDneg_fin.fun_comp Int.cast_zero).fun_mul_left _)]
  rw [discCounting_def, discCounting_def, hDinv, hsum, hDsplit 0]
  ring

/-!
### Sanity checks on concrete representatives
-/

-- Check 1: For `0 < r < 1`, `z ↦ 1 / z` has `discCounting = log r < 0`.
example {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    discCounting (fun z : ℂ ↦ 1 / z) r = Real.log r ∧
      discCounting (fun z : ℂ ↦ 1 / z) r < 0 := by
  simp [one_div, hr, Real.log_neg hr hr1]

-- Check 2: Both `1` and `0` have `discCounting = 0` (infinite meromorphic order is not a pole).
example (r : ℝ) :
    discCounting (fun _ : ℂ ↦ (1 : ℂ)) r = 0 ∧ discCounting (0 : ℂ → ℂ) r = 0 :=
  ⟨by simp, by simp⟩

-- Check 3: A simple pole on the boundary circle `sphere 0 ‖a‖` has weight zero in `discCounting`,
-- even though `meromorphicOrderAt = -1` at `a`.
example (a : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ 1 / (z - a)) a = -1 ∧
      discCounting (fun z : ℂ ↦ 1 / (z - a)) ‖a‖ = 0 := by
  have hana : AnalyticOnNhd ℂ (fun z : ℂ ↦ 1 / (z - a)) (ball 0 ‖a‖) := by
    intro z hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 fun h ↦ by
      subst h
      exact lt_irrefl ‖z‖ (mem_ball_zero_iff.1 hz)
    simp only [one_div]
    exact (analyticAt_id.fun_sub analyticAt_const).inv hza
  refine ⟨?_, hana.discCounting_eq_zero⟩
  simp [one_div, fun_meromorphicOrderAt_inv]

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
