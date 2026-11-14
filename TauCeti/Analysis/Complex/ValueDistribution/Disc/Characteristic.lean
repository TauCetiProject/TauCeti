/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Cartan
public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import TauCeti.Analysis.Complex.ValueDistribution.Disc.Counting
public import TauCeti.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation

/-!
# The disc-local Nevanlinna characteristic, First Main Theorem, and Cartan's formula

Mathlib's `ValueDistribution.characteristic f ⊤ = proximity f ⊤ + logCounting f ⊤` requires global
meromorphicity on `ℂ` for its counting term, First Main Theorem, and Cartan monotonicity theorem.
For functions meromorphic only on an open disc `ball 0 R` (such as universal covering maps on the
unit disc `ball 0 1`), `ValueDistribution.proximity f ⊤ r` already depends only on `sphere 0 |r|`,
while `TauCeti.discCounting f r` localizes the pole count to `closedBall 0 r`.

This file defines `TauCeti.discCharacteristic f r = ValueDistribution.proximity f ⊤ r +
discCounting f r` and establishes the disc-local counterparts of Nevanlinna's First Main Theorem and
Cartan's formula without manufacturing any global extension:

* **Comparison and holomorphic reduction**: `Meromorphic.discCharacteristic_eq_characteristic_top`
  shows agreement with `ValueDistribution.characteristic f ⊤ r` for `0 ≤ r` when `f` is globally
  meromorphic, while `AnalyticOnNhd.discCharacteristic_eq_proximity_top` and
  `DifferentiableOn.discCharacteristic_eq_proximity_top` reduce `discCharacteristic` to
  `ValueDistribution.proximity · ⊤` for holomorphic functions.
* **Power law** (`MeromorphicOn.discCharacteristic_pow`): `discCharacteristic (f ^ n) r =
  n * discCharacteristic f r` for `n : ℕ`.
* **Local First Main Theorem** (`MeromorphicOn.discCharacteristic_sub_discCharacteristic_inv`,
  `MeromorphicOn.abs_discCharacteristic_sub_discCharacteristic_inv_sub_le`, and
  `MeromorphicOn.abs_discCharacteristic_sub_discCharacteristic_one_div_sub_le`):
  `discCharacteristic f r - discCharacteristic f⁻¹ r = log ‖meromorphicTrailingCoeffAt f 0‖` for
  `0 < r`, and shifting by `a : ℂ` gives
  `|discCharacteristic f r - discCharacteristic (fun z ↦ 1 / (f z - a)) r - log ‖c(f - a, 0)‖| ≤
    log⁺ ‖a‖ + log 2`.
* **Disc-local Cartan formula and radial monotonicity**
  (`MeromorphicOn.discCharacteristic_eq_circleAverage_add_circleAverage`,
  `MeromorphicOn.discCharacteristic_mono`, `AnalyticOnNhd.monotoneOn_proximity_top_Icc`, and
  `DifferentiableOn.monotoneOn_proximity_top_Ico`): `discCharacteristic f` is monotone on `(0, R]`,
  and `ValueDistribution.proximity g ⊤` is monotone on `[0, R)` for holomorphic `g : ℂ → ℂ`.

## Implementation notes

The inversion and translation identities adapt
`Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem` (by Stefan Kebekus) to compact
subdiscs, and the Cartan formula and radial monotonicity adapt
`Mathlib.Analysis.Complex.ValueDistribution.Cartan` (by Matteo Cipollina and Stefan Kebekus) using
`TauCeti.discCounting` in place of the whole-plane `ValueDistribution.logCounting`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  **38** (2025), 627–702, §6.1 and Corollary 6.2.9.
* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.2.
-/

public section

open Filter Function Metric Real Set
open scoped Topology

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TauCeti

/-- The disc-local Nevanlinna characteristic function on `closedBall 0 r`:
`discCharacteristic f r = ValueDistribution.proximity f ⊤ r + discCounting f r`.
When `f` has a pole at `0` and `0 < r < 1`, `discCounting f r` carries a negative `log r` term, so
`discCharacteristic f r` need not be nonnegative without `0 ≤ meromorphicOrderAt f 0` or `1 ≤ r`. -/
noncomputable def discCharacteristic (f : ℂ → E) (r : ℝ) : ℝ :=
  ValueDistribution.proximity f ⊤ r + discCounting f r

theorem discCharacteristic_def (f : ℂ → E) (r : ℝ) :
    discCharacteristic f r = ValueDistribution.proximity f ⊤ r + discCounting f r := by
  rfl

@[simp]
theorem discCharacteristic_eval_zero (f : ℂ → E) :
    discCharacteristic f 0 = log⁺ ‖f 0‖ := by
  simp [discCharacteristic_def, ValueDistribution.proximity_top]

@[simp]
theorem discCharacteristic_const (c : E) :
    discCharacteristic (fun _ : ℂ ↦ c) = fun _ ↦ log⁺ ‖c‖ := by
  ext r
  simp [discCharacteristic_def]

@[simp]
theorem discCharacteristic_const_zero :
    discCharacteristic (0 : ℂ → E) = 0 := by
  change discCharacteristic (fun _ : ℂ ↦ (0 : E)) = fun _ ↦ 0
  simp

theorem discCharacteristic_one_div (f : ℂ → ℂ) :
    discCharacteristic (fun z ↦ 1 / f z) = discCharacteristic f⁻¹ := by
  simp only [one_div]
  rfl

/-- For `1 ≤ r`, `discCharacteristic f r` is nonnegative without any centre or meromorphicity
hypothesis. -/
theorem discCharacteristic_nonneg_of_one_le {r : ℝ} (hr : 1 ≤ r) (f : ℂ → E) :
    0 ≤ discCharacteristic f r :=
  add_nonneg (ValueDistribution.proximity_nonneg r) (discCounting_nonneg_of_one_le hr f)

/-- If `0 ≤ meromorphicOrderAt f 0` (including infinite order `⊤`), then
`0 ≤ discCharacteristic f r` for every `r : ℝ`. -/
theorem discCharacteristic_nonneg_of_meromorphicOrderAt_nonneg {f : ℂ → E}
    (h0 : 0 ≤ meromorphicOrderAt f 0) (r : ℝ) :
    0 ≤ discCharacteristic f r :=
  add_nonneg (ValueDistribution.proximity_nonneg r)
    (discCounting_nonneg_of_meromorphicOrderAt_nonneg h0 r)

end TauCeti

open TauCeti

/-- For globally meromorphic `f : ℂ → E` and `0 ≤ r`, `discCharacteristic f r` agrees with
`ValueDistribution.characteristic f ⊤ r`. -/
theorem Meromorphic.discCharacteristic_eq_characteristic_top {f : ℂ → E} (hf : Meromorphic f)
    {r : ℝ} (hr : 0 ≤ r) :
    discCharacteristic f r = ValueDistribution.characteristic f ⊤ r := by
  rw [discCharacteristic_def, ValueDistribution.characteristic, Pi.add_apply,
    hf.discCounting_eq_logCounting_top hr]

/-- Functions equal on a neighbourhood of `closedBall 0 r` (`0 ≤ r`) have equal
`discCharacteristic` at radius `r`. -/
theorem Filter.EventuallyEq.discCharacteristic_eq {f g : ℂ → E} {r : ℝ} (hr : 0 ≤ r)
    (hfg : f =ᶠ[𝓝ˢ (closedBall 0 r)] g) :
    discCharacteristic f r = discCharacteristic g r := by
  have heq_on : EqOn f g (closedBall 0 r) := subset_of_mem_nhdsSet hfg
  have hprox : ValueDistribution.proximity f ⊤ r = ValueDistribution.proximity g ⊤ r := by
    simp only [ValueDistribution.proximity_top]
    refine circleAverage_congr_sphere fun z hz ↦ ?_
    have hzc : z ∈ closedBall (0 : ℂ) r := by
      rw [abs_of_nonneg hr] at hz
      exact sphere_subset_closedBall hz
    simp [heq_on hzc]
  rw [discCharacteristic_def, discCharacteristic_def, hprox, hfg.discCounting_eq]

/-- If `f` is meromorphic on `closedBall 0 r` and analytic on the open disc `ball 0 r`, then
`discCharacteristic f r = ValueDistribution.proximity f ⊤ r`. -/
theorem MeromorphicOn.discCharacteristic_eq_proximity_top_of_analyticOnNhd_ball
    {f : ℂ → E} {r : ℝ} (hf : MeromorphicOn f (closedBall 0 r))
    (ha : AnalyticOnNhd ℂ f (ball 0 r)) :
    discCharacteristic f r = ValueDistribution.proximity f ⊤ r := by
  rw [discCharacteristic_def, hf.discCounting_eq_zero_of_analyticOnNhd_ball ha, add_zero]

/-- For `f` analytic on a neighbourhood of `closedBall 0 r`, `discCharacteristic f r` reduces to
`ValueDistribution.proximity f ⊤ r`. -/
theorem AnalyticOnNhd.discCharacteristic_eq_proximity_top {f : ℂ → E} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) :
    discCharacteristic f r = ValueDistribution.proximity f ⊤ r :=
  hf.meromorphicOn.discCharacteristic_eq_proximity_top_of_analyticOnNhd_ball
    (hf.mono ball_subset_closedBall)

/-- For `f` holomorphic on `ball 0 R` (`[CompleteSpace E]`) and `r < R`, `discCharacteristic f r`
reduces to `ValueDistribution.proximity f ⊤ r`. -/
theorem DifferentiableOn.discCharacteristic_eq_proximity_top [CompleteSpace E] {f : ℂ → E}
    {R r : ℝ} (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r < R) :
    discCharacteristic f r = ValueDistribution.proximity f ⊤ r := by
  have hana : AnalyticOnNhd ℂ f (ball 0 R) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2 hf
  exact (hana.mono (closedBall_subset_ball hr)).discCharacteristic_eq_proximity_top

/-- If `f` and `g` are meromorphic on `closedBall 0 r` (`0 < r`) and agree away from a discrete
subset of `closedBall 0 r`, then `discCharacteristic f r = discCharacteristic g r`. -/
theorem MeromorphicOn.discCharacteristic_congr_codiscreteWithin {f g : ℂ → E} {r : ℝ}
    (hr : 0 < r) (hf : MeromorphicOn f (closedBall 0 r)) (hg : MeromorphicOn g (closedBall 0 r))
    (hfg : f =ᶠ[codiscreteWithin (closedBall 0 r)] g) :
    discCharacteristic f r = discCharacteristic g r := by
  have hsphere : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g := by
    refine hfg.filter_mono (codiscreteWithin_mono ?_)
    rw [abs_of_pos hr]
    exact sphere_subset_closedBall
  have hball : f =ᶠ[codiscreteWithin (ball 0 r)] g :=
    hfg.filter_mono (codiscreteWithin_mono ball_subset_closedBall)
  rw [discCharacteristic_def, discCharacteristic_def,
    ValueDistribution.proximity_congr_codiscreteWithin hsphere hr.ne',
    hf.discCounting_congr_codiscreteWithin hg hball]

/-- Shifting `f` by a constant `a₀` leaves `discCounting` unchanged, so the difference of
`discCharacteristic` equals the difference of `ValueDistribution.proximity · ⊤`. -/
theorem MeromorphicOn.discCharacteristic_sub_discCharacteristic_sub_const {f : ℂ → E} {r : ℝ}
    (hf : MeromorphicOn f (closedBall 0 r)) (a₀ : E) :
    discCharacteristic f r - discCharacteristic (fun z ↦ f z - a₀) r =
      ValueDistribution.proximity f ⊤ r - ValueDistribution.proximity (fun z ↦ f z - a₀) ⊤ r := by
  rw [discCharacteristic_def, discCharacteristic_def, hf.discCounting_fun_sub_const a₀]
  ring

/-- Second part of the local First Main Theorem: if `f : ℂ → E` is meromorphic on `closedBall 0 r`
(`0 ≤ r`), then shifting by `a₀` changes `discCharacteristic` by at most `log⁺ ‖a₀‖ + log 2`. -/
theorem MeromorphicOn.abs_discCharacteristic_sub_discCharacteristic_sub_const_le
    {f : ℂ → E} {r : ℝ} (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 ≤ r) (a₀ : E) :
    |discCharacteristic f r - discCharacteristic (fun z ↦ f z - a₀) r| ≤
      log⁺ ‖a₀‖ + Real.log 2 := by
  have hsphere : MeromorphicOn f (sphere 0 |r|) := by
    rw [abs_of_nonneg hr]
    exact hf.mono_set sphere_subset_closedBall
  rw [hf.discCharacteristic_sub_discCharacteristic_sub_const a₀]
  exact hsphere.abs_proximity_top_sub_proximity_sub_const_le a₀

end NormedSpace

section ComplexValued

open TauCeti

namespace MeromorphicOn

variable {f : ℂ → ℂ} {r R : ℝ}

/-- Power scaling of the disc-local characteristic (Calegari–Dimitrov–Tang, §6.1.1 and
eq. (6.2.3)): for `f : ℂ → ℂ` meromorphic on `closedBall 0 r` and `n : ℕ`,
`discCharacteristic (f ^ n) r = n * discCharacteristic f r`. -/
@[to_fun discCharacteristic_fun_pow]
theorem discCharacteristic_pow (hf : MeromorphicOn f (closedBall 0 r)) (n : ℕ) :
    discCharacteristic (f ^ n) r = n * discCharacteristic f r := by
  rw [discCharacteristic_def, discCharacteristic_def, ValueDistribution.proximity_pow_top,
    Pi.smul_apply, nsmul_eq_mul, hf.discCounting_pow n, mul_add]

/-- **Local First Main Inversion Identity** (Calegari–Dimitrov–Tang, §6.1, eq. (6.1.4)): for
`f : ℂ → ℂ` meromorphic on `closedBall 0 r` and `0 < r`,
`discCharacteristic f r - discCharacteristic f⁻¹ r = log ‖meromorphicTrailingCoeffAt f 0‖`.
No global meromorphicity or centre regularity hypothesis is required; when
`meromorphicOrderAt f 0 ≠ ⊤`, `meromorphicTrailingCoeffAt f 0` is the nonzero leading Laurent
coefficient at `0`, while if `meromorphicOrderAt f 0 = ⊤` (`f = 0` away from a discrete set) both
sides vanish by totalization. -/
theorem discCharacteristic_sub_discCharacteristic_inv
    (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) :
    discCharacteristic f r - discCharacteristic f⁻¹ r =
      Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hsphere : MeromorphicOn f (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact hf.mono_set sphere_subset_closedBall
  rw [discCharacteristic_def, discCharacteristic_def]
  linarith [hsphere.proximity_top_sub_proximity_inv_top_eq_circleAverage,
    hf.circleAverage_log_norm_eq_discCounting_inv_sub hr]

/-- Closed-subdisc form of the translated local First Main Theorem: for `f : ℂ → ℂ` meromorphic on
`closedBall 0 r`, `a : ℂ`, and `0 < r`,
`|discCharacteristic f r - discCharacteristic (fun z ↦ (f z - a)⁻¹) r - log ‖c(f - a, 0)‖| ≤
  log⁺ ‖a‖ + log 2`. -/
theorem abs_discCharacteristic_sub_discCharacteristic_inv_sub_le
    (hf : MeromorphicOn f (closedBall 0 r)) (a : ℂ) (hr : 0 < r) :
    |discCharacteristic f r - discCharacteristic (fun z ↦ (f z - a)⁻¹) r -
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖| ≤
      log⁺ ‖a‖ + Real.log 2 := by
  have hinv :
      discCharacteristic (fun z ↦ f z - a) r - discCharacteristic (fun z ↦ (f z - a)⁻¹) r =
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ :=
    (hf.sub (MeromorphicOn.const a)).discCharacteristic_sub_discCharacteristic_inv hr
  have hdiff :
      discCharacteristic f r - discCharacteristic (fun z ↦ (f z - a)⁻¹) r -
          Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ =
        discCharacteristic f r - discCharacteristic (fun z ↦ f z - a) r := by
    linarith
  rw [hdiff]
  exact hf.abs_discCharacteristic_sub_discCharacteristic_sub_const_le hr.le a

/-- Circle integrability of `a ↦ discCounting (fun z ↦ (f z - a)⁻¹) r` on the unit circle for `f`
meromorphic on `closedBall 0 r`. -/
theorem circleIntegrable_discCounting_inv_sub (hf : MeromorphicOn f (closedBall 0 r)) :
    CircleIntegrable (fun a ↦ discCounting (fun z ↦ (f z - a)⁻¹) r) 0 1 := by
  by_cases hr : r ≤ 0
  · refine (circleIntegrable_congr fun a _ ↦ ?_).2 (circleIntegrable_const 0 0 1)
    exact discCounting_of_nonpos _ hr
  push Not at hr
  have hsphere : MeromorphicOn f (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact hf.mono_set sphere_subset_closedBall
  have hint :
      CircleIntegrable
        (fun a ↦
          circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 r + discCounting f r -
            Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 :=
    (hsphere.circleIntegrable_circleAverage_log_norm_sub.add
      (circleIntegrable_const (discCounting f r) 0 1)).sub
      ValueDistribution.circleIntegrable_log_meromorphicTrailingCoeffAt
  refine (circleIntegrable_congr fun a _ ↦ ?_).2 hint
  have hjensen :
      circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 r =
        discCounting (fun z ↦ (f z - a)⁻¹) r - discCounting (fun z ↦ f z - a) r +
          Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ :=
    (hf.sub (MeromorphicOn.const a)).circleAverage_log_norm_eq_discCounting_inv_sub hr
  have hsub : discCounting (fun z ↦ f z - a) r = discCounting f r :=
    hf.discCounting_fun_sub_const a
  linarith

/-- **Disc-local Cartan's formula**: for `f : ℂ → ℂ` meromorphic on `closedBall 0 r` and `0 < r`,
`discCharacteristic f r` is the sum of the unit-circle average of the `a`-point counting function
`discCounting (fun z ↦ (f z - a)⁻¹) r` and the radius-independent unit-circle average of
`log ‖meromorphicTrailingCoeffAt (f · - a) 0‖`. -/
theorem discCharacteristic_eq_circleAverage_add_circleAverage
    (hf : MeromorphicOn f (closedBall 0 r)) (hr : 0 < r) :
    discCharacteristic f r =
      circleAverage (fun a ↦ discCounting (fun z ↦ (f z - a)⁻¹) r) 0 1 +
        circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
  have hsphere : MeromorphicOn f (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact hf.mono_set sphere_subset_closedBall
  calc discCharacteristic f r
    _ = ValueDistribution.proximity f ⊤ r + discCounting f r := discCharacteristic_def f r
    _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 r) 0 1 +
          circleAverage (fun _ ↦ discCounting f r) 0 1 := by
      rw [hsphere.circleAverage_circleAverage_eq_proximity_top, circleAverage_const]
    _ = circleAverage
          (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 r + discCounting f r) 0 1 := by
      rw [← circleAverage_add hsphere.circleIntegrable_circleAverage_log_norm_sub
        (circleIntegrable_const (discCounting f r) 0 1)]
      rfl
    _ = circleAverage
          (fun a ↦
            discCounting (fun z ↦ (f z - a)⁻¹) r +
              Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
      refine circleAverage_congr_sphere fun a _ ↦ ?_
      have hjensen :
          circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 r =
            discCounting (fun z ↦ (f z - a)⁻¹) r - discCounting (fun z ↦ f z - a) r +
              Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ :=
        (hf.sub (MeromorphicOn.const a)).circleAverage_log_norm_eq_discCounting_inv_sub hr
      have hsub : discCounting (fun z ↦ f z - a) r = discCounting f r :=
        hf.discCounting_fun_sub_const a
      linarith
    _ = circleAverage (fun a ↦ discCounting (fun z ↦ (f z - a)⁻¹) r) 0 1 +
          circleAverage
            (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
      exact circleAverage_add hf.circleIntegrable_discCounting_inv_sub
        ValueDistribution.circleIntegrable_log_meromorphicTrailingCoeffAt

/-- Radial monotonicity of `discCharacteristic`: if `f : ℂ → ℂ` is meromorphic on
`closedBall 0 r₂` and `0 < r₁ ≤ r₂`, then `discCharacteristic f r₁ ≤ discCharacteristic f r₂`. -/
theorem discCharacteristic_mono {r₁ r₂ : ℝ} (hf : MeromorphicOn f (closedBall 0 r₂))
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) :
    discCharacteristic f r₁ ≤ discCharacteristic f r₂ := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hr₁₂
  have hf₁ : MeromorphicOn f (closedBall 0 r₁) :=
    hf.mono_set (closedBall_subset_closedBall hr₁₂)
  rw [hf₁.discCharacteristic_eq_circleAverage_add_circleAverage hr₁,
    hf.discCharacteristic_eq_circleAverage_add_circleAverage hr₂]
  have havg_le :
      circleAverage (fun a ↦ discCounting (fun z ↦ (f z - a)⁻¹) r₁) 0 1 ≤
        circleAverage (fun a ↦ discCounting (fun z ↦ (f z - a)⁻¹) r₂) 0 1 := by
    refine circleAverage_mono hf₁.circleIntegrable_discCounting_inv_sub
      hf.circleIntegrable_discCounting_inv_sub fun a _ ↦ ?_
    exact ((hf.sub (MeromorphicOn.const a)).inv).discCounting_mono hr₁ hr₁₂
  linarith

/-- If `f : ℂ → ℂ` is meromorphic on `closedBall 0 R`, then `discCharacteristic f` is monotone on
`Ioc 0 R`. -/
theorem monotoneOn_discCharacteristic_Ioc (hf : MeromorphicOn f (closedBall 0 R)) :
    MonotoneOn (discCharacteristic f) (Ioc 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hf.mono_set (closedBall_subset_closedBall hr₂.2)).discCharacteristic_mono hr₁.1 hr₁₂

/-- If `f : ℂ → ℂ` is meromorphic on `ball 0 R`, then `discCharacteristic f` is monotone on
`Ioo 0 R`. -/
theorem monotoneOn_discCharacteristic_Ioo (hf : MeromorphicOn f (ball 0 R)) :
    MonotoneOn (discCharacteristic f) (Ioo 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hf.mono_set (closedBall_subset_ball hr₂.2)).discCharacteristic_mono hr₁.1 hr₁₂

/-- **Translated local First Main Theorem** (Calegari–Dimitrov–Tang, §6.1, eq. (6.1.3)): for
`f : ℂ → ℂ` meromorphic on `ball 0 R`, `a : ℂ`, and `0 < r < R` (in particular `R = 1` on the unit
disc `ball 0 1`),
`|discCharacteristic f r - discCharacteristic (fun z ↦ 1 / (f z - a)) r - log ‖c(f - a, 0)‖| ≤
  log⁺ ‖a‖ + log 2`,
where `c(f - a, 0) = meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0` is the leading Laurent
coefficient of `f - a` at `0` (nonzero whenever `meromorphicOrderAt (fun z ↦ f z - a) 0 ≠ ⊤`, while
when `meromorphicOrderAt (fun z ↦ f z - a) 0 = ⊤` the bound also holds via `Real.log 0 = 0`). -/
theorem abs_discCharacteristic_sub_discCharacteristic_one_div_sub_le
    (hf : MeromorphicOn f (ball 0 R)) (a : ℂ) (hr : 0 < r) (hrR : r < R) :
    |discCharacteristic f r - discCharacteristic (fun z ↦ 1 / (f z - a)) r -
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖| ≤
      log⁺ ‖a‖ + Real.log 2 := by
  have hsub : MeromorphicOn f (closedBall 0 r) := hf.mono_set (closedBall_subset_ball hrR)
  simpa only [one_div] using hsub.abs_discCharacteristic_sub_discCharacteristic_inv_sub_le a hr

end MeromorphicOn

/-- Radial monotonicity of holomorphic proximity on a closed disc (Calegari–Dimitrov–Tang,
Corollary 6.2.9): if `g : ℂ → ℂ` is analytic on a neighbourhood of `closedBall 0 r₂` and
`0 ≤ r₁ ≤ r₂`, then `ValueDistribution.proximity g ⊤ r₁ ≤ ValueDistribution.proximity g ⊤ r₂`. -/
theorem AnalyticOnNhd.proximity_top_mono {g : ℂ → ℂ} {r₁ r₂ : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r₂)) (hr₁ : 0 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    ValueDistribution.proximity g ⊤ r₁ ≤ ValueDistribution.proximity g ⊤ r₂ := by
  rcases hr₁.lt_or_eq with hr₁_pos | rfl
  · have hg₁ : AnalyticOnNhd ℂ g (closedBall 0 r₁) :=
      hg.mono (closedBall_subset_closedBall hr₁₂)
    rw [← hg₁.discCharacteristic_eq_proximity_top, ← hg.discCharacteristic_eq_proximity_top]
    exact hg.meromorphicOn.discCharacteristic_mono hr₁_pos hr₁₂
  · rcases hr₁₂.lt_or_eq with hr₂_pos | rfl
    · have h0 : ValueDistribution.proximity g ⊤ 0 = max 0 (Real.log ‖g 0‖) := by
        rw [ValueDistribution.proximity_top, circleAverage_zero, posLog_apply]
      have hprox_nonneg : 0 ≤ ValueDistribution.proximity g ⊤ r₂ :=
        ValueDistribution.proximity_nonneg r₂
      rw [h0]
      by_cases hg0 : g 0 = 0
      · simpa [hg0] using hprox_nonneg
      have habs : |r₂| = r₂ := abs_of_pos hr₂_pos
      have hg' : AnalyticOnNhd ℂ g (closedBall 0 |r₂|) := habs.symm ▸ hg
      have hjensen := hg'.circleAverage_log_norm hg0
      rw [habs] at hjensen
      have hsum_nonneg :
          0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor g (closedBall 0 r₂) u : ℤ) : ℝ) *
            Real.log (r₂ * ‖(0 : ℂ) - u‖⁻¹) := by
        refine finsum_nonneg fun u ↦ ?_
        by_cases hu0 : u = 0
        · simp [hu0]
        by_cases hub : u ∈ closedBall (0 : ℂ) r₂
        · refine mul_nonneg (Int.cast_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg u))
            (Real.log_nonneg ?_)
          rw [zero_sub, norm_neg, ← div_eq_mul_inv, one_le_div (norm_pos_iff.2 hu0)]
          exact mem_closedBall_zero_iff.1 hub
        · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hub]
      have hlog_le_avg : Real.log ‖g 0‖ ≤ circleAverage (fun z ↦ Real.log ‖g z‖) 0 r₂ := by
        linarith
      have hsphere : MeromorphicOn g (sphere 0 |r₂|) := by
        rw [habs]
        exact hg.meromorphicOn.mono_set sphere_subset_closedBall
      have havg_le_prox :
          circleAverage (fun z ↦ Real.log ‖g z‖) 0 r₂ ≤ ValueDistribution.proximity g ⊤ r₂ := by
        rw [ValueDistribution.proximity_top]
        exact circleAverage_mono hsphere.circleIntegrable_log_norm
          hsphere.circleIntegrable_posLog_norm fun _ _ ↦ le_max_right _ _
      exact max_le hprox_nonneg (hlog_le_avg.trans havg_le_prox)
    · exact le_rfl

/-- If `g : ℂ → ℂ` is analytic on `closedBall 0 R`, then `ValueDistribution.proximity g ⊤` is
monotone on `Icc 0 R`. -/
theorem AnalyticOnNhd.monotoneOn_proximity_top_Icc {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) :
    MonotoneOn (ValueDistribution.proximity g ⊤) (Icc 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hg.mono (closedBall_subset_closedBall hr₂.2)).proximity_top_mono hr₁.1 hr₁₂

/-- If `g : ℂ → ℂ` is analytic on `ball 0 R`, then `ValueDistribution.proximity g ⊤` is monotone on
`Ico 0 R`. -/
theorem AnalyticOnNhd.monotoneOn_proximity_top_Ico {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) :
    MonotoneOn (ValueDistribution.proximity g ⊤) (Ico 0 R) :=
  fun _ hr₁ _ hr₂ hr₁₂ ↦
    (hg.mono (closedBall_subset_ball hr₂.2)).proximity_top_mono hr₁.1 hr₁₂

/-- Radial monotonicity of holomorphic proximity on an open disc (Calegari–Dimitrov–Tang,
Corollary 6.2.9): if `g : ℂ → ℂ` is holomorphic on `ball 0 R` and `0 ≤ r₁ ≤ r₂ < R`, then
`ValueDistribution.proximity g ⊤ r₁ ≤ ValueDistribution.proximity g ⊤ r₂`. -/
theorem DifferentiableOn.proximity_top_mono {g : ℂ → ℂ} {R r₁ r₂ : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hr₁ : 0 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ < R) :
    ValueDistribution.proximity g ⊤ r₁ ≤ ValueDistribution.proximity g ⊤ r₂ := by
  have hana : AnalyticOnNhd ℂ g (ball 0 R) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2 hg
  exact (hana.mono (closedBall_subset_ball hr₂)).proximity_top_mono hr₁ hr₁₂

/-- If `g : ℂ → ℂ` is holomorphic on `ball 0 R`, then `ValueDistribution.proximity g ⊤` is monotone
on `Ico 0 R`. -/
theorem DifferentiableOn.monotoneOn_proximity_top_Ico {g : ℂ → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) :
    MonotoneOn (ValueDistribution.proximity g ⊤) (Ico 0 R) :=
  ((Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2 hg).monotoneOn_proximity_top_Ico

/-!
### Sanity checks on concrete functions
-/

-- Check 1: For every constant `c` (including `0`), `discCharacteristic (fun _ ↦ c) r = log⁺ ‖c‖`.
example (c : ℂ) (r : ℝ) :
    discCharacteristic (fun _ : ℂ ↦ c) r = log⁺ ‖c‖ ∧
      discCharacteristic (0 : ℂ → ℂ) r = 0 :=
  ⟨by simp, by simp⟩

-- Check 2: For `0 < r ≤ 1`, `discCharacteristic id r = 0`.
example {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    discCharacteristic (fun z : ℂ ↦ z) r = 0 := by
  rw [analyticOnNhd_id.discCharacteristic_eq_proximity_top, ValueDistribution.proximity_top]
  refine (circleAverage_congr_sphere (f₂ := 0) fun z hz ↦ ?_).trans (circleAverage_const 0 0 r)
  have hnorm : ‖z‖ ≤ 1 := by
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hz
    exact hz ▸ hr1
  have h0 : log⁺ ‖z‖ = 0 := (posLog_eq_zero_iff ‖z‖).2 (by rwa [abs_of_nonneg (norm_nonneg z)])
  simp [h0]

-- Check 3: For `0 < r ≤ 1`, `z ↦ 1 / z` has `proximity = -log r` and `discCounting = log r`,
-- which cancel in `discCharacteristic (fun z ↦ 1 / z) r = 0`.
example {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ValueDistribution.proximity (fun z : ℂ ↦ 1 / z) ⊤ r = -Real.log r ∧
      discCounting (fun z : ℂ ↦ 1 / z) r = Real.log r ∧
      discCharacteristic (fun z : ℂ ↦ 1 / z) r = 0 := by
  have hprox : ValueDistribution.proximity (fun z : ℂ ↦ 1 / z) ⊤ r = -Real.log r := by
    rw [ValueDistribution.proximity_top]
    refine (circleAverage_congr_sphere (f₂ := fun _ ↦ -Real.log r) fun z hz ↦ ?_).trans
      (circleAverage_const (-Real.log r) 0 r)
    have hnorm : ‖z‖ = r := by
      simpa [mem_sphere_zero_iff_norm, abs_of_pos hr] using hz
    have habs_inv : 1 ≤ |r⁻¹| := by
      rw [abs_of_pos (inv_pos.2 hr)]
      exact (one_le_inv₀ hr).2 hr1
    rw [one_div, norm_inv, hnorm, posLog_eq_log habs_inv, Real.log_inv]
  have hcnt : discCounting (fun z : ℂ ↦ 1 / z) r = Real.log r := by
    rw [discCounting_one_div, show ((fun z : ℂ ↦ z)⁻¹) = fun z : ℂ ↦ z⁻¹ from rfl,
      discCounting_inv_id hr]
  exact ⟨hprox, hcnt, by rw [discCharacteristic_def, hprox, hcnt, neg_add_cancel]⟩

end ComplexValued
