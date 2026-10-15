/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The smooth transition function and cutoffs near zero

Mathlib's `Analysis/SpecialFunctions/SmoothTransition.lean` proves that
`Real.smoothTransition` is smooth and equals one on `[1, ∞)`, but states no derivative values.
This file records that its derivative vanishes on the open rays `(-∞, 0)` and `(1, ∞)`, where the
function is locally constant, so that the derivative is compactly supported. Being continuous, it
is then bounded, which bounds the gradients of cutoffs built from `Real.smoothTransition`.

It also uses the smooth transition to cut a function off near zero. For `m > 0` and a function
`g : ℝ → ℝ`, `TauCeti.positiveCutoff m g` is the product of `g` with a smooth transition from `0`
to `1` on `[m/4, m/2]`. It vanishes for `t ≤ m/4` and agrees with `g` for `t ≥ m/2`, so it is a
globally defined replacement for a function such as `t ↦ 1/t` or `Real.log` that is only well
behaved on `(0, ∞)`. If `g` is `C¹` on `(0, ∞)` then the cutoff is `C¹` on `ℝ`, and if `g'` is
bounded on `[m, ∞)` then the derivative of the cutoff is bounded on `ℝ`; these are the hypotheses
of chain rules for Sobolev functions.

## Main declarations

* `Real.smoothTransition.deriv_of_neg`: `deriv Real.smoothTransition x = 0` for `x < 0`.
* `Real.smoothTransition.deriv_of_one_lt`: `deriv Real.smoothTransition x = 0` for `1 < x`.
* `Real.smoothTransition.hasCompactSupport_deriv`: the derivative is compactly supported.
* `TauCeti.positiveCutoff`: the cutoff of `g` near zero.
* `TauCeti.contDiff_positiveCutoff`: the cutoff of a function that is `C¹` on `(0, ∞)` is `C¹`.
* `TauCeti.exists_nnnorm_deriv_positiveCutoff_le`: its derivative is bounded when `g'` is bounded
  on `[m, ∞)`.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff NNReal Topology

namespace Real.smoothTransition

/-- The smooth transition function has derivative zero to the left of `0`, where it is
identically zero. -/
theorem deriv_of_neg {x : ℝ} (hx : x < 0) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (Iio_mem_nhds hx) fun _ ht => zero_of_nonpos (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

/-- The smooth transition function has derivative zero to the right of `1`, where it is
identically one. -/
theorem deriv_of_one_lt {x : ℝ} (hx : 1 < x) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
    eventually_of_mem (Ioi_mem_nhds hx) fun _ ht => one_of_one_le (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth transition function is supported in `[0, 1]`. -/
theorem hasCompactSupport_deriv : HasCompactSupport (deriv smoothTransition) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    rcases not_and_or.1 hx with h | h
    · exact deriv_of_neg (not_le.1 h)
    · exact deriv_of_one_lt (not_le.1 h)

end Real.smoothTransition

namespace TauCeti

/-- The function `t ↦ s((4t - m)/m) g(t)`, where `s` is `Real.smoothTransition`. For `m > 0` it
vanishes for `t ≤ m/4` and agrees with `g` for `t ≥ m/2`, so it is a globally defined replacement
for a function `g` that is only well behaved on `(0, ∞)`. -/
def positiveCutoff (m : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((4 * t - m) / m) * g t

/-- The cutoff vanishes on `(-∞, m/4]`. -/
@[simp]
theorem positiveCutoff_of_le {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : t ≤ m / 4) : positiveCutoff m g t = 0 := by
  rw [positiveCutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hm.le), zero_mul]

/-- The cutoff agrees with `g` on `[m/2, ∞)`. -/
@[simp]
theorem positiveCutoff_of_ge {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : m / 2 ≤ t) : positiveCutoff m g t = g t := by
  rw [positiveCutoff, Real.smoothTransition.one_of_one_le
    (by rw [le_div_iff₀ hm]; linarith), one_mul]

/-- The cutoff agrees with `g` near every point of `(m/2, ∞)`. -/
theorem positiveCutoff_eventuallyEq {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : m / 2 < t) : positiveCutoff m g =ᶠ[𝓝 t] g := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact positiveCutoff_of_ge hm g (le_of_lt hs)

/-- On `(m/2, ∞)` the derivative of the cutoff is the derivative of `g`. -/
theorem deriv_positiveCutoff {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) {t : ℝ}
    (ht : m / 2 < t) : deriv (positiveCutoff m g) t = deriv g t :=
  (positiveCutoff_eventuallyEq hm g ht).deriv_eq

/-- The cutoff of a function that is nonnegative on `(0, ∞)` is nonnegative. -/
theorem positiveCutoff_nonneg {m : ℝ} (hm : 0 < m) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → 0 ≤ g t) (t : ℝ) : 0 ≤ positiveCutoff m g t := by
  rcases le_or_gt t (m / 4) with ht | ht
  · rw [positiveCutoff_of_le hm g ht]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (hg t (by linarith))

/-- The cutoff of a function that is `C¹` on `(0, ∞)` is `C¹` on the whole line. -/
theorem contDiff_positiveCutoff {m : ℝ} (hm : 0 < m) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ContDiffAt ℝ 1 g t) : ContDiff ℝ 1 (positiveCutoff m g) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (m / 4) with ht | ht
  · -- Below `m/4` the function vanishes identically.
    have hev : positiveCutoff m g =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact positiveCutoff_of_le hm g (le_of_lt hs)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hs : ContDiffAt ℝ 1 (fun s : ℝ => Real.smoothTransition ((4 * s - m) / m)) t :=
      Real.smoothTransition.contDiffAt.comp t
        (((contDiffAt_id.const_smul (4 : ℝ)).sub contDiffAt_const).div_const m)
    exact hs.mul (hg t (by linarith))

/-- If `g` is `C¹` on `(0, ∞)` and `|g'| ≤ K` on `[m, ∞)`, then the derivative of the cutoff is
bounded on the whole line. -/
theorem exists_nnnorm_deriv_positiveCutoff_le {m : ℝ} (hm : 0 < m) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ContDiffAt ℝ 1 g t) {K : ℝ} (hK : ∀ t, m ≤ t → |deriv g t| ≤ K) :
    ∃ M : ℝ≥0, ∀ t, ‖deriv (positiveCutoff m g) t‖₊ ≤ M := by
  have hcont : Continuous (deriv (positiveCutoff m g)) :=
    (contDiff_positiveCutoff hm hg).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Icc (m / 4) m))
  refine ⟨Real.toNNReal (max C K), fun t => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  rcases lt_or_ge t (m / 4) with ht | ht
  · -- Below `m/4` the derivative vanishes.
    have hev : positiveCutoff m g =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact positiveCutoff_of_le hm g (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const, norm_zero]
    exact le_trans (norm_nonneg _) ((hC (m / 4) ⟨le_rfl, by linarith⟩).trans (le_max_left _ _))
  rcases le_or_gt t m with htm | htm
  · exact (hC t ⟨ht, htm⟩).trans (le_max_left _ _)
  · rw [deriv_positiveCutoff hm g (by linarith), Real.norm_eq_abs]
    exact (hK t htm.le).trans (le_max_right _ _)

end TauCeti
