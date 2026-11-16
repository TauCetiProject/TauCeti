/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A smooth `1`-periodic bump function

For `t₀ c : ℝ`, `TauCeti.periodicBump t₀ c` is the smooth `1`-periodic function
`t ↦ Real.smoothTransition (2 (cos (2π(t - t₀)) - c) / (1 - c))`, with values in `[0, 1]`. For
`c < 1` it is `1` near `t₀ + ℤ`, where `cos (2π(t - t₀)) ≥ (1 + c)/2`, and vanishes where
`cos (2π(t - t₀)) ≤ c`; taking `c` close to `1` concentrates it near `t₀ + ℤ`. It localizes
variations of loops near a given time while keeping them loops.

## Main declarations

* `TauCeti.periodicBump`: the periodic bump, with defining formula `TauCeti.periodicBump_def`.
* `TauCeti.contDiff_periodicBump`, `TauCeti.periodicBump_add_one`: it is smooth and `1`-periodic.
* `TauCeti.periodicBump_eq_one`, `TauCeti.eventually_periodicBump_eq_one`: it is `1` where
  `cos (2π(t - t₀)) ≥ (1 + c)/2`, hence near its centre.
* `TauCeti.periodicBump_eq_zero`: it vanishes where `cos (2π(t - t₀)) ≤ c`.
* `TauCeti.tsupport_periodicBump_subset`: its closed support lies where `cos (2π(t - t₀)) ≥ c`.
-/

public section

noncomputable section

open Real
open scoped Topology

namespace TauCeti

/-- A smooth `1`-periodic bump function centred at `t₀ + ℤ`: for `c < 1` it is `1` where
`cos (2π(t - t₀)) ≥ (1 + c)/2` and `0` where `cos (2π(t - t₀)) ≤ c`. -/
def periodicBump (t₀ c t : ℝ) : ℝ :=
  smoothTransition (2 * (cos (2 * π * (t - t₀)) - c) / (1 - c))

/-- The defining formula of the periodic bump. -/
theorem periodicBump_def (t₀ c t : ℝ) :
    periodicBump t₀ c t = smoothTransition (2 * (cos (2 * π * (t - t₀)) - c) / (1 - c)) :=
  (rfl)

/-- The periodic bump is smooth. -/
theorem contDiff_periodicBump {n : ℕ∞} (t₀ c : ℝ) : ContDiff ℝ n (periodicBump t₀ c) :=
  smoothTransition.contDiff.comp
    (((contDiff_const.mul ((contDiff_cos.comp ((contDiff_const.mul
      (contDiff_id.sub contDiff_const)))).sub contDiff_const))).div_const _)

/-- The periodic bump is `1`-periodic. -/
@[simp]
theorem periodicBump_add_one (t₀ c t : ℝ) :
    periodicBump t₀ c (t + 1) = periodicBump t₀ c t := by
  rw [periodicBump, periodicBump, show 2 * π * (t + 1 - t₀) = 2 * π * (t - t₀) + 2 * π by ring,
    cos_add_two_pi]

/-- The periodic bump is nonnegative. -/
theorem periodicBump_nonneg (t₀ c t : ℝ) : 0 ≤ periodicBump t₀ c t :=
  smoothTransition.nonneg _

/-- The periodic bump is at most `1`. -/
theorem periodicBump_le_one (t₀ c t : ℝ) : periodicBump t₀ c t ≤ 1 :=
  smoothTransition.le_one _

/-- The periodic bump vanishes where `cos (2π(t - t₀)) ≤ c`. -/
@[simp]
theorem periodicBump_eq_zero {t₀ c t : ℝ} (hc : c < 1) (h : cos (2 * π * (t - t₀)) ≤ c) :
    periodicBump t₀ c t = 0 :=
  smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- The periodic bump is `1` where `cos (2π(t - t₀)) ≥ (1 + c)/2`. -/
@[simp]
theorem periodicBump_eq_one {t₀ c t : ℝ} (hc : c < 1)
    (h : (1 + c) / 2 ≤ cos (2 * π * (t - t₀))) : periodicBump t₀ c t = 1 := by
  refine smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The periodic bump is `1` near its centre. -/
theorem eventually_periodicBump_eq_one {t₀ c : ℝ} (hc : c < 1) :
    ∀ᶠ t in 𝓝 t₀, periodicBump t₀ c t = 1 := by
  have hcont : Continuous fun t ↦ cos (2 * π * (t - t₀)) := by fun_prop
  have hlt : (1 + c) / 2 < cos (2 * π * (t₀ - t₀)) := by rw [sub_self, mul_zero, cos_zero]; linarith
  filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hlt)] with t ht
  exact periodicBump_eq_one hc ht.le

/-- The support of the periodic bump lies where `cos (2π(t - t₀)) > c`. -/
theorem lt_cos_of_periodicBump_ne_zero {t₀ c t : ℝ} (hc : c < 1)
    (h : periodicBump t₀ c t ≠ 0) : c < cos (2 * π * (t - t₀)) :=
  not_le.mp fun hle ↦ h (periodicBump_eq_zero hc hle)

/-- The closed support of the periodic bump lies where `cos (2π(t - t₀)) ≥ c`. -/
theorem tsupport_periodicBump_subset {t₀ c : ℝ} (hc : c < 1) :
    tsupport (periodicBump t₀ c) ⊆ {t | c ≤ cos (2 * π * (t - t₀))} :=
  closure_minimal (fun _ ht ↦ (lt_cos_of_periodicBump_ne_zero hc ht).le)
    (isClosed_le continuous_const (by fun_prop))

end TauCeti
