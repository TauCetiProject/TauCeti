/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Real translations of the upper half-plane

A real number `r` translates a point `z` of `ℍ` to `r +ᵥ z`. The translation is an isometry of
the hyperbolic metric but not of the modulus: it preserves `‖z‖` exactly when `z` lies on the
perpendicular bisector `re = -r / 2` of `0` and `-r`, since then `z` and `r +ᵥ z` are mirror
images in the imaginary axis. For `r = ±1` that line contains a vertical edge of the standard
fundamental domain, which is how the fundamental-domain API uses these lemmas.

## Main results

* `UpperHalfPlane.normSq_coe_vadd_of_re_eq`, `UpperHalfPlane.norm_coe_vadd_of_re_eq`: on the
  line `re = -r / 2`, translation by `r` preserves the squared norm and the norm.
-/

public section

namespace UpperHalfPlane

/-- On the perpendicular bisector `re = -r / 2` of `0` and `-r`, translation by `r` preserves the
norm-square. -/
lemma normSq_coe_vadd_of_re_eq {r : ℝ} {p : ℍ} (hre : p.re = -r / 2) :
    Complex.normSq ((r +ᵥ p : ℍ) : ℂ) = Complex.normSq (p : ℂ) := by
  simp [Complex.normSq_add, hre]
  ring

/-- On the line `re = -r / 2`, translation by `r` preserves the norm. -/
lemma norm_coe_vadd_of_re_eq {r : ℝ} {p : ℍ} (hre : p.re = -r / 2) :
    ‖((r +ᵥ p : ℍ) : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [Complex.norm_def, Complex.norm_def, normSq_coe_vadd_of_re_eq hre]

end UpperHalfPlane

end
