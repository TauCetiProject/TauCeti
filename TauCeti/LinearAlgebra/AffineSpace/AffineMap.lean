/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Affine maps and line maps

Two computational facts about `AffineMap.lineMap`.

## Main results

* `AffineMap.apply_eq_add_mul_sub`: an affine function on the line is
  `s ↦ f 0 + s * (f 1 - f 0)`.
* `AffineMap.lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul`: the difference of points on two
  segments, at independent parameters, in terms of the endpoints.
-/

public section

namespace AffineMap

/-- An affine function on the line is determined by its values at `0` and `1`. -/
theorem apply_eq_add_mul_sub {k : Type*} [CommRing k] (f : k →ᵃ[k] k) (s : k) :
    f s = f 0 + s * (f 1 - f 0) := by
  have h := f.apply_lineMap (0 : k) 1 s
  rw [lineMap_apply_ring', lineMap_apply_ring'] at h
  simp only [sub_zero, mul_one, add_zero] at h
  rw [h]
  ring

/-- The difference of a point at parameter `s` on the segment `p₀ p₁` and a point at parameter
`t` on the segment `q₀ q₁`. Unlike `AffineMap.lineMap_vsub_lineMap`, the two parameters may
differ. -/
theorem lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul {k V P : Type*} [Ring k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (p₀ p₁ q₀ q₁ : P) (s t : k) :
    lineMap p₀ p₁ s -ᵥ lineMap q₀ q₁ t = (p₀ -ᵥ q₀) + s • (p₁ -ᵥ p₀) - t • (q₁ -ᵥ q₀) := by
  rw [lineMap_apply, lineMap_apply, vadd_vsub_vadd_comm]
  abel

end AffineMap
