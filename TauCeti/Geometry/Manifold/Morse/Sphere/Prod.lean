/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic

/-!
# The sum of two height functions on a product of spheres is a Morse function

On the product `Sⁿ × Sᵐ` of two unit spheres, the sum `sphereHeight v ∘ Prod.fst +
sphereHeight w ∘ Prod.snd` of the height functions in the directions of the unit vectors `v` and
`w` is a Morse function. Its critical points are the four pairs of poles `(±v, ±w)`, and its Morse
index at `(x, y)` is the sum of the indices of the two height functions, so the four critical
points have indices `n + m`, `n`, `m` and `0`. For `n = m = 1` this is the standard Morse function
on the two-torus `S¹ × S¹`, with one critical point of index `2`, two of index `1` and one of
index `0`.

## Main declarations

* `TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`: the sum of two height functions is Morse
  on the product of spheres.
* `TauCeti.mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff`: its critical points are the
  pairs of poles.
* `TauCeti.manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd`: its Morse index is the sum of
  the indices of the two height functions.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {n m : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ E' = m + 1)]

/-- **The sum of two height functions is a Morse function on a product of spheres.** -/
theorem isMorse_sphereHeight_comp_fst_add_comp_snd (v : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) :
    IsMorse ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) :=
  (isMorse_sphereHeight v).comp_fst_add_comp_snd (isMorse_sphereHeight w)

/-- The critical points of the sum of two height functions on a product of spheres are the four
pairs of poles. -/
@[simp]
theorem mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff (v x : sphere (0 : E) 1)
    (w y : sphere (0 : E') 1) :
    mvfderiv ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) (x, y) =
        0 ↔
      (x = v ∨ x = -v) ∧ (y = w ∨ y = -w) := by
  rw [mvfderiv_comp_fst_add_comp_snd_eq_zero_iff
    ((contMDiff_sphereHeight (m := 1) v x).mdifferentiableAt one_ne_zero)
    ((contMDiff_sphereHeight (m := 1) w y).mdifferentiableAt one_ne_zero),
    mvfderiv_sphereHeight_eq_zero_iff, mvfderiv_sphereHeight_eq_zero_iff]

/-- The Morse index of the sum of two height functions on a product of spheres is the sum of the
indices of the two height functions; at the four critical points these are `n + m`, `n`, `m` and
`0`. -/
@[simp]
theorem manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd (v x : sphere (0 : E) 1)
    (w y : sphere (0 : E') 1) :
    manifoldMorseIndex ((𝓡 n).prod (𝓡 m))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) (x, y) =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x + manifoldMorseIndex (𝓡 m) (sphereHeight w) y :=
  manifoldMorseIndex_comp_fst_add_comp_snd
    (contMDiff_sphereHeight (m := 2) v x).contDiffAt_comp_extChartAt_symm
    (contMDiff_sphereHeight (m := 2) w y).contDiffAt_comp_extChartAt_symm

end TauCeti

end
