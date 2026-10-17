/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Signature
public import TauCeti.LinearAlgebra.Matrix.Metabolic

/-!
# The trefoil is not algebraically slice

A knot is algebraically slice when its Seifert matrix is metabolic (`Matrix.IsMetabolic`). A
metabolic matrix `V` with `V + Vᵀ` invertible has signature zero
(`Matrix.IsMetabolic.signature_eq_zero`), so a Seifert matrix of nonzero signature is not
metabolic. This file applies the obstruction to the trefoil, whose Seifert matrix has signature
`-2` and `det (V + Vᵀ) = 3`, as a check that the predicate is not vacuous.

## Main results

* `TauCeti.KnotTheory.not_isMetabolic_map_trefoilSeifertMatrix` and
  `TauCeti.KnotTheory.not_isMetabolic_trefoilSeifertMatrix`: the Seifert matrix of the trefoil is
  not metabolic, even over an ordered field, so the trefoil is not algebraically slice.

## References

* J. Levine, *Knot cobordism groups in codimension two*, Comment. Math. Helv. 44 (1969),
  229--244.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8.
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The trefoil is not algebraically slice**: its Seifert matrix is not metabolic, even over an
ordered field, because its signature is `-2` while `V + Vᵀ` has determinant `3`. -/
theorem not_isMetabolic_map_trefoilSeifertMatrix :
    ¬ (trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜)).IsMetabolic := by
  intro h
  have hdet : IsUnit (trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜) +
      (trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜))ᵀ).det := by
    rw [map_trefoilSeifertMatrix, isUnit_iff_ne_zero, det_fin_two]
    norm_num
  have := h.signature_eq_zero hdet
  rw [signature_trefoilSeifertMatrix] at this
  omega

/-- The integral Seifert matrix of the trefoil is not metabolic. -/
theorem not_isMetabolic_trefoilSeifertMatrix : ¬ trefoilSeifertMatrix.IsMetabolic :=
  fun h => not_isMetabolic_map_trefoilSeifertMatrix (𝕜 := ℚ) (h.map (Int.castRingHom ℚ))

end TauCeti.KnotTheory
