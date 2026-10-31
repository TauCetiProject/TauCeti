/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Subspace.Basic
public import TauCeti.NumberTheory.Height.NumberField

import TauCeti.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Relative subspace heights in extensions of number fields

For a number-field extension `L / K`, extend a subspace of `K^ι` by taking the `L`-span of
its coordinatewise image in `L^ι`. Its relative sup height raises to the power `[L : K]`,
and its relative logarithmic height multiplies by that degree. This includes the zero
and whole subspaces, whose heights are one.

A basis remains independent after extension, and its Plücker coordinates are the images
of the original coordinates. Thus subspace-height transport uses the tuple-height
extension law without any choice of integral basis or primitive coordinates.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
-/

public noncomputable section

namespace Submodule

open Module Set TauCeti

variable {K L ι : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [LinearOrder ι] [Finite ι]

-- Simplify heights before the set image of the extended subspace is normalized.
/-- The relative sup height of a subspace raises to the extension degree after extending
scalars between number fields. -/
@[simp↓]
theorem relativeSubspaceHeight_span_image_algebraMap (U : Submodule K (ι → K)) :
    relativeSubspaceHeight (span L ((Pi.algebraMap ι K L) '' (U : Set (ι → K)))) =
      relativeSubspaceHeight U ^ finrank K L := by
  let b := finBasis K U
  rw [b.span_image (S := L)]
  simp only [Pi.algebraMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [relativeSubspaceHeight_span_range
    ((linearIndependent_algebraMap_comp_iff (R := K) (S := L)).mpr b.linearIndependent_coe_basis),
    relativeSubspaceHeight_eq_mulHeight_plucker b]
  exact (congrArg Height.mulHeight (Matrix.plucker_row_map (algebraMap K L)
    (Matrix.of fun i ↦ (b i : ι → K)))).trans
      (NumberField.mulHeight_algebraMap (L := L) (plucker fun i ↦ (b i : ι → K)))

/-- The relative logarithmic sup height of a subspace multiplies by the extension degree. -/
@[simp↓]
theorem relativeSubspaceLogHeight_span_image_algebraMap (U : Submodule K (ι → K)) :
    relativeSubspaceLogHeight (span L ((Pi.algebraMap ι K L) '' (U : Set (ι → K)))) =
      finrank K L * relativeSubspaceLogHeight U := by
  rw [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight,
    relativeSubspaceHeight_span_image_algebraMap, Real.log_pow,
    relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight]

end Submodule
