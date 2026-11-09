/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
public import TauCeti.NumberTheory.Height.Arakelov.Extension

import TauCeti.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Euclidean subspace heights in extensions of number fields

Extending a subspace from `K^ι` to its `L`-span in `L^ι` raises its relative Arakelov
height to the power `[L : K]` and preserves its absolute Euclidean height. The same laws
hold additively for their logarithms. They allow subspace-height estimates proved over a
normal closure to descend to the original number field.

These statements use the native Plücker point: the extended basis has the coordinatewise
images of the original maximal minors. The zero subspace is included, with its singleton
Plücker coordinate one, as is an empty ambient coordinate type.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1 and §6.3.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
-/

public noncomputable section

namespace Submodule

open Module Set TauCeti

variable {K L ι : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [LinearOrder ι] [Finite ι]

-- Simplify heights before the set image of the extended subspace is normalized.
/-- Relative Euclidean subspace height raises to the extension degree. -/
@[simp↓]
theorem relativeSubspaceArakelovHeight_span_image_algebraMap (U : Submodule K (ι → K)) :
    relativeSubspaceArakelovHeight (span L ((Pi.algebraMap ι K L) '' (U : Set (ι → K)))) =
      relativeSubspaceArakelovHeight U ^ finrank K L := by
  let b := finBasis K U
  rw [b.span_image (S := L)]
  simp only [Pi.algebraMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [relativeSubspaceArakelovHeight_span_range
    ((linearIndependent_algebraMap_comp_iff (R := K) (S := L)).mpr b.linearIndependent_coe_basis),
    relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b]
  exact (congrArg arakelovMulHeight (Matrix.plucker_row_map (algebraMap K L)
    (Matrix.of fun i ↦ (b i : ι → K)))).trans
      (arakelovMulHeight_algebraMap (L := L) (plucker fun i ↦ (b i : ι → K)))

/-- Relative logarithmic Euclidean subspace height multiplies by the extension degree. -/
@[simp↓]
theorem relativeSubspaceArakelovLogHeight_span_image_algebraMap (U : Submodule K (ι → K)) :
    relativeSubspaceArakelovLogHeight (span L ((Pi.algebraMap ι K L) '' (U : Set (ι → K)))) =
      finrank K L * relativeSubspaceArakelovLogHeight U := by
  rw [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight,
    relativeSubspaceArakelovHeight_span_image_algebraMap, Real.log_pow,
    relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight]

/-- Absolute Euclidean subspace height is independent of the containing number field. -/
@[simp↓]
theorem subspaceHeight_span_image_algebraMap (U : Submodule K (ι → K)) :
    subspaceHeight (span L ((Pi.algebraMap ι K L) '' (U : Set (ι → K)))) =
      subspaceHeight U := by
  let b := finBasis K U
  rw [b.span_image (S := L)]
  simp only [Pi.algebraMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [subspaceHeight_span_range
    ((linearIndependent_algebraMap_comp_iff (R := K) (S := L)).mpr b.linearIndependent_coe_basis),
    subspaceHeight_eq_height2_plucker b]
  exact (congrArg height2 (Matrix.plucker_row_map (algebraMap K L)
    (Matrix.of fun i ↦ (b i : ι → K)))).trans
      (height2_algebraMap (L := L) (plucker fun i ↦ (b i : ι → K)))

/-- Absolute logarithmic Euclidean subspace height is independent of the containing number
field. -/
@[simp↓]
theorem subspaceLogHeight_span_image_algebraMap (U : Submodule K (ι → K)) :
    subspaceLogHeight (span L ((Pi.algebraMap ι K L) '' (U : Set (ι → K)))) =
      subspaceLogHeight U := by
  simp only [subspaceLogHeight_eq_log_subspaceHeight, subspaceHeight_span_image_algebraMap]

end Submodule
