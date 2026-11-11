/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Product

/-!
# Faithful direct-sum representations

A direct sum of finite-dimensional comodules over a field is faithful if either summand is
faithful. The matrix coefficients and their antipode images for a faithful summand already
generate the coordinate Hopf algebra, and remain coefficients of the direct sum.

Faithfulness is the library's closed-immersion predicate `Comodule.IsFaithful`, equivalently
surjectivity of the coordinate Hopf-algebra morphism for a finite basis.
-/

public section

universe u

namespace TauCeti.Comodule

variable {k H M V : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
  [AddCommGroup V] [Module k V] [Comodule k H V] [Module.Finite k V]

attribute [local instance] Prod

/-- A direct sum with a faithful first summand is faithful. -/
theorem IsFaithful.prod_left (hM : IsFaithful (k := k) (H := H) (V := M)) :
    IsFaithful (k := k) (H := H) (V := M × V) := by
  apply (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top
    (Module.finBasis k (M × V))).mpr
  apply top_unique
  rw [← (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top
    (Module.finBasis k M)).mp hM, matrixCoefficientSubalgebra_prod]
  exact sup_le_sup le_sup_left (Subalgebra.map_mono le_sup_left)

/-- A direct sum with a faithful second summand is faithful. -/
theorem IsFaithful.prod_right (hV : IsFaithful (k := k) (H := H) (V := V)) :
    IsFaithful (k := k) (H := H) (V := M × V) := by
  apply (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top
    (Module.finBasis k (M × V))).mpr
  apply top_unique
  rw [← (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top
    (Module.finBasis k V)).mp hV, matrixCoefficientSubalgebra_prod]
  exact sup_le_sup le_sup_right (Subalgebra.map_mono le_sup_right)

end TauCeti.Comodule

