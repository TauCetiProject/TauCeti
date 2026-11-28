/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic

/-!
# Faithful direct-sum representations

A direct sum of finite free comodules over a commutative ring is faithful if either
summand is faithful. The matrix coefficients and their antipode images for a faithful summand
already generate the coordinate Hopf algebra, and remain coefficients of the direct sum.

Faithfulness is the library's closed-immersion predicate `Comodule.IsFaithful`, equivalently
surjectivity of the coordinate Hopf-algebra morphism for a finite basis.
-/

public section

universe u

namespace TauCeti.Comodule

variable {k H M V : Type u} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [AddCommMonoid M] [Module k M] [Comodule k H M]
  [AddCommMonoid V] [Module k V] [Comodule k H V]

attribute [local instance] Prod

/-- A direct sum with a faithful first summand is faithful. -/
theorem IsFaithful.prod_left [Module.Free k V] [Module.Finite k V]
    (hM : IsFaithful (k := k) (H := H) (V := M)) :
    IsFaithful (k := k) (H := H) (V := M × V) := by
  obtain ⟨_, b, -⟩ := isFaithful_def.mp hM
  let : Module.Free k M := Module.Free.of_basis b
  let : Module.Finite k M := Module.Finite.of_basis b
  apply (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top
    ((Module.Free.chooseBasis k (M × V)).reindex (Fintype.equivFin _))).mpr
  apply top_unique
  rw [← (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top b).mp hM,
    matrixCoefficientSubalgebra_prod]
  exact sup_le_sup le_sup_left (Subalgebra.map_mono le_sup_left)

/-- A direct sum with a faithful second summand is faithful. -/
theorem IsFaithful.prod_right [Module.Free k M] [Module.Finite k M]
    (hV : IsFaithful (k := k) (H := H) (V := V)) :
    IsFaithful (k := k) (H := H) (V := M × V) := by
  obtain ⟨_, b, -⟩ := isFaithful_def.mp hV
  let : Module.Free k V := Module.Free.of_basis b
  let : Module.Finite k V := Module.Finite.of_basis b
  apply (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top
    ((Module.Free.chooseBasis k (M × V)).reindex (Fintype.equivFin _))).mpr
  apply top_unique
  rw [← (isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top b).mp hV,
    matrixCoefficientSubalgebra_prod]
  exact sup_le_sup le_sup_right (Subalgebra.map_mono le_sup_right)

end TauCeti.Comodule

