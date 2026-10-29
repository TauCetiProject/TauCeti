/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Units from automorphisms of the rank-one free module

An automorphism of a ring as a module over itself sends one to a unit. Consequently,
the scalar comparing the images of one under two isomorphisms is a unit as well.
-/

public noncomputable section

open CategoryTheory

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

/-- An automorphism of the rank-one free module sends one to a unit. -/
theorem isUnit_apply_one_of_isIso (f : ModuleCat.of R R ⟶ ModuleCat.of R R) [IsIso f] :
    IsUnit (f 1) :=
  (((Module.End.isUnit_iff _).2 (ConcreteCategory.bijective_of_isIso f)).map
    (RingEquiv.moduleEndSelf R).symm).unop

/-- The scalar comparing the images of one under two module isomorphisms is a unit. -/
theorem isUnit_of_apply_one_eq_smul {M : ModuleCat R}
    (f g : ModuleCat.of R R ⟶ M) [IsIso f] [IsIso g] {a : R}
    (h : g 1 = a • f 1) : IsUnit a := by
  have hu := isUnit_apply_one_of_isIso (g ≫ inv f)
  simpa only [CategoryTheory.comp_apply, h, map_smul, IsIso.hom_inv_id_apply,
    smul_eq_mul, mul_one] using hu

end ModuleCat
