/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree.Simple
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.Stabilizer
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Restriction

/-!
# Restriction detects virtual S₃ modules in characteristic three

Over a field of characteristic three, restriction to any point stabilizer carries the
trivial–sign basis of the exact Grothendieck group of S₃ to the corresponding basis for
the stabilizer. Consequently restriction is bijective and preserves both integral
composition multiplicities. Equality of virtual S₃ modules can therefore be checked
after restriction to this subgroup of order two, where representations are semisimple.
This comparison permits induction calculations using restricted representations
without losing composition-factor information.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable (k : Type) [Field k] [CharP k 3] (a : Fin 3)

local instance : NeZero (2 : k) := NeZero.of_not_dvd k (by decide : ¬3 ∣ 2)

/-- Restriction to a point stabilizer preserves the two simple-class basis vectors of S₃
in characteristic three: the trivial line and the sign line. -/
-- Simplify before the basis-vector class formulas expand the argument.
@[simp↓]
theorem resK0_stabilizer_perm_fin_three_simpleClassBasis_apply (b : Bool) :
    resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype
        (symmetricThreeCharThreeSimpleClassBasis k b) =
      symmetricThreeStabilizerSimpleClassBasis k a b := by
  rw [symmetricThreeCharThreeSimpleClassBasis_apply,
    symmetricThreeStabilizerSimpleClassBasis_apply, resK0_of_asModule,
    Representation.ofLinearCharacter_comp]
  cases b <;> simp

private theorem resK0_eq_basisEquiv :
    (resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype).toIntLinearMap =
      ((symmetricThreeCharThreeSimpleClassBasis k).equiv
        (symmetricThreeStabilizerSimpleClassBasis k a) (Equiv.refl Bool)).toLinearMap := by
  apply (symmetricThreeCharThreeSimpleClassBasis k).ext
  intro b
  simpa only [AddMonoidHom.coe_toIntLinearMap, LinearEquiv.coe_coe,
    Module.Basis.equiv_apply, Equiv.refl_apply] using
    resK0_stabilizer_perm_fin_three_simpleClassBasis_apply k a b

/-- Restriction preserves the integral composition coordinates, ordered as trivial and sign.
In particular either multiplicity can be computed on the restricted representation. -/
@[simp]
theorem symmetricThreeStabilizerSimpleClassBasis_repr_resK0
    (x : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) :
    (symmetricThreeStabilizerSimpleClassBasis k a).repr
        (resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype x) =
      (symmetricThreeCharThreeSimpleClassBasis k).repr x := by
  have h : (symmetricThreeStabilizerSimpleClassBasis k a).repr.toLinearMap.comp
        (resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype).toIntLinearMap =
      (symmetricThreeCharThreeSimpleClassBasis k).repr.toLinearMap := by
    apply (symmetricThreeCharThreeSimpleClassBasis k).ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      AddMonoidHom.coe_toIntLinearMap, resK0_stabilizer_perm_fin_three_simpleClassBasis_apply,
      Module.Basis.repr_self]
  exact DFunLike.congr_fun h x

/-- Restriction from S₃ to any point stabilizer is bijective on exact Grothendieck groups
over every field of characteristic three. This concerns composition-factor classes;
it does not assert that restriction detects isomorphisms of representations. -/
theorem resK0_stabilizer_perm_fin_three_bijective :
    Function.Bijective (resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype) := by
  have h := resK0_eq_basisEquiv k a
  simpa only [← LinearEquiv.coe_toLinearMap, ← h, AddMonoidHom.coe_toIntLinearMap] using
    ((symmetricThreeCharThreeSimpleClassBasis k).equiv
      (symmetricThreeStabilizerSimpleClassBasis k a) (Equiv.refl Bool)).bijective

end TauCeti
