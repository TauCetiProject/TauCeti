/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.BaseChange
public import TauCeti.Algebra.CrossedProduct.TwoTorsion

/-!
# Base change of the `2`-torsion Brauer subgroup

Scalar extension preserves the subgroup of Brauer classes whose square is trivial. This file
restricts the Brauer-group base-change homomorphism to that subgroup and records its
functoriality.
-/

public section

universe u

namespace TauCeti.BrauerGroup

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

/-- The restriction of Brauer base change to the `2`-torsion subgroups. -/
def twoTorsionBaseChange : twoTorsion K →* twoTorsion L where
  toFun x := ⟨baseChange K L x, mem_twoTorsion.2 (by
    rw [← map_pow, mem_twoTorsion.mp x.property, map_one])⟩
  map_one' := Subtype.ext (map_one (baseChange K L))
  map_mul' x y := Subtype.ext (map_mul (baseChange K L)
    (x : BrauerGroup K) (y : BrauerGroup K))

/-- Coercing the restricted base-change homomorphism to the Brauer group gives ordinary base
change. -/
@[simp]
theorem coe_twoTorsionBaseChange (x : twoTorsion K) :
    ((twoTorsionBaseChange K L x : twoTorsion L) : BrauerGroup L) = baseChange K L x := (rfl)

/-- Base change along the identity restricts to the identity on `2`-torsion. -/
@[simp]
theorem twoTorsionBaseChange_self : twoTorsionBaseChange K K = MonoidHom.id (twoTorsion K) := by
  ext x
  rw [coe_twoTorsionBaseChange, baseChange_self]
  simp only [MonoidHom.id_apply]

variable (M : Type u) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- Restricted base change composes along a tower of field extensions. -/
@[simp]
theorem twoTorsionBaseChange_comp :
    (twoTorsionBaseChange L M).comp (twoTorsionBaseChange K L) = twoTorsionBaseChange K M := by
  ext x
  simp only [MonoidHom.comp_apply, coe_twoTorsionBaseChange]
  exact congrArg (fun f : BrauerGroup K →* BrauerGroup M => f (x : BrauerGroup K))
    (baseChange_comp K L M)

end TauCeti.BrauerGroup
