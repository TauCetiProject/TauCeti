/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LinearCharacter
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree.Restriction

/-!
# Inducing the sign line from a point stabilizer of S₃ in characteristic three

The two simple classes of a point stabilizer induce to `2[k] + [sgn]` and
`[k] + 2[sgn]`, respectively. The latter calculation uses the projection formula:
the sign line of the stabilizer is the restriction of the sign line of S₃, and its
square is the trivial line. These two vectors have determinant three in the
trivial–sign basis, the input for the index-three induced-subgroup calculation.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable (k : Type) [Field k] [CharP k 3] (a : Fin 3)

local instance : NeZero (2 : k) := NeZero.of_not_dvd k (by decide : ¬3 ∣ 2)
local notation "H" => MulAction.stabilizer (Equiv.Perm (Fin 3)) a
local notation "B" => symmetricThreeCharThreeSimpleClassBasis k
local notation "C" => symmetricThreeStabilizerSimpleClassBasis k a

omit [CharP k 3] in
private theorem signLinearCharacter_mul_self :
    signLinearCharacter k (Fin 3) * signLinearCharacter k (Fin 3) = 1 := by
  ext g
  simp only [MonoidHom.mul_apply, Units.val_mul, coe_signLinearCharacter_apply,
    MonoidHom.one_apply, Units.val_one]
  have h := Int.units_mul_self (Equiv.Perm.sign g)
  have hz : (Equiv.Perm.sign g : ℤ) * (Equiv.Perm.sign g : ℤ) = 1 :=
    congrArg Units.val h
  simpa only [Int.cast_mul, Int.cast_one] using congrArg (fun z : ℤ => (z : k)) hz

-- `symmetricThreeCharThreeSimpleClassBasis_apply` simplifies the left side before this theorem
-- can fire as a simp lemma; use the named theorem to rewrite the class product.
/-- The sign basis vector squares to the unit in the characteristic-three Grothendieck ring. -/
theorem symmetricThreeCharThreeSimpleClassBasis_true_mul_self :
    symmetricThreeCharThreeSimpleClassBasis k true *
        symmetricThreeCharThreeSimpleClassBasis k true = 1 := by
  rw [symmetricThreeCharThreeSimpleClassBasis_true, exactK0_ofLinearCharacter_mul,
    signLinearCharacter_mul_self]
  exact exactK0_ofLinearCharacter_one

/-- Induction of the restricted sign line from any point stabilizer of S₃ has one
trivial and two sign composition factors in characteristic three. -/
theorem indK0_sign_stabilizer_perm_fin_three_char_three :
    indK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a)
        (symmetricThreeStabilizerSimpleClassBasis k a true) =
      symmetricThreeCharThreeSimpleClassBasis k false +
        2 • symmetricThreeCharThreeSimpleClassBasis k true := by
  have hres : resK0 k (H : Subgroup (Equiv.Perm (Fin 3))).subtype (B true) = C true :=
    resK0_stabilizer_perm_fin_three_simpleClassBasis_apply k a true
  have hind : indK0 k H 1 = 2 • B false + B true := by
    rw [symmetricThreeCharThreeSimpleClassBasis_false,
      symmetricThreeCharThreeSimpleClassBasis_true]
    exact indK0_one_stabilizer_perm_fin_three_char_three k a
  calc
    indK0 k H (C true) =
        indK0 k H (1 * resK0 k (H : Subgroup (Equiv.Perm (Fin 3))).subtype (B true)) := by
      rw [one_mul, hres]
    _ = indK0 k H 1 * B true := indK0_mul_resK0 1 (B true)
    _ = B false + 2 • B true := by
      rw [hind, symmetricThreeCharThreeSimpleClassBasis_false, add_mul, smul_mul_assoc, one_mul,
        symmetricThreeCharThreeSimpleClassBasis_true_mul_self]
      abel

end TauCeti
