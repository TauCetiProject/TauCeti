/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic

/-!
# Restricting associative-algebra derivations to the center

Every derivation of an associative algebra preserves its center. Restriction is a Lie algebra
homomorphism to the ordinary derivations of the commutative center, and inner derivations are
in its kernel. Thus an outer derivation has a well-defined action on central characters.

## References

* N. Jacobson, *Lie Algebras* (1962), Chapter I, §2.
-/

public section

namespace TauCeti.derivationLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Derivations of an associative algebra preserve its center. -/
theorem map_mem_center (D : derivationLieAlgebra R A) {z : A}
    (hz : z ∈ Subalgebra.center R A) :
    (D : Module.End R A) z ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  have h := congrArg (D : Module.End R A) (hz a)
  simp only [leibniz] at h
  rw [hz ((D : Module.End R A) a), add_comm ((D : Module.End R A) z * a)] at h
  exact add_left_cancel h

variable (R A) in
/-- Restriction to the center, as a homomorphism of Lie algebras. -/
def restrictCenter : derivationLieAlgebra R A →ₗ⁅R⁆
    Derivation R (Subalgebra.center R A) (Subalgebra.center R A) where
  toFun D :=
    { toLinearMap :=
        { toFun z := ⟨(D : Module.End R A) z, map_mem_center D z.property⟩
          map_add' x y := Subtype.ext (map_add (D : Module.End R A) (x : A) (y : A))
          map_smul' r x := Subtype.ext (map_smul (D : Module.End R A) r (x : A)) }
      map_one_eq_zero' := Subtype.ext (apply_one_eq_zero D)
      leibniz' x y := Subtype.ext <| by
        dsimp
        rw [leibniz, Subalgebra.mem_center_iff.mp y.property ((D : Module.End R A) x),
          add_comm] }
  map_add' D E := by ext z; rfl
  map_smul' r D := by ext z; rfl
  map_lie' {D E} := by ext z; rfl

/-- Restriction evaluates by applying the original derivation. -/
@[simp]
theorem coe_restrictCenter_apply (D : derivationLieAlgebra R A) (z : Subalgebra.center R A) :
    (restrictCenter R A D z : A) = (D : Module.End R A) z :=
  (rfl)

/-- Inner derivations vanish on the center. -/
@[simp]
theorem restrictCenter_innerDerivation (b : A) :
    restrictCenter R A (innerDerivation R b) = 0 := by
  ext z
  simp only [coe_restrictCenter_apply, coe_innerDerivation, LieAlgebra.ad_apply,
    Ring.lie_def, Derivation.zero_apply, ZeroMemClass.coe_zero]
  exact sub_eq_zero.mpr (Subalgebra.mem_center_iff.mp z.property b)

end TauCeti.derivationLieAlgebra
