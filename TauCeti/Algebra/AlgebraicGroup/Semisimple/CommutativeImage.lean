/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Semisimple groups have no commutative images in characteristic zero

Every homomorphism from a semisimple affine group to a commutative affine group is trivial
in characteristic zero. This includes characters to the multiplicative group, and is the
vanishing statement used to rule out the abelian quotient by the derived subgroup.

The tangent Lie algebra of a semisimple group has nondegenerate Killing form, hence is
perfect. The tangent Lie algebra of a commutative group is abelian, so the differential
of the homomorphism vanishes. Connectedness then makes the homomorphism trivial. Extension
to an algebraic closure and descent give the result over an arbitrary ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
* J. E. Humphreys, *Linear Algebraic Groups*, §27.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every homomorphism from a semisimple affine group to a commutative affine group is trivial
in characteristic zero, as an equality of coordinate morphisms. -/
theorem hom_eq_unit_comp_counit (hH : semisimpleCommHopfAlgProperty k H)
    {C : _root_.CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k C] (f : C ⟶ H.obj) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k H).comp (Bialgebra.counitBialgHom k C)) := by
  let _ := hH.isKilling_lieAlgebra
  exact CommHopfAlgCat.eq_unit_comp_counit_of_isKilling hH.geometricallyConnected f

/-- A semisimple affine group has no nontrivial characters in characteristic zero.
Characters are represented by group-like elements of its coordinate Hopf algebra. -/
theorem groupLike_eq_one (hH : semisimpleCommHopfAlgProperty k H) (x : GroupLike k H) :
    x = 1 := by
  let C := CommHopfAlgCat.of k (MonoidAlgebra k (GroupLike k H))
  have h := hH.hom_eq_unit_comp_counit (C := C)
    (CommHopfAlgCat.ofHom (MonoidAlgebra.liftGroupLikeBialgHom (R := k) (A := H)))
  have hx := congrArg (fun f => f.hom (MonoidAlgebra.single x (1 : k))) h
  simp only [ConcreteCategory.hom_ofHom, BialgHom.comp_apply,
    Bialgebra.counitBialgHom_apply] at hx
  rw [MonoidAlgebra.liftGroupLikeBialgHom_single, MonoidAlgebra.counit_single] at hx
  apply GroupLike.ext
  simpa only [one_smul, CommSemiring.counit_apply, map_one, GroupLike.val_one] using hx

end semisimpleCommHopfAlgProperty

end TauCeti
