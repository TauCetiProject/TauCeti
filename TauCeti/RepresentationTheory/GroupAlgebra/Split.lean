/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RingTheory.Semisimple.Wedderburn.Split
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.Simple.Basic
import Mathlib.RepresentationTheory.Maschke

/-!
# Split group algebras from scalar Schur

For a finite group whose order is invertible in the coefficient field, scalar Schur
means that every simple finite-dimensional representation has a one-dimensional
endomorphism space. This condition can be checked on the simple left ideals of the
group algebra, and it yields a product decomposition into full matrix algebras over
the coefficient field.

The representation and module conditions are compared using the native group-algebra
module of a representation. Conversely, a simple left ideal gives a finite-dimensional
representation; shrinking its carrier permits independent universes for the group
and the field. Maschke supplies semisimplicity independently of scalar Schur.

These results do not require algebraic closure or characteristic zero. They separate
the splitting condition from the invertibility of the group order.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §§12–13.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and
  Associative Algebras*, §25.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped MonoidAlgebra

universe u v

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G]

/-- Scalar Schur for finite-dimensional representations is equivalent to the
one-dimensionality of the endomorphism algebras of simple left ideals of the group
algebra, when the group order is invertible in the coefficient field. -/
theorem forall_finrank_end_eq_one_iff_forall_ideal_finrank_end_eq_one
    (hG : IsUnit (Nat.card G : k)) :
    (∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1) ↔
      ∀ S : Ideal k[G], IsSimpleModule k[G] S →
        Module.finrank k (Module.End k[G] S) = 1 := by
  have : NeZero (Nat.card G : k) := ⟨hG.ne_zero⟩
  constructor
  · intro h S hS
    have : IsSimpleModule k[G] S := hS
    have : FiniteDimensional k S := inferInstance
    let ρ := _root_.Representation.ofModule' (k := k) (G := G) S
    let V := FDRep.ofShrink ρ
    let e : _root_.Representation.asModule V.ρ ≃ₗ[k[G]] S :=
      (Representation.asModuleLinearEquivOfEquiv (FDRep.ofShrinkEquiv ρ)).trans
        (Representation.ofModule'AsModuleEquiv S)
    have : IsSimpleModule k[G] (_root_.Representation.asModule V.ρ) := .congr e
    have : Simple V := (FDRep.simple_iff_isIrreducible V).mpr
      ((_root_.Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mpr inferInstance)
    calc
      Module.finrank k (Module.End k[G] S) =
          Module.finrank k (Module.End k[G] (_root_.Representation.asModule V.ρ)) :=
        (e.symm.conjAlgEquiv k).toLinearEquiv.finrank_eq
      _ = Module.finrank k (V ⟶ V) := (FDRep.finrank_end_eq_finrank_moduleEnd V).symm
      _ = 1 := h V inferInstance
  · intro h V hV
    have : Simple V := hV
    obtain ⟨S, ⟨e⟩⟩ :=
      _root_.IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule k[G]
        (_root_.Representation.asModule V.ρ)
    have : IsSimpleModule k[G] S := .congr e.symm
    calc
      Module.finrank k (V ⟶ V) =
          Module.finrank k (Module.End k[G] (_root_.Representation.asModule V.ρ)) :=
        FDRep.finrank_end_eq_finrank_moduleEnd V
      _ = Module.finrank k (Module.End k[G] S) := (e.conjAlgEquiv k).toLinearEquiv.finrank_eq
      _ = 1 := h S inferInstance

/-- A finite group algebra is a product of full matrix algebras over the coefficient
field if its order is invertible and every simple finite-dimensional representation
has only scalar endomorphisms. The matrix blocks all have positive size. -/
theorem nonempty_splitWedderburnAlgebraPresentation_of_scalarSchur
    (hG : IsUnit (Nat.card G : k))
    (hSplitG : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1) :
    Nonempty (SplitWedderburnAlgebraPresentation k k[G]) := by
  have : NeZero (Nat.card G : k) := ⟨hG.ne_zero⟩
  exact IsSemisimpleRing.nonempty_splitWedderburnAlgebraPresentation_of_finrank_end_eq_one k k[G]
    ((forall_finrank_end_eq_one_iff_forall_ideal_finrank_end_eq_one k G hG).mp hSplitG)

end TauCeti
