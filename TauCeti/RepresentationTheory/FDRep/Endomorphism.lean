/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Categorical endomorphisms and intertwining algebras

The endomorphism algebra of a finite-dimensional representation is the algebra of
intertwining operators on its underlying module. This comparison lets computations
of a commutant on a concrete carrier supply the native categorical endomorphism algebra.
It combines `FDRep.forget₂HomLinearEquiv` and `Rep.homLinearEquiv` with
`CategoryTheory.End.linearEquiv`, retaining the multiplication of the operator algebra.
-/

public section

open CategoryTheory

namespace FDRep

universe u v

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- Categorical endomorphisms of a finite-dimensional representation are its intertwining
operators, with the same composition and scalar multiplication. -/
noncomputable def endIntertwiningAlgEquiv (A : FDRep k G) :
    End A ≃ₐ[k] Representation.IntertwiningMap A.ρ A.ρ :=
  AlgEquiv.ofLinearEquiv
    ((End.linearEquiv (R := k)).trans ((forget₂HomLinearEquiv A A).symm.trans
      (Rep.homLinearEquiv _ _))) (by ext x; rfl) (by intro f g; ext x; rfl)

/-- The endomorphism comparison retains the underlying operator. -/
@[simp]
theorem endIntertwiningAlgEquiv_apply (A : FDRep k G) (f : End A) (x : A) :
    A.endIntertwiningAlgEquiv f x = f.asHom.hom.hom.hom x := (rfl)

/-- The inverse comparison bundles the same intertwining operator. -/
@[simp]
theorem endIntertwiningAlgEquiv_symm_apply (A : FDRep k G)
    (f : Representation.IntertwiningMap A.ρ A.ρ) (x : A) :
    (A.endIntertwiningAlgEquiv.symm f).asHom.hom.hom.hom x = f x := (rfl)

end FDRep
