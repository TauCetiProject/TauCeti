/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Algebra.Basic

/-!
# Restricting a representation to an invariant submodule

An algebra map `φ : A →ₐ[R] Module.End S M` whose image preserves an `S`-submodule `p` restricts to
an algebra map `A →ₐ[R] Module.End S p`, sending `a` to the restriction of `φ a`. This is the
algebra-map form of `LinearMap.restrict`; it presents an invariant subspace of a representation,
such as an eigenspace of a central or commuting element, as a representation in its own right.

## Main definitions

* `AlgHom.restrictEnd`: the restriction of `φ` to an invariant submodule `p`.
-/

public section

namespace AlgHom

variable {R S A M : Type*} [CommSemiring R] [Semiring S] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module S M] [Module R M] [SMul R S] [SMulCommClass S R M]
  [IsScalarTower R S M]

/-- An algebra map `φ` into the endomorphisms of `M` whose image preserves a submodule `p`
restricts to an algebra map into the endomorphisms of `p`, sending `a` to the restriction of
`φ a`. -/
def restrictEnd (φ : A →ₐ[R] Module.End S M) (p : Submodule S M)
    (hp : ∀ a, ∀ x ∈ p, φ a x ∈ p) : A →ₐ[R] Module.End S p where
  toFun a := (φ a).restrict (hp a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by ext; simp [LinearMap.restrict_apply]

@[simp]
theorem coe_restrictEnd_apply (φ : A →ₐ[R] Module.End S M) (p : Submodule S M)
    (hp : ∀ a, ∀ x ∈ p, φ a x ∈ p) (a : A) (x : p) :
    (φ.restrictEnd p hp a x : M) = φ a x :=
  (rfl)

end AlgHom
