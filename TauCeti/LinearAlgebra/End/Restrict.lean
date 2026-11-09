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

An algebra map `φ : A →ₐ[R] Module.End R M` whose image preserves a submodule `p` restricts to an
algebra map `A →ₐ[R] Module.End R p`, sending `a` to the restriction of `φ a`. This is the
algebra-map form of `LinearMap.restrict`; it presents an invariant subspace of a representation,
such as an eigenspace of a central or commuting element, as a representation in its own right.

## Main definitions

* `AlgHom.restrictEnd`: the restriction of `φ` to an invariant submodule `p`.
-/

public section

namespace AlgHom

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
  [Module R M]

/-- An algebra map `φ` into the endomorphisms of `M` whose image preserves a submodule `p`
restricts to an algebra map into the endomorphisms of `p`, sending `a` to the restriction of
`φ a`. -/
def restrictEnd (φ : A →ₐ[R] Module.End R M) (p : Submodule R M)
    (hp : ∀ a, ∀ x ∈ p, φ a x ∈ p) : A →ₐ[R] Module.End R p where
  toFun a := (φ a).restrict (hp a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by ext; simp

@[simp]
theorem restrictEnd_apply_coe (φ : A →ₐ[R] Module.End R M) (p : Submodule R M)
    (hp : ∀ a, ∀ x ∈ p, φ a x ∈ p) (a : A) (x : p) :
    (φ.restrictEnd p hp a x : M) = φ a x :=
  (rfl)

end AlgHom
