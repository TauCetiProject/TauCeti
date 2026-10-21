/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType

/-!
# Algebra homomorphisms out of a finite-type algebra into a finite algebra

An algebra homomorphism out of a finitely generated `R`-algebra `A` is determined by its values on
a finite generating set. So when the target `B` is finite there are only finitely many such
homomorphisms. Geometrically: an affine scheme of finite type over `R` has only finitely many
points with values in a finite `R`-algebra, for instance a finite field.

Mathlib's `Finite.algHom` and the instance on `S →ₐ[R] K` for `Module.Finite R S` need finiteness
of the source as a module; here the source is only of finite type and the target is finite as a
set instead.

## Main declarations

* `Algebra.FiniteType.finite_algHom`: `A →ₐ[R] B` is finite when `A` is a finite-type
  `R`-algebra and `B` is finite.
-/

public section

namespace Algebra.FiniteType

variable (R A B : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- There are only finitely many algebra homomorphisms from a finite-type algebra into a finite
algebra. -/
instance finite_algHom [Algebra.FiniteType R A] [Finite B] : Finite (A →ₐ[R] B) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  exact Finite.of_injective (fun f : A →ₐ[R] B ↦ fun x : s ↦ f x)
    fun f g hfg ↦ AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ congrFun hfg ⟨x, hx⟩

end Algebra.FiniteType
