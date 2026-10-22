/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType

/-!
# Finitely many homomorphisms out of a finite-type algebra into a finite algebra

An algebra homomorphism out of a finitely generated `R`-algebra `A` is determined by its values
on a finite generating set. So when the target `B` is finite there are only finitely many of
them. Applied to the coordinate algebra of an affine scheme of finite type over a finite field
`𝔽_q`, this says that the scheme has finitely many `𝔽_q`-points, and more generally finitely
many points over any finite `𝔽_q`-algebra.

## Main declarations

* `Algebra.FiniteType.finite_algHom`: `A →ₐ[R] B` is finite when `A` is of finite type over `R`
  and `B` is finite.
-/

public section

/-- **A finite-type algebra has finitely many homomorphisms into a finite algebra**: such a
homomorphism is determined by its values on a finite generating set. -/
instance Algebra.FiniteType.finite_algHom {R A B : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [Algebra.FiniteType R A] [Finite B] :
    Finite (A →ₐ[R] B) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  exact Finite.of_injective (fun φ : A →ₐ[R] B => fun x : (s : Set A) => φ x) fun φ ψ h =>
    AlgHom.ext_of_adjoin_eq_top hs fun x hx => congrFun h ⟨x, hx⟩
