/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Composition and basis bijectivity through the base change adjunction

For an `R`-algebra `A`, an `R`-algebra `S` and an `S`-algebra map `q : S →ₐ[S] T`,
`AlgHom.liftEquiv` identifies `R`-algebra maps `A → S` and `A → T` with `S`-algebra maps out of
`S ⊗[R] A`, compatibly with composition by `q`. We record the left-inverse identity
`AlgHom.liftEquiv_comp_includeRight` (composing `f.liftEquiv R S A B` with
`Algebra.TensorProduct.includeRight` recovers `f`) and show that composing with `q` is bijective on
`R`-algebra maps out of `A` if and only if it is bijective on `S`-algebra maps out of `S ⊗[R] A`
(`AlgHom.restrictScalars_comp_bijective_iff`). This reduces lifting problems for algebras over an
arbitrary base `R` to lifting problems over `S` itself.

When an `R`-algebra map `φ : A →ₐ[R] B` into an `S`-algebra `B` carries an `R`-basis of `A` to an
`S`-basis of `B`, the induced `S`-algebra multiplication map `AlgHom.liftEquiv R S A B φ` is
bijective (`AlgHom.liftEquiv_bijective_of_basis`).
-/

public section

open scoped TensorProduct

namespace AlgHom

/-- Composing `f.liftEquiv R S A B` with `Algebra.TensorProduct.includeRight` recovers `f`. -/
@[simp]
theorem liftEquiv_comp_includeRight {R S A B : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (f : A →ₐ[R] B) :
    ((f.liftEquiv R S A B).restrictScalars R).comp Algebra.TensorProduct.includeRight = f :=
  (AlgHom.liftEquiv R S A B).left_inv f

section Comp

variable (R : Type*) {S T : Type*} (A : Type*) [CommSemiring R] [CommSemiring S] [Semiring T]
  [Semiring A] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra R A]

/-- Composing with an `S`-algebra map `q : S →ₐ[S] T` is bijective on `R`-algebra maps out of `A`
if and only if it is bijective on `S`-algebra maps out of the base change `S ⊗[R] A`. -/
theorem restrictScalars_comp_bijective_iff (q : S →ₐ[S] T) :
    Function.Bijective ((q.restrictScalars R).comp : (A →ₐ[R] S) → A →ₐ[R] T) ↔
      Function.Bijective (q.comp : (S ⊗[R] A →ₐ[S] S) → S ⊗[R] A →ₐ[S] T) := by
  have hcomp : ((q.restrictScalars R).comp : (A →ₐ[R] S) → A →ₐ[R] T) =
      (liftEquiv R S A T).symm ∘ q.comp ∘ liftEquiv R S A S := by
    ext f a
    simp
  rw [hcomp, (liftEquiv R S A T).symm.bijective.of_comp_iff',
    Function.Bijective.of_comp_iff _ (liftEquiv R S A S).bijective]

end Comp

/-- If `φ : A →ₐ[R] B` maps an `R`-basis of `A` to an `S`-basis of `B`, the induced `S`-algebra
multiplication map `liftEquiv R S A B φ : S ⊗[R] A →ₐ[S] B` is bijective. -/
theorem liftEquiv_bijective_of_basis {R S A B ι : Type*} [CommSemiring R] [CommSemiring S]
    [Semiring A] [Semiring B] [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (φ : A →ₐ[R] B) (b : Module.Basis ι R A) (b' : Module.Basis ι S B)
    (hb : ∀ i, b' i = φ (b i)) :
    Function.Bijective (liftEquiv R S A B φ) := by
  let e := (b.baseChange S).equiv b' (Equiv.refl ι)
  have he : (liftEquiv R S A B φ).toLinearMap = e.toLinearMap :=
    (b.baseChange S).ext fun i ↦ by
      rw [LinearEquiv.coe_coe, (b.baseChange S).equiv_apply]
      simp [liftEquiv_tmul, hb]
  exact (liftEquiv R S A B φ).coe_toLinearMap ▸ he ▸ e.bijective

end AlgHom
