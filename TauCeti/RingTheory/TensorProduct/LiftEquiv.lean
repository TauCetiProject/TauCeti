/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
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

For Mathlib's `Algebra.TensorProduct.liftEquivRight`, the same adjunction with a commutative ring
as target, extensions commute with base change along an `R`-algebra map `ρ : A → B`
(`AlgHom.liftEquivRight_comp_map`), and extensions `A ⊗[R] M → A ⊗[R] N → A ⊗[R] M` compose to
the identity once they do so on `M` (`AlgHom.liftEquivRight_comp_liftEquivRight_eq_id`).
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

section LiftEquivRight

open Algebra.TensorProduct (includeRight liftEquivRight map)

variable {R A N : Type*} [CommSemiring R] [CommRing A] [Algebra R A] [CommSemiring N]
  [Algebra R N]

/-- `liftEquivRight` commutes with base change along an `R`-algebra map `ρ : A → B`: extending
`ρ ⊗ id ∘ φ` to `B ⊗[R] M` and precomposing with `ρ ⊗ id` is `ρ ⊗ id` after the extension of
`φ` to `A ⊗[R] M`. -/
theorem liftEquivRight_comp_map {B M : Type*} [CommRing B] [Algebra R B] [Semiring M]
    [Algebra R M] (ρ : A →ₐ[R] B) (φ : M →ₐ[R] A ⊗[R] N) :
    ((liftEquivRight R B M _ ((map ρ (AlgHom.id R N)).comp φ)).restrictScalars R).comp
        (map ρ (AlgHom.id R M)) =
      (map ρ (AlgHom.id R N)).comp ((liftEquivRight R A M _ φ).restrictScalars R) := by
  ext <;> simp

/-- If the extension of `ψ : N → A ⊗[R] M` to `A ⊗[R] N` sends `φ m` to `1 ⊗ m` for every `m`,
then the extensions of `φ` and `ψ` compose to the identity of `A ⊗[R] M`. -/
theorem liftEquivRight_comp_liftEquivRight_eq_id {M : Type*} [CommSemiring M] [Algebra R M]
    (φ : M →ₐ[R] A ⊗[R] N) (ψ : N →ₐ[R] A ⊗[R] M)
    (h : ((liftEquivRight R A N _ ψ).restrictScalars R).comp φ = includeRight) :
    (liftEquivRight R A N _ ψ).comp (liftEquivRight R A M _ φ) = AlgHom.id A _ := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun x ↦ ?_)
  simpa [← Algebra.TensorProduct.one_def] using congr($h x)

end LiftEquivRight

end AlgHom
