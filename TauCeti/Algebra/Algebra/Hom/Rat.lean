/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Ring homomorphisms out of `ℚ`-algebras

A ring homomorphism between `ℚ`-algebras is automatically `ℚ`-linear (`RingHom.equivRatAlgHom`),
so a finite-dimensional `ℚ`-algebra has only finitely many ring homomorphisms into an integral
domain that is a `ℚ`-algebra. For instance a finite product of number fields has finitely many
complex embeddings.

## Main declarations

* `Finite.ringHom_of_rat`: `R →+* K` is finite for a finite-dimensional `ℚ`-algebra
  `R` and an integral domain `K`.
* `TauCeti.ratTensorProductAlgHomEquiv`: extend ring homomorphisms out of a rational algebra to
  algebra homomorphisms on its base change, using `RingHom.equivRatAlgHom` and `AlgHom.liftEquiv`.
-/

public section

/-- A finite-dimensional `ℚ`-algebra has finitely many ring homomorphisms into an integral domain:
they are its `ℚ`-algebra homomorphisms, which are linearly independent. -/
instance Finite.ringHom_of_rat {R K : Type*} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R]
    [CommRing K] [IsDomain K] [Algebra ℚ K] : Finite (R →+* K) :=
  .of_equiv _ (RingHom.equivRatAlgHom R K).symm

open scoped TensorProduct

namespace TauCeti

variable (A E B : Type*) [CommSemiring A] [Ring E] [Ring B]
  [Algebra ℚ A] [Algebra ℚ E] [Algebra A B]

/-- For rational algebras `A` and `E` and an `A`-algebra `B`, ring homomorphisms `E →+* B`
extend uniquely to `A`-algebra homomorphisms on `A ⊗[ℚ] E`. -/
def ratTensorProductAlgHomEquiv : (E →+* B) ≃ (A ⊗[ℚ] E →ₐ[A] B) :=
  letI : Algebra ℚ B := Algebra.compHom B (algebraMap ℚ A)
  haveI : IsScalarTower ℚ A B := IsScalarTower.of_algebraMap_eq' rfl
  (RingHom.equivRatAlgHom E B).trans (AlgHom.liftEquiv ℚ A E B)

variable {A E B}

/-- On pure tensors, the extended homomorphism multiplies the images of the two factors. -/
@[simp]
theorem ratTensorProductAlgHomEquiv_tmul (f : E →+* B) (a : A) (e : E) :
    ratTensorProductAlgHomEquiv A E B f (a ⊗ₜ e) = algebraMap A B a * f e := by
  simp only [ratTensorProductAlgHomEquiv, Equiv.trans_apply, AlgHom.liftEquiv_tmul,
    RingHom.equivRatAlgHom_apply, RingHom.toRatAlgHom_apply, Algebra.smul_def]

end TauCeti
