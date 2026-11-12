/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of symmetric algebras

A derivation of `SymmetricAlgebra R M` is determined by its values on the canonical generators.
Conversely, every linear map from `M` to a module over its symmetric algebra extends uniquely to a
derivation. This file packages the extension and the resulting linear equivalence.

The public interface follows Mathlib's analogous `Polynomial.mkDerivation` and
`MvPolynomial.mkDerivation` APIs.

## Main definitions and results

* `SymmetricAlgebra.mkDerivation`: extend prescribed values on the canonical generators.
* `SymmetricAlgebra.derivation_ext`: symmetric-algebra derivations agree when they agree on the
  canonical generators.
* `SymmetricAlgebra.mkDerivationEquiv`: derivations are linearly equivalent to their restrictions
  to the canonical generators.

## Implementation notes

The construction uses the trivial square-zero extension. A prescribed value `f x` is paired with
the generator `SymmetricAlgebra.ι R M x`; the universal property of the symmetric algebra extends
this pair multiplicatively, and projection to the square-zero component gives the derivation.
-/

public section

namespace SymmetricAlgebra

noncomputable section

variable {R M A : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid A] [Module R A] [Module (SymmetricAlgebra R M) A]
variable [IsScalarTower R (SymmetricAlgebra R M) A]

/-- The right-module structure induced by commutativity, used by the square-zero extension. -/
local instance commOppositeModule (S A : Type*) [CommSemiring S] [AddCommMonoid A] [Module S A] :
    Module Sᵐᵒᵖ A :=
  Module.compHom A (RingEquiv.toOpposite S).symm.toRingHom

/-- Over a commutative semiring, the induced right action agrees with the left action. -/
local instance commCentralScalar (S A : Type*) [CommSemiring S] [AddCommMonoid A] [Module S A] :
    IsCentralScalar S A where
  op_smul_eq_smul _ _ := rfl

/-- The algebra map into the square-zero extension sending each generator `ι R M x` to
`ι R M x + ε f x`. -/
private def derivationLift (f : M →ₗ[R] A) :
    SymmetricAlgebra R M →ₐ[R] TrivSqZeroExt (SymmetricAlgebra R M) A :=
  lift <| (TrivSqZeroExt.inlAlgHom R (SymmetricAlgebra R M) A).toLinearMap ∘ₗ ι R M +
    ((TrivSqZeroExt.inrHom (SymmetricAlgebra R M) A).restrictScalars R) ∘ₗ f

private theorem derivationLift_fst (f : M →ₗ[R] A) (a : SymmetricAlgebra R M) :
    (derivationLift f a).fst = a := by
  have h : (TrivSqZeroExt.fstHom R (SymmetricAlgebra R M) A).comp (derivationLift f) =
      AlgHom.id R (SymmetricAlgebra R M) :=
    algHom_ext <| by ext; simp [derivationLift]
  exact AlgHom.congr_fun h a

omit [IsScalarTower R (SymmetricAlgebra R M) A] in
/-- Two derivations of a symmetric algebra are equal if they agree on the canonical generators. -/
@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R (SymmetricAlgebra R M) A}
    (h : ∀ x, D₁ (ι R M x) = D₂ (ι R M x)) : D₁ = D₂ := by
  ext a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x => exact h x
  | mul a b ha hb => simp only [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The derivation on `SymmetricAlgebra R M` taking the prescribed value `f x` on each canonical
generator `SymmetricAlgebra.ι R M x`. -/
def mkDerivation : (M →ₗ[R] A) →ₗ[R] Derivation R (SymmetricAlgebra R M) A where
  toFun f :=
    { toLinearMap :=
        ((TrivSqZeroExt.sndHom (SymmetricAlgebra R M) A).restrictScalars R) ∘ₗ
          (derivationLift f).toLinearMap
      map_one_eq_zero' := by simp
      leibniz' a b := by simp [derivationLift_fst] }
  map_add' f g := derivation_ext fun x => by simp [derivationLift]
  map_smul' r f := derivation_ext fun x => by simp [derivationLift]

/-- `mkDerivation` takes the prescribed value on a canonical symmetric-algebra generator. -/
@[simp]
theorem mkDerivation_ι (f : M →ₗ[R] A) (x : M) : mkDerivation f (ι R M x) = f x := by
  simp [mkDerivation, derivationLift]

/-- Restriction to the canonical generators identifies derivations of a symmetric algebra with
linear maps out of its generating module. -/
def mkDerivationEquiv : (M →ₗ[R] A) ≃ₗ[R] Derivation R (SymmetricAlgebra R M) A :=
  LinearEquiv.symm
    { invFun := mkDerivation
      toFun := fun D => D.toLinearMap ∘ₗ ι R M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_ι _
      right_inv := fun f => LinearMap.ext <| mkDerivation_ι f }

@[simp]
theorem mkDerivationEquiv_apply (f : M →ₗ[R] A) : mkDerivationEquiv f = mkDerivation f := by
  rfl

@[simp]
theorem mkDerivationEquiv_symm_apply (D : Derivation R (SymmetricAlgebra R M) A) :
    mkDerivationEquiv.symm D = D.toLinearMap ∘ₗ ι R M := by
  rfl

end

end SymmetricAlgebra
