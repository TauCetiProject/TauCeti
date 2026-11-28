/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product
public import TauCeti.Analysis.CStarAlgebra.TensorProduct.Unital

/-!
# The maximal tensor product of unital C*-algebras

Let `A` and `B` be unital C*-algebras. Like every C*-tensor product of unital C*-algebras, the
maximal tensor product `A ⊗max B` (`TauCeti.MaxTensorProduct A B`) is a unital C*-algebra with unit
`1 ⊗ 1` (`TauCeti.CStarTensorProduct.instCStarAlgebra`), with the unital star homomorphisms
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` (`TauCeti.CStarTensorProduct.includeLeft`,
`TauCeti.CStarTensorProduct.includeRight`). For unital commuting star homomorphisms
`φ : A → C` and `ψ : B → C` into a unital C*-algebra, the extension
`TauCeti.MaxTensorProduct.lift φ ψ` of the universal property is unital
(`TauCeti.MaxTensorProduct.liftStarAlgHom`), and it restricts to `φ` and `ψ` along the two
inclusions.

## Main declarations

* `TauCeti.MaxTensorProduct.liftStarAlgHom`: the unital form of the universal property.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3 (the maximal tensor product and its universal property).
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace MaxTensorProduct

open CStarTensorProduct

variable {C : Type (max u v)} [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
  (h : ∀ a b, Commute (φ a) (ψ b))

/-- **The universal property for unital algebras.** Commuting unital star homomorphisms
`φ : A → C` and `ψ : B → C` into a unital C*-algebra `C` in the universe `max u v` extend to the
unital star homomorphism `A ⊗max B → C` sending `a ⊗ b` to `φ a * ψ b`. -/
def liftStarAlgHom : MaxTensorProduct A B →⋆ₐ[ℂ] C where
  __ := lift φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h
  map_one' := by simpa using lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h 1 1
  commutes' r := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      congrArg (r • ·) (lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h 1 1)

/-- On `A ⊗[ℂ] B`, the unital extension is the integrated form `a ⊗ b ↦ φ a * ψ b`, Mathlib's
`Algebra.TensorProduct.lift`. -/
@[simp]
theorem liftStarAlgHom_of (x : A ⊗[ℂ] B) :
    liftStarAlgHom φ ψ h (of (maxCStarTensorNorm A B) x) =
      Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h a b
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The unital extension sends `a ⊗ b` to `φ a * ψ b`. -/
theorem liftStarAlgHom_of_tmul (a : A) (b : B) :
    liftStarAlgHom φ ψ h (of (maxCStarTensorNorm A B) (a ⊗ₜ b)) = φ a * ψ b :=
  lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h a b

/-- The unital extension restricts to `φ` along `a ↦ a ⊗ 1`. -/
@[simp]
theorem liftStarAlgHom_comp_includeLeft :
    (liftStarAlgHom φ ψ h).comp (includeLeft (maxCStarTensorNorm A B)) = φ :=
  StarAlgHom.ext fun a ↦ by simp

/-- The unital extension restricts to `ψ` along `b ↦ 1 ⊗ b`. -/
@[simp]
theorem liftStarAlgHom_comp_includeRight :
    (liftStarAlgHom φ ψ h).comp (includeRight (maxCStarTensorNorm A B)) = ψ :=
  StarAlgHom.ext fun b ↦ by simp

end MaxTensorProduct

end TauCeti
