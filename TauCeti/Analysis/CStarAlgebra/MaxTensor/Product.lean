/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Norm
public import TauCeti.Analysis.CStarAlgebra.TensorProduct

/-!
# The maximal C*-tensor product

Let `A` and `B` be (possibly non-unital) C*-algebras. The maximal C*-norm `TauCeti.maxTensorNorm`
is a C*-norm on `A ⊗[ℂ] B` (`TauCeti.maxCStarTensorNorm A B`). The completion of `A ⊗[ℂ] B` in it
is the **maximal tensor product** `TauCeti.MaxTensorProduct A B` (written A ⊗max B in the
literature; this file declares no notation for it), the C*-tensor product
`TauCeti.CStarTensorProduct` of the maximal norm, with the star homomorphism
`TauCeti.CStarTensorProduct.of (TauCeti.maxCStarTensorNorm A B)` from `A ⊗[ℂ] B`, which is
injective, isometric for the maximal norm and has dense range.

**Universal property.** Commuting star homomorphisms `φ : A → C` and `ψ : B → C` into a
C*-algebra `C` in the universe `max u v` integrate to a star homomorphism `a ⊗ b ↦ φ a * ψ b` on
`A ⊗[ℂ] B` bounded by the maximal norm (`TauCeti.norm_liftNonUnitalStarAlgHom_le_maxTensorNorm`),
which extends uniquely to `TauCeti.MaxTensorProduct A B` (`TauCeti.MaxTensorProduct.lift`, with
`TauCeti.MaxTensorProduct.lift_of_tmul` and the uniqueness
`TauCeti.CStarTensorProduct.starAlgHom_ext`).
In particular every commuting pair of representations of `A` and `B` integrates to a
representation of `TauCeti.MaxTensorProduct A B`
(`TauCeti.CommutingRepresentationPair.maxTensorHom`).

## Main declarations

* `TauCeti.maxCStarTensorNorm A B`: the maximal norm as a C*-norm.
* `TauCeti.MaxTensorProduct A B`: the completion of `A ⊗[ℂ] B` in it, a C*-algebra.
* `TauCeti.MaxTensorProduct.lift`: the universal property.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3.
-/

public section

noncomputable section

open TensorProduct

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The maximal norm `TauCeti.maxTensorNorm` as a C*-norm on `A ⊗[ℂ] B`. -/
def maxCStarTensorNorm : CStarTensorNorm A B where
  toFun := maxTensorNorm A B
  map_zero' := maxTensorNorm_zero
  add_le' := maxTensorNorm_add_le
  neg' := maxTensorNorm_neg
  eq_zero_of_map_eq_zero' _ := maxTensorNorm_eq_zero_iff.1
  smul' := maxTensorNorm_smul
  mul_le' := maxTensorNorm_mul_le
  star_mul_self_le' x := (maxTensorNorm_star_mul_self x).ge

@[simp]
theorem maxCStarTensorNorm_apply (x : A ⊗[ℂ] B) : maxCStarTensorNorm A B x = maxTensorNorm A B x :=
  (rfl)

/-- The **maximal tensor product** of C*-algebras `A` and `B`: the completion of the
algebraic tensor product `A ⊗[ℂ] B` in the maximal C*-norm. It is a C*-algebra, and the
canonical map `TauCeti.CStarTensorProduct.of (TauCeti.maxCStarTensorNorm A B)` from `A ⊗[ℂ] B` is
injective and isometric with dense range. -/
abbrev MaxTensorProduct : Type (max u v) :=
  CStarTensorProduct (maxCStarTensorNorm A B)

namespace MaxTensorProduct

open CStarTensorProduct

variable {A B}

/-- `‖a ⊗ b‖ = ‖a‖ ‖b‖` in `MaxTensorProduct A B`. -/
theorem norm_of_tmul (a : A) (b : B) :
    ‖of (maxCStarTensorNorm A B) (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of, maxCStarTensorNorm_apply, maxTensorNorm_tmul]

variable {C : Type (max u v)} [NonUnitalCStarAlgebra C] (φ : A →⋆ₙₐ[ℂ] C) (ψ : B →⋆ₙₐ[ℂ] C)
  (h : ∀ a b, Commute (φ a) (ψ b))

/-- **The universal property of `MaxTensorProduct A B`.** Commuting star homomorphisms
`φ : A → C` and `ψ : B → C` into a C*-algebra `C` in the universe `max u v` extend to the star
homomorphism `MaxTensorProduct A B → C` sending `a ⊗ b` to `φ a * ψ b`
(`TauCeti.MaxTensorProduct.lift_of_tmul`); it is unique by
`TauCeti.CStarTensorProduct.starAlgHom_ext`. -/
def lift : MaxTensorProduct A B →⋆ₙₐ[ℂ] C :=
  extend (Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h)
    (norm_liftNonUnitalStarAlgHom_le_maxTensorNorm φ ψ h)

/-- On `A ⊗[ℂ] B`, the extension is the integrated form `a ⊗ b ↦ φ a * ψ b`. -/
@[simp]
theorem lift_of (x : A ⊗[ℂ] B) :
    lift φ ψ h (of (maxCStarTensorNorm A B) x) =
      Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h x :=
  extend_of _ _ x

/-- The extension sends `a ⊗ b` to `φ a * ψ b`. -/
theorem lift_of_tmul (a : A) (b : B) :
    lift φ ψ h (of (maxCStarTensorNorm A B) (a ⊗ₜ b)) = φ a * ψ b := by
  rw [lift_of, Algebra.TensorProduct.liftNonUnitalStarAlgHom_tmul]

/-- Composing the extension with the canonical map recovers the integrated form. -/
@[simp]
theorem lift_comp_of :
    (lift φ ψ h).comp (of (maxCStarTensorNorm A B)) =
      Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h :=
  NonUnitalStarAlgHom.ext (lift_of φ ψ h)

end MaxTensorProduct

namespace CommutingRepresentationPair

open MaxTensorProduct

variable {A B}

/-- The representation of `MaxTensorProduct A B` integrating a commuting pair of representations
of `A` and `B`, `a ⊗ b ↦ π a * ρ b`. -/
def maxTensorHom (p : CommutingRepresentationPair A B) :
    MaxTensorProduct A B →⋆ₙₐ[ℂ] (p.H →L[ℂ] p.H) :=
  lift p.left p.right p.commute

/-- On `A ⊗[ℂ] B`, the representation of `MaxTensorProduct A B` is the integrated form of the
pair. -/
@[simp]
theorem maxTensorHom_of (p : CommutingRepresentationPair A B) (x : A ⊗[ℂ] B) :
    p.maxTensorHom (CStarTensorProduct.of (maxCStarTensorNorm A B) x) = p.tensorHom x := by
  rw [maxTensorHom, lift_of, tensorHom_def]

end CommutingRepresentationPair

end TauCeti
