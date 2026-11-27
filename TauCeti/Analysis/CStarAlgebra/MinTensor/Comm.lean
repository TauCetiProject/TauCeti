/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product.Map

/-!
# The flip of the minimal C*-tensor product

Let `A` and `B` be C*-algebras. The minimal norm is invariant under the flip
`A ⊗[ℂ] B ≃ B ⊗[ℂ] A` (`TauCeti.minTensorNorm_comm`), so the flip `a ⊗ b ↦ b ⊗ a` extends to a
star isomorphism `TauCeti.MinTensorProduct.comm A B : A ⊗min B ≃ B ⊗min A`. It is natural with
respect to `TauCeti.MinTensorProduct.map` (`TauCeti.MinTensorProduct.commHom_comp_map`) and
compatible with the flip of the maximal tensor product under the canonical surjection
`TauCeti.MaxTensorProduct.toMin` (`TauCeti.MaxTensorProduct.toMin_comp_commHom`).

## Main declarations

* `TauCeti.MinTensorProduct.commHom`: the flip as a star homomorphism.
* `TauCeti.MinTensorProduct.comm`: the flip `A ⊗min B ≃ B ⊗min A` as a star isomorphism.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.2.5.
-/

public section

noncomputable section

open TensorProduct

namespace TauCeti

namespace MinTensorProduct

open CStarTensorProduct

section Comm

variable (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The flip `A ⊗min B → B ⊗min A`, `a ⊗ b ↦ b ⊗ a`, as a star homomorphism: the extension of
the flip of `A ⊗[ℂ] B`, which is isometric for the minimal norms. -/
def commHom : MinTensorProduct A B →⋆ₙₐ[ℂ] MinTensorProduct B A :=
  extend ((of (minCStarTensorNorm B A)).comp
    (Algebra.TensorProduct.commNonUnitalStarAlgHom ℂ A B)) fun x ↦ by
    simp [Algebra.TensorProduct.coe_commNonUnitalStarAlgHom]

variable {A B}

/-- On `A ⊗[ℂ] B`, the flip of the minimal tensor product is the algebraic flip. -/
@[simp]
theorem commHom_of (x : A ⊗[ℂ] B) :
    commHom A B (of (minCStarTensorNorm A B) x) =
      of (minCStarTensorNorm B A) (TensorProduct.comm ℂ A B x) :=
  (extend_of _ _ x).trans (by simp [Algebra.TensorProduct.coe_commNonUnitalStarAlgHom])

/-- Flipping twice is the identity, as a composite of star homomorphisms. -/
@[simp]
theorem commHom_comp_commHom : (commHom B A).comp (commHom A B) = NonUnitalStarAlgHom.id ℂ _ :=
  starAlgHom_ext fun a b ↦ by simp

/-- Flipping twice is the identity. -/
@[simp]
theorem commHom_commHom (x : MinTensorProduct A B) : commHom B A (commHom A B x) = x :=
  DFunLike.congr_fun commHom_comp_commHom x

/-- The flip of the minimal tensor product is isometric. -/
@[simp]
theorem norm_commHom (x : MinTensorProduct A B) : ‖commHom A B x‖ = ‖x‖ :=
  norm_extend _ (fun x ↦ by simp [Algebra.TensorProduct.coe_commNonUnitalStarAlgHom]) x

variable (A B)

/-- **The flip of the minimal tensor product**: the star isomorphism `A ⊗min B ≃ B ⊗min A`
sending `a ⊗ b` to `b ⊗ a` (`TauCeti.MinTensorProduct.comm_of_tmul`). -/
def comm : MinTensorProduct A B ≃⋆ₐ[ℂ] MinTensorProduct B A :=
  .ofNonUnitalStarAlgHom (commHom A B) (commHom B A) commHom_comp_commHom commHom_comp_commHom

variable {A B}

/-- The flip is the star homomorphism `TauCeti.MinTensorProduct.commHom`. -/
@[simp]
theorem comm_apply (x : MinTensorProduct A B) : comm A B x = commHom A B x :=
  (rfl)

/-- The inverse of the flip is the flip. -/
@[simp]
theorem comm_symm : (comm A B).symm = comm B A :=
  StarAlgEquiv.symm_ofNonUnitalStarAlgHom _ _ _ _

/-- The flip sends `a ⊗ b` to `b ⊗ a`. -/
theorem comm_of_tmul (a : A) (b : B) :
    comm A B (of (minCStarTensorNorm A B) (a ⊗ₜ b)) = of (minCStarTensorNorm B A) (b ⊗ₜ a) := by
  simp [comm_apply]

end Comm

section CommMap

variable {A A' B B' : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B'] (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')

/-- **Naturality of the flip.** Flipping after `map φ ψ` is `map ψ φ` after flipping. -/
theorem commHom_comp_map : (commHom A' B').comp (map φ ψ) = (map ψ φ).comp (commHom A B) :=
  starAlgHom_ext fun a b ↦ by simp

/-- **Naturality of the flip**, pointwise. -/
theorem commHom_map (x : MinTensorProduct A B) :
    commHom A' B' (map φ ψ x) = map ψ φ (commHom A B x) :=
  DFunLike.congr_fun (commHom_comp_map φ ψ) x

end CommMap

end MinTensorProduct

namespace MaxTensorProduct

open CStarTensorProduct

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The canonical surjection `A ⊗max B → A ⊗min B` intertwines the flips. -/
theorem toMin_comp_commHom :
    toMin.comp (commHom A B) = (MinTensorProduct.commHom A B).comp toMin :=
  starAlgHom_ext fun a b ↦ by simp

/-- The canonical surjection `A ⊗max B → A ⊗min B` intertwines the flips, pointwise. -/
theorem toMin_commHom (x : MaxTensorProduct A B) :
    toMin (commHom A B x) = MinTensorProduct.commHom A B (toMin x) :=
  DFunLike.congr_fun toMin_comp_commHom x

end MaxTensorProduct

end TauCeti
