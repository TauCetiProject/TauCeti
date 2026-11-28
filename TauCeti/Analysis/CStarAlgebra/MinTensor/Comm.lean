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

Let `A` and `B` be C*-algebras. The minimal C*-norm is invariant under the flip
`A ⊗[ℂ] B ≃ B ⊗[ℂ] A` (`TauCeti.minCStarTensorNorm_comm`, from `TauCeti.minTensorNorm_comm`), so
the flip `a ⊗ b ↦ b ⊗ a` extends to a star isomorphism
`TauCeti.CStarTensorProduct.comm minCStarTensorNorm_comm : A ⊗min B ≃ B ⊗min A`. It is natural with
respect to `TauCeti.MinTensorProduct.map` (`TauCeti.MinTensorProduct.commHom_comp_map`) and
compatible with the flip of the maximal tensor product under the canonical surjection
`TauCeti.MaxTensorProduct.toMin` (`TauCeti.MaxTensorProduct.toMin_comp_commHom`).

## Main declarations

* `TauCeti.minCStarTensorNorm_comm`: the minimal C*-norm is invariant under the flip, so that
  `TauCeti.CStarTensorProduct.comm` gives the flip `A ⊗min B ≃ B ⊗min A`.
* `TauCeti.MinTensorProduct.commHom_comp_map`: naturality of the flip.
* `TauCeti.MaxTensorProduct.toMin_comp_commHom`: compatibility with the flip of `A ⊗max B`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.2.5.
-/

public section

noncomputable section

open TensorProduct

namespace TauCeti

/-- The minimal C*-norm is invariant under the flip `A ⊗[ℂ] B ≃ B ⊗[ℂ] A`. -/
theorem minCStarTensorNorm_comm {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (x : A ⊗[ℂ] B) :
    minCStarTensorNorm B A (TensorProduct.comm ℂ A B x) = minCStarTensorNorm A B x := by
  simp [minTensorNorm_comm]

namespace MinTensorProduct

open CStarTensorProduct

section CommMap

variable {A A' B B' : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B'] (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')

/-- **Naturality of the flip.** Flipping after `map φ ψ` is `map ψ φ` after flipping. -/
theorem commHom_comp_map :
    (commHom (minCStarTensorNorm_comm (A := A') (B := B'))).comp (map φ ψ) =
      (map ψ φ).comp (commHom minCStarTensorNorm_comm) :=
  starAlgHom_ext fun a b ↦ by simp

/-- **Naturality of the flip**, pointwise. -/
theorem commHom_map (x : MinTensorProduct A B) :
    commHom (minCStarTensorNorm_comm (A := A') (B := B')) (map φ ψ x) =
      map ψ φ (commHom minCStarTensorNorm_comm x) :=
  DFunLike.congr_fun (commHom_comp_map φ ψ) x

end CommMap

end MinTensorProduct

namespace MaxTensorProduct

open CStarTensorProduct

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The canonical surjection `A ⊗max B → A ⊗min B` intertwines the flips. -/
theorem toMin_comp_commHom :
    toMin.comp (commHom (maxCStarTensorNorm_comm (A := A) (B := B))) =
      (commHom minCStarTensorNorm_comm).comp toMin :=
  starAlgHom_ext fun a b ↦ by simp

/-- The canonical surjection `A ⊗max B → A ⊗min B` intertwines the flips, pointwise. -/
theorem toMin_commHom (x : MaxTensorProduct A B) :
    toMin (commHom maxCStarTensorNorm_comm x) = commHom minCStarTensorNorm_comm (toMin x) :=
  DFunLike.congr_fun toMin_comp_commHom x

end MaxTensorProduct

end TauCeti
