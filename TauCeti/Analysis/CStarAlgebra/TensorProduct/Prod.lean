/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.TensorProductLift
public import TauCeti.Analysis.CStarAlgebra.TensorProduct

/-!
# C*-tensor products distribute over direct sums

Let `N`, `N₁` and `N₂` be C*-norms on `(A × A') ⊗[ℂ] B`, `A ⊗[ℂ] B` and `A' ⊗[ℂ] B`. If
`N x = max (N₁ x₁) (N₂ x₂)` for every `x`, where `x₁ = (fst ⊗ id) x` and `x₂ = (snd ⊗ id) x`, then
`(fst ⊗ id, snd ⊗ id)` extends to a star isomorphism
`TauCeti.CStarTensorProduct.prodLeft : CStarTensorProduct N ≃ CStarTensorProduct N₁ ×
CStarTensorProduct N₂`. It is isometric by the norm formula, and surjective since its range is
closed and contains the dense set of pairs of elements of `A ⊗[ℂ] B` and `A' ⊗[ℂ] B`.

The minimal and the maximal norms satisfy the norm formula (`TauCeti.minTensorNorm_prod`,
`TauCeti.maxTensorNorm_prod`); `TauCeti.MinTensorProduct.prodLeft` and
`TauCeti.MaxTensorProduct.prodLeft` are the corresponding instances.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
-/

public section

noncomputable section

open TensorProduct Algebra.TensorProduct
open scoped CStarAlgebra

namespace TauCeti

namespace CStarTensorProduct

variable {A A' B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] {N : CStarTensorNorm (A × A') B} {N₁ : CStarTensorNorm A B}
  {N₂ : CStarTensorNorm A' B}

variable (N₁ N₂) in
/-- The star homomorphism `(A × A') ⊗[ℂ] B → CStarTensorProduct N₁ × CStarTensorProduct N₂`
with components `fst ⊗ id` and `snd ⊗ id`. -/
private def prodLeftAux :
    (A × A') ⊗[ℂ] B →⋆ₙₐ[ℂ] CStarTensorProduct N₁ × CStarTensorProduct N₂ :=
  ((of N₁).comp (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A')
    (NonUnitalStarAlgHom.id ℂ B))).prod
    ((of N₂).comp (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A')
      (NonUnitalStarAlgHom.id ℂ B)))

private theorem norm_prodLeftAux
    (h : ∀ x, N x = max
      (N₁ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x))
      (N₂ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
        x)))
    (x : (A × A') ⊗[ℂ] B) : ‖prodLeftAux N₁ N₂ x‖ = N x := by
  simp [prodLeftAux, h]

private theorem denseRange_prodLeftAux : DenseRange (prodLeftAux N₁ N₂) := by
  refine (denseRange_of.prodMap denseRange_of).mono ?_
  rintro _ ⟨⟨y, z⟩, rfl⟩
  exact ⟨mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y +
    mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B) z,
    by simp [prodLeftAux]⟩

/-- **Distributivity of C*-tensor products over direct sums**: if the C*-norms `N`, `N₁` and `N₂`
satisfy `N x = max (N₁ ((fst ⊗ id) x)) (N₂ ((snd ⊗ id) x))`, the star isomorphism
`CStarTensorProduct N ≃ CStarTensorProduct N₁ × CStarTensorProduct N₂` sending `x` to
`((fst ⊗ id) x, (snd ⊗ id) x)` on `(A × A') ⊗[ℂ] B`. -/
def prodLeft
    (h : ∀ x, N x = max
      (N₁ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x))
      (N₂ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
        x))) :
    CStarTensorProduct N ≃⋆ₐ[ℂ] CStarTensorProduct N₁ × CStarTensorProduct N₂ :=
  StarAlgEquiv.ofBijective (extend (prodLeftAux N₁ N₂) fun x ↦ (norm_prodLeftAux h x).le)
    ⟨extend_injective _ (norm_prodLeftAux h), extend_surjective _ _ denseRange_prodLeftAux⟩

variable (h : ∀ x, N x = max
  (N₁ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x))
  (N₂ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x)))

/-- On `(A × A') ⊗[ℂ] B`, the isomorphism is `(fst ⊗ id, snd ⊗ id)`. -/
@[simp]
theorem prodLeft_of (x : (A × A') ⊗[ℂ] B) :
    prodLeft h (of N x) =
      (of N₁ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
          x),
        of N₂ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
          x)) :=
  extend_of _ _ x

/-- On the algebraic tensor products, the inverse isomorphism sends `(y, z)` to
`(inl ⊗ id) y + (inr ⊗ id) z`. -/
theorem prodLeft_symm_of (y : A ⊗[ℂ] B) (z : A' ⊗[ℂ] B) :
    (prodLeft h).symm (of N₁ y, of N₂ z) =
      of N (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y +
        mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B) z) :=
  (prodLeft h).symm_apply_eq.2 (by simp)

/-- A continuous map that is `(fst ⊗ id, snd ⊗ id)` on `(A × A') ⊗[ℂ] B` is the isomorphism. -/
theorem prodLeft_eq_of_of
    {F : CStarTensorProduct N → CStarTensorProduct N₁ × CStarTensorProduct N₂} (hF : Continuous F)
    (hFof : ∀ x, F (of N x) =
      (of N₁ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
          x),
        of N₂ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
          x))) :
    ⇑(prodLeft h) = F :=
  funext fun u ↦ induction_on u (isClosed_eq (map_continuous _) hF) fun x ↦ by
    rw [prodLeft_of, hFof]

/-- The inverse isomorphism sends `(y, z)` to `G₁ y + G₂ z` for continuous maps `G₁` and `G₂`
that are `inl ⊗ id` and `inr ⊗ id` on the algebraic tensor products. -/
theorem prodLeft_symm_eq {G₁ : CStarTensorProduct N₁ → CStarTensorProduct N}
    {G₂ : CStarTensorProduct N₂ → CStarTensorProduct N} (hG₁ : Continuous G₁)
    (hG₂ : Continuous G₂)
    (hG₁of : ∀ y, G₁ (of N₁ y) =
      of N (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y))
    (hG₂of : ∀ z, G₂ (of N₂ z) =
      of N (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B) z))
    (y : CStarTensorProduct N₁) (z : CStarTensorProduct N₂) :
    (prodLeft h).symm (y, z) = G₁ y + G₂ z := by
  refine induction_on y (isClosed_eq ((map_continuous _).comp (.prodMk_left z))
    (hG₁.add continuous_const)) fun y ↦ ?_
  refine induction_on z (isClosed_eq ((map_continuous _).comp (.prodMk_right _))
    (continuous_const.add hG₂)) fun z ↦ ?_
  rw [prodLeft_symm_of, map_add, hG₁of, hG₂of]

end CStarTensorProduct

end TauCeti
