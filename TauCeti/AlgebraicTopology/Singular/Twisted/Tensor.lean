/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# The tensor diagonal of twisted singular chains

For local coefficient systems `L` and `K` over a commutative ring, the tensor product system
has fibre `L(x) ⊗ K(x)` at `x`. Its twisted singular chains map to the pointwise tensor product
of the twisted chains of `L` and of `K`: a tensor in the summand of a simplex is sent to the
tensor of the two summands of that same simplex. Transport in both factors follows the same
path inside the simplex, so this is a morphism of simplicial modules.

The diagonal commutes with maps of both coefficient systems and with continuous maps of spaces,
using the canonical tensor comparison for pullback. It supplies the simplicial input for
Alexander–Whitney diagonals with local coefficients, and hence for cup and cap products with
tensor pairings of local systems.

The ring and coefficient fibres share a universe, as required by Mathlib's monoidal structure
on `ModuleCat`; the space may belong to a smaller universe.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

universe v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] {X Y : TopCat.{v}}
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R X)

/-- Compute tensor composition from the two simplex-inclusion equations, keeping the
coefficient fibres in the presentations selected by those inclusions. -/
private lemma tensor_ιTwistedChains_comp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) {A B : ModuleCat.{max v w} R}
    {a : (twistedChains L).obj n ⟶ A} {b : (twistedChains K).obj n ⟶ B}
    {c : L.obj (initialVertex σ) ⟶ A} {d : K.obj (initialVertex σ) ⟶ B}
    (h₁ : ιTwistedChains L σ ≫ a = c) (h₂ : ιTwistedChains K σ ≫ b = d) :
    (ιTwistedChains L σ ⊗ₘ ιTwistedChains K σ) ≫ (a ⊗ₘ b) = c ⊗ₘ d := by
  rw [tensorHom_comp_tensorHom, h₁, h₂]

private def twistedChainsTensorDiagonalApp (n : SimplexCategoryᵒᵖ) :
    (twistedChains (L ⊗ K)).obj n ⟶ (twistedChains L ⊗ twistedChains K).obj n :=
  (isColimitCofanTwistedChains (L ⊗ K) n).desc
    (Cofan.mk _ fun σ ↦ ιTwistedChains L σ ⊗ₘ ιTwistedChains K σ)

@[reassoc]
private lemma ιTwistedChains_twistedChainsTensorDiagonalApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains (L ⊗ K) σ ≫ twistedChainsTensorDiagonalApp L K n =
      ιTwistedChains L σ ⊗ₘ ιTwistedChains K σ :=
  (isColimitCofanTwistedChains (L ⊗ K) n).fac
    (Cofan.mk _ fun τ ↦ ιTwistedChains L τ ⊗ₘ ιTwistedChains K τ) ⟨σ⟩

/-- The tensor diagonal of twisted singular simplicial chains sends the tensor-coefficient
summand of a simplex to the tensor of its two summands. -/
def twistedChainsTensorDiagonal :
    twistedChains (L ⊗ K) ⟶ twistedChains L ⊗ twistedChains K where
  app := twistedChainsTensorDiagonalApp L K
  naturality {m n} α := by
    -- `simp only` with the inclusion equations and `tensorObj_map` rewrites the left side,
    -- then cannot match the right inclusion-diagonal composite after its tensor fibre changes
    -- presentation. Typed transitivity preserves those carriers until the equations apply.
    apply twistedChains_hom_ext
    intro σ
    refine (ιTwistedChains_map_assoc (L ⊗ K) α σ _).trans ?_
    refine (congrArg ((L ⊗ K).map (vertexTransport α σ) ≫ ·)
      (ιTwistedChains_twistedChainsTensorDiagonalApp L K n _)).trans ?_
    refine Eq.trans ?_ (ιTwistedChains_twistedChainsTensorDiagonalApp_assoc L K m σ _).symm
    exact (tensorHom_comp_tensorHom _ _ _ _).trans
      (tensor_ιTwistedChains_comp L K m σ
        (ιTwistedChains_map L α σ) (ιTwistedChains_map K α σ)).symm

/-- On the coefficient fibre of a simplex, the tensor diagonal is the tensor product of the
two simplex inclusions. -/
-- Apply before child simplification changes the dependent tensor-fibre presentation.
@[reassoc (attr := simp↓)]
lemma ιTwistedChains_twistedChainsTensorDiagonal_app (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains (L ⊗ K) σ ≫ (twistedChainsTensorDiagonal L K).app n =
      ιTwistedChains L σ ⊗ₘ ιTwistedChains K σ :=
  ιTwistedChains_twistedChainsTensorDiagonalApp L K n σ

/-- A pure tensor attached to a singular simplex maps to the tensor of the two chains attached
to that simplex. -/
-- As for the morphism equation, tensor-fibre normalization must not precede matching.
@[simp↓]
lemma twistedChainsTensorDiagonal_app_ιTwistedChains_tmul (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) (a : L.obj (initialVertex σ))
    (b : K.obj (initialVertex σ)) :
    (twistedChainsTensorDiagonal L K).app n (ιTwistedChains (L ⊗ K) σ (a ⊗ₜ[R] b)) =
      ιTwistedChains L σ a ⊗ₜ[R] ιTwistedChains K σ b := by
  exact (congrArg (fun g ↦ g (a ⊗ₜ[R] b))
    (ιTwistedChains_twistedChainsTensorDiagonal_app L K n σ)).trans
      (ModuleCat.MonoidalCategory.tensorHom_tmul _ _ a b)

variable {L K} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- The tensor diagonal commutes with morphisms of both local coefficient systems. -/
@[reassoc]
lemma twistedChainsTensorDiagonal_naturality (η : L ⟶ L') (θ : K ⟶ K') :
    twistedChainsCoefficientMap (η ⊗ₘ θ) ≫ twistedChainsTensorDiagonal L' K' =
      twistedChainsTensorDiagonal L K ≫
        (twistedChainsCoefficientMap η ⊗ₘ twistedChainsCoefficientMap θ) := by
  apply NatTrans.ext
  funext n
  apply twistedChains_hom_ext
  intro σ
  -- `simp only` reaches the tensor of coefficient components but then cannot match the
  -- right inclusion-diagonal composite on its normalized dependent tensor fibre.
  refine (ιTwistedChains_twistedChainsCoefficientMap_app_assoc (η ⊗ₘ θ) n σ _).trans ?_
  refine (congrArg ((η ⊗ₘ θ).app (initialVertex σ) ≫ ·)
    (ιTwistedChains_twistedChainsTensorDiagonal_app L' K' n σ)).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsTensorDiagonal_app_assoc L K n σ _).symm
  exact (tensorHom_comp_tensorHom _ _ _ _).trans
    (tensor_ιTwistedChains_comp L K n σ
      (ιTwistedChains_twistedChainsCoefficientMap_app η n σ)
      (ιTwistedChains_twistedChainsCoefficientMap_app θ n σ)).symm

section Space

variable (f : X ⟶ Y) (L K : LocalCoefficientSystem.{max v w, v, max v w} R Y)

/-- The tensor diagonal commutes with a continuous map. The pullback tensor comparison is the
canonical identity on coefficient fibres. -/
@[reassoc]
lemma twistedChainsTensorDiagonal_space_naturality :
    twistedChainsMap f (L ⊗ K) ≫ twistedChainsTensorDiagonal L K =
      twistedChainsCoefficientMap (pullbackTensorIso f.hom L K).hom ≫
        twistedChainsTensorDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K) ≫
          (twistedChainsMap f L ⊗ₘ twistedChainsMap f K) := by
  apply NatTrans.ext
  funext n
  apply twistedChains_hom_ext
  intro σ
  -- `simp only` exposes the identity comparison, but cannot eliminate it or match the
  -- diagonal equations across the pullback-tensor fibre presentations.
  let δ := (pullbackTensorIso f.hom L K).hom
  have hδ : δ.app (initialVertex σ) = 𝟙 _ :=
    pullbackTensorIso_hom_app f.hom L K (initialVertex σ)
  refine (ιTwistedChains_twistedChainsMap_app_assoc f (L ⊗ K) n σ _).trans ?_
  refine (ιTwistedChains_twistedChainsTensorDiagonal_app L K n _).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsCoefficientMap_app_assoc δ n σ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) hδ).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsTensorDiagonal_app_assoc
    ((pullback f.hom).obj L) ((pullback f.hom).obj K) n σ _).symm
  exact (tensor_ιTwistedChains_comp ((pullback f.hom).obj L) ((pullback f.hom).obj K) n σ
    (ιTwistedChains_twistedChainsMap_app f L n σ)
    (ιTwistedChains_twistedChainsMap_app f K n σ)).symm

end Space

end TauCeti.LocalCoefficientSystem
