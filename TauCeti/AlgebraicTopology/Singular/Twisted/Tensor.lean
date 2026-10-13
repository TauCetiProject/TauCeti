/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

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

private def twistedChainsTensorDiagonalApp (n : SimplexCategoryᵒᵖ) :
    (twistedChains (L ⊗ K)).obj n ⟶ (twistedChains L ⊗ twistedChains K).obj n :=
  (isColimitTwistedChainsCofan (L ⊗ K) n).desc
    (Cofan.mk _ fun σ ↦ ιTwistedChains L σ ⊗ₘ ιTwistedChains K σ)

@[reassoc]
private lemma ιTwistedChains_twistedChainsTensorDiagonalApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains (L ⊗ K) σ ≫ twistedChainsTensorDiagonalApp L K n =
      ιTwistedChains L σ ⊗ₘ ιTwistedChains K σ :=
  (isColimitTwistedChainsCofan (L ⊗ K) n).fac
    (Cofan.mk _ fun τ ↦ ιTwistedChains L τ ⊗ₘ ιTwistedChains K τ) ⟨σ⟩

/-- The tensor diagonal of twisted singular simplicial chains sends the tensor-coefficient
summand of a simplex to the tensor of its two summands. -/
def twistedChainsTensorDiagonal :
    twistedChains (L ⊗ K) ⟶ twistedChains L ⊗ twistedChains K where
  app := twistedChainsTensorDiagonalApp L K
  naturality {m n} α := by
    -- Tensor normalization changes the dependent fibre presentation. Typed transitivity keeps
    -- the fibres selected by the simplex inclusions until their characteristic equations apply.
    apply twistedChains_hom_ext
    intro σ
    refine (ιTwistedChains_map_assoc (L ⊗ K) α σ _).trans ?_
    refine (congrArg ((L ⊗ K).map (vertexTransport α σ) ≫ ·)
      (ιTwistedChains_twistedChainsTensorDiagonalApp L K n _)).trans ?_
    refine Eq.trans ?_ (ιTwistedChains_twistedChainsTensorDiagonalApp_assoc L K m σ _).symm
    exact (tensorHom_comp_tensorHom _ _ _ _).trans
      ((congrArg₂ (fun a b ↦ a ⊗ₘ b) (ιTwistedChains_map L α σ).symm
        (ιTwistedChains_map K α σ).symm).trans (tensorHom_comp_tensorHom _ _ _ _).symm)

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
  refine (ιTwistedChains_twistedChainsCoefficientMap_app_assoc (η ⊗ₘ θ) n σ _).trans ?_
  refine (congrArg ((η ⊗ₘ θ).app (initialVertex σ) ≫ ·)
    (ιTwistedChains_twistedChainsTensorDiagonal_app L' K' n σ)).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsTensorDiagonal_app_assoc L K n σ _).symm
  exact (tensorHom_comp_tensorHom _ _ _ _).trans
    ((congrArg₂ (fun a b ↦ a ⊗ₘ b)
      (ιTwistedChains_twistedChainsCoefficientMap_app η n σ).symm
      (ιTwistedChains_twistedChainsCoefficientMap_app θ n σ).symm).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm)

section Space

variable (f : X ⟶ Y) (L K : LocalCoefficientSystem.{max v w, v, max v w} R Y)

/-- The tensor diagonal commutes with a continuous map. The pullback tensor comparison is the
cotensorator of the existing pointwise monoidal pullback functor. -/
@[reassoc]
lemma twistedChainsTensorDiagonal_space_naturality :
    twistedChainsMap f (L ⊗ K) ≫ twistedChainsTensorDiagonal L K =
      twistedChainsCoefficientMap (Functor.OplaxMonoidal.δ
        ((Functor.whiskeringLeft _ _ (ModuleCat.{max v w} R)).obj
          (FundamentalGroupoid.map f.hom)) L K) ≫
        twistedChainsTensorDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K) ≫
          (twistedChainsMap f L ⊗ₘ twistedChainsMap f K) := by
  apply NatTrans.ext
  funext n
  apply twistedChains_hom_ext
  intro σ
  -- Select the monoidal instance on the underlying whiskering functor: instance search does
  -- not unfold the public pullback presentation. Its cotensorator is the identity on fibres.
  let δ := Functor.OplaxMonoidal.δ
    ((Functor.whiskeringLeft _ _ (ModuleCat.{max v w} R)).obj
      (FundamentalGroupoid.map f.hom)) L K
  have hδ : δ.app (initialVertex σ) = 𝟙 _ := rfl
  refine (ιTwistedChains_twistedChainsMap_app_assoc f (L ⊗ K) n σ _).trans ?_
  refine (ιTwistedChains_twistedChainsTensorDiagonal_app L K n _).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsCoefficientMap_app_assoc δ n σ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) hδ).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsTensorDiagonal_app_assoc
    ((pullback f.hom).obj L) ((pullback f.hom).obj K) n σ _).symm
  exact ((tensorHom_comp_tensorHom _ _ _ _).trans
    (congrArg₂ (fun a b ↦ a ⊗ₘ b)
      (ιTwistedChains_twistedChainsMap_app f L n σ)
      (ιTwistedChains_twistedChainsMap_app f K n σ))).symm

end Space

end TauCeti.LocalCoefficientSystem
