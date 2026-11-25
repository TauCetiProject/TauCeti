/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Segre
import TauCeti.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite products of projective embeddings

Iterating the Segre closed immersion embeds a finite product of schemes with polynomial
projective embeddings into a polynomial projective spectrum over the same coefficient ring.
The empty product is the affine base, represented by the projective spectrum on one coordinate.

The construction retains the closed embedding and its compatibility with the coefficient
morphism, so the product can be used as a projective ambient scheme in the graph construction
of Chow's lemma.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


namespace Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

private noncomputable def segreOver (σ τ : Type u) :
    (Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R)) ⨯
      Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule τ R)) : Over (Spec (.of R))) ⟶
      Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule (σ × τ) R)) :=
  Over.homMk ((Over.prodLeftIsoPullback _ _).hom ≫ segre (σ := σ) (τ := τ) R) (by
    simp only [Over.mk_hom, Category.assoc, segre_toSpecCoeff]
    exact (Over.prodLeftIsoPullback_hom_fst_assoc _ _ _).trans (Over.w prod.fst))

private theorem segreOver_left (σ τ : Type u) :
    (segreOver R σ τ).left = (Over.prodLeftIsoPullback _ _).hom ≫
      segre (σ := σ) (τ := τ) R := rfl

private instance isClosedImmersion_segreOver (σ τ : Type u) :
    IsClosedImmersion (segreOver R σ τ).left := by
  rw [segreOver_left]
  infer_instance

private def hasPolynomialProjectiveEmbedding : ObjectProperty (Over (Spec (.of R))) :=
  fun X ↦ ∃ (σ : Type u) (_ : Finite σ)
    (f : X ⟶ Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R))),
    IsClosedImmersion f.left

private instance : (hasPolynomialProjectiveEmbedding R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨σ, hσ, f, hf⟩ := hX
    refine ⟨σ, hσ, e.inv ≫ f, ?_⟩
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
    -- Forgetting `Over` gives the scheme composite required by closed-immersion composition.
    change IsClosedImmersion (e.inv.left ≫ f.left)
    infer_instance

private theorem hasPolynomialProjectiveEmbedding_prod (X Y : Over (Spec (.of R)))
    (hX : hasPolynomialProjectiveEmbedding R X) (hY : hasPolynomialProjectiveEmbedding R Y) :
    hasPolynomialProjectiveEmbedding R (X ⨯ Y) := by
  obtain ⟨σ, hσ, f, hf⟩ := hX
  obtain ⟨τ, hτ, g, hg⟩ := hY
  -- Instance search does not reach composition stability through `IsMultiplicative` here.
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : IsClosedImmersion (prod.map f g).left :=
    MorphismProperty.prod_map_left (P := @IsClosedImmersion) f g hf hg
  refine ⟨σ × τ, inferInstance, prod.map f g ≫ segreOver R σ τ, ?_⟩
  -- The composition instance applies to the product embedding and Segre map as scheme maps.
  change IsClosedImmersion ((prod.map f g).left ≫ (segreOver R σ τ).left)
  infer_instance

private instance :
    (hasPolynomialProjectiveEmbedding R).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le X hX := by
    obtain ⟨t⟩ := (ObjectProperty.limitsOfShape_isEmpty_iff _ _ _).mp hX
    let Y := Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R))
    have hY : IsTerminal Y := Over.mkIdTerminal.ofIso
      (Over.isoMk (asIso (toSpecCoeff (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)))
        (by rfl)).symm
    refine ⟨PUnit.{u + 1}, inferInstance, (t.uniqueUpToIso hY).hom, ?_⟩
    have : IsIso (t.uniqueUpToIso hY).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (t.uniqueUpToIso hY).hom))
    infer_instance

private instance : (hasPolynomialProjectiveEmbedding R).IsClosedUnderBinaryProducts := by
  refine .mk' ?_
  rintro _ ⟨F, hF⟩
  exact (hasPolynomialProjectiveEmbedding R).prop_of_iso
    (HasLimit.isoOfNatIso (diagramIsoPair F)).symm
    (hasPolynomialProjectiveEmbedding_prod R _ _ (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))

private instance : (hasPolynomialProjectiveEmbedding R).IsClosedUnderFiniteProducts := .mk'

/-- A finite product of schemes admitting finite polynomial projective embeddings admits such
an embedding over the same coefficient ring. -/
theorem exists_isClosedImmersion_finite_product {ι : Type*} [Finite ι]
    (X : ι → Over (Spec (.of R)))
    (hX : ∀ i, ∃ (σ : Type u) (_ : Finite σ)
      (f : X i ⟶ Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R))),
      IsClosedImmersion f.left) :
    ∃ (σ : Type u) (_ : Finite σ)
      (f : (∏ᶜ X) ⟶ Over.mk (toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R))),
      IsClosedImmersion f.left :=
  (hasPolynomialProjectiveEmbedding R).prop_product hX

end Proj

end AlgebraicGeometry
