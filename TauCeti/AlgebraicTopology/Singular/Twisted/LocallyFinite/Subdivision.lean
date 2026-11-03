/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Twisted.Subdivision

/-!
# Barycentric subdivision of locally finite chains with local coefficients

Barycentric subdivision extends to locally finite twisted singular chains and is chain homotopic
to the identity. Both subdivision and the prism homotopy replace a simplex only by simplices
inside its image. This support control preserves local finiteness, even when the coefficient
system has nontrivial transport, and is needed for comparing locally finite singular and
simplicial chains.

`locallyFiniteSubdivisionChainMap` is the extension of `twistedSubdivisionChainMap`.
`locallyFiniteSubdivisionHomotopy` extends the existing twisted prism operator, so subdivision
induces the identity on Borel–Moore homology. Subdivision commutes with proper pushforward,
coefficient morphisms and the inclusion of finite chains.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, for subdivision and
  its prism operator, and Section 3.H for local coefficients.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Chapter V, for locally finite homology.
-/

public section

noncomputable section

open CategoryTheory SimplexCategory Convexity

open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- An operator obtained on each simplex by pushing forward an affine chain does not enlarge
that simplex's image. -/
lemma movesAlong_of_ιTwistedChainComplex_eq_twistedSingularChain {k m : ℕ}
    {A : (twistedChainComplex L).X k ⟶ (twistedChainComplex L).X m}
    (c : (Fin (m + 1) → StdSimplex ℝ (Fin (k + 1))) →₀ ℤ)
    (hA : ∀ σ, ιTwistedChainComplex L k σ ≫ A =
      twistedSingularChain L σ (toTopInitialVertex ⦋k⦌) m c) : MovesAlong (𝟙 X) A := by
  refine movesAlong_iff.mpr ?_
  intro ρ σ x hx
  rw [TopCat.hom_id, ContinuousMap.coe_id, Set.image_id]
  by_contra h
  have hz := twistedSingularChain_comp_twistedChainComplexCoeff_eq_zero L σ
    (toTopInitialVertex ⦋k⦌) c ρ h
  rw [← hA σ] at hz
  apply hx
  simpa only [matrixCoeff_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] using congrArg (fun f ↦ f.hom x) hz

/-- Every simplex occurring in the subdivision of a twisted simplex lies inside the original
simplex's image. -/
lemma movesAlong_twistedSubdivisionX (k : ℕ) : MovesAlong (𝟙 X) (twistedSubdivisionX L k) :=
  movesAlong_of_ιTwistedChainComplex_eq_twistedSingularChain L _
    (ιTwistedChainComplex_twistedSubdivisionX_eq L)

/-- The prism homotopy for twisted subdivision does not enlarge a simplex's image. -/
lemma movesAlong_twistedPrismX (k : ℕ) : MovesAlong (𝟙 X) (twistedPrismX L k) :=
  movesAlong_of_ιTwistedChainComplex_eq_twistedSingularChain L _
    (ιTwistedChainComplex_twistedPrismX L)

/-- Each component of twisted barycentric subdivision is properly supported. -/
lemma isProperlySupported_twistedSubdivisionChainMap_f (k : ℕ) :
    IsProperlySupported ((twistedSubdivisionChainMap L).f k) := by
  rw [twistedSubdivisionChainMap_f]
  exact .of_movesAlong isProperMap_id (movesAlong_twistedSubdivisionX L k)

/-- Barycentric subdivision of locally finite singular chains with coefficients in `L`. -/
def locallyFiniteSubdivisionChainMap : locallyFiniteChainComplex L ⟶ locallyFiniteChainComplex L :=
  extendLocallyFiniteChainMap (twistedSubdivisionChainMap L)
    (isProperlySupported_twistedSubdivisionChainMap_f L)

/-- Locally finite subdivision is the extension of twisted subdivision on finite chains. -/
lemma locallyFiniteSubdivisionChainMap_def :
    locallyFiniteSubdivisionChainMap L = extendLocallyFiniteChainMap
      (twistedSubdivisionChainMap L) (isProperlySupported_twistedSubdivisionChainMap_f L) := (rfl)

/-- In each degree, locally finite subdivision applies twisted subdivision simplex by simplex. -/
@[simp]
lemma locallyFiniteSubdivisionChainMap_f (k : ℕ) :
    (locallyFiniteSubdivisionChainMap L).f k =
      eqToHom (locallyFiniteChainComplex_X L k) ≫
        ModuleCat.ofHom (extendLocallyFinite
          (.of_movesAlong isProperMap_id (movesAlong_twistedSubdivisionX L k))) ≫
            eqToHom (locallyFiniteChainComplex_X L k).symm := by
  simp only [locallyFiniteSubdivisionChainMap_def, extendLocallyFiniteChainMap_f,
    twistedSubdivisionChainMap_f]

/-- **Locally finite twisted subdivision is chain homotopic to the identity.** The homotopy is
the extension of the twisted prism operator, not a homotopy chosen only on homology. -/
def locallyFiniteSubdivisionHomotopy : Homotopy (𝟙 _) (locallyFiniteSubdivisionChainMap L) :=
  ((Homotopy.ofEq (extendLocallyFiniteChainMap_id (L := L)
    (fun k ↦ by rw [HomologicalComplex.id_f]; exact isProperlySupported_id)).symm).trans
    (extendLocallyFiniteHomotopy
      (fun k ↦ by rw [HomologicalComplex.id_f]; exact isProperlySupported_id)
      (isProperlySupported_twistedSubdivisionChainMap_f L)
      (twistedSubdivisionHomotopy L) (fun k ↦ by
        rw [twistedSubdivisionHomotopy_hom]
        exact .of_movesAlong isProperMap_id (movesAlong_twistedPrismX L k)))).trans
    (Homotopy.ofEq (locallyFiniteSubdivisionChainMap_def L).symm)

/-- The locally finite subdivision homotopy is the extension of the twisted prism in every
adjacent pair of degrees. -/
@[simp]
lemma locallyFiniteSubdivisionHomotopy_hom (k : ℕ) :
    (locallyFiniteSubdivisionHomotopy L).hom k (k + 1) =
      eqToHom (locallyFiniteChainComplex_X L k) ≫
        ModuleCat.ofHom (extendLocallyFinite
          (.of_movesAlong isProperMap_id (movesAlong_twistedPrismX L k))) ≫
            eqToHom (locallyFiniteChainComplex_X L (k + 1)).symm := by
  simp only [locallyFiniteSubdivisionHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Pi.zero_apply, zero_add, add_zero, extendLocallyFiniteHomotopy_hom,
    twistedSubdivisionHomotopy_hom]

/-- Barycentric subdivision induces the identity on Borel–Moore homology with local coefficients. -/
@[simp]
lemma homologyMap_locallyFiniteSubdivisionChainMap (k : ℕ) :
    HomologicalComplex.homologyMap (locallyFiniteSubdivisionChainMap L) k = 𝟙 _ := by
  rw [← (locallyFiniteSubdivisionHomotopy L).homologyMap_eq k, HomologicalComplex.homologyMap_id]

/-- The inclusion of finite chains into locally finite chains commutes with subdivision. -/
@[reassoc]
lemma toLocallyFiniteChainComplex_comp_locallyFiniteSubdivisionChainMap :
    toLocallyFiniteChainComplex L ≫ locallyFiniteSubdivisionChainMap L =
      twistedSubdivisionChainMap L ≫ toLocallyFiniteChainComplex L := by
  rw [locallyFiniteSubdivisionChainMap_def]
  exact toLocallyFiniteChainComplex_comp_extendLocallyFiniteChainMap _ _

/-- Locally finite subdivision is natural in the local coefficient system. -/
@[reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteSubdivisionChainMap
    {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) :
    locallyFiniteChainComplexCoefficientMap η ≫ locallyFiniteSubdivisionChainMap K =
      locallyFiniteSubdivisionChainMap L ≫ locallyFiniteChainComplexCoefficientMap η := by
  rw [locallyFiniteSubdivisionChainMap_def, locallyFiniteSubdivisionChainMap_def,
    locallyFiniteChainComplexCoefficientMap_eq_extendLocallyFiniteChainMap,
    extendLocallyFiniteChainMap_comp, extendLocallyFiniteChainMap_comp]
  exact extendLocallyFiniteChainMap_congr _ _
    (twistedChainComplexCoefficientMap_comp_twistedSubdivisionChainMap η)

/-- Locally finite subdivision commutes with pushforward along a proper map. -/
@[reassoc]
lemma locallyFiniteChainComplexMap_comp_locallyFiniteSubdivisionChainMap
    (f : Y ⟶ X) (hf : IsProperMap f.hom) :
    locallyFiniteChainComplexMap f hf L ≫ locallyFiniteSubdivisionChainMap L =
      locallyFiniteSubdivisionChainMap ((pullback f.hom).obj L) ≫
        locallyFiniteChainComplexMap f hf L := by
  rw [locallyFiniteSubdivisionChainMap_def, locallyFiniteSubdivisionChainMap_def,
    locallyFiniteChainComplexMap_eq_extendLocallyFiniteChainMap,
    extendLocallyFiniteChainMap_comp, extendLocallyFiniteChainMap_comp]
  exact extendLocallyFiniteChainMap_congr _ _
    (twistedChainComplexMap_comp_twistedSubdivisionChainMap f L)

end TauCeti.LocalCoefficientSystem
