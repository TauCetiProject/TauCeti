/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# Naturality of the Wang mapping-cone map

The mapping cone of `id - φ₊` maps to the singular chains of the mapping torus of `φ`.
This file compares those maps for a continuous map intertwining two monodromies. The
comparison is needed to identify the mapping-cone model of the Wang sequence naturally.

The cylinder homotopy defining the cone map is itself natural: a map of mapping tori sends
its track at every time to the track of the image point. The induced singular-chain homotopy
then gives the required commutative square of chain maps.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits MonoidalCategory
open scoped Simplicial

universe w v u

namespace TauCeti.MappingTorus

variable {F G : Type w} [TopologicalSpace F] [TopologicalSpace G]
  (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (g : C(F, G)) (h : Function.Semiconj g φ ψ)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (R : C)

/-- The singular-chain homotopy of the mapping-torus cylinder is natural under a map
intertwining the monodromies. -/
@[reassoc]
lemma singularChainHomotopy_hom_naturality (φ : F ≃ₜ F) (R : C) (ψ : G ≃ₜ G)
    (g : C(F, G)) (h : Function.Semiconj g φ ψ) (i j : ℕ) :
    (fibreChainMap R g).f i ≫ (singularChainHomotopy ψ R).hom i j =
      (singularChainHomotopy φ R).hom i j ≫
        (mappingTorusChainMap φ R ψ g h).f j := by
  simp only [singularChainHomotopy_hom, fibreChainMap_def, mappingTorusChainMap_def]
  let hφ : TopCat.Homotopy
      (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)) ≫
        TopCat.ofHom (TauCeti.MappingTorus.incl φ))
      (TopCat.ofHom (TauCeti.MappingTorus.incl φ)) := monodromyHomotopy φ
  let hψ : TopCat.Homotopy
      (TopCat.ofHom (⟨ψ, ψ.continuous⟩ : C(G, G)) ≫
        TopCat.ofHom (TauCeti.MappingTorus.incl ψ))
      (TopCat.ofHom (TauCeti.MappingTorus.incl ψ)) := monodromyHomotopy ψ
  have ht : TopCat.ofHom g ▷ TopCat.I ≫ hψ.h =
      hφ.h ≫ TopCat.ofHom (map φ ψ g h) := by
    ext p
    -- Evaluate category morphisms as continuous maps to expose the homotopy tracks.
    change monodromyHomotopy ψ (TopCat.I.homeomorph p.2, g p.1) =
      map φ ψ g h (monodromyHomotopy φ (TopCat.I.homeomorph p.2, p.1))
    exact (map_monodromyHomotopy φ ψ g h (TopCat.I.homeomorph p.2) p.1).symm
  have hu : TopCat.toSSet.map (TopCat.ofHom g) ▷ Δ[1] ≫ hψ.toSSet.h =
      hφ.toSSet.h ≫ TopCat.toSSet.map (TopCat.ofHom (map φ ψ g h)) := by
    simp only [TopCat.Homotopy.toSSet, Category.assoc]
    rw [← whisker_exchange_assoc (TopCat.toSSet.map (TopCat.ofHom g))
      SSet.stdSimplex.toSSetObjI]
    rw [Functor.LaxMonoidal.μ_natural_left_assoc]
    simp only [← Functor.map_comp]
    rw [ht]
  exact hφ.toSSet.chainComplexMap_hom_comm hψ.toSSet hu R i j

variable [HasBinaryBiproducts C]

/-- The map from the Wang mapping cone to mapping-torus chains commutes with a map
intertwining the monodromies. -/
@[reassoc]
theorem wangMappingConeMap_naturality :
    wangMappingConeMapOfSemiconj φ R ψ g h ≫ wangMappingConeMap ψ R =
      wangMappingConeMap φ R ≫ mappingTorusChainMap φ R ψ g h := by
  have hInr : HomologicalComplex.homotopyCofiber.inr (wangEndomorphism φ R) ≫
        (wangMappingConeMapOfSemiconj φ R ψ g h ≫ wangMappingConeMap ψ R) =
      HomologicalComplex.homotopyCofiber.inr (wangEndomorphism φ R) ≫
        (wangMappingConeMap φ R ≫ mappingTorusChainMap φ R ψ g h) := by
    simp [fibreInclusionChainMap_comp_mappingTorusChainMap]
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      apply HomologicalComplex.homotopyCofiber.ext_from_X'
        (wangEndomorphism φ R) 0 (by simp)
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.homotopyCofiber.inr_f]
        using congrArg (fun k ↦ k.f 0) hInr
  | succ n =>
      apply HomologicalComplex.homotopyCofiber.ext_from_X
        (wangEndomorphism φ R) n (n + 1) (by simp)
      · simp only [HomologicalComplex.comp_f]
        rw [← Category.assoc, homotopyCofiber_inlX_comp_wangMappingConeMapOfSemiconj_f]
        conv_lhs => rw [Category.assoc, homotopyCofiber_inlX_comp_wangMappingConeMap_f]
        conv_rhs => rw [← Category.assoc, homotopyCofiber_inlX_comp_wangMappingConeMap_f]
        simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_inj]
        exact singularChainHomotopy_hom_naturality φ R ψ g h n (n + 1)
      · simpa only [HomologicalComplex.comp_f, HomologicalComplex.homotopyCofiber.inr_f]
          using congrArg (fun k ↦ k.f (n + 1)) hInr

end TauCeti.MappingTorus
