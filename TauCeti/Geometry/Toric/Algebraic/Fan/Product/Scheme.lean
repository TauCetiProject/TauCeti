/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic
public import TauCeti.Geometry.Toric.Algebraic.Product
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Products of toric fan schemes

The scheme of a product fan has a canonical morphism to the fibre product of the two factor
schemes over `Spec ℂ`. On the chart indexed by a pair of cones, this morphism is the affine
product isomorphism followed by the product of the two chart inclusions. Thus the global
comparison is locally the standard tensor-product comparison for affine toric schemes.

This is the local compatibility needed to identify the product-fan scheme with the fibre product
globally: the product charts cover the source, while the corresponding fibre products of affine
charts cover the target.

## Main declarations

* `TauCeti.Toric.Fan.algebraicProdComparison`: the canonical morphism from the product-fan
  scheme to the fibre product of the factor schemes.
* `TauCeti.Toric.Fan.affineToricChartι_comp_algebraicProdComparison`: the comparison's formula
  on every product affine chart.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

namespace FanHom

variable (Phi : Fan i) (Psi : Fan i')

/-- On a product affine chart, the algebraic map of the first fan projection is the affine
toric projection followed by the corresponding chart inclusion. -/
@[reassoc]
theorem affineToricChartι_prodCone_comp_fst_algebraicMap
    (sigma : Phi.cones) (tau : Psi.cones) :
    (Phi.prod Psi).affineToricChartι (Phi.prodCone Psi sigma tau) ≫
        (FanHom.fst Phi Psi).algebraicMap =
      affineToricSchemeMap (σ := sigma.1.prod tau.1) (τ := sigma.1)
          (Phi.lattice.prod Psi.lattice) Phi.lattice
          (AddMonoidHom.fst N N') (LinearMap.fst ℝ V V') (fun _ ↦ by simp)
          (by
            simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
              (Set.mapsTo_fst_prod (s := (sigma.1 : Set V)) (t := (tau.1 : Set V')))) ≫
        Phi.affineToricChartι sigma := by
  convert affineToricChartι_comp_algebraicMap_of_leastCone_eq (FanHom.fst Phi Psi)
    (Phi.prodCone Psi sigma tau) sigma (fst_leastCone_prodCone sigma tau)
    (fun _ hx ↦ by simpa only [FanHom.fst_realMap, LinearMap.fst_apply] using hx.1) using 3
  simp only [FanHom.fst_latticeMap, FanHom.fst_realMap]

/-- On a product affine chart, the algebraic map of the second fan projection is the affine
toric projection followed by the corresponding chart inclusion. -/
@[reassoc]
theorem affineToricChartι_prodCone_comp_snd_algebraicMap
    (sigma : Phi.cones) (tau : Psi.cones) :
    (Phi.prod Psi).affineToricChartι (Phi.prodCone Psi sigma tau) ≫
        (FanHom.snd Phi Psi).algebraicMap =
      affineToricSchemeMap (σ := sigma.1.prod tau.1) (τ := tau.1)
          (Phi.lattice.prod Psi.lattice) Psi.lattice
          (AddMonoidHom.snd N N') (LinearMap.snd ℝ V V') (fun _ ↦ by simp)
          (by
            simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
              (Set.mapsTo_snd_prod (s := (sigma.1 : Set V)) (t := (tau.1 : Set V')))) ≫
        Psi.affineToricChartι tau := by
  convert affineToricChartι_comp_algebraicMap_of_leastCone_eq (FanHom.snd Phi Psi)
    (Phi.prodCone Psi sigma tau) tau (snd_leastCone_prodCone sigma tau)
    (fun _ hx ↦ by simpa only [FanHom.snd_realMap, LinearMap.snd_apply] using hx.2) using 3
  simp only [FanHom.snd_latticeMap, FanHom.snd_realMap]

end FanHom

namespace Fan

variable (Phi : Fan i) (Psi : Fan i')

/-- The scheme of a product fan maps canonically to the fibre product of the two fan schemes
over `Spec ℂ`, through the algebraic maps induced by the fan projections. -/
noncomputable def algebraicProdComparison :
    (Phi.prod Psi).algebraicRealization ⟶
      pullback Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap :=
  pullback.lift (FanHom.fst Phi Psi).algebraicMap (FanHom.snd Phi Psi).algebraicMap <| by
    rw [← Phi.algebraicRealization_over, ← Psi.algebraicRealization_over]
    exact (comp_over (FanHom.fst Phi Psi).algebraicMap (Spec (.of ℂ))).trans
      (comp_over (FanHom.snd Phi Psi).algebraicMap (Spec (.of ℂ))).symm

/-- The first projection of the product comparison is the toric map induced by the first fan
projection. -/
@[reassoc (attr := simp)]
theorem algebraicProdComparison_fst :
    Phi.algebraicProdComparison Psi ≫
        pullback.fst Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap =
      (FanHom.fst Phi Psi).algebraicMap := by
  simp [algebraicProdComparison]

/-- The second projection of the product comparison is the toric map induced by the second fan
projection. -/
@[reassoc (attr := simp)]
theorem algebraicProdComparison_snd :
    Phi.algebraicProdComparison Psi ≫
        pullback.snd Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap =
      (FanHom.snd Phi Psi).algebraicMap := by
  simp [algebraicProdComparison]

/-- The product of two affine chart inclusions, as a morphism from the fibre product of the
affine charts to the fibre product of the two fan schemes. -/
noncomputable def affineToricChartProdMap (sigma : Phi.cones) (tau : Psi.cones) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Phi.lattice sigma.1))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Psi.lattice tau.1)))) ⟶
      pullback Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap :=
  pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Phi.lattice sigma.1))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Psi.lattice tau.1))))
    Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap
    (Phi.affineToricChartι sigma) (Psi.affineToricChartι tau) (𝟙 _) (by
      rw [Category.comp_id, affineToricChartι_comp_algebraicRealizationStructureMap]) (by
      rw [Category.comp_id, affineToricChartι_comp_algebraicRealizationStructureMap])

/-- The first projection of the product of two affine chart inclusions is the first local
projection followed by the first chart inclusion. -/
@[reassoc (attr := simp)]
theorem affineToricChartProdMap_fst (sigma : Phi.cones) (tau : Psi.cones) :
    Phi.affineToricChartProdMap Psi sigma tau ≫
        pullback.fst Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap =
      pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Phi.lattice sigma.1))))
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Psi.lattice tau.1)))) ≫
        Phi.affineToricChartι sigma := by
  simp [affineToricChartProdMap]

/-- The second projection of the product of two affine chart inclusions is the second local
projection followed by the second chart inclusion. -/
@[reassoc (attr := simp)]
theorem affineToricChartProdMap_snd (sigma : Phi.cones) (tau : Psi.cones) :
    Phi.affineToricChartProdMap Psi sigma tau ≫
        pullback.snd Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap =
      pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Phi.lattice sigma.1))))
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Psi.lattice tau.1)))) ≫
        Psi.affineToricChartι tau := by
  simp [affineToricChartProdMap]

/-- On the affine chart of a product cone, the global product comparison is the affine product
isomorphism followed by the product of the two chart inclusions. -/
@[reassoc]
theorem affineToricChartι_comp_algebraicProdComparison
    (sigma : Phi.cones) (tau : Psi.cones) :
    (Phi.prod Psi).affineToricChartι (Phi.prodCone Psi sigma tau) ≫
        Phi.algebraicProdComparison Psi =
      (affineToricSchemeProdIso Phi.lattice Psi.lattice sigma.1 tau.1).hom ≫
        Phi.affineToricChartProdMap Psi sigma tau := by
  apply pullback.hom_ext
  · simp only [Category.assoc, algebraicProdComparison_fst,
      FanHom.affineToricChartι_prodCone_comp_fst_algebraicMap,
      affineToricChartProdMap_fst, affineToricSchemeProdIso_hom_fst_assoc]
  · simp only [Category.assoc, algebraicProdComparison_snd,
      FanHom.affineToricChartι_prodCone_comp_snd_algebraicMap,
      affineToricChartProdMap_snd, affineToricSchemeProdIso_hom_snd_assoc]

/-- The product of two affine cone opens is open in the fibre product of the fan schemes. -/
instance isOpenImmersion_affineToricChartProdMap (σ : Phi.cones) (τ : Psi.cones) :
    IsOpenImmersion (Phi.affineToricChartProdMap Psi σ τ) := by
  unfold affineToricChartProdMap
  infer_instance

/-- The product chart is the locus where both projections lie in the respective cone opens. -/
theorem range_affineToricChartProdMap (σ : Phi.cones) (τ : Psi.cones) :
    Set.range (Phi.affineToricChartProdMap Psi σ τ) =
      pullback.fst Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap ⁻¹'
          Set.range (Phi.affineToricChartι σ) ∩
        pullback.snd Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap ⁻¹'
          Set.range (Psi.affineToricChartι τ) := by
  unfold affineToricChartProdMap
  exact Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _

/-- The product affine charts cover the fibre product of the fan schemes. -/
theorem exists_affineToricChartProdMap_apply_eq
    (x : ↥(pullback Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap)) :
    ∃ (σ : Phi.cones) (τ : Psi.cones), ∃ y, Phi.affineToricChartProdMap Psi σ τ y = x := by
  obtain ⟨σ, y, hy⟩ := Phi.exists_affineToricChartι_apply_eq
    (pullback.fst Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap x)
  obtain ⟨τ, z, hz⟩ := Psi.exists_affineToricChartι_apply_eq
    (pullback.snd Phi.algebraicRealizationStructureMap Psi.algebraicRealizationStructureMap x)
  have hx : x ∈ Set.range (Phi.affineToricChartProdMap Psi σ τ) := by
    rw [range_affineToricChartProdMap]
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  exact ⟨σ, τ, hx⟩

/-- Intersections of product cone opens are computed in each factor. -/
@[simp]
theorem range_affineToricChartProdMap_inter_range_affineToricChartProdMap
    (σ σ' : Phi.cones) (τ τ' : Psi.cones) :
    Set.range (Phi.affineToricChartProdMap Psi σ τ) ∩
        Set.range (Phi.affineToricChartProdMap Psi σ' τ') =
      Set.range (Phi.affineToricChartProdMap Psi (σ ⊓ σ') (τ ⊓ τ')) := by
  simp only [range_affineToricChartProdMap, ← range_affineToricChartι_inter_range_affineToricChartι,
    Set.preimage_inter]
  exact Set.inter_inter_inter_comm _ _ _ _

/-- On each product-cone chart the comparison is an open immersion. -/
instance isOpenImmersion_affineToricChartι_comp_algebraicProdComparison
    (σ : Phi.cones) (τ : Psi.cones) :
    IsOpenImmersion ((Phi.prod Psi).affineToricChartι (Phi.prodCone Psi σ τ) ≫
      Phi.algebraicProdComparison Psi) := by
  rw [affineToricChartι_comp_algebraicProdComparison]
  infer_instance

/-- The image of a product-cone chart under the comparison is the corresponding product open. -/
theorem range_affineToricChartι_comp_algebraicProdComparison (σ : Phi.cones) (τ : Psi.cones) :
    Set.range ((Phi.prod Psi).affineToricChartι (Phi.prodCone Psi σ τ) ≫
        Phi.algebraicProdComparison Psi) = Set.range (Phi.affineToricChartProdMap Psi σ τ) := by
  have hs : Function.Surjective
      (affineToricSchemeProdIso Phi.lattice Psi.lattice σ.1 τ.1).hom := by
    simpa only [Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso (affineToricSchemeProdIso Phi.lattice Psi.lattice σ.1 τ.1)).surjective
  rw [affineToricChartι_comp_algebraicProdComparison, Scheme.Hom.comp_base,
    TopCat.coe_comp, hs.range_comp]

/-- Every point of a product-fan scheme lies in a chart indexed by a pair of factor cones. -/
theorem exists_affineToricChartι_prodCone_apply_eq (x : (Phi.prod Psi).algebraicRealization) :
    ∃ (σ : Phi.cones) (τ : Psi.cones), ∃ y,
      (Phi.prod Psi).affineToricChartι (Phi.prodCone Psi σ τ) y = x := by
  obtain ⟨ξ, y, hy⟩ := (Phi.prod Psi).exists_affineToricChartι_apply_eq x
  obtain ⟨σ, τ, rfl⟩ := Phi.exists_prodCone_eq Psi ξ
  exact ⟨σ, τ, y, hy⟩

end Fan

end TauCeti.Toric
