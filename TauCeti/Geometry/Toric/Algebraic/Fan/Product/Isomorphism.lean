/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The scheme of a product fan

The canonical comparison from the scheme of a product fan to the fibre product of the factor
schemes over `Spec ℂ` is an isomorphism. The affine products of cone charts cover the fibre
product, and their intersections are the charts of the intersections of the factor cones.
Consequently the existing affine product isomorphisms identify the global schemes, including
when either fan is empty. No regularity hypothesis is needed.

The construction uses `affineToricSchemeProdIso` and the chart formula for
`Fan.algebraicProdComparison` from `Product.Scheme`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric.Fan

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Φ : Fan i) (Ψ : Fan i')

/-- The product affine charts cover the fibre product of the fan schemes. -/
theorem exists_affineToricChartProdMap_apply_eq
    (x : ↥(pullback Φ.algebraicRealizationStructureMap Ψ.algebraicRealizationStructureMap)) :
    ∃ (σ : Φ.cones) (τ : Ψ.cones), ∃ y, Φ.affineToricChartProdMap Ψ σ τ y = x := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineToricChartι_apply_eq
    (pullback.fst Φ.algebraicRealizationStructureMap Ψ.algebraicRealizationStructureMap x)
  obtain ⟨τ, z, hz⟩ := Ψ.exists_affineToricChartι_apply_eq
    (pullback.snd Φ.algebraicRealizationStructureMap Ψ.algebraicRealizationStructureMap x)
  have hx : x ∈ Set.range (Φ.affineToricChartProdMap Ψ σ τ) := by
    rw [range_affineToricChartProdMap]
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  exact ⟨σ, τ, hx⟩

/-- Intersections of product cone opens are computed in each factor. -/
theorem range_affineToricChartProdMap_inter (σ σ' : Φ.cones) (τ τ' : Ψ.cones) :
    Set.range (Φ.affineToricChartProdMap Ψ σ τ) ∩
        Set.range (Φ.affineToricChartProdMap Ψ σ' τ') =
      Set.range (Φ.affineToricChartProdMap Ψ (σ ⊓ σ') (τ ⊓ τ')) := by
  simp only [range_affineToricChartProdMap, ← range_affineToricChartι_inter,
    Set.preimage_inter]
  ext x
  simp only [Set.mem_inter_iff]
  tauto

/-- On each product-cone chart the comparison is an open immersion. -/
instance isOpenImmersion_affineToricChartι_comp_algebraicProdComparison
    (σ : Φ.cones) (τ : Ψ.cones) :
    IsOpenImmersion ((Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) ≫
      Φ.algebraicProdComparison Ψ) := by
  rw [affineToricChartι_comp_algebraicProdComparison]
  infer_instance

/-- The image of a product-cone chart under the comparison is the corresponding product open. -/
theorem range_affineToricChartι_comp_algebraicProdComparison (σ : Φ.cones) (τ : Ψ.cones) :
    Set.range ((Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) ≫
        Φ.algebraicProdComparison Ψ) = Set.range (Φ.affineToricChartProdMap Ψ σ τ) := by
  rw [affineToricChartι_comp_algebraicProdComparison, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp]
  have hs : Function.Surjective
      (affineToricSchemeProdIso Φ.lattice Ψ.lattice σ.1 τ.1).hom := by
    simpa only [Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso (affineToricSchemeProdIso Φ.lattice Ψ.lattice σ.1 τ.1)).surjective
  rw [Set.range_eq_univ.mpr hs, Set.image_univ]

/-- Every point of a product-fan scheme lies in a chart indexed by a pair of factor cones. -/
private theorem exists_affineToricChartι_prodCone_apply_eq (x : (Φ.prod Ψ).algebraicRealization) :
    ∃ (σ : Φ.cones) (τ : Ψ.cones), ∃ y,
      (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) y = x := by
  obtain ⟨ξ, y, hy⟩ := (Φ.prod Ψ).exists_affineToricChartι_apply_eq x
  obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ξ
  exact ⟨σ, τ, y, hy⟩

private theorem surjective_algebraicProdComparison :
    Function.Surjective (Φ.algebraicProdComparison Ψ) := by
  intro x
  obtain ⟨σ, τ, y, hy⟩ := Φ.exists_affineToricChartProdMap_apply_eq Ψ x
  have hx : x ∈ Set.range ((Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) ≫
      Φ.algebraicProdComparison Ψ) := by
    rw [range_affineToricChartι_comp_algebraicProdComparison]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  exact ⟨(Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) z, hz⟩

/-- The product comparison is injective: two local representatives with the same image
come from the chart of the intersections of their factor cones. -/
private theorem injective_algebraicProdComparison :
    Function.Injective (Φ.algebraicProdComparison Ψ) := by
  intro x y hxy
  obtain ⟨σ, τ, a, rfl⟩ := Φ.exists_affineToricChartι_prodCone_apply_eq Ψ x
  obtain ⟨σ', τ', b, rfl⟩ := Φ.exists_affineToricChartι_prodCone_apply_eq Ψ y
  let c := Φ.algebraicProdComparison Ψ
  let A := (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ)
  let B := (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ' τ')
  let C := (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ (σ ⊓ σ') (τ ⊓ τ'))
  have hq : c (A a) ∈ Set.range (Φ.affineToricChartProdMap Ψ (σ ⊓ σ') (τ ⊓ τ')) := by
    rw [← range_affineToricChartProdMap_inter]
    constructor
    · rw [← range_affineToricChartι_comp_algebraicProdComparison]
      exact ⟨a, rfl⟩
    · rw [← range_affineToricChartι_comp_algebraicProdComparison]
      exact ⟨b, hxy.symm⟩
  obtain ⟨z, hz⟩ : c (A a) ∈ Set.range (C ≫ c) := by
    rwa [range_affineToricChartι_comp_algebraicProdComparison]
  have hcone : Φ.prodCone Ψ σ τ ⊓ Φ.prodCone Ψ σ' τ' =
      Φ.prodCone Ψ (σ ⊓ σ') (τ ⊓ τ') := by
    apply Subtype.ext
    exact Submodule.prod_inf_prod _ _ _ _
  have hzin : C z ∈ Set.range A ∩ Set.range B := by
    rw [(Φ.prod Ψ).range_affineToricChartι_inter, hcone]
    exact ⟨z, rfl⟩
  obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := hzin
  have ha : a' = a := (A ≫ c).isOpenEmbedding.injective <| by
    simp only [Scheme.Hom.comp_apply]
    rw [ha']
    exact hz
  have hb : b' = b := (B ≫ c).isOpenEmbedding.injective <| by
    simp only [Scheme.Hom.comp_apply]
    rw [hb']
    exact hz.trans hxy
  exact (ha ▸ ha').trans (hb ▸ hb').symm

/-- The scheme of a product fan is the fibre product of the fan schemes over `Spec ℂ`. -/
instance isIso_algebraicProdComparison : IsIso (Φ.algebraicProdComparison Ψ) := by
  have : Surjective (Φ.algebraicProdComparison Ψ) :=
    ⟨Φ.surjective_algebraicProdComparison Ψ⟩
  have : IsOpenImmersion (Φ.algebraicProdComparison Ψ) := by
    apply IsOpenImmersion.of_openCover_source (Φ.algebraicProdComparison Ψ)
      (Φ.prod Ψ).affineToricOpenCover (Φ.injective_algebraicProdComparison Ψ)
    intro ξ
    obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ξ
    rw [affineToricOpenCover_f]
    exact Φ.isOpenImmersion_affineToricChartι_comp_algebraicProdComparison Ψ σ τ
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

/-- The canonical isomorphism from the product-fan scheme to the fibre product of its factors. -/
noncomputable def algebraicProdIso : (Φ.prod Ψ).algebraicRealization ≅
    pullback Φ.algebraicRealizationStructureMap Ψ.algebraicRealizationStructureMap :=
  asIso (Φ.algebraicProdComparison Ψ)

@[simp]
theorem algebraicProdIso_hom : (Φ.algebraicProdIso Ψ).hom = Φ.algebraicProdComparison Ψ :=
  (rfl)

@[simp]
theorem algebraicProdIso_inv : (Φ.algebraicProdIso Ψ).inv = inv (Φ.algebraicProdComparison Ψ) :=
  (rfl)

/-- On each product open, the inverse global comparison is the inverse affine product
isomorphism followed by the inclusion of the product-cone chart. -/
@[reassoc]
theorem affineToricChartProdMap_comp_algebraicProdIso_inv (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.affineToricChartProdMap Ψ σ τ ≫ (Φ.algebraicProdIso Ψ).inv =
      (affineToricSchemeProdIso Φ.lattice Ψ.lattice σ.1 τ.1).inv ≫
        (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) := by
  apply (cancel_mono (Φ.algebraicProdIso Ψ).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [algebraicProdIso_hom, Category.assoc,
    affineToricChartι_comp_algebraicProdComparison, Iso.inv_hom_id_assoc]

end TauCeti.Toric.Fan
