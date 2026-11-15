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

## Main declarations

* `TauCeti.Toric.Fan.isIso_algebraicProdComparison`: the product comparison is an isomorphism.
* `TauCeti.Toric.Fan.algebraicProdIso`: the canonical product-fan scheme isomorphism.
* `TauCeti.Toric.Fan.isPullback_fst_snd_algebraicMap`: the fan projections form a pullback
  square over `Spec ℂ`.
* `TauCeti.Toric.Fan.affineToricChartProdMap_comp_algebraicProdComparison_inv`: the inverse formula
  on each product affine chart.

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

/-- The product comparison is injective. -/
private theorem injective_algebraicProdComparison :
    Function.Injective (Φ.algebraicProdComparison Ψ) := by
  -- Representatives with the same image meet in the chart of the factor intersections.
  intro x y hxy
  obtain ⟨σ, τ, a, rfl⟩ := Φ.exists_affineToricChartι_prodCone_apply_eq Ψ x
  obtain ⟨σ', τ', b, rfl⟩ := Φ.exists_affineToricChartι_prodCone_apply_eq Ψ y
  let c := Φ.algebraicProdComparison Ψ
  let A := (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ)
  let B := (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ' τ')
  let C := (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ (σ ⊓ σ') (τ ⊓ τ'))
  have hq : c (A a) ∈ Set.range (Φ.affineToricChartProdMap Ψ (σ ⊓ σ') (τ ⊓ τ')) := by
    rw [← range_affineToricChartProdMap_inter_range_affineToricChartProdMap]
    constructor
    · rw [← range_affineToricChartι_comp_algebraicProdComparison]
      exact ⟨a, rfl⟩
    · rw [← range_affineToricChartι_comp_algebraicProdComparison]
      exact ⟨b, hxy.symm⟩
  obtain ⟨z, hz⟩ : c (A a) ∈ Set.range (C ≫ c) := by
    rwa [range_affineToricChartι_comp_algebraicProdComparison]
  have hzin : C z ∈ Set.range A ∩ Set.range B := by
    rw [(Φ.prod Ψ).range_affineToricChartι_inter_range_affineToricChartι,
      prodCone_inf_prodCone]
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

/-- The algebraic maps of the fan projections exhibit the product-fan scheme as a fibre
product over `Spec ℂ`. -/
theorem isPullback_fst_snd_algebraicMap :
    IsPullback (FanHom.fst Φ Ψ).algebraicMap (FanHom.snd Φ Ψ).algebraicMap
      Φ.algebraicRealizationStructureMap Ψ.algebraicRealizationStructureMap := by
  refine IsPullback.of_iso_pullback ?_ (Φ.algebraicProdIso Ψ) ?_ ?_
  · exact ⟨by
      rw [← Φ.algebraicProdComparison_fst Ψ, ← Φ.algebraicProdComparison_snd Ψ,
        Category.assoc, Category.assoc, pullback.condition]⟩
  · exact Φ.algebraicProdComparison_fst Ψ
  · exact Φ.algebraicProdComparison_snd Ψ

/-- On each product open, the inverse global comparison is the inverse affine product
isomorphism followed by the inclusion of the product-cone chart. -/
@[reassoc]
theorem affineToricChartProdMap_comp_algebraicProdComparison_inv (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.affineToricChartProdMap Ψ σ τ ≫ inv (Φ.algebraicProdComparison Ψ) =
      (affineToricSchemeProdIso Φ.lattice Ψ.lattice σ.1 τ.1).inv ≫
        (Φ.prod Ψ).affineToricChartι (Φ.prodCone Ψ σ τ) := by
  apply (cancel_mono (Φ.algebraicProdComparison Ψ)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc,
    affineToricChartι_comp_algebraicProdComparison, Iso.inv_hom_id_assoc]

end TauCeti.Toric.Fan
