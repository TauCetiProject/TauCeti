/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism
public import TauCeti.Geometry.Toric.Algebraic.Fan.TorusAction.Naturality

/-!
# The dense torus and the torus action of a product fan scheme

The scheme `X_{Φ × Ψ}` of a product fan is the fibre product `X_Φ ×_{Spec ℂ} X_Ψ`, through the
toric maps of the two fan projections (`TauCeti.Toric.Fan.isPullback_fst_snd_algebraicMap`), and
the dense torus `T_{N × N'}` of the product lattice is the fibre product `T_N ×_{Spec ℂ} T_{N'}`
of the dense tori of the factors, through the torus morphisms of the two lattice projections
(`TauCeti.Toric.isPullback_affineToricSchemeMap_fst_snd_bot`). This file shows that the toric
structure of `X_{Φ × Ψ}` is the product of the toric structures of `X_Φ` and `X_Ψ`:

* for nonempty fans, the dense-torus inclusion of `X_{Φ × Ψ}` is the product of the dense-torus
  inclusions of the factors;
* the domain `T_{N × N'} ×_{Spec ℂ} X_{Φ × Ψ}` of the torus action is the fibre product of the
  action domains `T_N ×_{Spec ℂ} X_Φ` and `T_{N'} ×_{Spec ℂ} X_Ψ`, through the maps of action
  domains induced by the fan projections, and under these identifications the action of
  `T_{N × N'}` on `X_{Φ × Ψ}` is the product of the actions of `T_N` on `X_Φ` and of `T_{N'}` on
  `X_Ψ`.

No regularity assumption on the fans is needed.

## Main declarations

* `TauCeti.Toric.Fan.denseTorusι_prod_comp_algebraicProdComparison`: the dense torus of a
  product fan scheme is the product of the dense tori of the factors.
* `TauCeti.Toric.Fan.isPullback_algebraicActionMap_fst_snd`: the action domain of a product fan
  scheme is the fibre product of the action domains of the factors.
* `TauCeti.Toric.Fan.algebraicRealizationAction_prod_comp_algebraicProdComparison`: the torus
  action on a product fan scheme is the product of the torus actions on the factors.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3--1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric.Fan

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Φ : Fan i) (Ψ : Fan i')

/-! ### The dense torus -/

/-- The dense-torus inclusion of a product of nonempty fans is the product of the dense-torus
inclusions of the factors, through the identifications of the dense torus of the product lattice
and of the product fan scheme with fibre products over `Spec ℂ`. -/
@[reassoc]
theorem denseTorusι_prod_comp_algebraicProdComparison (hΦ₀ : Nonempty Φ.cones)
    (hΨ₀ : Nonempty Ψ.cones) :
    (Φ.prod Ψ).denseTorusι ⟨Φ.prodCone Ψ hΦ₀.some hΨ₀.some⟩ ≫ Φ.algebraicProdComparison Ψ =
      (isPullback_affineToricSchemeMap_fst_snd_bot Φ.lattice Ψ.lattice).isoPullback.hom ≫
        pullback.map _ _ _ _ (Φ.denseTorusι hΦ₀) (Ψ.denseTorusι hΨ₀) (𝟙 _)
          (by
            rw [Category.comp_id, Φ.denseTorusι_eq_affineToricChartι hΦ₀ (Φ.bot_mem hΦ₀.some.2),
              affineToricChartι_comp_algebraicRealizationStructureMap])
          (by
            rw [Category.comp_id, Ψ.denseTorusι_eq_affineToricChartι hΨ₀ (Ψ.bot_mem hΨ₀.some.2),
              affineToricChartι_comp_algebraicRealizationStructureMap]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, algebraicProdComparison_fst, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc, FanHom.denseTorusι_comp_algebraicMap]
    simp [Φ.denseTorusι_eq hΦ₀]
  · simp only [Category.assoc, algebraicProdComparison_snd, pullback.lift_snd,
      IsPullback.isoPullback_hom_snd_assoc, FanHom.denseTorusι_comp_algebraicMap]
    simp [Ψ.denseTorusι_eq hΨ₀]

/-! ### The torus action -/

/-- The domain of the torus action on a product fan scheme is the fibre product over `Spec ℂ` of
the domains of the torus actions on the factors, through the maps of action domains induced by
the two fan projections. -/
theorem isPullback_algebraicActionMap_fst_snd :
    IsPullback (FanHom.fst Φ Ψ).algebraicActionMap (FanHom.snd Φ Ψ).algebraicActionMap
      (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ
            (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
          Φ.algebraicRealizationStructureMap ≫ Φ.algebraicRealizationStructureMap)
      (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ
            (affineCoordinateRing Ψ.lattice (⊥ : PointedCone ℝ V')))))
          Ψ.algebraicRealizationStructureMap ≫ Ψ.algebraicRealizationStructureMap) := by
  have h := IsPullback.pullback_map_pullback_map
    (t := Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (affineCoordinateRing (Φ.prod Ψ).lattice (⊥ : PointedCone ℝ (V × V'))))))
    (x := (Φ.prod Ψ).algebraicRealizationStructureMap)
    (isPullback_affineToricSchemeMap_fst_snd_bot Φ.lattice Ψ.lattice)
    (Φ.isPullback_fst_snd_algebraicMap Ψ)
    (affineToricSchemeMap_comp_specMap_algebraMap _ _ _ _ _ _)
    (affineToricSchemeMap_comp_specMap_algebraMap _ _ _ _ _ _)
    (FanHom.algebraicMap_comp_algebraicRealizationStructureMap _)
    (FanHom.algebraicMap_comp_algebraicRealizationStructureMap _)
  convert h using 1 <;> apply pullback.hom_ext <;> simp

/-- The torus action on a product fan scheme is the product of the torus actions on the factors:
under the identifications of its domain and of its target with fibre products over `Spec ℂ`, it
is the fibre product of the actions of the two factor tori on the two factor schemes. -/
@[reassoc]
theorem algebraicRealizationAction_prod_comp_algebraicProdComparison :
    (Φ.prod Ψ).algebraicRealizationAction ≫ Φ.algebraicProdComparison Ψ =
      (Φ.isPullback_algebraicActionMap_fst_snd Ψ).isoPullback.hom ≫
        pullback.map _ _ _ _ Φ.algebraicRealizationAction Ψ.algebraicRealizationAction (𝟙 _)
          (by
            rw [Category.comp_id,
              algebraicRealizationAction_comp_algebraicRealizationStructureMap])
          (by
            rw [Category.comp_id,
              algebraicRealizationAction_comp_algebraicRealizationStructureMap]) := by
  apply pullback.hom_ext
  · simp [FanHom.algebraicActionMap_comp_algebraicRealizationAction]
  · simp [FanHom.algebraicActionMap_comp_algebraicRealizationAction]

end TauCeti.Toric.Fan
