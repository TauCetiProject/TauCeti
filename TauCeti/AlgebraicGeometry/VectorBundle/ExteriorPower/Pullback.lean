/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Functoriality
-- Proof-only: identify the full-subcategory lifts with their underlying module functors.
import all TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
import all TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Pullback of exterior powers of vector bundles

For any scheme morphism `f : X ⟶ Y`, the canonical comparison
`f^* (⋀ⁿ E) ⟶ ⋀ⁿ (f^* E)` is an isomorphism of finite locally free sheaves,
natural in `E`. Its underlying map is `Scheme.Modules.pullbackExteriorPowerComparison`,
which is invertible on quasicoherent sheaves. No choice of a local basis is involved, and no
flatness or constant-rank hypothesis is needed.

`pullbackExteriorPowerIso_hom_app_id` and `pullbackExteriorPowerIso_hom_app_comp` express
compatibility with the identity and composition isomorphisms of vector-bundle pullback. These
allow exterior powers to be used together with successive changes of base.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

/-- Pullback commutes naturally with the `n`-th exterior power of finite locally free sheaves.
The forward map is the canonical exterior-power comparison of module sheaves. -/
def pullbackExteriorPowerIso (f : X ⟶ Y) (n : ℕ) :
    exteriorPower Y n ⋙ pullback f ≅ pullback f ⋙ exteriorPower X n :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      (asIso ((Scheme.Modules.pullbackExteriorPowerComparison f n).app E.obj) :))
    -- On underlying modules both functors are the corresponding full-subcategory lifts.
    fun φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.pullbackExteriorPowerComparison f n).naturality φ.hom)

/-- The forward comparison on underlying modules is the canonical exterior-power comparison,
through the object identifications of pullback and exterior power. -/
@[simp]
theorem pullbackExteriorPowerIso_hom_app_hom (f : X ⟶ Y) (n : ℕ)
    (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackExteriorPowerIso f n).hom.app E).hom =
      eqToHom (by simp only [Functor.comp_obj, pullback_obj_obj, exteriorPower_obj_obj]; rfl) ≫
        (Scheme.Modules.pullbackExteriorPowerComparison f n).app E.obj ≫
        eqToHom (by
          simp only [Functor.comp_obj, exteriorPower_obj_obj, pullback_obj_obj]; rfl) :=
  -- The transports are identities because both functors are full-subcategory lifts.
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The inverse comparison on underlying modules is the inverse of the canonical
exterior-power comparison. -/
@[simp]
theorem pullbackExteriorPowerIso_inv_app_hom (f : X ⟶ Y) (n : ℕ)
    (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackExteriorPowerIso f n).inv.app E).hom =
      eqToHom (by
          simp only [Functor.comp_obj, exteriorPower_obj_obj, pullback_obj_obj]; rfl) ≫
        inv ((Scheme.Modules.pullbackExteriorPowerComparison f n).app E.obj) ≫
        eqToHom (by
          simp only [Functor.comp_obj, pullback_obj_obj, exteriorPower_obj_obj]; rfl) :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The exterior-power pullback comparison along the identity agrees with the canonical
identity comparisons of vector-bundle pullback. -/
@[reassoc]
theorem pullbackExteriorPowerIso_hom_app_id (n : ℕ) (E : FiniteLocallyFreeSheaf X) :
    (pullbackExteriorPowerIso (𝟙 X) n).hom.app E ≫
        (exteriorPower X n).map ((pullbackId X).hom.app E) =
      (pullbackId X).hom.app ((exteriorPower X n).obj E) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackExteriorPowerIso_hom_app_hom,
    exteriorPower_map_hom, pullbackId_app_hom_hom]
  -- The remaining object transports are identities, by the defining full-subcategory lifts.
  exact pullbackExteriorPowerComparison_id n E.obj

/-- The exterior-power comparison along `f ≫ g` is the composite of the comparisons along
`g` and `f`, through the canonical composition isomorphisms of vector-bundle pullback. -/
@[reassoc]
theorem pullbackExteriorPowerIso_hom_app_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (E : FiniteLocallyFreeSheaf Z) :
    (pullbackExteriorPowerIso (f ≫ g) n).hom.app E ≫
        (exteriorPower X n).map ((pullbackComp f g).inv.app E) =
      (pullbackComp f g).inv.app ((exteriorPower Z n).obj E) ≫
        (pullback f).map ((pullbackExteriorPowerIso g n).hom.app E) ≫
        (pullbackExteriorPowerIso f n).hom.app ((pullback g).obj E) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackExteriorPowerIso_hom_app_hom,
    exteriorPower_map_hom, pullbackComp_inv_app_hom, pullback_map_hom]
  -- The full-subcategory transports are identities, leaving the ambient coherence equation.
  exact pullbackExteriorPowerComparison_comp f g n E.obj

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
