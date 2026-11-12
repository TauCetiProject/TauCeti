/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.SymmetricPower.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Functoriality
-- Proof-only: identify the full-subcategory lifts with their underlying module functors.
import all TauCeti.AlgebraicGeometry.VectorBundle.SymmetricPower.Basic
import all TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Pullback of symmetric powers of vector bundles

For any scheme morphism `f : X ⟶ Y`, the canonical comparison
`f^* (Symⁿ E) ⟶ Symⁿ (f^* E)` is an isomorphism of finite locally free sheaves,
natural in `E`. Its underlying map is `Scheme.Modules.pullbackSymmetricPowerComparison`,
which is invertible on quasicoherent sheaves. No choice of a local basis is involved, and no
flatness or constant-rank hypothesis is needed.

`pullbackSymmetricPowerIso_hom_app_id` and `pullbackSymmetricPowerIso_hom_app_comp` express
compatibility with the identity and composition isomorphisms of vector-bundle pullback. These
allow symmetric powers to be used together with successive changes of base.

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

/-- Pullback commutes naturally with the `n`-th symmetric power of finite locally free sheaves.
The forward map is the canonical symmetric-power comparison of module sheaves. -/
def pullbackSymmetricPowerIso (f : X ⟶ Y) (n : ℕ) :
    symmetricPower Y n ⋙ pullback f ≅ pullback f ⋙ symmetricPower X n :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      (asIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app E.obj) :))
    -- On underlying modules both functors are the corresponding full-subcategory lifts.
    fun φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.pullbackSymmetricPowerComparison f n).naturality φ.hom)

/-- The forward comparison on underlying modules is the canonical symmetric-power comparison,
through the object identifications of pullback and symmetric power. -/
@[simp]
theorem pullbackSymmetricPowerIso_hom_app_hom (f : X ⟶ Y) (n : ℕ)
    (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackSymmetricPowerIso f n).hom.app E).hom =
      eqToHom (by simp only [Functor.comp_obj, pullback_obj_obj, symmetricPower_obj_obj]; rfl) ≫
        (Scheme.Modules.pullbackSymmetricPowerComparison f n).app E.obj ≫
        eqToHom (by
          simp only [Functor.comp_obj, symmetricPower_obj_obj, pullback_obj_obj]; rfl) :=
  -- The transports are identities because both functors are full-subcategory lifts.
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The inverse comparison on underlying modules is the inverse of the canonical
symmetric-power comparison. -/
@[simp]
theorem pullbackSymmetricPowerIso_inv_app_hom (f : X ⟶ Y) (n : ℕ)
    (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackSymmetricPowerIso f n).inv.app E).hom =
      eqToHom (by
          simp only [Functor.comp_obj, symmetricPower_obj_obj, pullback_obj_obj]; rfl) ≫
        inv ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app E.obj) ≫
        eqToHom (by
          simp only [Functor.comp_obj, pullback_obj_obj, symmetricPower_obj_obj]; rfl) :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The symmetric-power pullback comparison along the identity agrees with the canonical
identity comparisons of vector-bundle pullback. -/
@[reassoc]
theorem pullbackSymmetricPowerIso_hom_app_id (n : ℕ) (E : FiniteLocallyFreeSheaf X) :
    (pullbackSymmetricPowerIso (𝟙 X) n).hom.app E ≫
        (symmetricPower X n).map ((pullbackId X).hom.app E) =
      (pullbackId X).hom.app ((symmetricPower X n).obj E) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackSymmetricPowerIso_hom_app_hom,
    symmetricPower_map_hom, pullbackId_app_hom_hom]
  -- The remaining object transports are identities, by the defining full-subcategory lifts.
  exact pullbackSymmetricPowerComparison_id n E.obj

/-- The symmetric-power comparison along `f ≫ g` is the composite of the comparisons along
`g` and `f`, through the canonical composition isomorphisms of vector-bundle pullback. -/
@[reassoc]
theorem pullbackSymmetricPowerIso_hom_app_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (E : FiniteLocallyFreeSheaf Z) :
    (pullbackSymmetricPowerIso (f ≫ g) n).hom.app E ≫
        (symmetricPower X n).map ((pullbackComp f g).inv.app E) =
      (pullbackComp f g).inv.app ((symmetricPower Z n).obj E) ≫
        (pullback f).map ((pullbackSymmetricPowerIso g n).hom.app E) ≫
        (pullbackSymmetricPowerIso f n).hom.app ((pullback g).obj E) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackSymmetricPowerIso_hom_app_hom,
    symmetricPower_map_hom, pullbackComp_inv_app_hom, pullback_map_hom]
  -- The full-subcategory transports are identities, leaving the ambient coherence equation.
  exact pullbackSymmetricPowerComparison_comp f g n E.obj

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
