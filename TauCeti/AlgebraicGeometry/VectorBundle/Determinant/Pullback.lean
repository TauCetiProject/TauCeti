/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.Determinant.Basic

/-!
# Pullback of the determinant of a vector bundle

Let `f : X ⟶ Y` be a morphism of schemes and `E` a finite locally free sheaf of constant rank `r`
on `Y`. Since `E` is quasicoherent, the canonical exterior-power comparison
`f^* (⋀ʳ E) ⟶ ⋀ʳ (f^* E)` is an isomorphism
(`TauCeti.AlgebraicGeometry.isIso_pullbackExteriorPowerComparison_app`). It therefore gives an
isomorphism of invertible sheaves `f^* (det E) ≅ det (f^* E)`, natural in `E`.

These comparisons are coherent: along the identity the comparison is induced by the identity
isomorphism of pullback, and along a composite `f ≫ g` it is the composite of the comparisons
along `g` and `f`, through the composition isomorphisms of pullback of invertible sheaves and of
fixed-rank sheaves.

## Main declarations

* `FiniteLocallyFreeSheaf.pullbackDeterminantIso f r`: the natural isomorphism
  `f^* (det E) ≅ det (f^* E)` of invertible sheaves, for `E` of constant rank `r`;
* `FiniteLocallyFreeSheaf.pullbackDeterminantIso_hom_app_id`: compatibility with the identity
  isomorphisms of pullback;
* `FiniteLocallyFreeSheaf.pullbackDeterminantIso_hom_app_comp`: compatibility with the
  composition isomorphisms of pullback.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

variable {X Y Z : Scheme.{u}}

/-- Pulling back the determinant of a finite locally free sheaf of constant rank `r` is naturally
isomorphic to taking the determinant of its pullback: `f^* (det E) ≅ det (f^* E)`. The forward map
is the canonical exterior-power comparison `f^* (⋀ʳ E) ⟶ ⋀ʳ (f^* E)`, which is invertible because
`E` is quasicoherent. -/
def pullbackDeterminantIso (f : X ⟶ Y) (r : ℕ) :
    determinant Y r ⋙ InvertibleSheaf.pullback f ≅ FixedRank.pullback f ⋙ determinant X r :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      (asIso ((Scheme.Modules.pullbackExteriorPowerComparison f r).app E.obj.obj) :))
    -- Both functors act on underlying sheaves by pullback and the `r`-th exterior power, so this is
    -- the naturality of the exterior-power comparison.
    fun φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.pullbackExteriorPowerComparison f r).naturality φ.hom.hom)

/-- On underlying sheaves, the forward map of `pullbackDeterminantIso` is the canonical
exterior-power comparison `f^* (⋀ʳ E) ⟶ ⋀ʳ (f^* E)`. -/
@[simp]
theorem pullbackDeterminantIso_hom_app_hom (f : X ⟶ Y) {r : ℕ} (E : FixedRank Y r) :
    ((pullbackDeterminantIso f r).hom.app E).hom =
      (Scheme.Modules.pullbackExteriorPowerComparison f r).app E.obj.obj :=
  (rfl)

/-- On underlying sheaves, the inverse map of `pullbackDeterminantIso` is the inverse of the
canonical exterior-power comparison `f^* (⋀ʳ E) ⟶ ⋀ʳ (f^* E)`. -/
@[simp]
theorem pullbackDeterminantIso_inv_app_hom (f : X ⟶ Y) {r : ℕ} (E : FixedRank Y r) :
    ((pullbackDeterminantIso f r).inv.app E).hom =
      inv ((Scheme.Modules.pullbackExteriorPowerComparison f r).app E.obj.obj) :=
  (rfl)

/-- The determinant pullback comparison along the identity is induced by the identity
isomorphisms of pullback of fixed-rank sheaves and of invertible sheaves. -/
@[reassoc]
theorem pullbackDeterminantIso_hom_app_id {r : ℕ} (E : FixedRank X r) :
    (pullbackDeterminantIso (𝟙 X) r).hom.app E ≫
        (determinant X r).map ((FixedRank.pullbackId X r).hom.app E) =
      (InvertibleSheaf.pullbackId X).hom.app ((determinant X r).obj E) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackDeterminantIso_hom_app_hom,
    determinant_map_hom, FixedRank.pullbackId_hom_app_hom, InvertibleSheaf.pullbackId_hom_app_hom,
    FiniteLocallyFreeSheaf.pullbackId_app_hom_hom]
  -- On underlying sheaves this is `pullbackExteriorPowerComparison_id`: the remaining `eqToHom`s
  -- transport along the defining equalities of the exposed lifts `determinant`,
  -- `FixedRank.pullback` and `InvertibleSheaf.pullback`, so they are identities.
  exact pullbackExteriorPowerComparison_id r E.obj.obj

/-- The determinant pullback comparison along a composite `f ≫ g` is the composite of the
comparisons along `g` and along `f`, through the composition isomorphisms of pullback of
fixed-rank sheaves and of invertible sheaves. -/
@[reassoc]
theorem pullbackDeterminantIso_hom_app_comp (f : X ⟶ Y) (g : Y ⟶ Z) {r : ℕ}
    (E : FixedRank Z r) :
    (pullbackDeterminantIso (f ≫ g) r).hom.app E ≫
        (determinant X r).map ((FixedRank.pullbackComp f g).inv.app E) =
      (InvertibleSheaf.pullbackComp f g).inv.app ((determinant Z r).obj E) ≫
        (InvertibleSheaf.pullback f).map ((pullbackDeterminantIso g r).hom.app E) ≫
        (pullbackDeterminantIso f r).hom.app ((FixedRank.pullback g).obj E) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackDeterminantIso_hom_app_hom,
    determinant_map_hom, FixedRank.pullbackComp_inv_app_hom,
    InvertibleSheaf.pullbackComp_inv_app_hom, FiniteLocallyFreeSheaf.pullbackComp_inv_app_hom,
    InvertibleSheaf.pullback_map]
  -- As in `pullbackDeterminantIso_hom_app_id`, the remaining `eqToHom`s are identities, and this is
  -- `pullbackExteriorPowerComparison_comp` on underlying sheaves.
  exact pullbackExteriorPowerComparison_comp f g r E.obj.obj

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
