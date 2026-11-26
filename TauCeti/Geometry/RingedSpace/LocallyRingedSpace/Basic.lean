/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Basic properties of locally ringed spaces and their morphisms

A morphism `f : X ⟶ Y` of locally ringed spaces which is surjective on points and whose maps on
sections `Γ(Y, U) ⟶ Γ(X, f⁻¹ U)` are all monomorphisms is an epimorphism
(`AlgebraicGeometry.LocallyRingedSpace.epi_of_base_surjective_of_c_app_mono`), deduced from the
presheafed-space criterion `AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`.
We also record left/right cancellation of global-section maps of an isomorphism
(`iso_inv_c_app_top_comp_hom`, `iso_hom_c_app_top_comp_inv`) and stalk locality inherited from a
factorization (`isLocalHom_stalkMap_of_comp_eq`). Descent along quotient maps is in
`TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Descent`.
-/

public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- **A morphism of locally ringed spaces which is surjective on points and a monomorphism on
sections is an epimorphism.** -/
theorem epi_of_base_surjective_of_c_app_mono {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.base) (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  exact PresheafedSpace.epi_of_base_surjective_of_c_app_mono _ h₁ h₂

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the left. -/
@[reassoc (attr := simp)]
theorem iso_inv_c_app_top_comp_hom {Y₁ Y₂ : LocallyRingedSpace.{_}} (e : Y₁ ≅ Y₂) :
    (e.inv.c.app (op ⊤) : Y₁.presheaf.obj (op ⊤) ⟶ Y₂.presheaf.obj (op ⊤)) ≫ e.hom.c.app (op ⊤) =
      𝟙 (Y₁.presheaf.obj (op ⊤)) :=
  (LocallyRingedSpace.Γ.map_comp e.inv.op e.hom.op).symm.trans <| by
    rw [← op_comp, e.hom_inv_id, op_id, LocallyRingedSpace.Γ.map_id]; rfl

/-- Global-section maps of an isomorphism of locally ringed spaces cancel on the right. -/
@[reassoc (attr := simp)]
theorem iso_hom_c_app_top_comp_inv {Y₁ Y₂ : LocallyRingedSpace.{_}} (e : Y₁ ≅ Y₂) :
    (e.hom.c.app (op ⊤) : Y₂.presheaf.obj (op ⊤) ⟶ Y₁.presheaf.obj (op ⊤)) ≫ e.inv.c.app (op ⊤) =
      𝟙 (Y₂.presheaf.obj (op ⊤)) := iso_inv_c_app_top_comp_hom e.symm

/-- If `c : X ⟶ Y` and `g : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace` compose to the underlying
morphism of `f : X ⟶ Z` and `c.base x' = x`, then the stalk map of `g` at `x` is local. -/
theorem isLocalHom_stalkMap_of_comp_eq {X Y Z : LocallyRingedSpace.{_}}
    (c : X ⟶ Y) (g : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace) (f : X ⟶ Z)
    (hcomp : c.toHom ≫ g = f.toHom) {x' : X} {x : Y} (hx : c.base x' = x) :
    IsLocalHom (g.stalkMap x).hom := by
  subst hx
  have hloc : IsLocalHom ((c.toHom ≫ g).stalkMap x').hom := by
    rw [PresheafedSpace.stalkMap.congr_hom _ _ hcomp x', CommRingCat.hom_comp]
    have := isLocalHom_of_isIso (eqToHom (hcomp ▸ rfl :
      Z.presheaf.stalk ((c.toHom ≫ g).base x') = Z.presheaf.stalk (f.base x')))
    have := f.prop x'
    exact CommRingCat.isLocalHom_comp _ _
  rw [PresheafedSpace.stalkMap.comp] at hloc
  -- `rw [CommRingCat.hom_comp] at hloc` fails: `g.stalkMap (c.base x')` has domain at
  -- `(c.toHom ≫ g).base x'`, only definitionally equal to `g.base (c.base x')`.
  have : IsLocalHom ((c.toHom.stalkMap x').hom.comp (g.stalkMap (c.base x')).hom) := hloc
  exact isLocalHom_of_comp _ (c.toHom.stalkMap x').hom

end LocallyRingedSpace

end AlgebraicGeometry
