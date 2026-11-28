/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Basic properties of locally ringed spaces and their morphisms

A morphism `f : X ⟶ Y` of locally ringed spaces which is surjective on points and whose maps on
sections `Γ(Y, U) ⟶ Γ(X, f⁻¹ U)` are all monomorphisms is an epimorphism
(`AlgebraicGeometry.LocallyRingedSpace.epi_of_base_surjective_of_c_app_mono`), deduced from the
presheafed-space criterion `AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`.
We also record the section-map action of a composite morphism (`comp_c_app_apply`), left/right
cancellation of global-section maps of an isomorphism (`iso_inv_c_app_top_comp_hom`,
`iso_hom_c_app_top_comp_inv`), inverse identification for restricted section maps
(`iso_inv_appLE_eq`), lifting a sheaf isomorphism over a fixed base (`isoOfSheafIso`,
`isoOfSheafIso_hom_c_app`, `isoOfSheafIso_inv_c_app`), and stalk locality inherited from a
factorization (`isLocalHom_stalkMap_of_comp_eq`). Descent along quotient maps is in
`TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Descent`.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- On sections over an open, the section map of a composite morphism of locally ringed spaces is
the composite of the section maps. -/
theorem comp_c_app_apply {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : (Opens Z)ᵒᵖ) (s : Z.presheaf.obj U) :
    (f ≫ g).c.app U s = f.c.app (op ((Opens.map g.base).obj U.unop)) (g.c.app U s) :=
  PresheafedSpace.comp_c_app_apply f.toHom g.toHom U s

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

/-- If `e : X ≅ Y` is an isomorphism of locally ringed spaces with
`e.hom.toHom.appLE U V hUV = f` and `g` is a left inverse to `f`, then
`e.inv.toHom.appLE V U hVU = g`. -/
theorem iso_inv_appLE_eq {X Y : LocallyRingedSpace}
    (e : X ≅ Y) (U : Opens Y) (V : Opens X)
    (hUV : V ≤ (Opens.map e.hom.base).obj U) (hVU : U ≤ (Opens.map e.inv.base).obj V)
    {f : Y.presheaf.obj (op U) ⟶ X.presheaf.obj (op V)}
    {g : X.presheaf.obj (op V) ⟶ Y.presheaf.obj (op U)}
    (hf : e.hom.toHom.appLE U V hUV = f) (hg : g ≫ f = 𝟙 (X.presheaf.obj (op V))) :
    e.inv.toHom.appLE V U hVU = g :=
  PresheafedSpace.Hom.iso_inv_appLE_eq
    ((forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).mapIso e)
    U V hUV hVU hf hg

-- Exposed so `.hom.base` and `.inv.base` reduce definitionally in the dependent types of the
-- `.c.app` lemmas and downstream stalk comparisons.
/-- Promote a sheaf isomorphism `P ≅ Q` over a fixed topological space `T`, together with
local-ring instances on the stalks of `P` and `Q`, to an isomorphism of locally ringed spaces. -/
@[expose]
def isoOfSheafIso {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x))
    (θ : P ≅ Q) :
    (⟨⟨⟨T, P.presheaf⟩, P.property⟩, hP⟩ : LocallyRingedSpace) ≅
      (⟨⟨⟨T, Q.presheaf⟩, Q.property⟩, hQ⟩ : LocallyRingedSpace) :=
  isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
    PresheafedSpace.isoOfComponents (Iso.refl T)
      (eqToIso (TopCat.Presheaf.Pushforward.id_eq P.presheaf) ≪≫
        (sheafToPresheaf _ _).mapIso θ)

/-- The forward direction of `isoOfSheafIso` is the identity on points. -/
@[simp]
theorem isoOfSheafIso_hom_base {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x)) (θ : P ≅ Q) :
    (isoOfSheafIso hP hQ θ).hom.base = 𝟙 T := (rfl)

/-- The inverse direction of `isoOfSheafIso` is the identity on points. -/
@[simp]
theorem isoOfSheafIso_inv_base {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x)) (θ : P ≅ Q) :
    (isoOfSheafIso hP hQ θ).inv.base = 𝟙 T := (rfl)

/-- On sections over `U`, `(isoOfSheafIso hP hQ θ).hom` acts by `θ.inv.hom.app (op U)`. -/
@[simp]
theorem isoOfSheafIso_hom_c_app {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x))
    (θ : P ≅ Q) (U : Opens T) :
    (isoOfSheafIso hP hQ θ).hom.c.app (op U) = θ.inv.hom.app (op U) := by
  have heq : (eqToHom (TopCat.Presheaf.Pushforward.id_eq P.presheaf).symm).app (op U) = 𝟙 _ :=
    (eqToHom_app _ _).trans (eqToHom_refl _ _)
  exact (congrArg (θ.inv.hom.app (op U) ≫ ·) heq).trans (Category.comp_id _)

/-- On sections over `U`, `(isoOfSheafIso hP hQ θ).inv` acts by `θ.hom.hom.app (op U)`. -/
@[simp]
theorem isoOfSheafIso_inv_c_app {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x))
    (θ : P ≅ Q) (U : Opens T) :
    (isoOfSheafIso hP hQ θ).inv.c.app (op U) = θ.hom.hom.app (op U) := by
  let e := isoOfSheafIso hP hQ θ
  have hf : e.hom.toHom.appLE U U le_rfl = θ.inv.hom.app (op U) :=
    (PresheafedSpace.Hom.appLE_eq_app e.hom.toHom U).trans (isoOfSheafIso_hom_c_app hP hQ θ U)
  have hg : θ.hom.hom.app (op U) ≫ θ.inv.hom.app (op U) = 𝟙 _ :=
    congrArg (fun k ↦ k.hom.app (op U)) θ.hom_inv_id
  exact (PresheafedSpace.Hom.appLE_eq_app e.inv.toHom U).symm.trans
    (iso_inv_appLE_eq e U U le_rfl le_rfl hf hg)

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
