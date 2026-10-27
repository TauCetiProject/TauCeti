/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Finite locally free sheaves as quasicoherent sheaves

Finite locally free sheaves on a scheme embed fully faithfully into the symmetric monoidal
category of quasicoherent sheaves by a symmetric monoidal functor, compatibly with pullback.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.toQuasicoherent`: the fully faithful
  symmetric monoidal inclusion;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pullbackToQuasicoherentIso`: the inclusion
  commutes with pullback;
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

namespace FiniteLocallyFreeSheaf

/-- The fully faithful symmetric monoidal inclusion of finite locally free sheaves into
quasicoherent sheaves. -/
abbrev toQuasicoherent : FiniteLocallyFreeSheaf X ⥤ QuasicoherentSheaf X :=
  ObjectProperty.ιOfLE fun E hE ↦
    let F : _root_.SheafOfModules X.ringCatSheaf := E
    have : F.IsLocallyFree := hE.1
    inferInstanceAs F.IsQuasicoherent

instance : (toQuasicoherent X).Full :=
  ObjectProperty.full_ιOfLE _

instance : (toQuasicoherent X).Faithful :=
  ObjectProperty.faithful_ιOfLE _

@[simp]
theorem toQuasicoherent_obj_obj (E : FiniteLocallyFreeSheaf X) :
    ((toQuasicoherent X).obj E).obj = E.obj :=
  rfl

@[simp]
theorem toQuasicoherent_map_hom {E F : FiniteLocallyFreeSheaf X} (f : E ⟶ F) :
    ((toQuasicoherent X).map f).hom = f.hom :=
  rfl

variable {X} in
/-- Pulling back a finite locally free sheaf and viewing it as a quasicoherent sheaf is pulling
back the underlying quasicoherent sheaf. -/
def pullbackToQuasicoherentIso {Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback f ⋙ toQuasicoherent X ≅ toQuasicoherent Y ⋙ QuasicoherentSheaf.pullback f :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _ (eqToIso ((pullback_obj_obj f E).trans
      (QuasicoherentSheaf.pullback_obj_obj f ((toQuasicoherent Y).obj E)).symm)))
    fun {E F} g ↦ by
      ext1
      simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, toQuasicoherent_map_hom,
        pullback_map_hom, QuasicoherentSheaf.pullback_map_hom, ObjectProperty.isoMk_hom,
        ObjectProperty.homMk_hom]
      -- Both sides are `(Scheme.Modules.pullback f).map g.hom` between transports along
      -- equalities of the same objects. The composites mix the instances of `SheafOfModules _`
      -- and `_.Modules`, which `simp` does not identify, so the transports are cancelled
      -- generically.
      have key : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ : X.Modules} (p₁ : A₁ = A₂) (p₂ : B₁ = B₂) (p₃ : B₂ = B₃)
          (p₄ : A₁ = A₃) (p₅ : A₃ = A₂) (p₆ : B₁ = B₃) (M : A₂ ⟶ B₁),
          (eqToHom p₁ ≫ M ≫ eqToHom p₂) ≫ eqToHom p₃ =
            eqToHom p₄ ≫ eqToHom p₅ ≫ M ≫ eqToHom p₆ := by
        intros
        subst_vars
        simp
      exact key _ _ ((pullback_obj_obj f F).trans
        (QuasicoherentSheaf.pullback_obj_obj f ((toQuasicoherent Y).obj F)).symm)
        ((pullback_obj_obj f E).trans
          (QuasicoherentSheaf.pullback_obj_obj f ((toQuasicoherent Y).obj E)).symm) _ _ _

variable {X} in
/-- The components of `pullbackToQuasicoherentIso` are identities of underlying sheaves, up to
the identifications of both pullbacks with the pullback of modules. -/
@[simp]
theorem pullbackToQuasicoherentIso_hom_app_hom {Y : Scheme.{u}} (f : X ⟶ Y)
    (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackToQuasicoherentIso f).hom.app E).hom =
      eqToHom ((pullback_obj_obj f E).trans
        (QuasicoherentSheaf.pullback_obj_obj f ((toQuasicoherent Y).obj E)).symm) :=
  (rfl)

variable {X} in
/-- The inverse components of `pullbackToQuasicoherentIso` are identities of underlying
sheaves, up to the identifications of both pullbacks with the pullback of modules. -/
@[simp]
theorem pullbackToQuasicoherentIso_inv_app_hom {Y : Scheme.{u}} (f : X ⟶ Y)
    (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackToQuasicoherentIso f).inv.app E).hom =
      eqToHom ((QuasicoherentSheaf.pullback_obj_obj f ((toQuasicoherent Y).obj E)).trans
        (pullback_obj_obj f E).symm) :=
  (rfl)

end FiniteLocallyFreeSheaf

end


end AlgebraicGeometry

end TauCeti
