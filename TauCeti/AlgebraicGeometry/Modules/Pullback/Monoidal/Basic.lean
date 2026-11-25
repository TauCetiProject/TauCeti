/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Pullback of quasicoherent sheaves preserves duals

Pullback from quasicoherent sheaves to all modules on the source of an arbitrary scheme
morphism is strong symmetric monoidal. Its inverse tensor comparison is the canonical oplax
tensorator of module pullback, and its inverse unit comparison is the structure-sheaf
identification. The existing identity and composition formulas for these canonical comparisons
therefore still apply. The canonical `QuasicoherentSheaf.pullback` functor inherits this strong
symmetric monoidal structure, with characteristic equations for all four comparisons on
underlying modules. No flatness or finiteness assumptions are needed.

In particular, arbitrary pullback preserves both left and right dualizability inside the
quasicoherent subcategories. This lets dualizability be transported to affine charts, where
it is equivalent to finite projectivity of the module of global sections.

The monoidal structure on pullback to modules is the composite of the strong symmetric
monoidal full-subcategory inclusion and module pullback. The structure on quasicoherent
pullback is lifted from this composite and transported along the canonical underlying-object
identifications. Dual preservation then follows from `Functor.mapHasLeftDual` and
`Functor.mapHasRightDual`.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
-/

public section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open _root_.AlgebraicGeometry.Scheme.Modules

/-- Pullback from quasicoherent sheaves to modules is the composite of the strong symmetric
monoidal inclusion and module pullback. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModulesBraided :
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f).Braided := by
  -- Synthesize with abstract carriers before specializing to the scheme-module aliases.
  let braidedComp {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
      [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
      (P : ObjectProperty C) [P.IsMonoidal] (G : C ⥤ D) [G.Braided] :
      (P.ι ⋙ G).Braided := inferInstance
  exact braidedComp (C := Y.Modules) (D := X.Modules) _ (pullback f)

/-- The inverse tensor comparison is the canonical module-pullback tensor comparison. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModules_δ
    (E F : QuasicoherentSheaf Y) :
    δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f) E F =
      δ (pullback f) E.obj F.obj := by
  -- The full-subcategory inclusion contributes an identity tensor comparison.
  exact (congrArg (· ≫ δ (pullback f) E.obj F.obj)
    ((pullback f).map_id (E.obj ⊗ F.obj))).trans (Category.id_comp _)

/-- The inverse unit comparison is the canonical structure-sheaf identification. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModules_η :
    η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f) =
      (pullbackObjUnitIso f).hom := by
  -- The full-subcategory inclusion contributes an identity unit comparison.
  exact (congrArg (· ≫ η (pullback f))
    ((pullback f).map_id (𝟙_ Y.Modules))).trans
      ((Category.id_comp _).trans (pullback_η f))

/-- The tensor comparison on quasicoherent inputs is the module-pullback comparison. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModules_μ
    (E F : QuasicoherentSheaf Y) :
    μ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f) E F =
      μ (pullback f) E.obj F.obj := by
  simp only [← Functor.Monoidal.inv_δ
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f),
    pullbackToModules_δ]
  exact Functor.Monoidal.inv_δ (pullback f) E.obj F.obj

/-- The unit comparison is the inverse structure-sheaf identification. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModules_ε :
    ε ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f) =
      (pullbackObjUnitIso f).inv := by
  simp only [← Functor.Monoidal.inv_η
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f),
    pullbackToModules_η, IsIso.Iso.inv_hom]

namespace QuasicoherentSheaf

/-- Pullback of quasicoherent sheaves is strong symmetric monoidal for every scheme morphism. -/
instance pullbackBraided : (pullback f).Braided := by
  -- Lift the module comparisons first, then transport them using the public pullback equations.
  let F : QuasicoherentSheaf Y ⥤ X.Modules :=
    (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f
  letI : F.Braided := Scheme.Modules.pullbackToModulesBraided f
  let H : QuasicoherentSheaf Y ⥤ QuasicoherentSheaf X :=
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
      F (fun E ↦ Scheme.Modules.isQuasicoherent_pullback f E.obj)
  letI : H.Braided := ObjectProperty.braidedLift _ F _
  -- Identify the explicit lift with the opaque canonical functor through its public API.
  let i : H ≅ pullback f :=
    NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk _
      (eqToIso (C := X.Modules) (pullback_obj_obj f E).symm)) (by
        intro E F φ
        apply ObjectProperty.hom_ext
        -- Reduce full-subcategory composition, keeping canonical pullback maps opaque.
        change (Scheme.Modules.pullback f).map φ.hom ≫
            eqToHom (C := X.Modules) (pullback_obj_obj f F).symm =
          eqToHom (C := X.Modules) (pullback_obj_obj f E).symm ≫ ((pullback f).map φ).hom
        rw [pullback_map_hom]
        -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
        exact ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (Scheme.Modules.pullback f).map φ.hom ≫
            eqToHom (C := X.Modules) (pullback_obj_obj f F).symm)
            (eqToIso (C := X.Modules) (pullback_obj_obj f E)).inv_hom_id).trans
              (Category.id_comp _))).symm)
  -- Mathlib transports both the monoidal structure and its compatibility with braiding.
  letI : (pullback f).Monoidal := Functor.Monoidal.transport i
  letI : NatTrans.IsMonoidal i.hom := Functor.Monoidal.natTransIsMonoidal_of_transport i
  exact { toMonoidal := inferInstance
          braided := (Functor.LaxBraided.ofNatIso i).braided }

/-- The inverse tensor comparison of quasicoherent pullback is the module comparison,
transported along the underlying-object identifications. -/
@[simp]
theorem pullback_δ_hom (E F : QuasicoherentSheaf Y) :
    (δ (pullback f) E F).hom =
      eqToHom (C := X.Modules) (pullback_obj_obj f (E ⊗ F)) ≫
        δ (Scheme.Modules.pullback f) E.obj F.obj ≫
          (eqToHom (C := X.Modules) (pullback_obj_obj f E).symm ⊗ₘ
            eqToHom (C := X.Modules) (pullback_obj_obj f F).symm) := by
  -- Compute only the transported comparison; the canonical pullback remains opaque.
  change (eqToHom (C := X.Modules) (pullback_obj_obj f (E ⊗ F)) ≫
    δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
      Scheme.Modules.pullback f) E F) ≫ _ = _
  erw [Category.assoc]
  exact congrArg (fun t ↦ eqToHom (C := X.Modules) (pullback_obj_obj f (E ⊗ F)) ≫ t ≫
    (eqToHom (C := X.Modules) (pullback_obj_obj f E).symm ⊗ₘ
      eqToHom (C := X.Modules) (pullback_obj_obj f F).symm))
    (Scheme.Modules.pullbackToModules_δ f E F)

/-- The inverse unit comparison of quasicoherent pullback is the structure-sheaf comparison. -/
@[simp]
theorem pullback_η_hom :
    (η (pullback f)).hom =
      eqToHom (C := X.Modules) (pullback_obj_obj f (𝟙_ (QuasicoherentSheaf Y))) ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom := by
  -- Compute the transported unit comparison without unfolding canonical pullback.
  change _ ≫ η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
    Scheme.Modules.pullback f) = _
  exact congrArg (eqToHom (C := X.Modules)
    (pullback_obj_obj f (𝟙_ (QuasicoherentSheaf Y))) ≫ ·)
    (Scheme.Modules.pullbackToModules_η f)

/-- The tensor comparison of quasicoherent pullback inverts the module comparison,
transported along the underlying-object identifications. -/
@[simp]
theorem pullback_μ_hom (E F : QuasicoherentSheaf Y) :
    (μ (pullback f) E F).hom =
      (eqToHom (C := X.Modules) (pullback_obj_obj f E) ⊗ₘ
        eqToHom (C := X.Modules) (pullback_obj_obj f F)) ≫
        inv (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
          Scheme.Modules.pullback f) E F) ≫
            eqToHom (C := X.Modules) (pullback_obj_obj f (E ⊗ F)).symm := by
  let G := (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f
  let : G.Braided := Scheme.Modules.pullbackToModulesBraided f
  -- The lifted tensor comparison has the underlying map of `G`.
  let t := eqToHom (C := X.Modules) (pullback_obj_obj f E) ⊗ₘ
    eqToHom (C := X.Modules) (pullback_obj_obj f F)
  let e := eqToHom (C := X.Modules) (pullback_obj_obj f (E ⊗ F)).symm
  change (t ≫ μ G E F) ≫ e = t ≫ inv (δ G E F) ≫ e
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ t ≫ m ≫ e) (Functor.Monoidal.inv_δ G E F).symm)

/-- The unit comparison of quasicoherent pullback inverts the structure-sheaf comparison. -/
@[simp]
theorem pullback_ε_hom :
    (ε (pullback f)).hom = (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      eqToHom (C := X.Modules) (pullback_obj_obj f (𝟙_ (QuasicoherentSheaf Y))).symm := by
  let G := (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f
  let : G.Braided := Scheme.Modules.pullbackToModulesBraided f
  -- The lifted unit comparison has the underlying map of `G`.
  change ε G ≫ _ = _
  exact congrArg (· ≫ eqToHom (C := X.Modules)
    (pullback_obj_obj f (𝟙_ (QuasicoherentSheaf Y))).symm)
    (Scheme.Modules.pullbackToModules_ε f)

/-- Arbitrary pullback carries a left dual of a quasicoherent sheaf to a left dual of its
pullback. -/
theorem nonempty_hasLeftDual_pullback (E : QuasicoherentSheaf Y) (f : X ⟶ Y)
    (hE : Nonempty (HasLeftDual E)) : Nonempty (HasLeftDual ((pullback f).obj E)) := by
  obtain ⟨hE⟩ := hE
  exact ⟨(pullback f).mapHasLeftDual E⟩

/-- Arbitrary pullback preserves right dualizability of quasicoherent sheaves. -/
theorem nonempty_hasRightDual_pullback (E : QuasicoherentSheaf Y) (f : X ⟶ Y)
    (hE : Nonempty (HasRightDual E)) : Nonempty (HasRightDual ((pullback f).obj E)) := by
  obtain ⟨hE⟩ := hE
  exact ⟨(pullback f).mapHasRightDual E⟩

end QuasicoherentSheaf

end

end TauCeti.AlgebraicGeometry
