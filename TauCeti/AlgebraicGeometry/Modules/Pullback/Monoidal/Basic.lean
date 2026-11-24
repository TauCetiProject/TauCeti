/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
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
  -- Explicit module carriers let typeclass search match Mathlib's composite instance.
  let F : QuasicoherentSheaf Y ⥤ Y.Modules := ObjectProperty.ι _
  let G : Y.Modules ⥤ X.Modules := pullback f
  letI : F.Braided := ObjectProperty.instBraidedFullSubcategoryι (C := Y.Modules) _
  letI : G.Braided := Scheme.Modules.pullbackBraided f
  exact Functor.Braided.instComp F G

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
  let H : QuasicoherentSheaf Y ⥤ QuasicoherentSheaf X :=
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
      ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
      fun E ↦ Scheme.Modules.isQuasicoherent_pullback f E.obj
  -- The explicit lift lets each coherence law reduce to the corresponding module law.
  letI : H.OplaxMonoidal := {
    η := ObjectProperty.homMk
      (η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f))
    δ E F := ObjectProperty.homMk
      (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E F)
    δ_natural_left φ E := by
      apply ObjectProperty.hom_ext
      exact Functor.OplaxMonoidal.δ_natural_left
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) φ E
    δ_natural_right E φ := by
      apply ObjectProperty.hom_ext
      exact Functor.OplaxMonoidal.δ_natural_right
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E φ
    oplax_associativity E F G := by
      apply ObjectProperty.hom_ext
      exact Functor.OplaxMonoidal.associativity
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E F G
    oplax_left_unitality E := by
      apply ObjectProperty.hom_ext
      exact Functor.OplaxMonoidal.left_unitality
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E
    oplax_right_unitality E := by
      apply ObjectProperty.hom_ext
      exact Functor.OplaxMonoidal.right_unitality
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E }
  letI : H.Monoidal := by
    have : IsIso (η H) := by
      apply (ObjectProperty.isIso_hom_iff _).mp
      exact inferInstanceAs (IsIso (η
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)))
    have (E F : QuasicoherentSheaf Y) : IsIso (δ H E F) := by
      apply (ObjectProperty.isIso_hom_iff _).mp
      exact inferInstanceAs (IsIso (δ
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E F))
    exact Functor.Monoidal.ofOplaxMonoidal H
  letI : H.Braided := {
    toMonoidal := inferInstance
    braided E F := by
      apply ObjectProperty.hom_ext
      -- Express full-subcategory composition on underlying modules before rewriting inverses.
      change (μ H E F).hom ≫ _ = _ ≫ (μ H F E).hom
      have hμ (E F : QuasicoherentSheaf Y) : (μ H E F).hom =
          μ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
            Scheme.Modules.pullback f) E F := by
        rw [← Functor.Monoidal.inv_δ, ObjectProperty.hom_inv]
        -- The lifted oplax tensor comparison forgets to the module comparison.
        exact Functor.Monoidal.inv_δ
          ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
            Scheme.Modules.pullback f) E F
      rw [hμ, hμ]
      exact @Functor.LaxBraided.braided _ _ _ _ _ _ _ _
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
        inferInstance E F }
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
  let H : QuasicoherentSheaf Y ⥤ QuasicoherentSheaf X :=
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
      ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
      fun E ↦ Scheme.Modules.isQuasicoherent_pullback f E.obj
  let d : H.obj (E ⊗ F) ⟶ H.obj E ⊗ H.obj F := ObjectProperty.homMk
    (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E F)
  have : IsIso d := (ObjectProperty.isIso_hom_iff d).mp
    (inferInstanceAs (IsIso (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
      Scheme.Modules.pullback f) E F)))
  -- Name the lifted map to rewrite its inverse before forgetting the subcategory.
  change ((eqToHom (C := X.Modules) (pullback_obj_obj f E) ⊗ₘ
    eqToHom (C := X.Modules) (pullback_obj_obj f F)) ≫ (inv d).hom) ≫ _ = _
  rw [ObjectProperty.hom_inv]
  exact Category.assoc _ _ _

/-- The unit comparison of quasicoherent pullback inverts the structure-sheaf comparison. -/
@[simp]
theorem pullback_ε_hom :
    (ε (pullback f)).hom = (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      eqToHom (C := X.Modules) (pullback_obj_obj f (𝟙_ (QuasicoherentSheaf Y))).symm := by
  let U : QuasicoherentSheaf X := ⟨(Scheme.Modules.pullback f).obj (𝟙_ Y.Modules),
    Scheme.Modules.isQuasicoherent_pullback f _⟩
  let e : U ⟶ 𝟙_ (QuasicoherentSheaf X) := ObjectProperty.homMk
    (η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f))
  have : IsIso e := (ObjectProperty.isIso_hom_iff e).mp
    (inferInstanceAs (IsIso (η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
      Scheme.Modules.pullback f))))
  -- As for the tensor comparison, forget the named lifted inverse before rewriting it.
  change (inv e).hom ≫ _ = _
  rw [ObjectProperty.hom_inv]
  -- Express the forgotten map in `X.Modules`; rewriting under `inv` mixes category instances.
  change inv (η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
    Scheme.Modules.pullback f)) ≫ _ = _
  congr 1
  apply IsIso.inv_eq_of_hom_inv_id
  rw [Scheme.Modules.pullbackToModules_η]
  exact (Scheme.Modules.pullbackObjUnitIso f).hom_inv_id

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
