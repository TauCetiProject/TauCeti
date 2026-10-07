/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
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

The monoidal structure is obtained from the invertibility of the existing oplax comparisons,
using Mathlib's `Functor.Monoidal.ofOplaxMonoidal`. The duals are carried back into the full
quasicoherent subcategory by `ObjectProperty.exactPairingFullSubcategory`.

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

/-- Pulling back a tensor product with a fixed quasicoherent left factor commutes with tensoring
by its pullback, naturally in the other, arbitrary sheaf of modules. -/
def _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorLeftIso
    (M : Y.Modules) [M.IsQuasicoherent] :
    tensorLeft M ⋙ pullback f ≅ pullback f ⋙ tensorLeft ((pullback f).obj M) := by
  have : IsIso ((pullback f).oplaxCommTensorLeft M) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [Functor.oplaxCommTensorLeft_app]
    infer_instance
  exact asIso ((pullback f).oplaxCommTensorLeft M)

/-- The left tensor comparison is the canonical oplax tensor map of pullback. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorLeftIso_hom_app
    (M N : Y.Modules) [M.IsQuasicoherent] :
    (pullbackTensorLeftIso f M).hom.app N = δ (pullback f) M N :=
  Functor.oplaxCommTensorLeft_app _ _ _

/-- Pulling back a tensor product with a fixed quasicoherent right factor commutes with tensoring
by its pullback, naturally in the other, arbitrary sheaf of modules. -/
def _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorRightIso
    (N : Y.Modules) [N.IsQuasicoherent] :
    tensorRight N ⋙ pullback f ≅ pullback f ⋙ tensorRight ((pullback f).obj N) := by
  have : IsIso ((pullback f).oplaxCommTensorRight N) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [Functor.oplaxCommTensorRight_app]
    infer_instance
  exact asIso ((pullback f).oplaxCommTensorRight N)

/-- The right tensor comparison is the canonical oplax tensor map of pullback. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorRightIso_hom_app
    (M N : Y.Modules) [N.IsQuasicoherent] :
    (pullbackTensorRightIso f N).hom.app M = δ (pullback f) M N :=
  Functor.oplaxCommTensorRight_app _ _ _

/-- Pullback from quasicoherent sheaves to all modules on the source is strong monoidal,
with inverse comparisons inherited from module pullback. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModulesMonoidal :
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f).Monoidal := by
  let I : QuasicoherentSheaf Y ⥤ Y.Modules := ObjectProperty.ι _
  have : I.Monoidal := @ObjectProperty.monoidalι Y.Modules _ _ _
    (Scheme.Modules.isMonoidal_isQuasicoherent Y)
  have : IsIso (η (I ⋙ pullback f)) := by
    rw [Functor.OplaxMonoidal.comp_η]
    infer_instance
  have (E F : QuasicoherentSheaf Y) : IsIso (δ (I ⋙ pullback f) E F) := by
    rw [Functor.OplaxMonoidal.comp_δ]
    have : E.obj.IsQuasicoherent := E.property
    have : IsIso (δ (pullback f) (I.obj E) (I.obj F)) :=
      isIso_pullback_δ_of_isQuasicoherent f E.obj F.obj
    infer_instance
  exact Functor.Monoidal.ofOplaxMonoidal (I ⋙ pullback f)

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

/-- Pullback of quasicoherent sheaves, viewed in all modules, respects symmetry. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.pullbackToModulesBraided :
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f).Braided where
  toMonoidal := pullbackToModulesMonoidal f
  braided E F := by
    let H := (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f
    rw [← cancel_epi (δ H E F)]
    erw [Functor.Monoidal.δ_μ_assoc]
    rw [pullbackToModules_δ]
    -- The full-subcategory braiding is the ambient braiding on underlying objects.
    have hb : H.map (β_ E F).hom =
        (pullback f).map (@BraidedCategory.braiding Y.Modules _ _ _ E.obj F.obj).hom := rfl
    rw [hb]
    erw [← pullback_map_braiding_hom_comp_δ_assoc, ← pullbackToModules_δ]
    exact ((congrArg ((pullback f).map
      (@BraidedCategory.braiding Y.Modules _ _ _ E.obj F.obj).hom ≫ ·)
      (Functor.Monoidal.δ_μ H F E)).trans (Category.comp_id _)).symm

namespace QuasicoherentSheaf

/-- The canonical quasicoherent pullback inherits the oplax comparisons of module pullback. -/
instance pullbackOplaxMonoidal : (pullback f).OplaxMonoidal where
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
      ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E

/-- Pullback of quasicoherent sheaves is strong monoidal for every morphism of schemes. -/
instance pullbackMonoidal : (pullback f).Monoidal := by
  have : IsIso (η (pullback f)) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    exact inferInstanceAs (IsIso (η
      ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)))
  have (E F : QuasicoherentSheaf Y) : IsIso (δ (pullback f) E F) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    exact inferInstanceAs (IsIso (δ
      ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f) E F))
  exact Functor.Monoidal.ofOplaxMonoidal (pullback f)

/-- The inverse tensor comparison of quasicoherent pullback is the module comparison. -/
@[simp]
theorem pullback_δ_hom (E F : QuasicoherentSheaf Y) :
    (δ (pullback f) E F).hom = δ (Scheme.Modules.pullback f) E.obj F.obj :=
  Scheme.Modules.pullbackToModules_δ f E F

/-- The inverse unit comparison of quasicoherent pullback is the structure-sheaf comparison. -/
@[simp]
theorem pullback_η_hom :
    (η (pullback f)).hom = (Scheme.Modules.pullbackObjUnitIso f).hom :=
  Scheme.Modules.pullbackToModules_η f

/-- The tensor comparison of quasicoherent pullback inverts the module comparison. -/
@[simp]
theorem pullback_μ_hom (E F : QuasicoherentSheaf Y) :
    (μ (pullback f) E F).hom =
      inv (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f) E F) := by
  rw [← Functor.Monoidal.inv_δ, ObjectProperty.hom_inv]
  rfl

/-- The unit comparison of quasicoherent pullback inverts the structure-sheaf comparison. -/
@[simp]
theorem pullback_ε_hom :
    (ε (pullback f)).hom = (Scheme.Modules.pullbackObjUnitIso f).inv := by
  rw [← Functor.Monoidal.inv_η, ObjectProperty.hom_inv]
  -- Express the lifted comparison in `X.Modules`: rewriting under `inv` otherwise mixes
  -- the full-subcategory and ambient category instances at reducible transparency.
  change inv (η ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
    Scheme.Modules.pullback f)) = _
  apply IsIso.inv_eq_of_hom_inv_id
  rw [Scheme.Modules.pullbackToModules_η]
  exact (Scheme.Modules.pullbackObjUnitIso f).hom_inv_id

/-- The canonical quasicoherent pullback respects the symmetry of tensor products. -/
instance pullbackBraided : (pullback f).Braided where
  toMonoidal := pullbackMonoidal f
  braided E F := by
    apply ObjectProperty.hom_ext
    -- Forget the full-subcategory composite so the comparison lemmas can rewrite its factors.
    change (μ (pullback f) E F).hom ≫ _ = _ ≫ (μ (pullback f) F E).hom
    rw [pullback_μ_hom, pullback_μ_hom]
    exact @Functor.LaxBraided.braided _ _ _ _ _ _ _ _
      ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
      inferInstance E F

/-- Arbitrary pullback carries a left dual of a quasicoherent sheaf to a left dual of its
pullback. -/
theorem nonempty_hasLeftDual_pullback (E : QuasicoherentSheaf Y) (f : X ⟶ Y)
    (hE : Nonempty (HasLeftDual E)) : Nonempty (HasLeftDual ((pullback f).obj E)) := by
  obtain ⟨hE⟩ := hE
  let : ExactPairing (C := X.Modules) ((Scheme.Modules.pullback f).obj (ᘁE).obj)
      ((Scheme.Modules.pullback f).obj E.obj) :=
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
      Scheme.Modules.pullback f).mapExactPairing (ᘁE) E
  let : ExactPairing (C := X.Modules) ((pullback f).obj (ᘁE)).obj ((pullback f).obj E).obj :=
    exactPairingCongr (C := X.Modules) (eqToIso (pullback_obj_obj f (ᘁE)))
      (eqToIso (pullback_obj_obj f E))
  let : ExactPairing ((pullback f).obj (ᘁE)) ((pullback f).obj E) :=
    @ObjectProperty.exactPairingFullSubcategory X.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent X) _ _ this
  exact ⟨⟨(pullback f).obj (ᘁE)⟩⟩

/-- Arbitrary pullback preserves right dualizability of quasicoherent sheaves. -/
theorem nonempty_hasRightDual_pullback (E : QuasicoherentSheaf Y) (f : X ⟶ Y)
    (hE : Nonempty (HasRightDual E)) : Nonempty (HasRightDual ((pullback f).obj E)) := by
  obtain ⟨hE⟩ := hE
  let _ : HasLeftDual E := BraidedCategory.hasLeftDualOfHasRightDual
  obtain ⟨hF⟩ := E.nonempty_hasLeftDual_pullback f ⟨inferInstance⟩
  let _ : HasLeftDual ((pullback f).obj E) := hF
  exact ⟨BraidedCategory.hasRightDualOfHasLeftDual⟩

end QuasicoherentSheaf

end

end TauCeti.AlgebraicGeometry
