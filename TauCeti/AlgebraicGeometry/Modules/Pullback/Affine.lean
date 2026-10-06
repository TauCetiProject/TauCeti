/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Presentation
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Presentation
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Pullback of tensor products from an affine base

For a morphism `f : X ⟶ Y` with affine target `Y`, the canonical comparison
`f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` is an isomorphism whenever either factor is quasicoherent.
The other factor is an arbitrary sheaf of modules. No flatness or finiteness assumption is
required. The comparison is the tensor map of the existing oplax monoidal pullback, so its
associativity and unit compatibilities are retained. These affine statements are the local input
for the same comparison over an arbitrary target
(`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent` in
`TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent`).

In particular, pullback from quasicoherent sheaves on `Y` to modules on `X` is strong
symmetric monoidal (`Scheme.Modules.pullbackFromAffineBraided`). The tensor comparisons are also
exposed as natural isomorphisms with either quasicoherent factor fixed. These affine computations
let tensor and duality constructions on sheaves be compared with their module counterparts.
For instance, pullback from `Y` carries a quasicoherent sheaf with a left or right dual in
`QuasicoherentSheaf Y` to one with the corresponding dual in `QuasicoherentSheaf X`.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)

open _root_.AlgebraicGeometry.Scheme.Modules

/-- Pullback from an affine base preserves a tensor product with a quasicoherent left factor.
The right factor need not be quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ_of_isAffine
    (M N : Y.Modules)
    [M.IsQuasicoherent] : IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) := by
  obtain ⟨P⟩ := M.nonempty_presentation_of_isAffine
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  exact P.isIso_pullback_δ f.toRingCatSheafHom N

/-- Pullback from an affine base preserves a tensor product with a quasicoherent right factor.
The left factor need not be quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ_right_of_isAffine
    (M N : Y.Modules)
    [N.IsQuasicoherent] : IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) := by
  obtain ⟨P⟩ := N.nonempty_presentation_of_isAffine
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  exact P.isIso_pullback_δ_right f.toRingCatSheafHom M

/-- Pulling back the tensor product with a fixed quasicoherent left factor from an affine scheme
commutes with tensoring by its pullback, naturally in the other sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorLeftIso
    (M : Y.Modules) [M.IsQuasicoherent] :
    tensorLeft M ⋙ pullback f ≅ pullback f ⋙ tensorLeft ((pullback f).obj M) := by
  have : IsIso ((pullback f).oplaxCommTensorLeft M) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [Functor.oplaxCommTensorLeft_app]
    exact isIso_pullback_δ_of_isAffine f M N
  exact asIso ((pullback f).oplaxCommTensorLeft M)

/-- The left tensor comparison is the canonical oplax tensor map of pullback. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorLeftIso_hom_app
    (M N : Y.Modules) [M.IsQuasicoherent] :
    (pullbackTensorLeftIso f M).hom.app N = Functor.OplaxMonoidal.δ (pullback f) M N := by
  exact Functor.oplaxCommTensorLeft_app _ _ _

/-- Pulling back the tensor product with a fixed quasicoherent right factor from an affine scheme
commutes with tensoring by its pullback, naturally in the other sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorRightIso
    (N : Y.Modules) [N.IsQuasicoherent] :
    tensorRight N ⋙ pullback f ≅ pullback f ⋙ tensorRight ((pullback f).obj N) := by
  have : IsIso ((pullback f).oplaxCommTensorRight N) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [Functor.oplaxCommTensorRight_app]
    exact isIso_pullback_δ_right_of_isAffine f M N
  exact asIso ((pullback f).oplaxCommTensorRight N)

/-- The right tensor comparison is the canonical oplax tensor map of pullback. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorRightIso_hom_app
    (M N : Y.Modules) [N.IsQuasicoherent] :
    (pullbackTensorRightIso f N).hom.app M = Functor.OplaxMonoidal.δ (pullback f) M N := by
  exact Functor.oplaxCommTensorRight_app _ _ _

/-- Pullback of quasicoherent sheaves from an affine scheme, viewed in the category of all
modules on the source, is strong monoidal. Its inverse tensor comparison is the canonical
oplax tensor map of module pullback. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.pullbackFromAffineMonoidal :
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f).Monoidal := by
  let I : QuasicoherentSheaf Y ⥤ Y.Modules := ObjectProperty.ι _
  have : I.Monoidal := @ObjectProperty.monoidalι Y.Modules _ _ _
    (Scheme.Modules.isMonoidal_isQuasicoherent Y)
  have : IsIso (Functor.OplaxMonoidal.η (I ⋙ pullback f)) := by
    rw [Functor.OplaxMonoidal.comp_η]
    infer_instance
  have (E F : QuasicoherentSheaf Y) :
      IsIso (Functor.OplaxMonoidal.δ (I ⋙ pullback f) E F) := by
    rw [Functor.OplaxMonoidal.comp_δ]
    have : E.obj.IsQuasicoherent := E.property
    have : IsIso (Functor.OplaxMonoidal.δ (pullback f) (I.obj E) (I.obj F)) :=
      isIso_pullback_δ_of_isAffine f E.obj F.obj
    infer_instance
  exact Functor.Monoidal.ofOplaxMonoidal (I ⋙ pullback f)

/-- The inverse tensor comparison of strong monoidal affine pullback is the canonical
tensor comparison of the underlying module pullback. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackFromAffine_δ
    (E F : QuasicoherentSheaf Y) :
    Functor.OplaxMonoidal.δ
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f) E F =
      Functor.OplaxMonoidal.δ (pullback f) E.obj F.obj := by
  -- The full-subcategory inclusion has identity tensor comparisons; compute its composite
  -- before simplifying, since rewriting does not see through the scheme-module category.
  exact (congrArg (· ≫ Functor.OplaxMonoidal.δ (pullback f) E.obj F.obj)
    ((pullback f).map_id (E.obj ⊗ F.obj))).trans (Category.id_comp _)

/-- The inverse unit comparison of strong monoidal affine pullback is the canonical
identification of the pulled-back structure sheaf. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackFromAffine_η :
    Functor.OplaxMonoidal.η
        ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f) =
      (pullbackObjUnitIso f).hom := by
  -- As for the tensor comparison, the inclusion contributes an identity map.
  exact (congrArg (· ≫ Functor.OplaxMonoidal.η (pullback f))
    ((pullback f).map_id (𝟙_ Y.Modules))).trans
      ((Category.id_comp _).trans (pullback_η f))

omit [IsAffine Y] in
/-- Pullback sends the inherited braiding of quasicoherent sheaves to the pullback of
the braiding of their underlying sheaves of modules. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackFromAffine_map_braiding
    (E F : QuasicoherentSheaf Y) :
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f).map
        (β_ E F).hom =
      (pullback f).map (@BraidedCategory.braiding Y.Modules _ _ _ E.obj F.obj).hom :=
  (rfl)

/-- Pullback of quasicoherent sheaves from an affine base to modules on the source is
symmetric monoidal, with the existing canonical tensor comparisons. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.pullbackFromAffineBraided :
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f).Braided where
  toMonoidal := pullbackFromAffineMonoidal f
  braided E F := by
    let H := (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ pullback f
    rw [← cancel_epi (Functor.OplaxMonoidal.δ H E F)]
    erw [Functor.Monoidal.δ_μ_assoc]
    rw [pullbackFromAffine_δ]
    rw [pullbackFromAffine_map_braiding]
    erw [← pullback_map_braiding_hom_comp_δ_assoc, ← pullbackFromAffine_δ]
    exact ((congrArg ((pullback f).map
      (@BraidedCategory.braiding Y.Modules _ _ _ E.obj F.obj).hom ≫ ·)
      (Functor.Monoidal.δ_μ H F E)).trans (Category.comp_id _)).symm

namespace QuasicoherentSheaf

/-- Pullback along a morphism to an affine scheme preserves dualizability of quasicoherent
sheaves: the pullback of a left dual of `E` is a left dual of the pullback of `E`. -/
theorem nonempty_hasLeftDual_pullback (E : QuasicoherentSheaf Y) (f : X ⟶ Y)
    (hE : Nonempty (HasLeftDual E)) : Nonempty (HasLeftDual ((pullback f).obj E)) := by
  obtain ⟨hE⟩ := hE
  -- Strong monoidal pullback carries the exact pairing of `ᘁE` and `E` to one in `X.Modules`
  -- between the pulled-back underlying sheaves.
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

/-- Pullback along a morphism to an affine scheme preserves right dualizability of quasicoherent
sheaves. -/
theorem nonempty_hasRightDual_pullback (E : QuasicoherentSheaf Y) (f : X ⟶ Y)
    (hE : Nonempty (HasRightDual E)) : Nonempty (HasRightDual ((pullback f).obj E)) := by
  obtain ⟨hE⟩ := hE
  let _ : HasLeftDual E := BraidedCategory.hasLeftDualOfHasRightDual
  obtain ⟨hF⟩ := E.nonempty_hasLeftDual_pullback f ⟨inferInstance⟩
  let _ : HasLeftDual ((pullback f).obj E) := hF
  exact ⟨BraidedCategory.hasRightDualOfHasLeftDual⟩

end QuasicoherentSheaf

end

end AlgebraicGeometry

end TauCeti
