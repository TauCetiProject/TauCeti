/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Invertible
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Image
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Base ideals of linear systems

The base ideal of a map to a line bundle is the image after twisting by the inverse line bundle.
Equivalently it is the zeroth Fitting ideal of the cokernel. This gives the scheme structure of
base points, including nonreduced ones, and gives pullback compatibility without flatness for
the *pulled-back map*. For the complete linear system we use the free sheaf indexed by all global
sections as a presentation of the evaluation image.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, §7 (linear systems).
* The Stacks Project, [Tag 0C3C](https://stacks.math.columbia.edu/tag/0C3C) (Fitting ideal sheaves).
-/

public section

open _root_.AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

noncomputable section

variable {X Y : Scheme.{u}}

/-- The scheme-theoretic base ideal of a map to a line bundle. Its closed subscheme is
`(L.baseIdeal φ).subscheme`. -/
def baseIdeal (L : InvertibleSheaf X) {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ L.obj) : X.IdealSheafData :=
  (φ ▷ L.dual.obj ≫ (L.evaluationDualIso).hom).imageIdealSheaf

/-- The base ideal is the image of the map tensored by the inverse line bundle. -/
theorem baseIdeal_eq_imageIdealSheaf (L : InvertibleSheaf X) {M : X.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ L.obj) :
    L.baseIdeal φ = Hom.imageIdealSheaf (φ ▷ L.dual.obj ≫ (L.evaluationDualIso).hom) :=
  (rfl)

/-- The base ideal is the zeroth Fitting ideal of the cokernel of the evaluation map. -/
theorem baseIdeal_eq_fittingIdeal_cokernel (L : InvertibleSheaf X) {M : X.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ L.obj) :
    L.baseIdeal φ = (cokernel φ).fittingIdeal
      (fun U ↦ (cokernel φ).finite_sections_of_isAffineOpen U.val U.property) 0 := by
  rw [baseIdeal_eq_imageIdealSheaf, Hom.imageIdealSheaf_eq_fittingIdeal_cokernel]
  let F := tensorRight L.dual.obj
  let e : cokernel (φ ▷ L.dual.obj ≫ (L.evaluationDualIso).hom) ≅ (cokernel φ) ⊗ L.dual.obj :=
    cokernel.mapIso _ (F.map φ) (Iso.refl _) L.evaluationDualIso.symm (by simp [F]) ≪≫
      (PreservesCokernel.iso F φ).symm
  exact (Scheme.Modules.fittingIdeal_congr _ e 0).trans
    (fittingIdeal_tensor_of_isInvertible _ L.dual.obj 0)

/-- Commuting isomorphisms of the source and the target of evaluation identify their base
ideals. -/
theorem baseIdeal_congr {L K : InvertibleSheaf X} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {φ : M ⟶ L.obj} {ψ : N ⟶ K.obj}
    (e : M ≅ N) (a : L.obj ≅ K.obj) (h : φ ≫ a.hom = e.hom ≫ ψ) :
    L.baseIdeal φ = K.baseIdeal ψ := by
  simp only [baseIdeal_eq_fittingIdeal_cokernel]
  exact Scheme.Modules.fittingIdeal_congr _ (cokernel.mapIso φ ψ e a h) 0

/-- The base ideal of a pulled-back map is the extended base ideal, for any morphism of
schemes. This does not assert that all global sections on the pullback come from the original
line bundle. -/
@[simp]
theorem baseIdeal_pullback (L : InvertibleSheaf X) {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ L.obj) (f : Y ⟶ X) :
    ((InvertibleSheaf.pullback f).obj L).baseIdeal ((Scheme.Modules.pullback f).map φ) =
      (L.baseIdeal φ).comap f := by
  rw [baseIdeal_eq_fittingIdeal_cokernel L φ, ← fittingIdeal_pullback]
  exact (baseIdeal_eq_fittingIdeal_cokernel ((InvertibleSheaf.pullback f).obj L)
    ((Scheme.Modules.pullback f).map φ)).trans
      (Scheme.Modules.fittingIdeal_congr _
        (PreservesCokernel.iso (Scheme.Modules.pullback f) φ).symm 0)

/-- The base scheme is empty exactly when the evaluation map is an epimorphism. -/
@[simp]
theorem baseIdeal_eq_top_iff (L : InvertibleSheaf X) {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ L.obj) : L.baseIdeal φ = ⊤ ↔ Epi φ := by
  rw [baseIdeal_eq_imageIdealSheaf]
  let ψ : M ⊗ L.dual.obj ⟶ 𝟙_ X.Modules := φ ▷ L.dual.obj ≫ L.evaluationDualIso.hom
  have h : ψ.imageIdealSheaf = ⊤ ↔ Epi ψ := by
    constructor
    · intro he
      apply Hom.epi_of_surjective_on_affineOpens ψ
      intro U hU t
      apply (Hom.mem_imageIdeal ψ (U := U)).mp
      rw [← Hom.imageIdealSheaf_ideal ψ ⟨U, hU⟩, he]
      exact Submodule.mem_top
    · intro
      apply Scheme.IdealSheafData.ext
      funext U
      rw [Hom.imageIdealSheaf_ideal]
      exact top_unique fun t _ ↦ (Hom.mem_imageIdeal ψ).mpr
        (Hom.app_surjective_of_epi_of_isAffineOpen ψ U.val U.property t)
  rw [h]
  refine (epi_comp_iff_of_isIso _ _).trans ?_
  have hE := L.tensorRightDualEquivalence.functor.epi_map_iff_epi φ
  rw [tensorRightDualEquivalence_functor] at hE
  exact hE

/-- The base ideal is zero exactly when the evaluation map vanishes. -/
@[simp]
theorem baseIdeal_eq_bot_iff (L : InvertibleSheaf X) {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ L.obj) : L.baseIdeal φ = ⊥ ↔ φ = 0 := by
  rw [baseIdeal_eq_imageIdealSheaf]
  let ψ : M ⊗ L.dual.obj ⟶ 𝟙_ X.Modules := φ ▷ L.dual.obj ≫ L.evaluationDualIso.hom
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hz : ψ = 0 := by
      ext U s
      have hs := Hom.app_mem_imageIdealSheaf_sections ψ U s
      rw [h, Scheme.IdealSheafData.sections_bot] at hs
      exact (Ideal.mem_bot (R := Γ(X, U))).mp hs
    have ht : (tensorRight L.dual.obj).map φ = 0 :=
      (cancel_mono L.evaluationDualIso.hom).mp (hz.trans (by simp only [zero_comp]))
    apply L.tensorRightDualEquivalence.functor.map_injective
    rw [Functor.map_zero, tensorRightDualEquivalence_functor]
    exact ht
  · have hz : ψ = 0 := by
      dsimp only [ψ]
      exact (congrArg (fun p ↦ (tensorRight L.dual.obj).map p ≫ L.evaluationDualIso.hom) h).trans
        (by rw [Functor.map_zero, zero_comp])
    apply le_antisymm _ bot_le
    have he : (0 : M ⊗ L.dual.obj ⟶ (⊥ : X.IdealSheafData).sheaf) ≫
        (⊥ : X.IdealSheafData).sheafι = (0 : M ⊗ L.dual.obj ⟶ 𝟙_ X.Modules) := zero_comp
    exact Hom.imageIdealSheaf_le_of_factor ψ ⊥ 0 (he.trans hz.symm)

/-- The base ideal of a family of global sections, using the map from a free sheaf whose
basis sections are sent to the given sections. -/
def sectionBaseIdeal (L : InvertibleSheaf X) {I : Type u} (s : I → Γ(L.obj, ⊤)) :
    X.IdealSheafData :=
  haveI : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_sigma _
  L.baseIdeal (L.obj.freeHomEquiv.symm fun i ↦ L.obj.sectionsEquivTop.symm (s i))

/-- The base ideal of a section family is the base ideal of its free-sheaf evaluation map. -/
theorem sectionBaseIdeal_eq_baseIdeal (L : InvertibleSheaf X) {I : Type u}
    (s : I → Γ(L.obj, ⊤)) :
    letI : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_sigma _
    L.sectionBaseIdeal s =
      L.baseIdeal (L.obj.freeHomEquiv.symm fun i ↦ L.obj.sectionsEquivTop.symm (s i)) :=
  (rfl)

/-- An empty family cuts out all of the scheme. -/
@[simp]
theorem sectionBaseIdeal_of_isEmpty (L : InvertibleSheaf X) {I : Type u} [IsEmpty I]
    (s : I → Γ(L.obj, ⊤)) : L.sectionBaseIdeal s = ⊥ := by
  let P : X.Modules := SheafOfModules.free I
  let φ : P ⟶ L.obj := L.obj.freeHomEquiv.symm fun i ↦ L.obj.sectionsEquivTop.symm (s i)
  have : P.IsQuasicoherent := Scheme.Modules.isQuasicoherent_sigma _
  rw [sectionBaseIdeal_eq_baseIdeal]
  exact (baseIdeal_eq_bot_iff L φ).2 (L.obj.freeHomEquiv.injective (Subsingleton.elim _ _))

/-- Reindexing a family and transporting its sections across a line-bundle isomorphism does
not change its base ideal. -/
theorem sectionBaseIdeal_congr {L K : InvertibleSheaf X} (a : L.obj ≅ K.obj)
    {I J : Type u} (e : I ≃ J) (s : I → Γ(L.obj, ⊤)) (t : J → Γ(K.obj, ⊤))
    (h : ∀ i, a.hom.app ⊤ (s i) = t (e i)) : L.sectionBaseIdeal s = K.sectionBaseIdeal t := by
  rw [sectionBaseIdeal_eq_baseIdeal, sectionBaseIdeal_eq_baseIdeal]
  refine baseIdeal_congr ((SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso)
    a ?_
  rw [Functor.mapIso_hom, SheafOfModules.freeFunctor_map]
  apply K.obj.freeHomEquiv.injective
  funext i
  -- The free-sheaf equivalence is stated for `SheafOfModules`, rather than `X.Modules`.
  erw [SheafOfModules.freeHomEquiv_comp_apply]
  simp only [Equiv.apply_symm_apply]
  have hr {f : SheafOfModules.free (R := X.ringCatSheaf) J ⟶ K.obj} :
      K.obj.freeHomEquiv (SheafOfModules.freeMap e.toIso.hom ≫ f) i =
        K.obj.freeHomEquiv f (e i) := by
    apply K.obj.unitHomEquiv.symm.injective
    erw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    exact SheafOfModules.ιFree_freeMap_assoc _ _ _
  erw [hr]
  simp only [Equiv.apply_symm_apply]
  apply K.obj.sectionsEquivTop.injective
  simpa only [sectionsEquivTop_sectionsMap, Equiv.apply_symm_apply] using h i

/-- The base ideal formed from the pulled-back sections is the extension of the original base
ideal, even when the morphism is not flat. -/
theorem sectionBaseIdeal_pullback (L : InvertibleSheaf X) (f : Y ⟶ X)
    {I : Type u} (s : I → Γ(L.obj, ⊤)) :
    ((InvertibleSheaf.pullback f).obj L).sectionBaseIdeal
        (fun i ↦ f.pullbackSections L.obj ⊤ (s i)) = (L.sectionBaseIdeal s).comap f := by
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
  let P : X.Modules := SheafOfModules.free I
  let Q : Y.Modules := SheafOfModules.free I
  let K := (InvertibleSheaf.pullback f).obj L
  let φ : P ⟶ L.obj := L.obj.freeHomEquiv.symm fun i ↦ L.obj.sectionsEquivTop.symm (s i)
  let ψ : Q ⟶ K.obj := K.obj.freeHomEquiv.symm fun i ↦
    K.obj.sectionsEquivTop.symm (f.pullbackSections L.obj ⊤ (s i))
  have : P.IsQuasicoherent := Scheme.Modules.isQuasicoherent_sigma _
  have : Q.IsQuasicoherent := Scheme.Modules.isQuasicoherent_sigma _
  -- At the top open the pullback sections already have domain of definition all of `Y`.
  erw [sectionBaseIdeal_eq_baseIdeal, sectionBaseIdeal_eq_baseIdeal]
  refine Eq.trans ?_ (baseIdeal_pullback L φ f)
  let e : Q ≅ F.obj P := (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).symm
  refine baseIdeal_congr (φ := ψ) (ψ := F.map φ) e (Iso.refl _) ?_
  rw [Iso.refl_hom, Category.comp_id]
  apply K.obj.freeHomEquiv.injective
  funext i
  apply K.obj.unitHomEquiv.symm.injective
  erw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  have he : SheafOfModules.ιFree i ≫ e.hom ≫ F.map φ =
      (pullbackObjUnitIso f).inv ≫ F.map (SheafOfModules.ιFree i ≫ φ) :=
    (ιFree_pullbackObjFreeIso_inv_assoc f i (F.map φ)).trans <|
      (Category.assoc _ _ _).trans <| congrArg ((pullbackObjUnitIso f).inv ≫ ·)
        (F.map_comp (SheafOfModules.ιFree i : (𝟙_ X.Modules) ⟶ P) φ).symm
  apply K.obj.unitHomEquiv.injective
  apply K.obj.sectionsEquivTop.injective
  refine Eq.trans (b := f.pullbackSections L.obj ⊤ (s i)) ?_
    ((congrArg (K.obj.sectionsEquivTop ∘ K.obj.unitHomEquiv) he).trans ?_).symm
  · erw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
    let t (j : I) := K.obj.sectionsEquivTop.symm (f.pullbackSections L.obj ⊤ (s j))
    exact (congrArg K.obj.sectionsEquivTop
      (congrFun (Equiv.apply_symm_apply K.obj.freeHomEquiv t) i)).trans
      (Equiv.apply_symm_apply _ _)
  · -- Evaluate at `1`, which becomes the pullback of `1` under the unit comparison.
    erw [Function.comp_apply, sectionsEquivTop_apply, SheafOfModules.unitHomEquiv_apply_coe]
    have hφ : L.obj.sectionsEquivTop (L.obj.unitHomEquiv (SheafOfModules.ιFree i ≫ φ)) = s i := by
      erw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
      exact (congrArg L.obj.sectionsEquivTop (congrFun (Equiv.apply_symm_apply
        L.obj.freeHomEquiv (fun j ↦ L.obj.sectionsEquivTop.symm (s j))) i)).trans
        (Equiv.apply_symm_apply _ _)
    erw [sectionsEquivTop_apply, SheafOfModules.unitHomEquiv_apply_coe] at hφ
    exact (congrArg (Hom.app (F.map (SheafOfModules.ιFree i ≫ φ)) ⊤)
      (f.pullbackObjUnitIso_inv_app_one)).trans
        ((f.pullbackSections_naturality _ ⊤ _ _).trans
          (congrArg (f.pullbackSections L.obj ⊤) hφ))

/-- The base ideal of the complete linear system of `L`, generated by all its global sections. -/
def completeBaseIdeal (L : InvertibleSheaf X) : X.IdealSheafData :=
  L.sectionBaseIdeal id

/-- The complete base ideal uses the family of all global sections. -/
theorem completeBaseIdeal_eq_sectionBaseIdeal (L : InvertibleSheaf X) :
    L.completeBaseIdeal = L.sectionBaseIdeal id :=
  (rfl)

/-- Isomorphic line bundles have the same complete base ideal. -/
theorem completeBaseIdeal_congr {L K : InvertibleSheaf X} (a : L.obj ≅ K.obj) :
    L.completeBaseIdeal = K.completeBaseIdeal := by
  simp only [completeBaseIdeal_eq_sectionBaseIdeal]
  let e := Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso (a.hom.app ⊤))
  exact sectionBaseIdeal_congr a e id id (fun _ ↦ rfl)

/-- The complete base scheme is empty exactly when the line bundle is generated by its global
sections. -/
@[simp]
theorem completeBaseIdeal_eq_top_iff (L : InvertibleSheaf X) :
    L.completeBaseIdeal = ⊤ ↔ L.IsGloballyGenerated := by
  let φ : (SheafOfModules.free Γ(L.obj, ⊤) : X.Modules) ⟶ L.obj :=
    L.obj.freeHomEquiv.symm L.obj.sectionsEquivTop.symm
  have : (SheafOfModules.free (R := X.ringCatSheaf) Γ(L.obj, ⊤) : X.Modules).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_sigma _
  rw [completeBaseIdeal_eq_sectionBaseIdeal, sectionBaseIdeal_eq_baseIdeal]
  refine (baseIdeal_eq_top_iff L φ).trans ?_
  constructor
  · intro h
    exact isGloballyGenerated_iff_nonempty_generatingSections.mpr
      ⟨{ I := Γ(L.obj, ⊤), s := L.obj.sectionsEquivTop.symm, epi := h }⟩
  · intro h
    constructor
    intro N f g hfg
    apply h.hom_ext f g
    intro s
    let t := sectionsEquivTop (SheafOfModules.free (R := X.ringCatSheaf) Γ(L.obj, ⊤))
      (SheafOfModules.freeSection s)
    have ht : Hom.app φ ⊤ t = s := app_freeHomEquiv_symm_freeSection L.obj id s
    have he : f.app ⊤ (Hom.app φ ⊤ t) = g.app ⊤ (Hom.app φ ⊤ t) :=
      congrArg (fun p : (SheafOfModules.free Γ(L.obj, ⊤) : X.Modules) ⟶ N ↦ Hom.app p ⊤ t) hfg
    simpa only [ht] using he

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
