/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Restriction
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction

/-!
# Gluing ideal sheaves on open covers

Compatible ideal sheaves on open subschemes glue by their local membership condition inside
the fixed structure sheaf. The resulting submodule is quasi-coherent because this can be
checked on the given open cover.
-/

public section

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
  (I : ∀ i, (U i).toScheme.IdealSheafData)

private def gluingIdeal (V : X.Opens) : Ideal Γ(X, V) :=
  ⨅ i, ((I i).sections ((U i).ι ⁻¹ᵁ V)).comap ((U i).ι.app V).hom

private lemma map_mem_gluingIdeal {V W : X.Opens} (f : W ⟶ V) {s : Γ(X, V)}
    (hs : s ∈ gluingIdeal U I V) : X.presheaf.map f.op s ∈ gluingIdeal U I W := by
  refine Ideal.mem_iInf.mpr fun i ↦ ?_
  have h := (I i).map_mem_sections ((TopologicalSpace.Opens.map (U i).ι.base).map f)
    (Ideal.mem_iInf.mp hs i)
  rw [Ideal.mem_comap]
  have hnat : (U i).ι.app W (X.presheaf.map f.op s) =
      (U i).toScheme.presheaf.map ((TopologicalSpace.Opens.map (U i).ι.base).map f).op
        ((U i).ι.app V s) := ConcreteCategory.congr_hom ((U i).ι.naturality f.op) s
  exact hnat.symm ▸ h

private lemma mem_gluingIdeal_of_forall_exists {V : X.Opens} (s : Γ(X, V))
    (hs : ∀ x ∈ V, ∃ (W : X.Opens) (j : W ⟶ V),
      X.presheaf.map j.op s ∈ gluingIdeal U I W ∧ x ∈ W) :
    s ∈ gluingIdeal U I V := by
  refine Ideal.mem_iInf.mpr fun i ↦ ?_
  apply (I i).mem_sections_of_forall_exists
  intro x hx
  obtain ⟨W, j, hj, hxW⟩ := hs ((U i).ι x) hx
  refine ⟨(U i).ι ⁻¹ᵁ W, (TopologicalSpace.Opens.map (U i).ι.base).map j, hxW, ?_⟩
  have h := Ideal.mem_iInf.mp hj i
  exact ConcreteCategory.congr_hom ((U i).ι.naturality j.op) s ▸ h

/-- Sections of the structure sheaf belonging to every local ideal after restriction to its
open subscheme. -/
def gluingSubmodule : (Scheme.Modules.unit X).Submodule where
  obj V := gluingIdeal U I V.unop
  map f _s hs := map_mem_gluingIdeal U I f.unop hs
  isSheaf {_V} s hs := mem_gluingIdeal_of_forall_exists U I s hs

/-- Membership in the gluing submodule is membership in each inverse-image local ideal. -/
theorem mem_gluingSubmodule_iff (V : X.Opens) (s : Γ(X, V)) :
    s ∈ (gluingSubmodule U I).toSubmodule.obj (op V) ↔
      ∀ i, (U i).ι.app V s ∈ (I i).sections ((U i).ι ⁻¹ᵁ V) :=
  Ideal.mem_iInf

variable (hI : ∀ (i j : ι) {W : Scheme.{u}} (a : W ⟶ (U i).toScheme)
  (b : W ⟶ (U j).toScheme), a ≫ (U i).ι = b ≫ (U j).ι →
    (I i).comap a = (I j).comap b)

include hI in
private lemma mem_gluingIdeal_iff_of_le (i : ι) (V : X.Opens) (hV : V ≤ U i)
    (s : Γ(X, V)) :
    s ∈ gluingIdeal U I V ↔ (U i).ι.app V s ∈ (I i).sections ((U i).ι ⁻¹ᵁ V) := by
  refine ⟨fun hs ↦ Ideal.mem_iInf.mp hs i, fun hs ↦ Ideal.mem_iInf.mpr fun j ↦ ?_⟩
  let W := (U j).ι ⁻¹ᵁ V
  let g : W.toScheme ⟶ X := W.ι ≫ (U j).ι
  have hg : Set.range g ⊆ Set.range (U i).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV x.property
  let a : W.toScheme ⟶ (U i).toScheme := IsOpenImmersion.lift (U i).ι g hg
  have ha : a ≫ (U i).ι = g := IsOpenImmersion.lift_fac _ _ _
  have he : (⊤ : W.toScheme.Opens) ≤ a ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ha]
    exact fun x _ ↦ x.property
  have ht := (I i).appLE_mem_sections_comap a he hs
  rw [hI i j a W.ι ha] at ht
  have ht' := ((I j).mem_sections_comap_iff W.ι ⊤ _).mp ht
  have he' : (⊤ : W.toScheme.Opens) ≤ g ⁻¹ᵁ V := fun x _ ↦ x.property
  have hsMap : a.appLE ((U i).ι ⁻¹ᵁ V) ⊤ he ((U i).ι.app V s) =
      g.appLE V ⊤ he' s := by
    have h : g.appLE V ⊤ he' = (U i).ι.app V ≫ a.appLE ((U i).ι ⁻¹ᵁ V) ⊤ he := by
      simpa only [ha] using Scheme.Hom.comp_appLE a (U i).ι V ⊤ he
    exact (ConcreteCategory.congr_hom h s).symm
  rw [hsMap] at ht'
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at ht'
  have ht'' := (I j).map_mem_sections (eqToHom W.ι_image_top.symm) ht'
  rw [Ideal.mem_comap]
  exact Scheme.Opens.topIso_hom_appLE (U j) V s he' ▸ ht''

include hI in
private lemma mem_gluingIdeal_image_iff (i : ι) (V : (U i).toScheme.Opens)
    (s : Γ(X, (U i).ι ''ᵁ V)) :
    s ∈ gluingIdeal U I ((U i).ι ''ᵁ V) ↔
      ((U i).ι.appIso V).hom s ∈ (I i).sections V := by
  rw [mem_gluingIdeal_iff_of_le U I hI i _ ((U i).ι_image_le V)]
  constructor
  · intro hs
    rw [Scheme.Hom.appIso_hom']
    exact (I i).map_mem_sections (homOfLE ((U i).ι.preimage_image_eq V).ge) hs
  · intro hs
    have h := (I i).map_mem_sections (eqToHom ((U i).ι.preimage_image_eq V)) hs
    have heq : (U i).toScheme.presheaf.map (eqToHom ((U i).ι.preimage_image_eq V)).op
        (((U i).ι.appIso V).hom s) = (U i).ι.app ((U i).ι ''ᵁ V) s := by
      rw [← Scheme.Hom.appIso_inv_app]
      exact congrArg ((U i).ι.app ((U i).ι ''ᵁ V))
        (Iso.hom_inv_id_apply ((U i).ι.appIso V) s)
    exact heq ▸ h

private abbrev gluingModule : X.Modules :=
  (gluingSubmodule U I).toSheafOfModules

private def gluingι : gluingModule U I ⟶ Scheme.Modules.unit X :=
  (gluingSubmodule U I).ι

private instance : Mono (gluingι U I) :=
  SheafOfModules.Submodule.instMonoι (gluingSubmodule U I)

private def gluingRestrictionι (i : ι) :
    (gluingModule U I).restrict (U i).ι ⟶
      Scheme.Modules.unit (U i).toScheme :=
  (Scheme.Modules.restrictFunctor (U i).ι).map (gluingSubmodule U I).ι ≫
    (Scheme.Modules.restrictUnitIso (U i).ι).hom

private lemma gluingRestrictionι_app (i : ι) (V : (U i).toScheme.Opens)
    (t : Γ((gluingModule U I).restrict (U i).ι, V)) :
    (gluingRestrictionι U I i).app V t = ((U i).ι.appIso V).hom
      (((gluingModule U I).restrictAppIso (U i).ι V).hom t).val := by
  rw [gluingRestrictionι, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.restrictUnitIso_hom_app]
  exact congrArg ((U i).ι.appIso V).hom
    (ConcreteCategory.congr_hom
      (Scheme.Modules.restrictFunctor_map_app_restrictAppIso_hom (U i).ι
        (gluingSubmodule U I).ι V) t)

include hI in
private def gluingToLocal (i : ι) : (gluingModule U I).restrict (U i).ι ⟶ (I i).sheaf :=
  (I i).sheafLift (gluingRestrictionι U I i) (by
    intro V t
    rw [gluingRestrictionι_app]
    exact (mem_gluingIdeal_image_iff U I hI i V _).mp
      (((gluingModule U I).restrictAppIso (U i).ι V).hom t).property)

include hI in
private lemma gluingToLocal_app_sheafι (i : ι) (V : (U i).toScheme.Opens)
    (t : Γ((gluingModule U I).restrict (U i).ι, V)) :
    (I i).sheafι.app V ((gluingToLocal U I hI i).app V t) =
      ((U i).ι.appIso V).hom
        (((gluingModule U I).restrictAppIso (U i).ι V).hom t).val := by
  exact (ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ Scheme.Modules.Hom.app φ V)
      ((I i).sheafLift_ι (gluingRestrictionι U I i) _)) t).trans
        (gluingRestrictionι_app U I i V t)

include hI in
private lemma isIso_gluingToLocal (i : ι) : IsIso (gluingToLocal U I hI i) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun s t h ↦ ?_, fun t ↦ ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso
      ((gluingModule U I).restrictAppIso (U i).ι V).hom).injective
    apply Subtype.ext
    apply (ConcreteCategory.bijective_of_isIso ((U i).ι.appIso V).hom).injective
    have he := congrArg ((I i).sheafι.app V) h
    exact (gluingToLocal_app_sheafι U I hI i V s).symm.trans
      (he.trans (gluingToLocal_app_sheafι U I hI i V t))
  · let r : Γ((U i).toScheme, V) := (I i).sheafι.app V t
    let s := ((U i).ι.appIso V).inv r
    have hs : s ∈ gluingIdeal U I ((U i).ι ''ᵁ V) :=
      (mem_gluingIdeal_image_iff U I hI i V s).mpr (by
        exact (Iso.inv_hom_id_apply ((U i).ι.appIso V) r).symm ▸
          (I i).sheafι_app_mem V t)
    let t' : Γ(gluingModule U I, (U i).ι ''ᵁ V) := ⟨s, hs⟩
    refine ⟨((gluingModule U I).restrictAppIso (U i).ι V).inv t', ?_⟩
    apply (I i).sheafι_app_injective V
    rw [gluingToLocal_app_sheafι, Iso.inv_hom_id_apply]
    exact Iso.inv_hom_id_apply ((U i).ι.appIso V) _

include hI in
/-- The sheaf defined by the gluing membership condition is quasicoherent if the local ideals
are compatible and their opens cover the scheme. -/
theorem isQuasicoherent_gluingSubmodule (hU : ⨆ i, U i = ⊤) :
    (gluingSubmodule U I).toSheafOfModules.IsQuasicoherent := by
  refine ((gluingModule U I).isQuasicoherent_iff_of_iSup_eq_top U hU).mpr fun i ↦ ?_
  have := isIso_gluingToLocal U I hI i
  exact (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
    (asIso (gluingToLocal U I hI i)).symm inferInstance

/-- The ideal sheaf obtained by gluing a compatible family of ideal sheaves on an open cover. -/
def glue (hU : ⨆ i, U i = ⊤) : X.IdealSheafData :=
  letI := isQuasicoherent_gluingSubmodule U I hI hU
  Scheme.Modules.Hom.imageIdealSheaf (gluingι U I)

private lemma mem_glue_sections_iff (hU : ⨆ i, U i = ⊤) (V : X.Opens) (s : Γ(X, V)) :
    s ∈ (glue U I hI hU).sections V ↔ s ∈ gluingIdeal U I V := by
  have := isQuasicoherent_gluingSubmodule U I hI hU
  unfold glue
  rw [Scheme.Modules.Hom.imageIdealSheaf_sections, Scheme.Modules.Hom.mem_imageIdeal]
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ t.property, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩

/-- A section belongs to the glued ideal exactly when all of its restrictions belong to the
prescribed local ideals. -/
theorem mem_sections_glue_iff (hU : ⨆ i, U i = ⊤) (V : X.Opens) (s : Γ(X, V)) :
    s ∈ (glue U I hI hU).sections V ↔
      ∀ i, (U i).ι.app V s ∈ (I i).sections ((U i).ι ⁻¹ᵁ V) := by
  rw [mem_glue_sections_iff]
  exact Ideal.mem_iInf

/-- The glued ideal sheaf restricts to each prescribed local ideal. -/
@[simp]
theorem comap_glue (hU : ⨆ i, U i = ⊤) (i : ι) :
    (glue U I hI hU).comap (U i).ι = I i := by
  ext V s
  rw [← sections_eq_ideal _ V, ← sections_eq_ideal _ V, mem_sections_comap_iff,
    mem_glue_sections_iff, mem_gluingIdeal_image_iff U I hI]
  exact Iff.of_eq (congrArg (fun r ↦ r ∈ (I i).sections V.val)
    (Iso.inv_hom_id_apply ((U i).ι.appIso V.val) s))

include hI in
/-- Compatible ideal sheaves on an open cover glue uniquely. Compatibility is stated on
arbitrary common probes into the opens. -/
theorem existsUnique_comap_ι_eq (hU : ⨆ i, U i = ⊤) :
    ∃! J : X.IdealSheafData, ∀ i, J.comap (U i).ι = I i := by
  refine ⟨glue U I hI hU, comap_glue U I hI hU, fun J hJ ↦ ?_⟩
  apply ext_of_comap_openCover (X.openCoverOfIsOpenCover U (.mk hU))
  intro i
  exact (hJ i).trans (comap_glue U I hI hU i).symm

/-- Compatible ideal sheaves on the members of a scheme-theoretic open cover glue uniquely. -/
theorem existsUnique_comap_eq_of_isOpenImmersion {Z : ι → Scheme.{u}} (j : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcover : ⨆ i, (j i).opensRange = ⊤)
    (K : ∀ i, (Z i).IdealSheafData)
    (hK : ∀ (i k : ι) {W : Scheme.{u}} (a : W ⟶ Z i) (b : W ⟶ Z k),
      a ≫ j i = b ≫ j k → (K i).comap a = (K k).comap b) :
    ∃! J : X.IdealSheafData, ∀ i, J.comap (j i) = K i := by
  let V (i : ι) := (j i).opensRange
  let L (i : ι) := (K i).comap (j i).isoOpensRange.inv
  have hL (i k : ι) {W : Scheme.{u}} (a : W ⟶ (V i).toScheme)
      (b : W ⟶ (V k).toScheme) (hab : a ≫ (V i).ι = b ≫ (V k).ι) :
      (L i).comap a = (L k).comap b := by
    dsimp only [L]
    rw [← comap_comp, ← comap_comp]
    apply hK
    simpa only [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using hab
  obtain ⟨J, hJ, huniq⟩ := existsUnique_comap_ι_eq V L hL hcover
  have hJ' (i : ι) : J.comap (j i) = K i := by
    have h := congrArg (comap · (j i).isoOpensRange.hom) (hJ i)
    dsimp only [V, L] at h
    simpa only [← comap_comp, Scheme.Hom.isoOpensRange_hom_ι,
      Iso.hom_inv_id, comap_id] using h
  refine ⟨J, hJ', fun J' hJ' ↦ huniq J' fun i ↦ ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp (j i), comap_comp, hJ']

end AlgebraicGeometry.Scheme.IdealSheafData
