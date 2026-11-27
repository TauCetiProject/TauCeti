/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.Grp.Sections
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Basic
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.LiftingGerbe.Fiber

/-!
# The positive band of the groupoid of lifts

For an extension `1 → A → B → D → 1` with commutative `B`, the automorphism group of
any lift of a `D`-torsor is the group of compatible global sections of `A`. The identification
sends a section to positive translation through `A → B`. The statement applies to arbitrary
sites, without a terminal object and without assuming that the lifted torsor has global sections.

The displacement of an automorphism descends from the cover where its underlying torsor
has sections. Compatibility with the structure isomorphism kills its image in `D`, and
exactness then gives the unique section of `A`. For a short exact sequence of abelian sheaves,
`ShortComplex.ShortExact.isGroupExtension` supplies precisely this kernel calculation.

## References

J. S. Milne, *Étale Cohomology*, IV §2, p. 9, for the lifting gerbe with its kernel band.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor.LiftingFiber

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

section GroupExtension

variable {A B D : Sheaf J GrpCat.{w}} {i : A ⟶ B} {φ : B ⟶ D}
  [∀ U, IsMulCommutative (B.obj.obj U)]
  (hE : IsGroupExtension i φ) {P : Torsor D} (L : LiftingFiber φ P)

include hE

/-- Positive translation by a section of the kernel is an endomorphism of a lift. -/
def kernelTranslationHom (a : (A.obj ⋙ forget GrpCat).sections) : L ⟶ L :=
  CostructuredArrow.homMk (L.left.translationHom (GrpCat.sectionsMap i.hom a)) (by
    dsimp only [mapFunctor]
    rw [mapHom_translationHom_eq_id]
    · exact Category.id_comp _
    · intro U
      simpa [GrpCat.sectionsπMonoidHom] using hE.app_app_eq_one (a.val U))

lemma kernelTranslationHom_left (a : (A.obj ⋙ forget GrpCat).sections) :
    (kernelTranslationHom hE L a).left =
      L.left.translationHom (GrpCat.sectionsMap i.hom a) := (rfl)

@[simp]
lemma kernelTranslationHom_hom_app (a : (A.obj ⋙ forget GrpCat).sections) (U : Cᵒᵖ)
    (p : L.left.sheaf.obj.obj U) :
    (kernelTranslationHom hE L a).left.hom.hom.app U p = i.hom.app U (a.val U) • p := by
  rw [kernelTranslationHom_left]
  simp [GrpCat.sectionsπMonoidHom]

/-- The homomorphism from kernel sections to automorphisms, with the positive sign convention. -/
def kernelTranslation : (A.obj ⋙ forget GrpCat).sections →* Aut L where
  toFun a := .of (asIso (kernelTranslationHom hE L a))
  map_one' := by ext U p; simp [kernelTranslationHom]
  map_mul' a b := by ext U p; simp [kernelTranslationHom, mul_smul]

@[simp]
lemma kernelTranslation_hom_app (a : (A.obj ⋙ forget GrpCat).sections) (U : Cᵒᵖ)
    (p : L.left.sheaf.obj.obj U) :
    (kernelTranslation hE L a).asIso.hom.left.hom.hom.app U p =
      i.hom.app U (a.val U) • p :=
  kernelTranslationHom_hom_app hE L a U p

/-- Sections of the kernel act faithfully on every lift, even a nontrivial torsor. -/
theorem kernelTranslation_injective : Function.Injective (kernelTranslation hE L) := by
  intro a b hab
  have ht : L.left.translationHom (GrpCat.sectionsMap i.hom a) =
      L.left.translationHom (GrpCat.sectionsMap i.hom b) :=
    congrArg (fun e : Aut L ↦ e.asIso.hom.left) hab
  have hs : GrpCat.sectionsMap i.hom a = GrpCat.sectionsMap i.hom b :=
    L.left.translation_injective (by
      ext U p
      simpa [GrpCat.sectionsπMonoidHom] using
        congrArg (fun k : L.left ⟶ L.left ↦ k.hom.hom.app U p) ht)
  apply Subtype.ext
  funext U
  exact hE.injective U (by simpa using congrArg (fun s ↦ s.val U) hs)

omit hE [∀ U, IsMulCommutative (B.obj.obj U)] in
/-- An endomorphism of a lift induces the identity on its extended torsor. -/
@[simp]
lemma mapHom_left_eq_id (f : L ⟶ L) : mapHom φ f.left = 𝟙 (L.left.map φ) := by
  apply (cancel_mono L.hom).mp
  simpa only [mapFunctor, Category.id_comp] using CostructuredArrow.w f

/-- Every endomorphism of a lift is a positive translation by a kernel section. -/
theorem exists_kernelTranslationHom_eq (f : L ⟶ L) :
    ∃ a : (A.obj ⋙ forget GrpCat).sections, kernelTranslationHom hE L a = f := by
  obtain ⟨s, hs⟩ := L.left.exists_translationHom_eq f.left
  have hm : (L.left.translationHom s).hom ≫ L.left.toMap φ = L.left.toMap φ := by
    rw [← toMap_mapHom, hs, mapHom_left_eq_id]
    simp
  have hk : ∀ (U : Cᵒᵖ) (_p : L.left.sheaf.obj.obj U),
      φ.hom.app U (GrpCat.sectionsπMonoidHom B.obj U s) = 1 := by
    intro U p
    apply (L.left.map φ).smul_left_injective ((L.left.toMap φ).hom.app U p)
    dsimp only
    rw [one_smul]
    exact (Torsor.toMap_smul φ L.left (GrpCat.sectionsπMonoidHom B.obj U s) p).symm.trans
      ((congrArg ((L.left.toMap φ).hom.app U) (L.left.translationHom_hom_app s U p)).symm.trans
        (congrArg (fun k ↦ k.hom.app U p) hm))
  have hzero : GrpCat.sectionsMap φ.hom s = 1 := by
    apply L.left.coversTop.sections_ext ((sheafCompose J (forget GrpCat.{w})).obj D)
    rintro ⟨U, ⟨p⟩⟩
    simpa [GrpCat.sectionsπMonoidHom] using hk (op U) p
  obtain ⟨a, ha, -⟩ := (hE.existsUnique_sections_iff s).mpr (fun U ↦ by
    have h := congrArg (GrpCat.sectionsπMonoidHom D.obj U) hzero
    simpa [GrpCat.sectionsπMonoidHom] using h)
  refine ⟨a, CostructuredArrow.hom_ext _ _ ?_⟩
  have has : GrpCat.sectionsMap i.hom a = s := by ext U; simpa using ha U
  simpa only [kernelTranslationHom, CostructuredArrow.homMk_left, has] using hs

/-- Kernel sections are exactly the automorphisms of each lift. -/
def kernelTranslationEquiv : (A.obj ⋙ forget GrpCat).sections ≃* Aut L :=
  MulEquiv.ofBijective (kernelTranslation hE L) ⟨kernelTranslation_injective hE L, fun f ↦ by
    obtain ⟨a, ha⟩ := exists_kernelTranslationHom_eq hE L f.asIso.hom
    exact ⟨a, by apply Aut.ext; exact Iso.ext ha⟩⟩

@[simp]
lemma kernelTranslationEquiv_apply (a : (A.obj ⋙ forget GrpCat).sections) :
    kernelTranslationEquiv hE L a = kernelTranslation hE L a := (rfl)

end GroupExtension

section Abelian

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
  (hS : S.ShortExact)
  {P : Torsor ((abelianSheafToGrpSheaf J).obj S.X₃)}
  (L : LiftingFiber ((abelianSheafToGrpSheaf J).map S.g) P)

/-- The automorphisms of a lift through a short exact sequence of abelian sheaves are the
compatible global sections of its kernel, written multiplicatively, acting positively. -/
def abelianBandEquiv :
    (((abelianSheafToGrpSheaf J).obj S.X₁).obj ⋙ forget GrpCat).sections ≃* Aut L := by
  letI : ∀ U, IsMulCommutative (((abelianSheafToGrpSheaf J).obj S.X₂).obj.obj U) := fun U ↦
    (abelianSheafToGrpSheafObjEquiv S.X₂ U).isMulCommutative.mp ⟨⟨mul_comm⟩⟩
  exact kernelTranslationEquiv hS.isGroupExtension L

/-- The abelian band sends `a` to translation by its positive image under the kernel inclusion. -/
@[simp]
lemma abelianBandEquiv_hom_app
    (a : (((abelianSheafToGrpSheaf J).obj S.X₁).obj ⋙ forget GrpCat).sections)
    (U : Cᵒᵖ) (p : L.left.sheaf.obj.obj U) :
    (abelianBandEquiv hS L a).asIso.hom.left.hom.hom.app U p =
      ((abelianSheafToGrpSheaf J).map S.f).hom.app U (a.val U) • p := by
  simp [abelianBandEquiv, kernelTranslationEquiv, kernelTranslation]

end Abelian

end CategoryTheory.Sheaf.Torsor.LiftingFiber
