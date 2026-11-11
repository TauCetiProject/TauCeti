/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# A sheaf is the right Kan extension of its restriction along a cover-dense functor

Let `G : C ⥤ D` be locally full and cover dense for a Grothendieck topology `K` on `D`.
A sheaf `ℱ` on `D`, with the identity as counit, is the pointwise right Kan extension of
its restriction `G.op ⋙ ℱ` along `G.op`. For every object `X` of `D`, the value
`ℱ.obj (op X)` is the limit of the values `ℱ.obj (op (G.obj Y))` over the arrows
`G.obj Y ⟶ X`, with the restriction maps of `ℱ` as the legs. No topology on `C`, local
faithfulness of `G`, or completeness assumption on the value category is needed.

For the inclusion of a basis of a topological space into its opens, this says that a sheaf is
determined on every open `V` by its values on the basic opens contained in `V`: it is the
adaptedness of `TopCat.Presheaf.IsAdapted` for every sheaf.

Sheafification can also be computed on a cover-dense family. If a morphism `β : F ⟶ Q` from a
presheaf to a sheaf is bijective on the objects `G.obj X`, then it is locally injective and locally
surjective, and the map `F ⟶ F^#` to the sheafification is bijective on the objects `G.obj X`.
So a presheaf that agrees with a sheaf on a basis has the sections of that sheaf over the basic
opens.

## Main results

* `CategoryTheory.Functor.IsCoverDense.isRightKanExtension`: a sheaf, with the identity as
  counit, is a right Kan extension of its restriction along a locally full, cover-dense functor.
* `CategoryTheory.Functor.IsCoverDense.isPointwiseRightKanExtension`: this extension is pointwise.
* `CategoryTheory.Functor.IsCoverDense.isIso_ranAdjunction_unit_app`: when restriction admits
  a right Kan extension functor, its adjunction unit is an isomorphism at a sheaf.
* `CategoryTheory.Functor.IsCoverDense.bijective_toSheafify_app`: a presheaf mapping to a sheaf
  bijectively on the objects `G.obj X` has the same sections there as its sheafification.

## References

* P. T. Johnstone, *Sketches of an Elephant*, C2.2, the comparison lemma. The gluing of
  morphisms used here is Mathlib's `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom`.
-/

public section

universe w w' v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.IsCoverDense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (K : GrothendieckTopology D) {A : Type w} [Category.{w'} A]
  [G.IsCoverDense K] [G.IsLocallyFull K]

/-- A sheaf `ℱ`, with the identity as counit, is a right Kan extension of its restriction
along a locally full, cover-dense functor. -/
theorem isRightKanExtension (ℱ : Sheaf K A) :
    ℱ.obj.IsRightKanExtension (𝟙 (G.op ⋙ ℱ.obj)) := by
  refine ⟨⟨IsTerminal.ofUniqueHom (fun E ↦ CostructuredArrow.homMk
    (sheafHom E.hom) (by simp [sheafHom_restrict_eq])) ?_⟩⟩
  intro E f
  apply CostructuredArrow.hom_ext
  rw [← sheafHom_eq G f.left]
  congr 1
  simpa using CostructuredArrow.w f

/-- A sheaf is the pointwise right Kan extension of its restriction along a locally full,
cover-dense functor. For every object `X` of `D`, its restriction maps exhibit `ℱ.obj (op X)`
as the limit of the values `ℱ.obj (op (G.obj Y))` over the arrows `G.obj Y ⟶ X`.
This holds without any completeness assumption on the value category. -/
noncomputable def isPointwiseRightKanExtension (ℱ : Sheaf K A) :
    (RightExtension.mk ℱ.obj (𝟙 (G.op ⋙ ℱ.obj))).IsPointwiseRightKanExtension := by
  intro Y
  apply coyonedaJointlyReflectsLimits
  intro X
  -- Lift hom sets to a universe large enough for the comma-category limits. The hom functors
  -- and universe lift preserve the sheaf condition and jointly reflect the desired limit.
  let U := uliftFunctor.{max u₁ v₁ v₂, w'}
  let F : Sheaf K (Type (max u₁ v₁ v₂ w')) :=
    ⟨ℱ.obj ⋙ coyoneda.obj X ⋙ U,
      Presheaf.isSheaf_comp_of_isSheaf K ℱ.obj _ ℱ.property⟩
  haveI := isRightKanExtension G K F
  let h := isPointwiseRightKanExtensionOfIsRightKanExtension F.obj
    (𝟙 (G.op ⋙ F.obj)) Y
  apply isLimitOfReflects U
  exact IsLimit.ofIsoLimit h (Cone.ext (Iso.refl _) (by
    intro j
    simp [F, U, RightExtension.coneAt]))

/-- When restriction along a locally full, cover-dense functor admits a right Kan extension
functor, the unit of that adjunction is an isomorphism at every sheaf. -/
theorem isIso_ranAdjunction_unit_app [∀ F : Cᵒᵖ ⥤ A, G.op.HasRightKanExtension F]
    (ℱ : Sheaf K A) : IsIso ((G.op.ranAdjunction A).unit.app ℱ.obj) :=
  (G.op.isIso_ranAdjunction_unit_app_iff ℱ.obj).mpr (isRightKanExtension G K ℱ)

section Sheafify

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {G : C ⥤ D}
  {K : GrothendieckTopology D} [G.IsCoverDense K]
  {A : Type w} [Category.{w'} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- A morphism of presheaves that is injective on the objects `G.obj X` of a
cover-dense functor is locally injective. -/
lemma isLocallyInjective_of_injective_app {F Q : Dᵒᵖ ⥤ A} (β : F ⟶ Q)
    (hβ : ∀ X : C, Function.Injective (β.app (op (G.obj X)))) :
    Presheaf.IsLocallyInjective K β where
  equalizerSieve_mem {U} x y h := by
    refine K.superset_covering ?_ (G.is_cover_of_isCoverDense K U.unop)
    rintro V f ⟨⟨Z, g, k, rfl⟩⟩
    have : F.map k.op x = F.map k.op y := hβ Z (by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h])
    simp only [Presheaf.equalizerSieve_apply, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
    rw [this]

/-- A morphism of presheaves that is surjective on the objects `G.obj X` of a cover-dense functor
is locally surjective. -/
lemma isLocallySurjective_of_surjective_app {F Q : Dᵒᵖ ⥤ A} (β : F ⟶ Q)
    (hβ : ∀ X : C, Function.Surjective (β.app (op (G.obj X)))) :
    Presheaf.IsLocallySurjective K β where
  imageSieve_mem {U} s := by
    refine K.superset_covering ?_ (G.is_cover_of_isCoverDense K U)
    rintro V f ⟨⟨Z, g, k, rfl⟩⟩
    obtain ⟨t, ht⟩ := hβ Z (Q.map k.op s)
    refine ⟨F.map g.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **Sheafification on a cover-dense family.** If a morphism `β : F ⟶ Q` from a presheaf to a
sheaf is bijective on the objects `G.obj X` of a cover-dense functor `G`, then so is the map
`F ⟶ F^#` from `F` to its sheafification. -/
lemma bijective_toSheafify_app [HasWeakSheafify K A] [K.WEqualsLocallyBijective A]
    {F : Dᵒᵖ ⥤ A} {Q : Sheaf K A} (β : F ⟶ Q.obj)
    (hβ : ∀ X : C, Function.Bijective (β.app (op (G.obj X)))) (X : C) :
    Function.Bijective ((toSheafify K F).app (op (G.obj X))) := by
  have hW : K.W β := (K.W_iff_isLocallyBijective β).2
    ⟨isLocallyInjective_of_injective_app β fun X ↦ (hβ X).1,
      isLocallySurjective_of_surjective_app β fun X ↦ (hβ X).2⟩
  have : IsIso ((presheafToSheaf K A).map β) := (K.W_iff β).1 hW
  have : IsIso (toSheafify K Q.obj) := isIso_toSheafify K Q.property
  have : IsIso ((sheafifyMap K β).app (op (G.obj X))) := by
    change IsIso (((sheafToPresheaf K A).map ((presheafToSheaf K A).map β)).app _)
    infer_instance
  have e : ⇑((sheafifyMap K β).app (op (G.obj X))) ∘ ⇑((toSheafify K F).app (op (G.obj X))) =
      ⇑((toSheafify K Q.obj).app (op (G.obj X))) ∘ ⇑(β.app (op (G.obj X))) := by
    ext x
    have := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality K β) (op (G.obj X))) x
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
    exact this.symm
  refine (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso ((sheafifyMap K β).app (op (G.obj X)))) _).1 ?_
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso _).comp (hβ X)

end Sheafify

end CategoryTheory.Functor.IsCoverDense

end
