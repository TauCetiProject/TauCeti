/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

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

## Main results

* `CategoryTheory.Functor.IsCoverDense.isRightKanExtension`: a sheaf, with the identity as
  counit, is a right Kan extension of its restriction along a locally full, cover-dense functor.
* `CategoryTheory.Functor.IsCoverDense.isPointwiseRightKanExtension`: this extension is pointwise.
* `CategoryTheory.Functor.IsCoverDense.isIso_ranAdjunction_unit_app`: when restriction admits
  a right Kan extension functor, its adjunction unit is an isomorphism at a sheaf.

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
  apply (restrictHomEquivHom (G := G) (ℱ' := ℱ)).symm.injective
  simpa [restrictHomEquivHom, sheafHom_restrict_eq] using CostructuredArrow.w f

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

end CategoryTheory.Functor.IsCoverDense

end
