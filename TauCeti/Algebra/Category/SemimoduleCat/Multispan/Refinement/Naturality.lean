/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.SemimoduleCat.Multispan.Refinement.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Multispan.Subdivision.Morphism

/-!
# Coefficient naturality of matching-section refinement

Subdivision pullback commutes with every coefficient transformation. Whenever
the connected identity-face subdivision gives matching-section equivalences,
their inverses commute with the same transformation. Thus refining and descending
matching families are compatible with coefficient maps, without assuming that
those coefficient maps are injective or surjective.

Adapted from `Mei/Algebra/Category/SemimoduleCat/Multispan/Refinement/Naturality.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
The original source credits Codex and carries the notice
Copyright (c) 2026 Mei contributors. All rights reserved.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.MultispanShape.Subdivision

universe r m

variable {J : MultispanShape} (D : Subdivision J)
  {R : Type r} [Semiring R] {I I' : MultispanIndex J (SemimoduleCat.{m} R)}

/-- Changing coefficients and copying a matching family commute, including on
inserted identity faces. No coverage or injectivity assumptions are needed. -/
theorem sectionsPullback_naturality (η : I.multispan ⟶ I'.multispan) :
    (SemimoduleCat.sectionsMap (D.mapNatTrans η)).comp (D.sectionsPullback I) =
      (D.sectionsPullback I').comp (SemimoduleCat.sectionsMap η) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  rcases x with (⟨b, a⟩ | ⟨j, e⟩) | ⟨j, a⟩
  · simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
      mapNatTrans_app_copy, sectionsPullback_apply_copy]
    rfl
  · simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
      mapNatTrans_app_edge, sectionsPullback_apply_edge]
    rfl
  · simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
      mapNatTrans_app_right, sectionsPullback_apply_right]
    rfl

variable [∀ j, Nonempty (D.chambers j)] [∀ b, Nonempty (D.faces b)]

/-- Descending a refined matching family commutes with arbitrary coefficient
maps when both original diagrams have jointly injective face spans. -/
theorem sectionsEquiv_symm_naturality
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hinj' : ∀ b, Function.Injective ((I'.fst b).hom.prod (I'.snd b).hom))
    (η : I.multispan ⟶ I'.multispan) :
    (D.sectionsEquiv I' hc hinj').symm.toLinearMap.comp
        (SemimoduleCat.sectionsMap (D.mapNatTrans η)) =
      (SemimoduleCat.sectionsMap η).comp (D.sectionsEquiv I hc hinj).symm.toLinearMap := by
  apply LinearMap.ext
  intro s
  apply (D.sectionsEquiv I' hc hinj').injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    sectionsEquiv_apply]
  have h := LinearMap.congr_fun (D.sectionsPullback_naturality η)
    ((D.sectionsEquiv I hc hinj).symm s)
  have hpre : D.sectionsPullback I ((D.sectionsEquiv I hc hinj).symm s) = s :=
    (D.sectionsEquiv_apply I hc hinj _).symm.trans
      ((D.sectionsEquiv I hc hinj).apply_symm_apply s)
  simpa only [LinearMap.comp_apply, hpre] using h

end CategoryTheory.Limits.MultispanShape.Subdivision
