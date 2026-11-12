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
      mapNatTrans_app_left_inl, sectionsPullback_apply_left_inl]
    rfl
  · simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
      mapNatTrans_app_left_inr, sectionsPullback_apply_left_inr]
    rfl
  · simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
      mapNatTrans_app_right, sectionsPullback_apply_right]
    rfl

/-- Pointwise coefficient naturality of matching-section pullback. -/
theorem sectionsPullback_naturality_apply (η : I.multispan ⟶ I'.multispan)
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    SemimoduleCat.sectionsMap (D.mapNatTrans η) (D.sectionsPullback I s) =
      D.sectionsPullback I' (SemimoduleCat.sectionsMap η s) :=
  LinearMap.congr_fun (D.sectionsPullback_naturality η) s

/-- Compatible-family pullback commutes with arbitrary coefficient changes. -/
theorem compatibleMap_naturality (η : I.multispan ⟶ I'.multispan) :
    (MultispanIndex.compatibleFamiliesMap (D.mapNatTrans η)).comp (D.compatibleMap I) =
      (D.compatibleMap I').comp (MultispanIndex.compatibleFamiliesMap η) := by
  ext x ⟨j, a⟩
  simp only [LinearMap.comp_apply,
    MultispanIndex.compatibleFamiliesMap_apply (D.mapNatTrans η),
    MultispanIndex.compatibleFamiliesMap_apply η, D.compatibleMap_apply I,
    D.compatibleMap_apply I', D.mapNatTrans_app_right]
  rfl

/-- Pointwise coefficient naturality of compatible-family pullback. -/
theorem compatibleMap_naturality_apply (η : I.multispan ⟶ I'.multispan)
    (x : I.compatibleFamilies) :
    MultispanIndex.compatibleFamiliesMap (D.mapNatTrans η) (D.compatibleMap I x) =
      D.compatibleMap I' (MultispanIndex.compatibleFamiliesMap η x) :=
  LinearMap.congr_fun (D.compatibleMap_naturality η) x

/-- Coefficient transport preserves agreement between copies of each chamber. -/
theorem sectionsMap_chambers_eq (η : I.multispan ⟶ I'.multispan)
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hs : ∀ j (c d : D.chambers j),
      s.val (.right ⟨j, c⟩) = s.val (.right ⟨j, d⟩)) :
    ∀ j (c d : D.chambers j),
      (SemimoduleCat.sectionsMap (D.mapNatTrans η) s).val (.right ⟨j, c⟩) =
        (SemimoduleCat.sectionsMap (D.mapNatTrans η) s).val (.right ⟨j, d⟩) := by
  intro j c d
  simp only [SemimoduleCat.sectionsMap_apply, mapNatTrans_app_right]
  exact congrArg (η.app (.right j)).hom (hs j c d)

variable [∀ j, Nonempty (D.chambers j)] [∀ b, Nonempty (D.faces b)]

/-- Linear descent commutes with coefficient maps, without requiring connected
identity-face graphs or injectivity of the coefficient maps. -/
theorem sectionsDescend_naturality
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hinj' : ∀ b, Function.Injective ((I'.fst b).hom.prod (I'.snd b).hom))
    (η : I.multispan ⟶ I'.multispan)
    {E : Type*} [AddCommMonoid E] [Module R E]
    (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hℓ : ∀ x j (c d : D.chambers j),
      (ℓ x).val (.right ⟨j, c⟩) = (ℓ x).val (.right ⟨j, d⟩)) :
    D.sectionsDescend I' hinj' ((SemimoduleCat.sectionsMap (D.mapNatTrans η)).comp ℓ)
        (fun x => D.sectionsMap_chambers_eq η (ℓ x) (hℓ x)) =
      (SemimoduleCat.sectionsMap η).comp (D.sectionsDescend I hinj ℓ hℓ) := by
  apply LinearMap.ext
  intro x
  apply D.sectionsPullback_injective_of_nonempty_faces I'
  simpa only [LinearMap.comp_apply, sectionsPullback_sectionsDescend] using
    D.sectionsPullback_naturality_apply η (D.sectionsDescend I hinj ℓ hℓ x)

/-- Pointwise coefficient naturality of linear-family descent. -/
theorem sectionsDescend_naturality_apply
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hinj' : ∀ b, Function.Injective ((I'.fst b).hom.prod (I'.snd b).hom))
    (η : I.multispan ⟶ I'.multispan)
    {E : Type*} [AddCommMonoid E] [Module R E]
    (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hℓ : ∀ x j (c d : D.chambers j),
      (ℓ x).val (.right ⟨j, c⟩) = (ℓ x).val (.right ⟨j, d⟩)) (x : E) :
    D.sectionsDescend I' hinj' ((SemimoduleCat.sectionsMap (D.mapNatTrans η)).comp ℓ)
        (fun x => D.sectionsMap_chambers_eq η (ℓ x) (hℓ x)) x =
      SemimoduleCat.sectionsMap η (D.sectionsDescend I hinj ℓ hℓ x) :=
  LinearMap.congr_fun (D.sectionsDescend_naturality hinj hinj' η ℓ hℓ) x

/-- Compatible-family descent commutes with coefficient changes under chamber
and face coverage and connected identity-face graphs. No span injectivity is needed. -/
theorem compatibleEquiv_symm_naturality
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (η : I.multispan ⟶ I'.multispan) :
    (D.compatibleEquiv I' hc).symm.toLinearMap.comp
        (MultispanIndex.compatibleFamiliesMap (D.mapNatTrans η)) =
      (MultispanIndex.compatibleFamiliesMap η).comp
        (D.compatibleEquiv I hc).symm.toLinearMap := by
  ext x : 1
  apply D.compatibleMap_injective I'
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    D.compatibleMap_compatibleEquiv_symm I hc,
    D.compatibleMap_compatibleEquiv_symm I' hc] using
    D.compatibleMap_naturality_apply η ((D.compatibleEquiv I hc).symm x)

/-- Pointwise coefficient naturality of compatible-family descent. -/
theorem compatibleEquiv_symm_naturality_apply
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (η : I.multispan ⟶ I'.multispan) (x : (D.index I).compatibleFamilies) :
    (D.compatibleEquiv I' hc).symm (MultispanIndex.compatibleFamiliesMap (D.mapNatTrans η) x) =
      MultispanIndex.compatibleFamiliesMap η ((D.compatibleEquiv I hc).symm x) :=
  LinearMap.congr_fun (D.compatibleEquiv_symm_naturality hc η) x

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
  ext s : 1
  apply D.sectionsPullback_injective_of_nonempty_faces I'
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    sectionsPullback_sectionsEquiv_symm] using
    D.sectionsPullback_naturality_apply η ((D.sectionsEquiv I hc hinj).symm s)

/-- Pointwise coefficient naturality of matching-section descent. -/
theorem sectionsEquiv_symm_naturality_apply
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hinj' : ∀ b, Function.Injective ((I'.fst b).hom.prod (I'.snd b).hom))
    (η : I.multispan ⟶ I'.multispan)
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) :
    (D.sectionsEquiv I' hc hinj').symm (SemimoduleCat.sectionsMap (D.mapNatTrans η) s) =
      SemimoduleCat.sectionsMap η ((D.sectionsEquiv I hc hinj).symm s) :=
  LinearMap.congr_fun (D.sectionsEquiv_symm_naturality hc hinj hinj' η) s

end CategoryTheory.Limits.MultispanShape.Subdivision
