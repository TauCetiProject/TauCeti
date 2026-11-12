/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.SemimoduleCat.Multispan.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Multispan.Subdivision.Basic
public import Mathlib.Logic.Relation

/-!
# Matching families under subdivisions with identity faces

A subdivision copies chambers and faces and adds identity faces between chamber
copies. Provided every chamber and face has at least one copy and the identity
faces connect each chamber's copies, compatible chamber families descend uniquely.
If the original face spans are jointly injective, this gives an equivalence of
matching sections. Individual incidence maps need not be injective and the index
sets may be infinite. Disconnected identity graphs also permit descent of a supplied
section, or a linear family of sections, when its chamber copies already agree.

Surjectivity permits chambers with no copies, assigning them zero. Injectivity
of section pullback requires joint injectivity only at faces without copies;
with full face coverage it holds for arbitrary spans. Pullback combines the
linear version of Mathlib's section precomposition with the canonical
coefficient-diagram isomorphism.

Adapted from `Mei/Algebra/Category/SemimoduleCat/Multispan/Refinement.lean` in
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
  {R : Type r} [Semiring R] (I : MultispanIndex J (SemimoduleCat.{m} R))

/-- A compatible chamber family pulls back by giving every copy the old value. -/
def compatibleMap : I.compatibleFamilies →ₗ[R] (D.index I).compatibleFamilies :=
  (D.index I).piCompatibleFamilies
    (fun j => LinearMap.proj j.1 ∘ₗ I.compatibleFamilies.subtype) (by
      intro x b
      rcases b with (⟨b, _⟩ | ⟨j, e⟩)
      · exact I.mem_compatibleFamilies_iff_forall_mem_range.mp x.property b
      · refine ⟨x.val j, ?_⟩
        simp only [SemimoduleCat.hom_id, LinearMap.prod_apply, Function.prod_apply,
          LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          Submodule.subtype_apply])

/-- Pullback reads the original value at every chamber copy. -/
@[simp]
theorem compatibleMap_apply (x : I.compatibleFamilies) (j : J.R) (a : D.chambers j) :
    (D.compatibleMap I x).val ⟨j, a⟩ = x.val j := by
  -- The copied coefficient objects agree definitionally across the generic index.
  dsimp only [compatibleMap]
  erw [MultispanIndex.piCompatibleFamilies_apply]
  rfl

/-- Compatibility at identity faces makes values constant along their equivalence closure. -/
theorem eq_of_eqvGen_edgeRel (x : (D.index I).compatibleFamilies) (j : J.R)
    {a b : D.chambers j} (hab : Relation.EqvGen (D.edgeRel j) a b) :
    x.val ⟨j, a⟩ = x.val ⟨j, b⟩ := by
  let f : D.chambers j → I.right j := fun c => x.val ⟨j, c⟩
  have h' : Relation.EqvGen (InvImage Eq f) a b := by
    apply Relation.EqvGen.mono (fun a b h => ?_) a b hab
    rw [edgeRel_iff] at h
    obtain ⟨e, rfl, rfl⟩ := h
    obtain ⟨z, hs, ht⟩ := (D.index I).mem_compatibleFamilies.mp x.property (.inr ⟨j, e⟩)
    simp only [SemimoduleCat.hom_id, LinearMap.id_apply] at hs ht
    exact hs.symm.trans ht
  exact (InvImage.equivalence Eq f eq_equivalence).eqvGen_iff.mp h'

/-- Restrict an original matching section to the copied objects and identity faces. -/
def sectionsPullback : SemimoduleCat.sectionsSubmodule I.multispan →ₗ[R]
    SemimoduleCat.sectionsSubmodule (D.index I).multispan :=
  (SemimoduleCat.sectionsMap (D.multispanIso I).inv).comp
    (SemimoduleCat.sectionsPrecomp D.projection I.multispan)

/-- Pullback is section precomposition followed by the canonical coefficient comparison. -/
theorem sectionsPullback_apply (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (x : WalkingMultispan D.shape) :
    (D.sectionsPullback I s).val x =
      ((D.multispanIso I).inv.app x).hom (s.val (D.projection.obj x)) := by
  rw [sectionsPullback, LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
    SemimoduleCat.sectionsPrecomp_apply]

/-- Restriction preserves the value at every chamber copy. -/
@[simp]
theorem sectionsPullback_apply_right (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (a : D.chambers j) :
    (D.sectionsPullback I s).val (.right ⟨j, a⟩) = s.val (.right j) := by
  rw [sectionsPullback_apply, multispanIso_inv_app]
  erw [eqToHom_refl (C := SemimoduleCat.{m} R), SemimoduleCat.hom_id, LinearMap.id_apply]
  rfl

/-- Restriction preserves each copied original face value. -/
@[simp]
theorem sectionsPullback_apply_copy (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (b : J.L) (a : D.faces b) :
    (D.sectionsPullback I s).val (.left (.inl ⟨b, a⟩)) = s.val (.left b) := by
  rw [sectionsPullback_apply, multispanIso_inv_app]
  erw [eqToHom_refl (C := SemimoduleCat.{m} R), SemimoduleCat.hom_id, LinearMap.id_apply]
  rfl

/-- An identity face receives the old chamber value. -/
@[simp]
theorem sectionsPullback_apply_edge (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (e : D.edges j) :
    (D.sectionsPullback I s).val (.left (.inr ⟨j, e⟩)) = s.val (.right j) := by
  rw [sectionsPullback_apply, multispanIso_inv_app]
  erw [eqToHom_refl (C := SemimoduleCat.{m} R), SemimoduleCat.hom_id, LinearMap.id_apply]
  rfl

variable [∀ j, Nonempty (D.chambers j)]

/-- Pullback is injective if every original chamber has at least one copy. -/
theorem compatibleMap_injective : Function.Injective (D.compatibleMap I) := by
  classical
  intro x y h
  apply Subtype.ext
  funext j
  have he := congrArg (fun z => z.val ⟨j, Classical.choice inferInstance⟩) h
  erw [compatibleMap_apply, compatibleMap_apply] at he
  exact he

omit [∀ j, Nonempty (D.chambers j)] in
/-- A compatible family with equal chamber copies descends when every face has a copy.
No connectivity or chamber coverage is required; missing chambers receive zero. -/
theorem exists_compatibleMap_eq_of_copies_eq [∀ b, Nonempty (D.faces b)]
    (y : (D.index I).compatibleFamilies)
    (hy : ∀ j (c d : D.chambers j), y.val ⟨j, c⟩ = y.val ⟨j, d⟩) :
    ∃ x, D.compatibleMap I x = y := by
  classical
  let value (j : J.R) : I.right j :=
    if h : Nonempty (D.chambers j) then y.val ⟨j, Classical.choice h⟩ else 0
  have hconst (j : J.R) (b : D.chambers j) : y.val ⟨j, b⟩ = value j := by
    have h : Nonempty (D.chambers j) := ⟨b⟩
    dsimp only [value]
    rw [dite_eq_left h]
    exact hy j b (Classical.choice h)
  let x : I.compatibleFamilies := ⟨value, by
    apply I.mem_compatibleFamilies.mpr
    intro b
    let c : D.faces b := Classical.choice inferInstance
    obtain ⟨z, hs, ht⟩ := (D.index I).mem_compatibleFamilies.mp y.property (.inl ⟨b, c⟩)
    exact ⟨z, hs.trans (hconst _ _), ht.trans (hconst _ _)⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext ⟨j, b⟩
  erw [compatibleMap_apply]
  exact (hconst j b).symm

omit [∀ j, Nonempty (D.chambers j)] in
/-- If every face has a copy and each chamber's identity-face graph is connected,
every compatible refined family descends. Missing isolated chambers receive zero. -/
theorem compatibleMap_surjective [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    Function.Surjective (D.compatibleMap I) := by
  intro y
  exact D.exists_compatibleMap_eq_of_copies_eq I y
    (fun j c d => D.eq_of_eqvGen_edgeRel I y j (hc j c d))

/-- If every chamber and face has a copy and each chamber's identity-face graph is
connected, compatible chamber families are linearly equivalent before and after subdivision. -/
noncomputable def compatibleEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    I.compatibleFamilies ≃ₗ[R] (D.index I).compatibleFamilies :=
  LinearEquiv.ofBijective (D.compatibleMap I)
    ⟨D.compatibleMap_injective I, D.compatibleMap_surjective I hc⟩

/-- The comparison equivalence is the canonical chamber pullback. -/
@[simp]
theorem compatibleEquiv_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) (x : I.compatibleFamilies) :
    D.compatibleEquiv I hc x = D.compatibleMap I x := (rfl)

/-- Descending a refined family recovers its value at every copy of each chamber. -/
theorem compatibleEquiv_symm_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (y : (D.index I).compatibleFamilies) (j : J.R) (a : D.chambers j) :
    ((D.compatibleEquiv I hc).symm y).val j = y.val ⟨j, a⟩ := by
  have he := congrArg (fun z : (D.index I).compatibleFamilies => z.val ⟨j, a⟩)
    ((D.compatibleEquiv I hc).apply_symm_apply y)
  erw [compatibleEquiv_apply, compatibleMap_apply] at he
  exact he

omit [∀ j, Nonempty (D.chambers j)] in
/-- Copied face spans and identity face spans remain jointly injective. -/
theorem index_jointly_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    ∀ b, Function.Injective (((D.index I).fst b).hom.prod ((D.index I).snd b).hom) := by
  rintro (⟨b, _⟩ | ⟨j, e⟩)
  · exact hinj b
  · intro x y h
    simpa only [index_fst_edge, SemimoduleCat.hom_id, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.id_apply] using congrArg _root_.Prod.fst h

/-- Pullback is injective when every chamber has a copy and the spans at faces
without copies are jointly injective. Copied faces retain their values directly. -/
theorem sectionsPullback_injective
    (hinj : ∀ b, IsEmpty (D.faces b) →
      Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Injective (D.sectionsPullback I) := by
  classical
  intro s t h
  have hch (j : J.R) : s.val (.right j) = t.val (.right j) := by
    have he := congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      z.val (.right ⟨j, Classical.choice inferInstance⟩)) h
    erw [sectionsPullback_apply_right, sectionsPullback_apply_right] at he
    exact he
  apply Subtype.ext
  funext x
  cases x with
  | right j => exact hch j
  | left b =>
    by_cases hb : Nonempty (D.faces b)
    · have he := congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
        z.val (.left (.inl ⟨b, Classical.choice hb⟩))) h
      erw [sectionsPullback_apply_copy, sectionsPullback_apply_copy] at he
      exact he
    · apply hinj b (not_nonempty_iff.mp hb)
      apply Prod.ext
      · exact ((SemimoduleCat.mem_sectionsSubmodule.mp s.property) (.fst b)).trans
          ((hch _).trans ((SemimoduleCat.mem_sectionsSubmodule.mp t.property) (.fst b)).symm)
      · exact ((SemimoduleCat.mem_sectionsSubmodule.mp s.property) (.snd b)).trans
          ((hch _).trans ((SemimoduleCat.mem_sectionsSubmodule.mp t.property) (.snd b)).symm)

/-- When every chamber and face has a copy, section pullback is injective for
arbitrary face spans, including spans with a nonzero common kernel. -/
theorem sectionsPullback_injective_of_face_coverage [∀ b, Nonempty (D.faces b)] :
    Function.Injective (D.sectionsPullback I) := by
  classical
  exact D.sectionsPullback_injective I (fun b hb =>
    (hb.false (Classical.choice inferInstance)).elim)

omit [∀ j, Nonempty (D.chambers j)] in
/-- A refined matching section descends when its chamber copies agree and the original
face spans are jointly injective. Identity graphs may be disconnected. Chambers with
no copies receive zero, so chamber coverage is not required for existence. -/
theorem exists_sectionsPullback_eq_of_copies_eq [∀ b, Nonempty (D.faces b)]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (y : SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hy : ∀ j (c d : D.chambers j), y.val (.right ⟨j, c⟩) = y.val (.right ⟨j, d⟩)) :
    ∃ s, D.sectionsPullback I s = y := by
  obtain ⟨x, hx⟩ := D.exists_compatibleMap_eq_of_copies_eq I
    ((D.index I).restrictSections y) (by
      intro j c d
      erw [MultispanIndex.restrictSections_apply, MultispanIndex.restrictSections_apply]
      exact hy j c d)
  obtain ⟨s, hs⟩ := I.restrictSections_surjective x
  refine ⟨s, ?_⟩
  apply (D.index I).restrictSections_injective (D.index_jointly_injective I hinj)
  ext ⟨j, c⟩
  erw [MultispanIndex.restrictSections_apply, sectionsPullback_apply_right,
    MultispanIndex.restrictSections_apply]
  have hs' := congrArg (fun z : I.compatibleFamilies => z.val j) hs
  erw [MultispanIndex.restrictSections_apply] at hs'
  have hx' := congrArg (fun z : (D.index I).compatibleFamilies => z.val ⟨j, c⟩) hx
  erw [compatibleMap_apply, MultispanIndex.restrictSections_apply] at hx'
  exact hs'.trans hx'

/-- A linear refined family whose chamber copies agree has a unique linear descent
when every chamber and face has a copy. Recovery is equality of complete matching
families, including every copied face and identity face. -/
theorem existsUnique_sectionsPullback_lift_of_copies_eq [∀ b, Nonempty (D.faces b)]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    {E : Type*} [AddCommMonoid E] [Module R E]
    (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hℓ : ∀ x j (c d : D.chambers j),
      (ℓ x).val (.right ⟨j, c⟩) = (ℓ x).val (.right ⟨j, d⟩)) :
    ∃! a : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
      (D.sectionsPullback I).comp a = ℓ := by
  let P := D.sectionsPullback I
  have hi : Function.Injective P := D.sectionsPullback_injective_of_face_coverage I
  have hmem x : ℓ x ∈ P.range :=
    D.exists_sectionsPullback_eq_of_copies_eq I hinj (ℓ x) (hℓ x)
  let a := ℓ.codLift P hi hmem
  have ha : P.comp a = ℓ := LinearMap.comp_codLift ℓ P hi hmem
  refine ⟨a, ha, ?_⟩
  intro q hq
  apply LinearMap.ext
  intro x
  exact hi ((LinearMap.congr_fun hq x).trans (LinearMap.congr_fun ha x).symm)

omit [∀ j, Nonempty (D.chambers j)] in
/-- If every face has a copy, identity graphs are connected and old spans are
jointly injective, every refined matching section descends without chamber coverage. -/
theorem sectionsPullback_surjective [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Surjective (D.sectionsPullback I) := by
  intro y
  apply D.exists_sectionsPullback_eq_of_copies_eq I hinj y
  intro j c d
  have h := D.eq_of_eqvGen_edgeRel I ((D.index I).restrictSections y) j (hc j c d)
  erw [MultispanIndex.restrictSections_apply, MultispanIndex.restrictSections_apply] at h
  exact h

/-- If every chamber and face has a copy, each chamber's identity-face graph is connected
and the original face spans are jointly injective, pullback of matching sections is a
linear equivalence. -/
noncomputable def sectionsEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    SemimoduleCat.sectionsSubmodule I.multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (D.index I).multispan :=
  LinearEquiv.ofBijective (D.sectionsPullback I)
    ⟨D.sectionsPullback_injective_of_face_coverage I, D.sectionsPullback_surjective I hc hinj⟩

/-- The section comparison is the actual pullback along the incidence projection. -/
@[simp]
theorem sectionsEquiv_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    D.sectionsEquiv I hc hinj s = D.sectionsPullback I s := (rfl)

/-- Descent recovers each old chamber value from any of its refined copies. -/
theorem sectionsEquiv_symm_apply_right [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) (j : J.R)
    (a : D.chambers j) :
    ((D.sectionsEquiv I hc hinj).symm s).val (.right j) = s.val (.right ⟨j, a⟩) := by
  simpa only [MultispanIndex.multispan_obj_right, index_right,
    sectionsEquiv_apply, sectionsPullback_apply_right] using
    congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      z.val (.right ⟨j, a⟩)) ((D.sectionsEquiv I hc hinj).apply_symm_apply s)


/-- Descent recovers each original face value from any of its refined copies. -/
theorem sectionsEquiv_symm_apply_copy [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) (b : J.L)
    (a : D.faces b) :
    ((D.sectionsEquiv I hc hinj).symm s).val (.left b) = s.val (.left (.inl ⟨b, a⟩)) := by
  simpa only [MultispanIndex.multispan_obj_left, index_left_copy,
    sectionsEquiv_apply, sectionsPullback_apply_copy] using
    congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      z.val (.left (.inl ⟨b, a⟩))) ((D.sectionsEquiv I hc hinj).apply_symm_apply s)

end CategoryTheory.Limits.MultispanShape.Subdivision
