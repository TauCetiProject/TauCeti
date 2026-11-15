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
section when its chamber copies already agree, every face has a copy and the
original spans are jointly injective (`exists_sectionsPullback_eq_of_chambers_eq`).
Chamber coverage also yields uniqueness and linear-family descent (`sectionsDescend`
and `existsUnique_sectionsPullback_comp_eq_of_chambers_eq`).

Surjectivity assumes face coverage but permits chambers with no copies. Injectivity
of section pullback assumes chamber coverage and requires joint injectivity only
at faces without copies; with full face coverage it holds for arbitrary spans.
Pullback combines the linear version of Mathlib's section precomposition with the canonical
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

/-- Pullback factors as restriction along the projection followed by coefficient comparison. -/
theorem sectionsPullback_def :
    D.sectionsPullback I = (SemimoduleCat.sectionsMap (D.multispanIso I).inv).comp
      (SemimoduleCat.sectionsPrecomp D.projection I.multispan) := (rfl)

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
  -- The exposed projection and abbreviated index identify coefficient objects on
  -- this constructor definitionally; extended rewriting reduces these carriers.
  erw [eqToHom_refl (C := SemimoduleCat.{m} R), SemimoduleCat.hom_id, LinearMap.id_apply]
  rfl

/-- Restriction preserves each copied original face value. -/
@[simp]
theorem sectionsPullback_apply_left_inl (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (b : J.L) (a : D.faces b) :
    (D.sectionsPullback I s).val (.left (.inl ⟨b, a⟩)) = s.val (.left b) := by
  rw [sectionsPullback_apply, multispanIso_inv_app]
  -- The exposed projection and abbreviated index identify coefficient objects on
  -- this constructor definitionally; extended rewriting reduces these carriers.
  erw [eqToHom_refl (C := SemimoduleCat.{m} R), SemimoduleCat.hom_id, LinearMap.id_apply]
  rfl

/-- An identity face receives the old chamber value. -/
@[simp]
theorem sectionsPullback_apply_left_inr (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (e : D.edges j) :
    (D.sectionsPullback I s).val (.left (.inr ⟨j, e⟩)) = s.val (.right j) := by
  rw [sectionsPullback_apply, multispanIso_inv_app]
  -- The exposed projection and abbreviated index identify coefficient objects on
  -- this constructor definitionally; extended rewriting reduces these carriers.
  erw [eqToHom_refl (C := SemimoduleCat.{m} R), SemimoduleCat.hom_id, LinearMap.id_apply]
  rfl

/-- Chamber restriction commutes with subdivision pullback. -/
@[simp]
theorem restrictSections_sectionsPullback
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    (D.index I).restrictSections (D.sectionsPullback I s) =
      D.compatibleMap I (I.restrictSections s) := by
  ext ⟨j, a⟩
  simp only [(D.index I).restrictSections_apply, D.sectionsPullback_apply_right I,
    D.compatibleMap_apply I, I.restrictSections_apply]
  rfl

/-- Chamber restriction and subdivision pullback commute as linear maps. -/
theorem restrictSections_comp_sectionsPullback :
    (D.index I).restrictSections.comp (D.sectionsPullback I) =
      (D.compatibleMap I).comp I.restrictSections := by
  ext s : 1
  exact D.restrictSections_sectionsPullback I s

variable [∀ j, Nonempty (D.chambers j)]

/-- Pullback is injective if every original chamber has at least one copy. -/
theorem compatibleMap_injective : Function.Injective (D.compatibleMap I) := by
  classical
  intro x y h
  apply Subtype.ext
  funext j
  have he := congrArg (fun z => z.val ⟨j, Classical.choice inferInstance⟩) h
  simpa only [index_right, D.compatibleMap_apply I] using he

omit [∀ j, Nonempty (D.chambers j)] in
/-- A compatible family with equal chamber copies descends when every face has a copy.
No connectivity or chamber coverage is required. -/
theorem exists_compatibleMap_eq_of_chambers_eq [∀ b, Nonempty (D.faces b)]
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
  simpa only [index_right, D.compatibleMap_apply I] using (hconst j b).symm

omit [∀ j, Nonempty (D.chambers j)] in
/-- With face coverage, a compatible family is a pullback exactly when its chamber
copies agree; no chamber coverage or identity-edge connectivity is needed. -/
theorem mem_range_compatibleMap_iff [∀ b, Nonempty (D.faces b)]
    (y : (D.index I).compatibleFamilies) :
    y ∈ (D.compatibleMap I).range ↔
      ∀ j (c d : D.chambers j), y.val ⟨j, c⟩ = y.val ⟨j, d⟩ := by
  constructor
  · rintro ⟨x, rfl⟩ j c d
    simp only [D.compatibleMap_apply I]
  · exact D.exists_compatibleMap_eq_of_chambers_eq I y

omit [∀ j, Nonempty (D.chambers j)] in
/-- If every face has a copy and each chamber's identity-face graph is connected,
every compatible refined family descends. Chamber coverage is not required. -/
theorem compatibleMap_surjective [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    Function.Surjective (D.compatibleMap I) := by
  intro y
  exact D.exists_compatibleMap_eq_of_chambers_eq I y
    (fun j c d => D.eq_of_eqvGen_edgeRel I y j (hc j c d))

/-- If every chamber and face has a copy and each chamber's identity-face graph is
connected, compatible chamber families are linearly equivalent before and after subdivision. -/
noncomputable def compatibleEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    I.compatibleFamilies ≃ₗ[R] (D.index I).compatibleFamilies :=
  LinearEquiv.ofBijective (D.compatibleMap I)
    ⟨D.compatibleMap_injective I, D.compatibleMap_surjective I hc⟩

/-- The underlying linear map of the chamber comparison is pullback. -/
@[simp]
theorem compatibleEquiv_toLinearMap [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    (D.compatibleEquiv I hc).toLinearMap = D.compatibleMap I := (rfl)

/-- The comparison equivalence is the canonical chamber pullback. -/
@[simp]
theorem compatibleEquiv_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) (x : I.compatibleFamilies) :
    D.compatibleEquiv I hc x = D.compatibleMap I x := (rfl)

/-- Descent cancels compatible-family pullback. -/
@[simp]
theorem compatibleEquiv_symm_compatibleMap [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) (x : I.compatibleFamilies) :
    (D.compatibleEquiv I hc).symm (D.compatibleMap I x) = x :=
  (D.compatibleEquiv I hc).symm_apply_apply x

/-- Pullback cancels compatible-family descent. -/
@[simp]
theorem compatibleMap_compatibleEquiv_symm [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (y : (D.index I).compatibleFamilies) :
    D.compatibleMap I ((D.compatibleEquiv I hc).symm y) = y :=
  (D.compatibleEquiv I hc).apply_symm_apply y

/-- Descending a refined family recovers its value at every copy of each chamber. -/
theorem compatibleEquiv_symm_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (y : (D.index I).compatibleFamilies) (j : J.R) (a : D.chambers j) :
    ((D.compatibleEquiv I hc).symm y).val j = y.val ⟨j, a⟩ := by
  have he := congrArg (fun z : (D.index I).compatibleFamilies => z.val ⟨j, a⟩)
    ((D.compatibleEquiv I hc).apply_symm_apply y)
  simpa only [index_right, D.compatibleEquiv_apply I, D.compatibleMap_apply I] using he

omit [∀ j, Nonempty (D.chambers j)] in
/-- Copied face spans and identity face spans remain jointly injective. -/
theorem index_fst_prod_snd_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    ∀ b, Function.Injective (((D.index I).fst b).hom.prod ((D.index I).snd b).hom) := by
  rintro (⟨b, _⟩ | ⟨j, e⟩)
  · exact hinj b
  · intro x y h
    simpa only [index_fst_inr, SemimoduleCat.hom_id, LinearMap.prod_apply, Function.prod_apply,
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
    simpa only [MultispanIndex.multispan_obj_right, index_right,
      sectionsPullback_apply_right] using he
  apply Subtype.ext
  funext x
  cases x with
  | right j => exact hch j
  | left b =>
    by_cases hb : Nonempty (D.faces b)
    · have he := congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
        z.val (.left (.inl ⟨b, Classical.choice hb⟩))) h
      simpa only [MultispanIndex.multispan_obj_left, index_left_inl,
        sectionsPullback_apply_left_inl] using he
    · apply hinj b (not_nonempty_iff.mp hb)
      apply Prod.ext
      · exact ((SemimoduleCat.mem_sectionsSubmodule.mp s.property) (.fst b)).trans
          ((hch _).trans ((SemimoduleCat.mem_sectionsSubmodule.mp t.property) (.fst b)).symm)
      · exact ((SemimoduleCat.mem_sectionsSubmodule.mp s.property) (.snd b)).trans
          ((hch _).trans ((SemimoduleCat.mem_sectionsSubmodule.mp t.property) (.snd b)).symm)

/-- When every chamber and face has a copy, section pullback is injective for
arbitrary face spans, including spans with a nonzero common kernel. -/
theorem sectionsPullback_injective_of_nonempty_faces [∀ b, Nonempty (D.faces b)] :
    Function.Injective (D.sectionsPullback I) := by
  classical
  exact D.sectionsPullback_injective I (fun b hb =>
    (hb.false (Classical.choice inferInstance)).elim)

omit [∀ j, Nonempty (D.chambers j)] in
/-- A refined matching section descends when its chamber copies agree and the original
face spans are jointly injective and every face has a copy. Identity graphs may be
disconnected; chamber coverage is not required for existence. -/
theorem exists_sectionsPullback_eq_of_chambers_eq [∀ b, Nonempty (D.faces b)]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (y : SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hy : ∀ j (c d : D.chambers j), y.val (.right ⟨j, c⟩) = y.val (.right ⟨j, d⟩)) :
    ∃ s, D.sectionsPullback I s = y := by
  obtain ⟨x, hx⟩ := D.exists_compatibleMap_eq_of_chambers_eq I
    ((D.index I).restrictSections y) (by
      intro j c d
      simpa only [MultispanIndex.multispan_obj_right, index_right,
    (D.index I).restrictSections_apply] using hy j c d)
  obtain ⟨s, hs⟩ := I.restrictSections_surjective x
  refine ⟨s, ?_⟩
  apply (D.index I).restrictSections_injective (D.index_fst_prod_snd_injective I hinj)
  rw [restrictSections_sectionsPullback, hs, hx]

omit [∀ j, Nonempty (D.chambers j)] in
/-- With face coverage and jointly injective original spans, a refined section is
a pullback exactly when its chamber copies agree. -/
theorem mem_range_sectionsPullback_iff [∀ b, Nonempty (D.faces b)]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (y : SemimoduleCat.sectionsSubmodule (D.index I).multispan) :
    y ∈ (D.sectionsPullback I).range ↔
      ∀ j (c d : D.chambers j), y.val (.right ⟨j, c⟩) = y.val (.right ⟨j, d⟩) := by
  constructor
  · rintro ⟨s, rfl⟩ j c d
    simp only [D.sectionsPullback_apply_right I]
    rfl
  · exact D.exists_sectionsPullback_eq_of_chambers_eq I hinj y

section Descent

variable [∀ b, Nonempty (D.faces b)]
  (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
  {E : Type*} [AddCommMonoid E] [Module R E]
  (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.index I).multispan)
  (hℓ : ∀ x j (c d : D.chambers j),
    (ℓ x).val (.right ⟨j, c⟩) = (ℓ x).val (.right ⟨j, d⟩))

/-- Descend a linear family with agreeing chamber copies, when every chamber and
face has a copy and the original spans are jointly injective. -/
noncomputable def sectionsDescend :
    E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan :=
  ℓ.codLift (D.sectionsPullback I) (D.sectionsPullback_injective_of_nonempty_faces I)
    (fun x => D.exists_sectionsPullback_eq_of_chambers_eq I hinj (ℓ x) (hℓ x))

/-- Pullback recovers the entire linear family after descent. -/
@[simp]
theorem sectionsPullback_comp_sectionsDescend :
    (D.sectionsPullback I).comp (D.sectionsDescend I hinj ℓ hℓ) = ℓ :=
  LinearMap.comp_codLift _ _ _ _

/-- Pullback recovers each descended section. -/
@[simp]
theorem sectionsPullback_sectionsDescend (x : E) :
    D.sectionsPullback I (D.sectionsDescend I hinj ℓ hℓ x) = ℓ x :=
  LinearMap.congr_fun (D.sectionsPullback_comp_sectionsDescend I hinj ℓ hℓ) x

/-- Linear descent recovers the value at any copy of an original chamber. -/
theorem sectionsDescend_apply_right (x : E) (j : J.R) (a : D.chambers j) :
    (D.sectionsDescend I hinj ℓ hℓ x).val (.right j) = (ℓ x).val (.right ⟨j, a⟩) := by
  simpa only [MultispanIndex.multispan_obj_right, index_right,
    D.sectionsPullback_apply_right I] using
    congrArg (fun s : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      s.val (.right ⟨j, a⟩)) (D.sectionsPullback_sectionsDescend I hinj ℓ hℓ x)

/-- Linear descent recovers the value at any copy of an original face. -/
theorem sectionsDescend_apply_left (x : E) (b : J.L) (a : D.faces b) :
    (D.sectionsDescend I hinj ℓ hℓ x).val (.left b) = (ℓ x).val (.left (.inl ⟨b, a⟩)) := by
  simpa only [MultispanIndex.multispan_obj_left, index_left_inl,
    D.sectionsPullback_apply_left_inl I] using
    congrArg (fun s : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      s.val (.left (.inl ⟨b, a⟩))) (D.sectionsPullback_sectionsDescend I hinj ℓ hℓ x)

/-- A linear map is the descent exactly when its pullback is the supplied family. -/
theorem eq_sectionsDescend_iff
    (a : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan) :
    a = D.sectionsDescend I hinj ℓ hℓ ↔ (D.sectionsPullback I).comp a = ℓ := by
  rw [← LinearMap.cancel_left (D.sectionsPullback_injective_of_nonempty_faces I),
    D.sectionsPullback_comp_sectionsDescend I hinj ℓ hℓ]

omit ℓ hℓ in
/-- Descending the pullback of a linear family recovers that family. -/
@[simp]
theorem sectionsDescend_sectionsPullback_comp
    (a : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan)
    (ha : ∀ x j (c d : D.chambers j),
      ((D.sectionsPullback I).comp a x).val (.right ⟨j, c⟩) =
        ((D.sectionsPullback I).comp a x).val (.right ⟨j, d⟩)) :
    D.sectionsDescend I hinj ((D.sectionsPullback I).comp a) ha = a :=
  ((D.eq_sectionsDescend_iff I hinj _ ha a).mpr rfl).symm

end Descent

/-- A linear refined family whose chamber copies agree has a unique linear descent
when every chamber and face has a copy and the original face spans are jointly
injective. Recovery is equality of complete matching families, including every copied
face and identity face. -/
theorem existsUnique_sectionsPullback_comp_eq_of_chambers_eq [∀ b, Nonempty (D.faces b)]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    {E : Type*} [AddCommMonoid E] [Module R E]
    (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.index I).multispan)
    (hℓ : ∀ x j (c d : D.chambers j),
      (ℓ x).val (.right ⟨j, c⟩) = (ℓ x).val (.right ⟨j, d⟩)) :
    ∃! a : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
      (D.sectionsPullback I).comp a = ℓ := by
  refine ⟨D.sectionsDescend I hinj ℓ hℓ,
    D.sectionsPullback_comp_sectionsDescend I hinj ℓ hℓ, ?_⟩
  intro q hq
  apply LinearMap.ext
  intro x
  apply D.sectionsPullback_injective_of_nonempty_faces I
  exact (LinearMap.congr_fun hq x).trans
    (D.sectionsPullback_sectionsDescend I hinj ℓ hℓ x).symm

/-- Under chamber and face coverage and joint injectivity, a linear family has a unique
descent exactly when all of its chamber copies agree. -/
theorem existsUnique_sectionsPullback_comp_eq_iff [∀ b, Nonempty (D.faces b)]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    {E : Type*} [AddCommMonoid E] [Module R E]
    (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.index I).multispan) :
    (∃! a : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
      (D.sectionsPullback I).comp a = ℓ) ↔
      ∀ x j (c d : D.chambers j),
        (ℓ x).val (.right ⟨j, c⟩) = (ℓ x).val (.right ⟨j, d⟩) := by
  constructor
  · rintro ⟨a, ha, -⟩ x
    exact (D.mem_range_sectionsPullback_iff I hinj (ℓ x)).mp
      ⟨a x, LinearMap.congr_fun ha x⟩
  · exact D.existsUnique_sectionsPullback_comp_eq_of_chambers_eq I hinj ℓ

omit [∀ j, Nonempty (D.chambers j)] in
/-- If every face has a copy, identity graphs are connected and old spans are
jointly injective, every refined matching section descends without chamber coverage. -/
theorem sectionsPullback_surjective [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Surjective (D.sectionsPullback I) := by
  intro y
  apply D.exists_sectionsPullback_eq_of_chambers_eq I hinj y
  intro j c d
  have h := D.eq_of_eqvGen_edgeRel I ((D.index I).restrictSections y) j (hc j c d)
  simpa only [MultispanIndex.multispan_obj_right, index_right,
    (D.index I).restrictSections_apply] using h

/-- If every chamber and face has a copy, each chamber's identity-face graph is connected
and the original face spans are jointly injective, pullback of matching sections is a
linear equivalence. -/
noncomputable def sectionsEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    SemimoduleCat.sectionsSubmodule I.multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (D.index I).multispan :=
  LinearEquiv.ofBijective (D.sectionsPullback I)
    ⟨D.sectionsPullback_injective_of_nonempty_faces I, D.sectionsPullback_surjective I hc hinj⟩

/-- The underlying linear map of the section comparison is pullback. -/
@[simp]
theorem sectionsEquiv_toLinearMap [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    (D.sectionsEquiv I hc hinj).toLinearMap = D.sectionsPullback I := (rfl)

/-- The section comparison is the actual pullback along the incidence projection. -/
@[simp]
theorem sectionsEquiv_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    D.sectionsEquiv I hc hinj s = D.sectionsPullback I s := (rfl)

/-- Descent cancels section pullback. -/
@[simp]
theorem sectionsEquiv_symm_sectionsPullback [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    (D.sectionsEquiv I hc hinj).symm (D.sectionsPullback I s) = s :=
  (D.sectionsEquiv I hc hinj).symm_apply_apply s

/-- Section pullback cancels descent. -/
@[simp]
theorem sectionsPullback_sectionsEquiv_symm [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) :
    D.sectionsPullback I ((D.sectionsEquiv I hc hinj).symm s) = s :=
  (D.sectionsEquiv I hc hinj).apply_symm_apply s

/-- Restricting descended sections agrees with descending their chamber values. -/
@[simp]
theorem restrictSections_sectionsEquiv_symm [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) :
    I.restrictSections ((D.sectionsEquiv I hc hinj).symm s) =
      (D.compatibleEquiv I hc).symm ((D.index I).restrictSections s) := by
  apply D.compatibleMap_injective I
  rw [← restrictSections_sectionsPullback, sectionsPullback_sectionsEquiv_symm,
    compatibleMap_compatibleEquiv_symm]

omit [∀ j, Nonempty (D.chambers j)] in
/-- Reconstructing a matching section commutes with subdivision pullback. -/
theorem sectionsPullback_matchingFamilyEquiv_symm
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (x : I.compatibleFamilies) :
    D.sectionsPullback I ((I.matchingFamilyEquiv hinj).symm x) =
      ((D.index I).matchingFamilyEquiv (D.index_fst_prod_snd_injective I hinj)).symm
        (D.compatibleMap I x) := by
  apply (D.index I).restrictSections_injective (D.index_fst_prod_snd_injective I hinj)
  rw [restrictSections_sectionsPullback,
    ← I.matchingFamilyEquiv_apply hinj, LinearEquiv.apply_symm_apply,
    ← (D.index I).matchingFamilyEquiv_apply (D.index_fst_prod_snd_injective I hinj),
    LinearEquiv.apply_symm_apply]

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
theorem sectionsEquiv_symm_apply_left [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) (b : J.L)
    (a : D.faces b) :
    ((D.sectionsEquiv I hc hinj).symm s).val (.left b) = s.val (.left (.inl ⟨b, a⟩)) := by
  simpa only [MultispanIndex.multispan_obj_left, index_left_inl,
    sectionsEquiv_apply, sectionsPullback_apply_left_inl] using
    congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      z.val (.left (.inl ⟨b, a⟩))) ((D.sectionsEquiv I hc hinj).apply_symm_apply s)

end CategoryTheory.Limits.MultispanShape.Subdivision
