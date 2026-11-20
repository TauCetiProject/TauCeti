/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.SemimoduleCat.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Matching families for jointly injective spans

For an incidence diagram, regard the right objects as chamber modules and the left objects
as face modules. A matching section is determined by its chamber values when each pair of
face maps is jointly injective. Its possible chamber values are exactly those whose pairs
at every face lie in the range of the two face maps. `matchingFamilyEquiv` gives this as a
linear equivalence, with explicit chamber evaluations and equations characterizing the
reconstructed face values.

The incidence category is Mathlib's `WalkingMultispan`: its only nonidentity arrows are the
two incidences at each face. No finite index set, grading, or surjectivity of either leg is
required. We use `LinearEquiv.ofBijective` to equip restriction to chamber values with its
linear inverse; the compatible-family carrier is `SemimoduleCat.sectionsSubmodule`.

Linear chamber maps `α j : E →ₗ[R] I.right j` from an arbitrary semimodule whose incident
pairs lie in each span image assemble to a linear map `piCompatibleFamilies` into compatible
families. For jointly injective spans, `sectionsLift` glues them to a linear map into matching
sections whose face values map to the incident chamber values, and
`existsUnique_sections_lift_iff` shows that such a gluing exists, and is then
unique, precisely when every incident pair lies in the span image.

Natural transformations of the incidence diagrams transport compatible chamber
families and matching sections. Joint injectivity makes reconstruction of face
values commute with these coefficient changes, including maps with kernels.

Adapted from `yuma-mizuno-lean/Mei`, commit
`61509bfe75ce943898bc99cfa509fb40bb78c614`, under the Apache 2.0 license.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

variable {R : Type*} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (SemimoduleCat R))

/-- Chamber families whose incident pairs belong to the range of each face span. -/
def compatibleFamilies : Submodule R (∀ j, I.right j) :=
  ⨅ b, (LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)).comap
    ((LinearMap.proj (J.fst b)).prod (LinearMap.proj (J.snd b)))

/-- A compatible chamber family has a simultaneous preimage at every face. -/
@[simp]
theorem mem_compatibleFamilies {s : ∀ j, I.right j} :
    s ∈ I.compatibleFamilies ↔ ∀ b, ∃ x : I.left b,
      I.fst b x = s (J.fst b) ∧ I.snd b x = s (J.snd b) := by
  simp [compatibleFamilies, LinearMap.mem_range, Prod.ext_iff]

/-- Compatibility of a chamber family is membership of each incident pair in the span image. -/
theorem mem_compatibleFamilies_iff_forall_mem_range {s : ∀ j, I.right j} :
    s ∈ I.compatibleFamilies ↔ ∀ b, (s (J.fst b), s (J.snd b)) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom) := by
  simp [compatibleFamilies]

/-- Compatibility for a section of an incidence diagram is determined by its two kinds
of generating arrows. -/
@[simp high]
theorem mem_sectionsSubmodule_multispan {s : ∀ j, I.multispan.obj j} :
    s ∈ SemimoduleCat.sectionsSubmodule I.multispan ↔
      (∀ b, I.fst b (s (.left b)) = s (.right (J.fst b))) ∧
      (∀ b, I.snd b (s (.left b)) = s (.right (J.snd b))) := by
  rw [SemimoduleCat.mem_sectionsSubmodule]
  constructor
  · intro hs
    exact ⟨fun b => hs (WalkingMultispan.Hom.fst b),
      fun b => hs (WalkingMultispan.Hom.snd b)⟩
  · rintro ⟨hf, hg⟩ x y f
    cases f with
    | id x => simp
    | fst b => exact hf b
    | snd b => exact hg b

/-- Restrict a matching family to its chamber values. -/
def restrictSections : SemimoduleCat.sectionsSubmodule I.multispan →ₗ[R]
    I.compatibleFamilies where
  toFun s := ⟨fun j => s.val (.right j), (I.mem_compatibleFamilies).mpr fun b =>
    ⟨s.val (.left b), (I.mem_sectionsSubmodule_multispan.mp s.property).1 b,
      (I.mem_sectionsSubmodule_multispan.mp s.property).2 b⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction evaluates a section at its chamber object. -/
@[simp]
theorem restrictSections_apply (s : SemimoduleCat.sectionsSubmodule I.multispan) (j : J.R) :
    (I.restrictSections s).val j = s.val (.right j) := (rfl)

/-- Every compatible chamber family extends to a matching section. This existence statement
needs no injectivity; only uniqueness needs joint injectivity. -/
theorem restrictSections_surjective : Function.Surjective I.restrictSections := by
  classical
  intro s
  have hs := (I.mem_compatibleFamilies).mp s.property
  choose x hx hy using hs
  let t : ∀ j, I.multispan.obj j := fun j => match j with
    | .left b => x b
    | .right j => s.val j
  have ht : t ∈ SemimoduleCat.sectionsSubmodule I.multispan :=
    (I.mem_sectionsSubmodule_multispan).mpr ⟨hx, hy⟩
  exact ⟨⟨t, ht⟩, rfl⟩

/-- Jointly injective face spans make restriction to chambers injective. -/
theorem restrictSections_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Injective I.restrictSections := by
  intro s t hst
  have hr (j : J.R) : s.val (.right j) = t.val (.right j) :=
    congrArg (fun x : I.compatibleFamilies => x.val j) hst
  apply Subtype.ext
  funext j
  cases j with
  | right j => exact hr j
  | left b =>
    apply hinj b
    apply Prod.ext
    · exact ((I.mem_sectionsSubmodule_multispan.mp s.property).1 b).trans
        ((hr _).trans ((I.mem_sectionsSubmodule_multispan.mp t.property).1 b).symm)
    · exact ((I.mem_sectionsSubmodule_multispan.mp s.property).2 b).trans
        ((hr _).trans ((I.mem_sectionsSubmodule_multispan.mp t.property).2 b).symm)

/-- Linear maps into matching sections agree when all chamber components agree
and every face span is jointly injective. -/
theorem linearMap_ext_of_injective {E : Type*} [AddCommMonoid E] [Module R E]
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    {s t : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan}
    (h : ∀ a j, (s a).val (.right j) = (t a).val (.right j)) : s = t := by
  apply LinearMap.ext
  intro a
  apply I.restrictSections_injective hinj
  apply Subtype.ext
  funext j
  simp only [restrictSections_apply]
  exact h a j

/-- Matching sections are linearly equivalent to compatible chamber families when the
face maps are jointly injective. -/
noncomputable def matchingFamilyEquiv
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    SemimoduleCat.sectionsSubmodule I.multispan ≃ₗ[R] I.compatibleFamilies :=
  LinearEquiv.ofBijective I.restrictSections
    ⟨I.restrictSections_injective hinj, I.restrictSections_surjective⟩

/-- The equivalence forgets the face values. -/
@[simp]
theorem matchingFamilyEquiv_apply
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    I.matchingFamilyEquiv hinj s = I.restrictSections s := (rfl)

/-- Reconstructing a section retains the prescribed chamber values. -/
@[simp]
theorem matchingFamilyEquiv_symm_apply_right
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (j : J.R) :
    ((I.matchingFamilyEquiv hinj).symm s).val (.right j) = s.val j := by
  exact congrArg (fun x : I.compatibleFamilies => x.val j)
    ((I.matchingFamilyEquiv hinj).apply_symm_apply s)

/-- The reconstructed face value maps to the prescribed first chamber value. -/
@[simp]
theorem fst_matchingFamilyEquiv_symm_apply_left
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    I.fst b (((I.matchingFamilyEquiv hinj).symm s).val (.left b)) = s.val (J.fst b) := by
  exact ((I.mem_sectionsSubmodule_multispan.mp
    ((I.matchingFamilyEquiv hinj).symm s).property).1 b).trans
    (I.matchingFamilyEquiv_symm_apply_right hinj s _)

/-- The reconstructed face value maps to the prescribed second chamber value. -/
@[simp]
theorem snd_matchingFamilyEquiv_symm_apply_left
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    I.snd b (((I.matchingFamilyEquiv hinj).symm s).val (.left b)) = s.val (J.snd b) := by
  exact ((I.mem_sectionsSubmodule_multispan.mp
    ((I.matchingFamilyEquiv hinj).symm s).property).2 b).trans
    (I.matchingFamilyEquiv_symm_apply_right hinj s _)

section Lift

variable {E : Type*} [AddCommMonoid E] [Module R E] (α : ∀ j, E →ₗ[R] I.right j)

/-- Linear chamber maps whose incident pairs lie in each span image, assembled into a linear
map to compatible chamber families. -/
def piCompatibleFamilies
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) :
    E →ₗ[R] I.compatibleFamilies :=
  (LinearMap.pi α).codRestrict I.compatibleFamilies fun x =>
    I.mem_compatibleFamilies_iff_forall_mem_range.mpr (hα x)

/-- The assembled compatible family evaluates to the given chamber maps. -/
@[simp]
theorem piCompatibleFamilies_apply
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) (x : E) (j : J.R) :
    (I.piCompatibleFamilies α hα x).val j = α j x := (rfl)

/-- For jointly injective face spans, linear chamber maps whose incident pairs lie in each
span image glue to a linear map into matching sections. -/
noncomputable def sectionsLift
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) :
    E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan :=
  (I.matchingFamilyEquiv h).symm.toLinearMap ∘ₗ I.piCompatibleFamilies α hα

/-- The glued matching section has the given chamber values. -/
@[simp]
theorem sectionsLift_apply_right
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) (x : E) (j : J.R) :
    (I.sectionsLift α h hα x).val (.right j) = α j x :=
  I.matchingFamilyEquiv_symm_apply_right h _ j

/-- The glued matching section is the reconstruction of the assembled compatible family. -/
theorem sectionsLift_apply
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) (x : E) :
    I.sectionsLift α h hα x =
      (I.matchingFamilyEquiv h).symm (I.piCompatibleFamilies α hα x) := (rfl)

/-- The glued face value maps to the first incident chamber value. -/
@[simp]
theorem fst_sectionsLift_apply_left
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) (x : E) (b : J.L) :
    I.fst b ((I.sectionsLift α h hα x).val (.left b)) = α (J.fst b) x :=
  I.fst_matchingFamilyEquiv_symm_apply_left h _ b

/-- The glued face value maps to the second incident chamber value. -/
@[simp]
theorem snd_sectionsLift_apply_left
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hα : ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)) (x : E) (b : J.L) :
    I.snd b ((I.sectionsLift α h hα x).val (.left b)) = α (J.snd b) x :=
  I.snd_matchingFamilyEquiv_symm_apply_left h _ b

/-- When each face span is jointly injective, linear chamber maps `α` extend uniquely to a
linear map into matching sections iff every incident pair `(α (fst b) x, α (snd b) x)` lies in
the range of the span. The extension is then `sectionsLift`. -/
theorem existsUnique_sections_lift_iff
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    (∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
        ∀ x j, (ℓ x).val (.right j) = α j x) ↔
      ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
        LinearMap.range ((I.fst b).hom.prod (I.snd b).hom) := by
  constructor
  · rintro ⟨ℓ, hℓ, -⟩ x b
    simpa only [restrictSections_apply, hℓ] using
      I.mem_compatibleFamilies_iff_forall_mem_range.mp (I.restrictSections (ℓ x)).property b
  intro hα
  refine ⟨I.sectionsLift α h hα, I.sectionsLift_apply_right α h hα, fun ℓ hℓ => ?_⟩
  ext x : 1
  apply I.restrictSections_injective h
  ext j
  simp [hℓ]

end Lift

/-- A face value is the reconstructed common lift exactly when its two images are the
prescribed chamber values. Joint injectivity gives uniqueness of this lift. -/
theorem eq_matchingFamilyEquiv_symm_apply_left_iff
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) {x : I.left b} :
    x = ((I.matchingFamilyEquiv hinj).symm s).val (.left b) ↔
      I.fst b x = s.val (J.fst b) ∧ I.snd b x = s.val (J.snd b) := by
  refine ⟨by rintro rfl; simp, fun h => hinj b (Prod.ext ?_ ?_)⟩
  · exact h.1.trans (I.fst_matchingFamilyEquiv_symm_apply_left hinj s b).symm
  · exact h.2.trans (I.snd_matchingFamilyEquiv_symm_apply_left hinj s b).symm

section Maps

variable {I} {I' I'' : MultispanIndex J (SemimoduleCat R)}

/-- A natural transformation carries compatible chamber values to compatible values. -/
def compatibleFamiliesMap (α : I.multispan ⟶ I'.multispan) :
    I.compatibleFamilies →ₗ[R] I'.compatibleFamilies where
  toFun x := by
    refine ⟨fun j => (α.app (.right j)).hom (x.val j), ?_⟩
    obtain ⟨s, rfl⟩ := I.restrictSections_surjective x
    have he : (fun j => (α.app (.right j)).hom ((I.restrictSections s).val j)) =
        (I'.restrictSections (SemimoduleCat.sectionsMap α s)).val := by
      funext j
      simp
    exact he.symm ▸ (I'.restrictSections (SemimoduleCat.sectionsMap α s)).property
  map_add' x y := by ext j; exact map_add (α.app (.right j)).hom _ _
  map_smul' r x := by ext j; exact map_smul (α.app (.right j)).hom r _

/-- Compatible-family transport acts by each chamber's coefficient map. -/
@[simp]
theorem compatibleFamiliesMap_apply (α : I.multispan ⟶ I'.multispan)
    (x : I.compatibleFamilies) (j : J.R) :
    (compatibleFamiliesMap α x).val j = (α.app (.right j)).hom (x.val j) := (rfl)

/-- Identity transformations fix compatible chamber families. -/
@[simp]
theorem compatibleFamiliesMap_id :
    compatibleFamiliesMap (𝟙 I.multispan) = LinearMap.id := by
  ext x j
  rfl

/-- Transport of compatible families respects composition. -/
@[simp]
theorem compatibleFamiliesMap_comp (α : I.multispan ⟶ I'.multispan)
    (β : I'.multispan ⟶ I''.multispan) :
    compatibleFamiliesMap (α ≫ β) =
      (compatibleFamiliesMap β).comp (compatibleFamiliesMap α) := by
  ext x j
  rfl

/-- Restriction to chamber values commutes with coefficient changes. -/
theorem restrictSections_naturality (α : I.multispan ⟶ I'.multispan) :
    I'.restrictSections.comp (SemimoduleCat.sectionsMap α) =
      (compatibleFamiliesMap α).comp I.restrictSections := by
  ext x j
  simp

/-- Reconstructing the face values commutes with coefficient changes whenever
both sets of face spans are jointly injective. Individual legs may have kernels. -/
theorem matchingFamilyEquiv_symm_naturality
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (hinj' : ∀ b, Function.Injective ((I'.fst b).hom.prod (I'.snd b).hom))
    (α : I.multispan ⟶ I'.multispan) (x : I.compatibleFamilies) :
    SemimoduleCat.sectionsMap α ((I.matchingFamilyEquiv hinj).symm x) =
      (I'.matchingFamilyEquiv hinj').symm (compatibleFamiliesMap α x) := by
  apply I'.restrictSections_injective hinj'
  ext j
  simp

end Maps

end CategoryTheory.Limits.MultispanIndex
