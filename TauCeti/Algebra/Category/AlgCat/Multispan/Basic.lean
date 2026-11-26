/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.AlgCat.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.Algebra.Algebra.Prod
public import TauCeti.Algebra.Category.SemimoduleCat.Multispan.Basic

/-!
# Algebra-valued matching families

For a diagram of spans of algebras, compatible chamber values are those for which
each pair of incident values belongs to the range of the corresponding span.
Restriction from sections is an algebra homomorphism. Joint injectivity of each
span gives an algebra equivalence, so reconstruction preserves multiplication
as well as the underlying linear operations.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e`, under the Apache 2.0 license.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

universe u v w t

variable {R : Type u} [CommRing R] {J : MultispanShape.{v, w}}
  (I : MultispanIndex J (AlgCat.{t} R))

/-- Chamber values whose incident pairs lie in the ranges of the face spans. -/
def compatibleAlgebraFamilies : Subalgebra R (∀ b, I.right b) :=
  ⨅ a, ((I.fst a).hom.prod (I.snd a).hom).range.comap
    ((Pi.evalAlgHom R (fun b => I.right b) (J.fst a)).prod
      (Pi.evalAlgHom R (fun b => I.right b) (J.snd a)))

/-- Each face span must have a common preimage for the two incident values. -/
@[simp]
theorem mem_compatibleAlgebraFamilies {x : ∀ b, I.right b} :
    x ∈ I.compatibleAlgebraFamilies ↔
      ∀ a, (x (J.fst a), x (J.snd a)) ∈ ((I.fst a).hom.prod (I.snd a).hom).range := by
  simp [compatibleAlgebraFamilies]

/-- Matching algebra sections of a multispan are characterized by their two incident equations. -/
@[simp high]
theorem mem_sectionsSubalgebra_multispan {x : ∀ j, I.multispan.obj j} :
    x ∈ AlgCat.sectionsSubalgebra I.multispan ↔
      (∀ a, (I.fst a).hom (x (.left a)) = x (.right (J.fst a))) ∧
      (∀ a, (I.snd a).hom (x (.left a)) = x (.right (J.snd a))) := by
  rw [AlgCat.mem_sectionsSubalgebra]
  have hfmap (a : J.L) := congrArg
    (fun f : I.left a ⟶ I.right (J.fst a) => f.hom (x (.left a))) (I.multispan_map_fst a)
  have hgmap (a : J.L) := congrArg
    (fun f : I.left a ⟶ I.right (J.snd a) => f.hom (x (.left a))) (I.multispan_map_snd a)
  constructor
  · intro hx
    exact ⟨fun a => (hfmap a).symm.trans (hx (.fst a)),
      fun a => (hgmap a).symm.trans (hx (.snd a))⟩
  · rintro ⟨hf, hg⟩ j j' f
    cases f with
    | id j => simp
    | fst a => exact (hfmap a).trans (hf a)
    | snd a => exact (hgmap a).trans (hg a)

/-- Restriction from matching sections to their compatible chamber values. -/
def restrictAlgebraSections : AlgCat.sectionsSubalgebra I.multispan →ₐ[R]
    I.compatibleAlgebraFamilies where
  toFun x := ⟨fun b => x.val (.right b), I.mem_compatibleAlgebraFamilies.mpr fun a =>
    ⟨x.val (.left a), Prod.ext ((I.mem_sectionsSubalgebra_multispan.mp x.property).1 a)
      ((I.mem_sectionsSubalgebra_multispan.mp x.property).2 a)⟩⟩
  map_zero' := by ext b; rfl
  map_one' := by ext b; rfl
  map_add' _ _ := by ext b; rfl
  map_mul' _ _ := by ext b; rfl
  commutes' _ := by ext b; rfl

/-- Restriction reads the section at each chamber object. -/
@[simp]
theorem restrictAlgebraSections_apply (s : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.restrictAlgebraSections s).val b = s.val (.right b) := (rfl)

/-- The underlying semimodule diagram has the same objects and linear incidence maps. -/
abbrev asSemimoduleIndex : MultispanIndex J (SemimoduleCat.{t} R) where
  left a := SemimoduleCat.of R (I.left a)
  right b := SemimoduleCat.of R (I.right b)
  fst a := SemimoduleCat.ofHom (I.fst a).hom.toLinearMap
  snd a := SemimoduleCat.ofHom (I.snd a).hom.toLinearMap

/-- The underlying linear fst incidence map acts by the corresponding algebra map. -/
theorem asSemimoduleIndex_fst_apply (a : J.L) (x : I.left a) :
    (I.asSemimoduleIndex.fst a).hom x = (I.fst a).hom x := by
  simp only [asSemimoduleIndex, SemimoduleCat.hom_ofHom]
  exact AlgHom.toLinearMap_apply _ _

/-- The underlying linear snd incidence map acts by the corresponding algebra map. -/
theorem asSemimoduleIndex_snd_apply (a : J.L) (x : I.left a) :
    (I.asSemimoduleIndex.snd a).hom x = (I.snd a).hom x := by
  simp only [asSemimoduleIndex, SemimoduleCat.hom_ofHom]
  exact AlgHom.toLinearMap_apply _ _

private theorem asSemimoduleIndex_span_apply (a : J.L) (x : I.left a) :
    ((I.asSemimoduleIndex.fst a).hom.prod (I.asSemimoduleIndex.snd a).hom) x =
      ((I.fst a).hom.prod (I.snd a).hom) x := by
  rw [LinearMap.prod_apply, Function.prod_apply, AlgHom.prod_apply]
  exact Prod.ext (I.asSemimoduleIndex_fst_apply a x) (I.asSemimoduleIndex_snd_apply a x)

/-- The two incidence maps are jointly injective exactly when their underlying linear maps are. -/
theorem asSemimoduleIndex_span_injective_iff (a : J.L) :
    Function.Injective ((I.asSemimoduleIndex.fst a).hom.prod (I.asSemimoduleIndex.snd a).hom) ↔
      Function.Injective ((I.fst a).hom.prod (I.snd a).hom) := by
  have h (x : I.left a) := I.asSemimoduleIndex_span_apply a x
  constructor
  · intro hinj x y hxy
    exact hinj ((h x).trans (hxy.trans (h y).symm))
  · intro hinj x y hxy
    exact hinj ((h x).symm.trans (hxy.trans (h y)))

/-- Forgetting the algebra multispan gives the multispan of the underlying semimodule index. -/
def asSemimoduleIndexIso :
    (I.multispan ⋙ forget₂ (AlgCat R) (ModuleCat R) ⋙ ModuleCat.equivalenceSemimoduleCat.functor) ≅
      I.asSemimoduleIndex.multispan :=
  -- At each incidence, the forgotten algebra map is the underlying linear map.
  WalkingMultispan.functorExt (fun _ => Iso.refl _) (fun _ => Iso.refl _)
    (fun a => by
      simp only [Iso.refl_hom, Functor.comp_map, multispan_map_fst]
      rfl)
    (fun a => by
      simp only [Iso.refl_hom, Functor.comp_map, multispan_map_snd]
      rfl)

-- The two object families agree definitionally at each constructor.
-- WalkingMultispan.functorExt uses the supplied reflexive isomorphism at that component.

/-- The forward comparison is the identity at a face. -/
@[simp]
theorem asSemimoduleIndexIso_hom_app_left (a : J.L) :
    I.asSemimoduleIndexIso.hom.app (.left a) = 𝟙 (SemimoduleCat.of R (I.left a)) :=
  (rfl)

/-- The forward comparison is the identity at a chamber. -/
@[simp]
theorem asSemimoduleIndexIso_hom_app_right (b : J.R) :
    I.asSemimoduleIndexIso.hom.app (.right b) = 𝟙 (SemimoduleCat.of R (I.right b)) :=
  (rfl)

/-- The inverse comparison is the identity at a face. -/
@[simp]
theorem asSemimoduleIndexIso_inv_app_left (a : J.L) :
    I.asSemimoduleIndexIso.inv.app (.left a) = 𝟙 (SemimoduleCat.of R (I.left a)) :=
  (rfl)

/-- The inverse comparison is the identity at a chamber. -/
@[simp]
theorem asSemimoduleIndexIso_inv_app_right (b : J.R) :
    I.asSemimoduleIndexIso.inv.app (.right b) = 𝟙 (SemimoduleCat.of R (I.right b)) :=
  (rfl)

/-- The algebra sections and the sections of the underlying semimodule diagram
are linearly equivalent via their unchanged components. -/
def multispanSectionsLinearEquiv : AlgCat.sectionsSubalgebra I.multispan ≃ₗ[R]
    SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan :=
  (AlgCat.sectionsLinearEquiv I.multispan).trans
    (SemimoduleCat.sectionsLinearEquivOfIso I.asSemimoduleIndexIso)

/-- The comparison of sections preserves a face component. -/
@[simp]
theorem multispanSectionsLinearEquiv_apply_left
    (s : AlgCat.sectionsSubalgebra I.multispan) (a : J.L) :
    (I.multispanSectionsLinearEquiv s).val (.left a) = s.val (.left a) := by
  simp [multispanSectionsLinearEquiv]
  -- The linear map underlying the categorical identity is the linear identity.
  rfl

/-- The comparison of sections preserves a chamber component. -/
@[simp]
theorem multispanSectionsLinearEquiv_apply_right
    (s : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.multispanSectionsLinearEquiv s).val (.right b) = s.val (.right b) := by
  simp [multispanSectionsLinearEquiv]
  -- The linear map underlying the categorical identity is the linear identity.
  rfl

/-- The inverse comparison of sections preserves a face component. -/
@[simp]
theorem multispanSectionsLinearEquiv_symm_apply_left
    (s : SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan) (a : J.L) :
    (I.multispanSectionsLinearEquiv.symm s).val (.left a) = s.val (.left a) := by
  simp [multispanSectionsLinearEquiv]
  -- The linear map underlying the categorical identity is the linear identity.
  rfl

/-- The inverse comparison of sections preserves a chamber component. -/
@[simp]
theorem multispanSectionsLinearEquiv_symm_apply_right
    (s : SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan) (b : J.R) :
    (I.multispanSectionsLinearEquiv.symm s).val (.right b) = s.val (.right b) := by
  simp [multispanSectionsLinearEquiv]
  -- The linear map underlying the categorical identity is the linear identity.
  rfl

/-- A chamber family is compatible over the algebras exactly when it is compatible over
their underlying semimodules. -/
theorem mem_compatibleFamilies_asSemimoduleIndex_iff {x : ∀ b, I.right b} :
    x ∈ I.asSemimoduleIndex.compatibleFamilies ↔ x ∈ I.compatibleAlgebraFamilies := by
  rw [I.asSemimoduleIndex.mem_compatibleFamilies_iff_forall_mem_range,
    I.mem_compatibleAlgebraFamilies]
  constructor
  · intro hx a
    obtain ⟨y, hy⟩ := hx a
    exact ⟨y, (I.asSemimoduleIndex_span_apply a y).symm.trans hy⟩
  · intro hx a
    obtain ⟨y, hy⟩ := hx a
    exact ⟨y, (I.asSemimoduleIndex_span_apply a y).trans hy⟩

/-- Compatible algebra chamber families and the underlying linear families
are linearly equivalent via their unchanged chamber values. -/
def compatibleAlgebraFamiliesLinearEquiv :
    I.compatibleAlgebraFamilies ≃ₗ[R] I.asSemimoduleIndex.compatibleFamilies where
  toFun x := ⟨x.val, I.mem_compatibleFamilies_asSemimoduleIndex_iff.mpr x.property⟩
  invFun x := ⟨x.val, I.mem_compatibleFamilies_asSemimoduleIndex_iff.mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The comparison of compatible families preserves each chamber value. -/
@[simp]
theorem compatibleAlgebraFamiliesLinearEquiv_apply (x : I.compatibleAlgebraFamilies) (b : J.R) :
    (I.compatibleAlgebraFamiliesLinearEquiv x).val b = x.val b := (rfl)

/-- The inverse comparison of compatible families preserves each chamber value. -/
@[simp]
theorem compatibleAlgebraFamiliesLinearEquiv_symm_apply
    (x : I.asSemimoduleIndex.compatibleFamilies) (b : J.R) :
    (I.compatibleAlgebraFamiliesLinearEquiv.symm x).val b = x.val b := (rfl)

/-- The algebraic and linear restriction maps agree under the componentwise comparisons. -/
theorem restrictAlgebraSections_linearComparison :
    I.compatibleAlgebraFamiliesLinearEquiv.toLinearMap.comp I.restrictAlgebraSections.toLinearMap =
      I.asSemimoduleIndex.restrictSections.comp I.multispanSectionsLinearEquiv.toLinearMap := by
  ext s b
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, AlgHom.toLinearMap_apply,
    compatibleAlgebraFamiliesLinearEquiv_apply, restrictAlgebraSections_apply,
    restrictSections_apply, multispanSectionsLinearEquiv_apply_right]
  -- The semimodule carrier at the right object is definitionally its algebra carrier.
  rfl

/-- Under joint injectivity, the chamber values determine the entire section. -/
theorem restrictAlgebraSections_injective
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    Function.Injective I.restrictAlgebraSections := by
  intro s t h
  have square (x : AlgCat.sectionsSubalgebra I.multispan) :=
    LinearMap.congr_fun I.restrictAlgebraSections_linearComparison x
  apply I.multispanSectionsLinearEquiv.injective
  apply I.asSemimoduleIndex.restrictSections_injective
    (fun a => (I.asSemimoduleIndex_span_injective_iff a).mpr (hinj a))
  exact (square s).symm.trans
    ((congrArg I.compatibleAlgebraFamiliesLinearEquiv h).trans (square t))

/-- Every compatible chamber family admits a matching extension. -/
theorem restrictAlgebraSections_surjective :
    Function.Surjective I.restrictAlgebraSections := by
  intro x
  obtain ⟨s, hs⟩ := I.asSemimoduleIndex.restrictSections_surjective
    (I.compatibleAlgebraFamiliesLinearEquiv x)
  refine ⟨I.multispanSectionsLinearEquiv.symm s,
    I.compatibleAlgebraFamiliesLinearEquiv.injective ?_⟩
  have square := LinearMap.congr_fun I.restrictAlgebraSections_linearComparison
    (I.multispanSectionsLinearEquiv.symm s)
  exact square.trans (by simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using hs)

/-- For jointly injective spans, restriction to chamber values is an algebra equivalence. -/
noncomputable def matchingFamilyAlgEquiv
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    AlgCat.sectionsSubalgebra I.multispan ≃ₐ[R] I.compatibleAlgebraFamilies :=
  AlgEquiv.ofBijective I.restrictAlgebraSections
    ⟨I.restrictAlgebraSections_injective hinj, I.restrictAlgebraSections_surjective⟩

/-- The bundled forward algebra homomorphism is restriction to chamber values. -/
@[simp]
theorem matchingFamilyAlgEquiv_toAlgHom
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    (I.matchingFamilyAlgEquiv hinj).toAlgHom = I.restrictAlgebraSections :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- The forward equivalence restricts to the chamber values. -/
@[simp]
theorem matchingFamilyAlgEquiv_apply
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (s : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.matchingFamilyAlgEquiv hinj s).val b = s.val (.right b) := by
  rw [← AlgEquiv.coe_toAlgHom, matchingFamilyAlgEquiv_toAlgHom, restrictAlgebraSections_apply]

/-- Restricting a reconstructed section recovers the original compatible family. -/
@[simp]
theorem restrictAlgebraSections_matchingFamilyAlgEquiv_symm_apply
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) :
    I.restrictAlgebraSections ((I.matchingFamilyAlgEquiv hinj).symm x) = x := by
  rw [← I.matchingFamilyAlgEquiv_toAlgHom hinj, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]

/-- The reconstructed section has the prescribed value at each chamber. -/
@[simp]
theorem matchingFamilyAlgEquiv_symm_apply_right
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) (b : J.R) :
    ((I.matchingFamilyAlgEquiv hinj).symm x).val (.right b) = x.val b := by
  have h := congrArg (fun z : I.compatibleAlgebraFamilies => z.val b)
    (I.restrictAlgebraSections_matchingFamilyAlgEquiv_symm_apply hinj x)
  rw [restrictAlgebraSections_apply] at h
  -- The right object of the walking multispan uses the given chamber carrier.
  exact h

/-- Chamber algebra maps compatible with every face span lift to algebra sections. -/
noncomputable def algebraSectionsLift {E : Type*} [Semiring E] [Algebra R E]
    (α : ∀ b, E →ₐ[R] I.right b)
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (hα : ∀ x a, (α (J.fst a) x, α (J.snd a) x) ∈
      ((I.fst a).hom.prod (I.snd a).hom).range) :
    E →ₐ[R] AlgCat.sectionsSubalgebra I.multispan :=
  (I.matchingFamilyAlgEquiv hinj).symm.toAlgHom.comp
    ((AlgHom.pi α).codRestrict I.compatibleAlgebraFamilies
      fun x => I.mem_compatibleAlgebraFamilies.mpr (hα x))

/-- The bundled lift evaluates to the prescribed algebra map at each chamber. -/
@[simp]
theorem algebraSectionsLift_apply_right {E : Type*} [Semiring E] [Algebra R E]
    (α : ∀ b, E →ₐ[R] I.right b)
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (hα : ∀ x a, (α (J.fst a) x, α (J.snd a) x) ∈
      ((I.fst a).hom.prod (I.snd a).hom).range) (x : E) (b : J.R) :
    (I.algebraSectionsLift α hinj hα x).val (.right b) = α b x := by
  simp only [algebraSectionsLift, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    matchingFamilyAlgEquiv_symm_apply_right, AlgHom.coe_codRestrict, AlgHom.pi_apply]
  -- The right entry of the multispan has the specified chamber carrier.
  rfl

/-- Jointly injective incident pairs let chamber algebra maps glue uniquely to an algebra map
to the sections precisely when each incident pair is in the range of its span. -/
theorem existsUnique_algebraSections_lift_iff {E : Type*} [Semiring E] [Algebra R E]
    (α : ∀ b, E →ₐ[R] I.right b)
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    (∃! ℓ : E →ₐ[R] AlgCat.sectionsSubalgebra I.multispan,
        ∀ x b, (ℓ x).val (.right b) = α b x) ↔
      ∀ x a, (α (J.fst a) x, α (J.snd a) x) ∈
        ((I.fst a).hom.prod (I.snd a).hom).range := by
  constructor
  · rintro ⟨ℓ, hℓ, -⟩ x a
    simpa only [restrictAlgebraSections_apply, hℓ] using
      I.mem_compatibleAlgebraFamilies.mp (I.restrictAlgebraSections (ℓ x)).property a
  · intro hα
    refine ⟨I.algebraSectionsLift α hinj hα, I.algebraSectionsLift_apply_right α hinj hα, ?_⟩
    intro ℓ hℓ
    ext x : 1
    apply I.restrictAlgebraSections_injective hinj
    apply Subtype.ext
    funext b
    simp only [restrictAlgebraSections_apply, hℓ, algebraSectionsLift_apply_right]

/-- The first incident map sends a reconstructed face to its prescribed chamber value. -/
@[simp]
theorem fst_matchingFamilyAlgEquiv_symm_apply_left
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) (a : J.L) :
    (I.fst a).hom (((I.matchingFamilyAlgEquiv hinj).symm x).val (.left a)) =
      x.val (J.fst a) :=
  ((I.mem_sectionsSubalgebra_multispan.mp
    ((I.matchingFamilyAlgEquiv hinj).symm x).property).1 a).trans
    (I.matchingFamilyAlgEquiv_symm_apply_right hinj x (J.fst a))

/-- The second incident map sends a reconstructed face to its prescribed chamber value. -/
@[simp]
theorem snd_matchingFamilyAlgEquiv_symm_apply_left
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) (a : J.L) :
    (I.snd a).hom (((I.matchingFamilyAlgEquiv hinj).symm x).val (.left a)) =
      x.val (J.snd a) :=
  ((I.mem_sectionsSubalgebra_multispan.mp
    ((I.matchingFamilyAlgEquiv hinj).symm x).property).2 a).trans
    (I.matchingFamilyAlgEquiv_symm_apply_right hinj x (J.snd a))

/-- The reconstructed value at a face is the unique common lift of the two incident values. -/
theorem eq_matchingFamilyAlgEquiv_symm_apply_left_iff
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) (a : J.L) {y : I.left a} :
    y = ((I.matchingFamilyAlgEquiv hinj).symm x).val (.left a) ↔
      (I.fst a).hom y = x.val (J.fst a) ∧ (I.snd a).hom y = x.val (J.snd a) := by
  have hf := I.fst_matchingFamilyAlgEquiv_symm_apply_left hinj x a
  have hg := I.snd_matchingFamilyAlgEquiv_symm_apply_left hinj x a
  exact ⟨by rintro rfl; exact ⟨hf, hg⟩, fun h =>
    hinj a (Prod.ext (h.1.trans hf.symm) (h.2.trans hg.symm))⟩

section Maps

variable {I} {I' I'' : MultispanIndex J (AlgCat.{t} R)}

/-- A map of span diagrams transports compatible families componentwise. -/
def compatibleAlgebraFamiliesMap (α : I.multispan ⟶ I'.multispan) :
    I.compatibleAlgebraFamilies →ₐ[R] I'.compatibleAlgebraFamilies where
  toFun x := by
    refine ⟨fun b => (α.app (.right b)).hom (x.val b), ?_⟩
    obtain ⟨s, rfl⟩ := I.restrictAlgebraSections_surjective x
    have hvalues :
        (fun b => (α.app (.right b)).hom ((I.restrictAlgebraSections s).val b)) =
          (I'.restrictAlgebraSections (AlgCat.sectionsMap α s)).val := by
      funext b
      simp only [restrictAlgebraSections_apply, AlgCat.sectionsMap_apply]
    rw [hvalues]
    exact (I'.restrictAlgebraSections (AlgCat.sectionsMap α s)).property
  map_zero' := by ext b; exact map_zero (α.app (.right b)).hom
  map_one' := by ext b; exact map_one (α.app (.right b)).hom
  map_add' x y := by ext b; exact map_add (α.app (.right b)).hom _ _
  map_mul' x y := by ext b; exact map_mul (α.app (.right b)).hom _ _
  commutes' r := by ext b; exact (α.app (.right b)).hom.commutes r

/-- The transport of a family acts by the coefficient map at each chamber. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_apply (α : I.multispan ⟶ I'.multispan)
    (x : I.compatibleAlgebraFamilies) (b : J.R) :
    (compatibleAlgebraFamiliesMap α x).val b = (α.app (.right b)).hom (x.val b) := (rfl)

/-- Restriction commutes with coefficient transport as an equality of algebra homomorphisms.
No injectivity hypothesis is required. -/
theorem restrictAlgebraSections_naturality (α : I.multispan ⟶ I'.multispan) :
    I'.restrictAlgebraSections.comp (AlgCat.sectionsMap α) =
      (compatibleAlgebraFamiliesMap α).comp I.restrictAlgebraSections := by
  ext s b
  simp only [AlgHom.comp_apply, restrictAlgebraSections_apply,
    AlgCat.sectionsMap_apply, compatibleAlgebraFamiliesMap_apply]
  -- The right object of the multispan is definitionally the chamber algebra.
  rfl

private theorem restrictAlgebraSections_naturality_apply
    (α : I.multispan ⟶ I'.multispan) (s : AlgCat.sectionsSubalgebra I.multispan) :
    I'.restrictAlgebraSections (AlgCat.sectionsMap α s) =
      compatibleAlgebraFamiliesMap α (I.restrictAlgebraSections s) :=
  AlgHom.congr_fun (restrictAlgebraSections_naturality α) s

/-- Identity coefficient maps fix compatible algebra families. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_id :
    compatibleAlgebraFamiliesMap (𝟙 I.multispan) = AlgHom.id R _ := by
  ext x : 1
  obtain ⟨s, rfl⟩ := I.restrictAlgebraSections_surjective x
  simpa only [AlgCat.sectionsMap_id, AlgHom.id_apply] using
    (restrictAlgebraSections_naturality_apply (𝟙 I.multispan) s).symm

/-- Compatible-family transport respects composition of coefficient maps. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_comp (α : I.multispan ⟶ I'.multispan)
    (β : I'.multispan ⟶ I''.multispan) :
    compatibleAlgebraFamiliesMap (α ≫ β) =
      (compatibleAlgebraFamiliesMap β).comp (compatibleAlgebraFamiliesMap α) := by
  ext x : 1
  obtain ⟨s, rfl⟩ := I.restrictAlgebraSections_surjective x
  rw [← restrictAlgebraSections_naturality_apply (α ≫ β), AlgCat.sectionsMap_comp,
    AlgHom.comp_apply, restrictAlgebraSections_naturality_apply β,
    restrictAlgebraSections_naturality_apply α, AlgHom.comp_apply]

/-- Inverse reconstruction commutes with coefficient changes as a bundled algebra map. -/
theorem matchingFamilyAlgEquiv_symm_naturality
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (hinj' : ∀ a, Function.Injective ((I'.fst a).hom.prod (I'.snd a).hom))
    (α : I.multispan ⟶ I'.multispan) :
    (AlgCat.sectionsMap α).comp (I.matchingFamilyAlgEquiv hinj).symm.toAlgHom =
      (I'.matchingFamilyAlgEquiv hinj').symm.toAlgHom.comp (compatibleAlgebraFamiliesMap α) := by
  ext x : 1
  apply I'.restrictAlgebraSections_injective hinj'
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    restrictAlgebraSections_matchingFamilyAlgEquiv_symm_apply] using
    restrictAlgebraSections_naturality_apply α ((I.matchingFamilyAlgEquiv hinj).symm x)

end Maps

end CategoryTheory.Limits.MultispanIndex
