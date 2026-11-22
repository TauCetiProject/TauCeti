/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.AlgCat.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.Algebra.Algebra.Prod
import TauCeti.Algebra.Category.SemimoduleCat.Multispan.Basic

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

/-- Compatible families form the meet of the comaps of the face-span ranges. -/
theorem compatibleAlgebraFamilies_def :
    I.compatibleAlgebraFamilies =
      ⨅ a, ((I.fst a).hom.prod (I.snd a).hom).range.comap
        ((Pi.evalAlgHom R (fun b => I.right b) (J.fst a)).prod
          (Pi.evalAlgHom R (fun b => I.right b) (J.snd a))) := (rfl)

/-- Each face span must have a common preimage for the two incident values. -/
@[simp]
theorem mem_compatibleAlgebraFamilies {x : ∀ b, I.right b} :
    x ∈ I.compatibleAlgebraFamilies ↔
      ∀ a, (x (J.fst a), x (J.snd a)) ∈ ((I.fst a).hom.prod (I.snd a).hom).range := by
  simp [compatibleAlgebraFamilies]

private theorem mem_sectionsSubalgebra_multispan {x : ∀ j, I.multispan.obj j} :
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

private def asSemimoduleIndex : MultispanIndex J (SemimoduleCat.{t} R) where
  left a := SemimoduleCat.of R (I.left a)
  right b := SemimoduleCat.of R (I.right b)
  fst a := SemimoduleCat.ofHom (I.fst a).hom.toLinearMap
  snd a := SemimoduleCat.ofHom (I.snd a).hom.toLinearMap

private theorem asSemimoduleIndex_span_apply (a : J.L) (x : I.left a) :
    ((I.asSemimoduleIndex.fst a).hom.prod (I.asSemimoduleIndex.snd a).hom) x =
      ((I.fst a).hom.prod (I.snd a).hom) x := by
  -- The private index changes the bundled objects and their inferred module instances.
  -- Rewriting applications cannot align those instances until this carrier is normalized.
  change ((I.fst a).hom.toLinearMap.prod (I.snd a).hom.toLinearMap) x =
    ((I.fst a).hom.prod (I.snd a).hom) x
  simp only [LinearMap.prod_apply, Function.prod_apply, AlgHom.prod_apply]
  exact Prod.ext ((I.fst a).hom.toLinearMap_apply x) ((I.snd a).hom.toLinearMap_apply x)


private def toLinearSection (s : AlgCat.sectionsSubalgebra I.multispan) :
    SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan :=
  ⟨fun j => match j with
    | .left a => (AlgCat.sectionsLinearEquiv I.multispan s).val (.left a)
    | .right b => (AlgCat.sectionsLinearEquiv I.multispan s).val (.right b), by
      apply I.asSemimoduleIndex.mem_sectionsSubmodule_multispan.mpr
      have hs := I.mem_sectionsSubalgebra_multispan.mp s.property
      constructor
      · intro a
        -- Normalize only the local index wrapper before using the public application equations.
        change (I.fst a).hom.toLinearMap
          ((AlgCat.sectionsLinearEquiv I.multispan s).val (.left a)) =
            (AlgCat.sectionsLinearEquiv I.multispan s).val (.right (J.fst a))
        simp only [AlgCat.sectionsLinearEquiv_apply]
        exact ((I.fst a).hom.toLinearMap_apply (s.val (.left a))).trans (hs.1 a)
      · intro a
        change (I.snd a).hom.toLinearMap
          ((AlgCat.sectionsLinearEquiv I.multispan s).val (.left a)) =
            (AlgCat.sectionsLinearEquiv I.multispan s).val (.right (J.snd a))
        simp only [AlgCat.sectionsLinearEquiv_apply]
        exact ((I.snd a).hom.toLinearMap_apply (s.val (.left a))).trans (hs.2 a)⟩


private theorem toLinearSection_apply_left
    (s : AlgCat.sectionsSubalgebra I.multispan) (a : J.L) :
    (I.toLinearSection s).val (.left a) = s.val (.left a) :=
  AlgCat.sectionsLinearEquiv_apply I.multispan s (.left a)

private theorem toLinearSection_apply_right
    (s : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.toLinearSection s).val (.right b) = s.val (.right b) :=
  AlgCat.sectionsLinearEquiv_apply I.multispan s (.right b)

private def toAlgebraSection (s : SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan) :
    AlgCat.sectionsSubalgebra I.multispan :=
  ⟨fun j => match j with
    | .left a => s.val (.left a)
    | .right b => s.val (.right b), by
      apply I.mem_sectionsSubalgebra_multispan.mpr
      obtain ⟨hf, hg⟩ := I.asSemimoduleIndex.mem_sectionsSubmodule_multispan.mp s.property
      constructor
      · intro a
        have h := hf a
        -- The linear index has the same carrier; this exposes its bundled module instance.
        change (I.fst a).hom.toLinearMap (s.val (.left a)) = s.val (.right (J.fst a)) at h
        exact ((I.fst a).hom.toLinearMap_apply (s.val (.left a))).symm.trans h
      · intro a
        have h := hg a
        change (I.snd a).hom.toLinearMap (s.val (.left a)) = s.val (.right (J.snd a)) at h
        exact ((I.snd a).hom.toLinearMap_apply (s.val (.left a))).symm.trans h⟩


private theorem toAlgebraSection_apply_right
    (s : SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan) (b : J.R) :
    (I.toAlgebraSection s).val (.right b) = s.val (.right b) := rfl

/-- Under joint injectivity, the chamber values determine the entire section. -/
theorem restrictAlgebraSections_injective
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    Function.Injective I.restrictAlgebraSections := by
  intro s t h
  have hr : I.asSemimoduleIndex.restrictSections (I.toLinearSection s) =
      I.asSemimoduleIndex.restrictSections (I.toLinearSection t) := by
    apply Subtype.ext
    funext b
    simp only [restrictSections_apply, toLinearSection_apply_right]
    exact congrArg (fun x => x.val b) h
  have hlinear (a : J.L) :
      Function.Injective ((I.asSemimoduleIndex.fst a).hom.prod
        (I.asSemimoduleIndex.snd a).hom) := by
    intro x y hxy
    apply hinj a
    rw [← I.asSemimoduleIndex_span_apply a x, ← I.asSemimoduleIndex_span_apply a y]
    exact hxy
  have hs := I.asSemimoduleIndex.restrictSections_injective hlinear hr
  apply Subtype.ext
  funext j
  cases j with
  | left a =>
    exact (I.toLinearSection_apply_left s a).symm.trans
      ((congrArg (fun x => x.val (.left a)) hs).trans (I.toLinearSection_apply_left t a))
  | right b =>
    exact (I.toLinearSection_apply_right s b).symm.trans
      ((congrArg (fun x => x.val (.right b)) hs).trans (I.toLinearSection_apply_right t b))

/-- Every compatible chamber family admits a matching extension. -/
theorem restrictAlgebraSections_surjective :
    Function.Surjective I.restrictAlgebraSections := by
  intro x
  have hx : (fun b => x.val b) ∈ I.asSemimoduleIndex.compatibleFamilies :=
    I.asSemimoduleIndex.mem_compatibleFamilies_iff_forall_mem_range.mpr
      (fun a => by
        obtain ⟨y, hy⟩ := I.mem_compatibleAlgebraFamilies.mp x.property a
        exact ⟨y, (I.asSemimoduleIndex_span_apply a y).trans hy⟩)
  obtain ⟨s, hs⟩ := I.asSemimoduleIndex.restrictSections_surjective ⟨_, hx⟩
  refine ⟨I.toAlgebraSection s, Subtype.ext (funext fun b => ?_)⟩
  rw [restrictAlgebraSections_apply, toAlgebraSection_apply_right]
  have hb := congrArg (fun y => y.val b) hs
  rw [restrictSections_apply] at hb
  exact hb

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
    (I.matchingFamilyAlgEquiv hinj).toAlgHom = I.restrictAlgebraSections := (rfl)

/-- The forward equivalence restricts to the chamber values. -/
@[simp]
theorem matchingFamilyAlgEquiv_apply
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (s : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.matchingFamilyAlgEquiv hinj s).val b = s.val (.right b) := (rfl)

/-- The reconstructed section has the prescribed value at each chamber. -/
@[simp]
theorem matchingFamilyAlgEquiv_symm_apply_right
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) (b : J.R) :
    ((I.matchingFamilyAlgEquiv hinj).symm x).val (.right b) = x.val b :=
  congrArg (fun z => z.val b) ((I.matchingFamilyAlgEquiv hinj).apply_symm_apply x)

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
    have hvalues : (fun b => (α.app (.right b)).hom ((I.restrictAlgebraSections s).val b)) =
        (I'.restrictAlgebraSections (AlgCat.sectionsMap α s)).val := by
      funext b
      simp only [restrictAlgebraSections_apply, AlgCat.sectionsMap_apply]
    exact hvalues.symm ▸ (I'.restrictAlgebraSections (AlgCat.sectionsMap α s)).property
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

/-- Identity coefficient maps fix compatible algebra families. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_id :
    compatibleAlgebraFamiliesMap (𝟙 I.multispan) = AlgHom.id R _ := by
  ext x b
  rfl

/-- Compatible-family transport respects composition of coefficient maps. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_comp (α : I.multispan ⟶ I'.multispan)
    (β : I'.multispan ⟶ I''.multispan) :
    compatibleAlgebraFamiliesMap (α ≫ β) =
      (compatibleAlgebraFamiliesMap β).comp (compatibleAlgebraFamiliesMap α) := by
  ext x b
  rfl

/-- Restriction commutes with coefficient transport as an equality of algebra homomorphisms.
No injectivity hypothesis is required. -/
theorem restrictAlgebraSections_naturality (α : I.multispan ⟶ I'.multispan) :
    I'.restrictAlgebraSections.comp (AlgCat.sectionsMap α) =
      (compatibleAlgebraFamiliesMap α).comp I.restrictAlgebraSections := by
  ext s b
  simp only [AlgHom.comp_apply, restrictAlgebraSections_apply,
    AlgCat.sectionsMap_apply, compatibleAlgebraFamiliesMap_apply]
  rfl

/-- Inverse reconstruction commutes with coefficient changes as a bundled algebra map. -/
theorem matchingFamilyAlgEquiv_symm_naturality
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (hinj' : ∀ a, Function.Injective ((I'.fst a).hom.prod (I'.snd a).hom))
    (α : I.multispan ⟶ I'.multispan) :
    (AlgCat.sectionsMap α).comp (I.matchingFamilyAlgEquiv hinj).symm.toAlgHom =
      (I'.matchingFamilyAlgEquiv hinj').symm.toAlgHom.comp (compatibleAlgebraFamiliesMap α) := by
  ext x : 1
  apply I'.restrictAlgebraSections_injective hinj'
  apply Subtype.ext
  funext b
  simp only [AlgHom.comp_apply, restrictAlgebraSections_apply,
    AlgCat.sectionsMap_apply, matchingFamilyAlgEquiv_symm_apply_right,
    compatibleAlgebraFamiliesMap_apply, AlgEquiv.coe_toAlgHom]
  rfl

end Maps

end CategoryTheory.Limits.MultispanIndex
