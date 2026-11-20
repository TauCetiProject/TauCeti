/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.AlgCat.Limits
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

/-- Each face span must have a common preimage for the two incident values. -/
@[simp]
theorem mem_compatibleAlgebraFamilies {x : ∀ b, I.right b} :
    x ∈ I.compatibleAlgebraFamilies ↔
      ∀ a, (x (J.fst a), x (J.snd a)) ∈ ((I.fst a).hom.prod (I.snd a).hom).range := by
  simp [compatibleAlgebraFamilies]

/-- Restriction from matching sections to their compatible chamber values. -/
def restrictAlgebraSections : AlgCat.sectionsSubalgebra I.multispan →ₐ[R]
    I.compatibleAlgebraFamilies where
  toFun x := ⟨fun b => x.val (.right b), I.mem_compatibleAlgebraFamilies.mpr fun a =>
    ⟨x.val (.left a), Prod.ext (x.property (.fst a)) (x.property (.snd a))⟩⟩
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

private def toLinearSection (s : AlgCat.sectionsSubalgebra I.multispan) :
    SemimoduleCat.sectionsSubmodule I.asSemimoduleIndex.multispan :=
  ⟨fun j => match j with
    | .left a => s.val (.left a)
    | .right b => s.val (.right b),
    I.asSemimoduleIndex.mem_sectionsSubmodule_multispan.mpr
      ⟨fun a => s.property (.fst a), fun a => s.property (.snd a)⟩⟩

/-- Under joint injectivity, the chamber values determine the entire section. -/
theorem restrictAlgebraSections_injective
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    Function.Injective I.restrictAlgebraSections := by
  intro s t h
  have hr : I.asSemimoduleIndex.restrictSections (I.toLinearSection s) =
      I.asSemimoduleIndex.restrictSections (I.toLinearSection t) := by
    apply Subtype.ext
    funext b
    rw [restrictSections_apply, restrictSections_apply]
    change s.val (.right b) = t.val (.right b)
    exact congrArg (fun x => x.val b) h
  have hs := I.asSemimoduleIndex.restrictSections_injective hinj hr
  apply Subtype.ext
  funext j
  cases j with
  | left a => exact congrArg (fun x => x.val (.left a)) hs
  | right b => exact congrArg (fun x => x.val (.right b)) hs

/-- Every compatible chamber family admits a matching extension. -/
theorem restrictAlgebraSections_surjective :
    Function.Surjective I.restrictAlgebraSections := by
  intro x
  have hx : (fun b => x.val b) ∈ I.asSemimoduleIndex.compatibleFamilies :=
    I.asSemimoduleIndex.mem_compatibleFamilies_iff_forall_mem_range.mpr
      (I.mem_compatibleAlgebraFamilies.mp x.property)
  obtain ⟨s, hs⟩ := I.asSemimoduleIndex.restrictSections_surjective ⟨_, hx⟩
  let t : ∀ j, I.multispan.obj j := fun j => match j with
    | .left a => s.val (.left a)
    | .right b => s.val (.right b)
  have ht : t ∈ AlgCat.sectionsSubalgebra I.multispan := by
    obtain ⟨hf, hg⟩ := I.asSemimoduleIndex.mem_sectionsSubmodule_multispan.mp s.property
    intro j j' f
    cases f with
    | id j => rfl
    | fst a => exact hf a
    | snd a => exact hg a
  apply Exists.intro ⟨t, ht⟩
  apply Subtype.ext
  funext b
  have hb := congrArg (fun y => y.val b) hs
  rw [restrictSections_apply] at hb
  change s.val (.right b) = x.val b at hb ⊢
  exact hb

/-- For jointly injective spans, restriction to chamber values is an algebra equivalence. -/
noncomputable def matchingFamilyAlgEquiv
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom)) :
    AlgCat.sectionsSubalgebra I.multispan ≃ₐ[R] I.compatibleAlgebraFamilies :=
  AlgEquiv.ofBijective I.restrictAlgebraSections
    ⟨I.restrictAlgebraSections_injective hinj, I.restrictAlgebraSections_surjective⟩

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

/-- The reconstructed value at a face is the unique common lift of the two incident values. -/
theorem eq_matchingFamilyAlgEquiv_symm_apply_left_iff
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (x : I.compatibleAlgebraFamilies) (a : J.L) {y : I.left a} :
    y = ((I.matchingFamilyAlgEquiv hinj).symm x).val (.left a) ↔
      (I.fst a).hom y = x.val (J.fst a) ∧ (I.snd a).hom y = x.val (J.snd a) := by
  let s := (I.matchingFamilyAlgEquiv hinj).symm x
  have hf := (s.property (.fst a)).trans
    (I.matchingFamilyAlgEquiv_symm_apply_right hinj x (J.fst a))
  have hg := (s.property (.snd a)).trans
    (I.matchingFamilyAlgEquiv_symm_apply_right hinj x (J.snd a))
  exact ⟨by rintro rfl; exact ⟨hf, hg⟩, fun h =>
    hinj a (Prod.ext (h.1.trans hf.symm) (h.2.trans hg.symm))⟩

section Maps

variable {I} {I' : MultispanIndex J (AlgCat.{t} R)}

private def mapAlgebraSection (α : I.multispan ⟶ I'.multispan)
    (s : AlgCat.sectionsSubalgebra I.multispan) : AlgCat.sectionsSubalgebra I'.multispan :=
  ⟨fun j => (α.app j).hom (s.val j), by
    intro j k f
    have h := congrArg (fun g => g.hom (s.val j)) (α.naturality f)
    exact h.symm.trans (congrArg (α.app k).hom (s.property f))⟩

/-- A map of span diagrams transports compatible families componentwise. -/
def compatibleAlgebraFamiliesMap (α : I.multispan ⟶ I'.multispan) :
    I.compatibleAlgebraFamilies →ₐ[R] I'.compatibleAlgebraFamilies where
  toFun x := by
    refine ⟨fun b => (α.app (.right b)).hom (x.val b), ?_⟩
    obtain ⟨s, rfl⟩ := I.restrictAlgebraSections_surjective x
    exact (I'.restrictAlgebraSections (mapAlgebraSection α s)).property
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

/-- Reconstructing a section commutes pointwise with a map of span diagrams. -/
theorem matchingFamilyAlgEquiv_symm_naturality
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (hinj' : ∀ a, Function.Injective ((I'.fst a).hom.prod (I'.snd a).hom))
    (α : I.multispan ⟶ I'.multispan) (x : I.compatibleAlgebraFamilies)
    (j : WalkingMultispan J) :
    ((I'.matchingFamilyAlgEquiv hinj').symm (compatibleAlgebraFamiliesMap α x)).val j =
      (α.app j).hom (((I.matchingFamilyAlgEquiv hinj).symm x).val j) := by
  let s := mapAlgebraSection α ((I.matchingFamilyAlgEquiv hinj).symm x)
  have hs : (I'.matchingFamilyAlgEquiv hinj').symm (compatibleAlgebraFamiliesMap α x) = s := by
    apply I'.restrictAlgebraSections_injective hinj'
    apply Subtype.ext
    funext b
    simp [s, mapAlgebraSection]
  exact congrArg (fun z => z.val j) hs

end Maps

end CategoryTheory.Limits.MultispanIndex
