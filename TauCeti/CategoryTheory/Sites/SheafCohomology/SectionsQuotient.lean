/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# First cohomology as a quotient of local sections

For a Mayer–Vietoris square in a site, the connecting map sends a section on the
intersection to a first-cohomology class on the covered object. Its kernel consists
exactly of differences of restrictions from the two covering objects. If first
cohomology vanishes on those two objects, this gives an additive equivalence from
sections on the intersection modulo those differences to first cohomology.

For two open subsets of a space this computes first cohomology from a two-member
cover. Only vanishing in degree one on the two members is needed; neither vanishing on
the intersection nor acyclicity in higher degrees is assumed. The class of a section
is characterized by the Mayer–Vietoris connecting homomorphism, fixing its sign.

The construction uses Mathlib's Mayer–Vietoris sequence and first isomorphism theorem
for abelian groups, and `cohomologyPresheafZeroIso` to identify the degree-zero terms
and their restriction maps with sections.

Use `TauCeti.CategoryTheory.mayerVietorisSectionsQuotientEquiv S F h₂ h₃` for the
quotient comparison, where `S` is the square and `F` is the coefficient sheaf.
Opening `TauCeti.CategoryTheory` makes the unqualified names available.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, §4 (Čech cohomology).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})

omit [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})] in
/-- The difference of the restrictions of sections from the two covering objects to
 their intersection. -/
def mayerVietorisSectionsDifference :
    (F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) →+ F.obj.obj (op S.X₁) :=
  ((F.obj.map S.f₁₂.op).hom.comp (AddMonoidHom.fst _ _)) -
    ((F.obj.map S.f₁₃.op).hom.comp (AddMonoidHom.snd _ _))

omit [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})] in
@[simp]
lemma mayerVietorisSectionsDifference_apply
    (s₂ : F.obj.obj (op S.X₂)) (s₃ : F.obj.obj (op S.X₃)) :
    mayerVietorisSectionsDifference S F (s₂, s₃) =
      F.obj.map S.f₁₂.op s₂ - F.obj.map S.f₁₃.op s₃ :=
  (rfl)

/-- The first-cohomology class of a section on the intersection, with the sign of
Mathlib's Mayer–Vietoris connecting homomorphism. -/
def mayerVietorisSectionClass : F.obj.obj (op S.X₁) →+ F.H' 1 S.X₄ :=
  (S.δ F 0 1 rfl).hom.comp ((cohomologyPresheafZeroIso F).inv.app (op S.X₁)).hom

@[simp]
lemma mayerVietorisSectionClass_apply (s : F.obj.obj (op S.X₁)) :
    mayerVietorisSectionClass S F s =
      S.δ F 0 1 rfl ((cohomologyZeroSectionsEquiv F S.X₁).symm s) := by
  simp only [mayerVietorisSectionClass, AddMonoidHom.comp_apply,
    cohomologyPresheafZeroIso_inv_app_apply]

private lemma difference_eq_fromBiprod
    (x₂ : F.H' 0 S.X₂) (x₃ : F.H' 0 S.X₃) :
    mayerVietorisSectionsDifference S F
        (cohomologyZeroSectionsEquiv F S.X₂ x₂, cohomologyZeroSectionsEquiv F S.X₃ x₃) =
      cohomologyZeroSectionsEquiv F S.X₁
        (S.fromBiprod F 0 ((AddCommGrpCat.biprodIsoProd _ _).inv (x₂, x₃))) := by
  rw [S.fromBiprod_biprodIsoProd_inv_apply, map_sub,
    cohomologyZeroSectionsEquiv_naturality_left,
    cohomologyZeroSectionsEquiv_naturality_left]
  exact mayerVietorisSectionsDifference_apply S F _ _

/-- A section on the intersection has zero connecting class exactly when it is a
 difference of restrictions of sections from the two covering objects. No acyclicity
 hypothesis is needed for this characterization. -/
@[simp↓]
lemma mayerVietorisSectionClass_eq_zero_iff (s : F.obj.obj (op S.X₁)) :
    mayerVietorisSectionClass S F s = 0 ↔
      ∃ s₂ s₃, F.obj.map S.f₁₂.op s₂ - F.obj.map S.f₁₃.op s₃ = s := by
  rw [mayerVietorisSectionClass_apply]
  have hex : Function.Exact (S.fromBiprod F 0) (S.δ F 0 1 rfl) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      ((S.sequence_exact F 0 1 rfl).exact' 1 2 3)
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := (hex ((cohomologyZeroSectionsEquiv F S.X₁).symm s)).mp hs
    let p := (AddCommGrpCat.biprodIsoProd _ _).hom x
    refine ⟨cohomologyZeroSectionsEquiv F S.X₂ p.1,
      cohomologyZeroSectionsEquiv F S.X₃ p.2, ?_⟩
    rw [← mayerVietorisSectionsDifference_apply, difference_eq_fromBiprod]
    simp only [p, Prod.mk.eta, Iso.hom_inv_id_apply, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨s₂, s₃, rfl⟩
    let x₂ := (cohomologyZeroSectionsEquiv F S.X₂).symm s₂
    let x₃ := (cohomologyZeroSectionsEquiv F S.X₃).symm s₃
    apply (hex _).mpr
    refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv (x₂, x₃), ?_⟩
    apply (cohomologyZeroSectionsEquiv F S.X₁).injective
    rw [← difference_eq_fromBiprod]
    simp [x₂, x₃]

/-- Differences of local restrictions are exactly the kernel of the connecting class map. -/
lemma range_mayerVietorisSectionsDifference :
    (mayerVietorisSectionsDifference S F).range = (mayerVietorisSectionClass S F).ker := by
  ext s
  simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker,
    mayerVietorisSectionClass_eq_zero_iff, Prod.exists,
    mayerVietorisSectionsDifference_apply]

/-- If first cohomology vanishes on both covering objects, every first-cohomology
class on the covered object comes from a section on the intersection. -/
lemma mayerVietorisSectionClass_surjective
    (h₂ : Subsingleton (F.H' 1 S.X₂)) (h₃ : Subsingleton (F.H' 1 S.X₃)) :
    Function.Surjective (mayerVietorisSectionClass S F) :=
  ((AddCommGrpCat.epi_iff_surjective _).mp (S.epi_δ F 0 1 rfl h₂ h₃)).comp
    ((cohomologyPresheafZeroIso F).symm.app (op S.X₁)).addCommGroupIsoToAddEquiv.surjective

/-- For a two-member cover whose members have vanishing first cohomology, first
cohomology is sections on the intersection modulo differences of local sections. -/
def mayerVietorisSectionsQuotientEquiv
    (h₂ : Subsingleton (F.H' 1 S.X₂)) (h₃ : Subsingleton (F.H' 1 S.X₃)) :
    (F.obj.obj (op S.X₁) ⧸ (mayerVietorisSectionsDifference S F).range) ≃+ F.H' 1 S.X₄ :=
  (QuotientAddGroup.quotientAddEquivOfEq (range_mayerVietorisSectionsDifference S F)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (mayerVietorisSectionClass S F)
      (mayerVietorisSectionClass_surjective S F h₂ h₃))

/-- The quotient comparison sends the class of a section to its connecting class. -/
@[simp]
lemma mayerVietorisSectionsQuotientEquiv_mk
    (h₂ : Subsingleton (F.H' 1 S.X₂)) (h₃ : Subsingleton (F.H' 1 S.X₃))
    (s : F.obj.obj (op S.X₁)) :
    mayerVietorisSectionsQuotientEquiv S F h₂ h₃ (QuotientAddGroup.mk s) =
      mayerVietorisSectionClass S F s := by
  simp only [mayerVietorisSectionsQuotientEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  exact QuotientAddGroup.kerLift_mk (mayerVietorisSectionClass S F) s

end TauCeti.CategoryTheory
