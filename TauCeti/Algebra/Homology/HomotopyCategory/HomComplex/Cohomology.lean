/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Cohomology of Hom complexes

Mathlib's cohomology-class equivalence identifies exactness of a Hom complex with the
subsingleton condition on its cohomology classes. No abelian hypothesis on the category is
needed.

In an `R`-linear category, Mathlib's identification of cohomology classes of degree `n` with
morphisms `K ⟶ L⟦n⟧` in the homotopy category is `R`-linear
(`CochainComplex.HomComplex.CohomologyClass.homLinearEquiv`).
-/

public section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/-- A Hom complex is exact in degree `n` precisely when its degree-`n` cohomology classes
form a subsingleton. -/
theorem exactAt_homComplex_iff_subsingleton_cohomologyClass (n : ℤ) :
    (HomComplex K L).ExactAt n ↔ Subsingleton (CohomologyClass K L n) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    AddCommGrpCat.isZero_iff_subsingleton,
    (homologyAddEquiv K L n).toEquiv.subsingleton_congr]

end TauCeti

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (R : Type*) [Ring R] [Linear R C] (K L : CochainComplex C ℤ) (n : ℤ)

/-- Cohomology classes of degree `n` of the Hom complex from `K` to `L` are the morphisms
`K ⟶ L⟦n⟧` in the homotopy category, as `R`-modules. This is the `R`-linear form of Mathlib's
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv`. -/
noncomputable def homLinearEquiv :
    CohomologyClass K L n ≃ₗ[R]
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  { homAddEquiv (K := K) (L := L) (n := n) with
    map_smul' r x := by
      induction x using CohomologyClass.rec with | mk x => ?_
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, AddEquiv.coe_toEquiv,
        homAddEquiv_apply, ← mk_smul, toHom_mk, RingHom.id_apply,
        Cocycle.equivHomShift_symm_smul, Functor.map_smul] }

@[simp]
lemma homLinearEquiv_mk (x : Cocycle K L n) :
    homLinearEquiv R K L n (mk x) =
      (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) :=
  toHom_mk x

end CochainComplex.HomComplex.CohomologyClass
