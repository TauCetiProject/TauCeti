/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.EulerCharacteristic

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Homology.CochainComplexOpposite
import TauCeti.Algebra.Homology.EulerCharacteristic.FiniteDimensional

/-!
# The Euler characteristic of fully blocked grid homology

The fully blocked grid differential preserves the Alexander grading and lowers the Maslov grading.
For a fixed Alexander degree, this file regards its graded complex as a bounded complex of
finite-dimensional `ZMod 2`-vector spaces. Reindexing Maslov degree `m` as cohomological degree
`-m` puts the complex in the cochain convention used by the finite-dimensional Euler--Poincaré
theorem.

The resulting homology Euler characteristic agrees with the alternating count of grid states in
each Alexander degree. Summing these coefficients identifies the graded Euler characteristic of
fully blocked grid homology with the existing grid-determinant expression.

## Main definitions

* `TauCeti.OddComponentGridDiagram.alexanderHomologyEulerChar`: the alternating dimension of the
  homology in one Alexander degree.
* `TauCeti.OddComponentGridDiagram.gradedHomologyEulerChar`: these characteristics assembled as a
  Laurent polynomial in the Alexander variable.

## Main results

* `TauCeti.OddComponentGridDiagram.alexanderHomologyEulerChar_eq_alexanderEulerChar`: the
  coefficientwise Euler--Poincaré identity.
* `TauCeti.OddComponentGridDiagram.gradedHomologyEulerChar_eq_smul_T_mul_det_weightMatrix`: the
  graded homology Euler characteristic is the normalized grid determinant.

## References

The Euler--Poincaré comparison is the algebraic step in Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Sections 4.3--4.4, that identifies the graded Euler characteristic computed
from grid states with the one computed from grid homology.
-/

public section

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The fully blocked grid complex in Alexander degree `a`, with its homogeneous pieces regarded
as finite-dimensional `ZMod 2`-modules. -/
private noncomputable def gradedFullyBlockedFGComplex (a : ℤ) :
    ChainComplex (FGModuleCat (ZMod 2)) ℤ :=
  ChainComplex.of
    (fun m => FGModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (m, a)))
    (fun m => FGModuleCat.ofHom (G.gradedFullyBlockedDifferential a m))
    (fun m => by
      ext : 1
      rw [FGModuleCat.hom_hom_comp]
      exact G.gradedFullyBlockedDifferential_comp_eq_zero a m)

/-- The object in Maslov degree `m` of the finite-dimensional fully blocked grid complex. -/
@[simp]
private theorem gradedFullyBlockedFGComplex_X (a m : ℤ) :
    (G.gradedFullyBlockedFGComplex a).X m =
      FGModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (m, a)) := by
  simp only [gradedFullyBlockedFGComplex]

/-- The finite-dimensional fully blocked grid complex, reindexed so that cohomological degree is
the negative of Maslov degree. -/
private noncomputable def gradedFullyBlockedFGCochainComplex (a : ℤ) :
    CochainComplex (FGModuleCat (ZMod 2)) ℤ :=
  (ChainComplex.cochainComplexEquivalence (FGModuleCat (ZMod 2))).functor.obj
    (G.gradedFullyBlockedFGComplex a)

/-- Cohomological degree `i` is Maslov degree `-i` in the reindexed grid complex. -/
@[simp]
private theorem gradedFullyBlockedFGCochainComplex_X (a i : ℤ) :
    (G.gradedFullyBlockedFGCochainComplex a).X i =
      FGModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (-i, a)) := by
  rw [gradedFullyBlockedFGCochainComplex, ChainComplex.cochainComplexEquivalence,
    ComplexShape.Embedding.restrictionFunctor_obj, HomologicalComplex.restriction_X,
    ComplexShape.embeddingUpIntDownInt_f]
  exact G.gradedFullyBlockedFGComplex_X a (-i)

/-- The reindexed fully blocked cochain complex after forgetting the finite-dimensionality
witness on each homogeneous piece. -/
private noncomputable abbrev gradedFullyBlockedCochainComplex (a : ℤ) :
    CochainComplex (ModuleCat (ZMod 2)) ℤ :=
  ((forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapHomologicalComplex _).obj
    (G.gradedFullyBlockedFGCochainComplex a)

/-- Reindexing by negation does not change the alternating dimension of the terms of the fully
blocked grid complex. -/
@[simp]
private theorem eulerChar_gradedFullyBlockedCochainComplex (a : ℤ) :
    (G.gradedFullyBlockedCochainComplex a).eulerChar =
      G.alexanderEulerChar (ZMod 2) a := by
  rw [← G.eulerChar_gradedFullyBlockedComplex a]
  unfold HomologicalComplex.eulerChar GradedObject.eulerChar
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  apply finsum_congr
  intro i
  simp only [ComplexShape.eulerCharSignsUpInt_χ,
    Functor.mapHomologicalComplex_obj_X, ComplexShape.eulerCharSignsDownInt_χ]
  rw [Equiv.neg_apply, FGModuleCat.finrank_forget₂_obj]
  have hleft := congrArg
    (fun X : FGModuleCat (ZMod 2) => Module.finrank (ZMod 2) X)
    (G.gradedFullyBlockedFGCochainComplex_X a (-i))
  have hright := congrArg
    (fun X : ModuleCat (ZMod 2) => Module.finrank (ZMod 2) X)
    (G.gradedFullyBlockedComplex_X a i)
  rw [hleft, hright]
  simp

private theorem isZero_gradedFullyBlockedFGCochainComplex_X_of_forall_ne (a i : ℤ)
    (h : ∀ x : GridState n, G.1.maslovOℤ x ≠ -i) :
    IsZero ((G.gradedFullyBlockedFGCochainComplex a).X i) := by
  rw [G.gradedFullyBlockedFGCochainComplex_X]
  have hempty : IsEmpty {x : GridState n // G.bidegree x = (-i, a)} :=
    ⟨fun x => h x (by rw [← G.bidegree_fst x, x.property])⟩
  have hsub : Subsingleton (G.BigradedChainPiece (ZMod 2) (-i, a)) :=
    ⟨fun c d => by
      ext x
      exact isEmptyElim x⟩
  let hsubInst : Subsingleton (G.BigradedChainPiece (ZMod 2) (-i, a)) := hsub
  have hzero : IsZero
      (ModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (-i, a))) :=
    ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_full_of_faithful_of_isZero
    (forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2)))
    (FGModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (-i, a)))
    hzero

/-- The finite-dimensional fully blocked cochain complex is supported in a finite interval of
cohomological degrees. -/
private theorem exists_isStrictlyBounded_gradedFullyBlockedFGCochainComplex (a : ℤ) :
    ∃ lo hi : ℤ, (G.gradedFullyBlockedFGCochainComplex a).IsStrictlyGE lo ∧
      (G.gradedFullyBlockedFGCochainComplex a).IsStrictlyLE hi := by
  let s : Finset ℤ := Finset.univ.image G.1.maslovOℤ
  have hs : s.Nonempty := by
    refine ⟨G.1.maslovOℤ ⟨Equiv.refl (Fin n)⟩, ?_⟩
    simp [s]
  refine ⟨-s.max' hs, -s.min' hs, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    apply G.isZero_gradedFullyBlockedFGCochainComplex_X_of_forall_ne a i
    intro x hx
    have hle : G.1.maslovOℤ x ≤ s.max' hs :=
      s.le_max' _ (by simp [s])
    omega
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    apply G.isZero_gradedFullyBlockedFGCochainComplex_X_of_forall_ne a i
    intro x hx
    have hle : s.min' hs ≤ G.1.maslovOℤ x :=
      s.min'_le _ (by simp [s])
    omega

/-- The Euler characteristic of fully blocked grid homology in Alexander degree `a`.

The homology is taken after forgetting the finite-dimensionality witness from the bounded
cochain complex whose cohomological degree is the negative Maslov degree. -/
noncomputable def alexanderHomologyEulerChar (a : ℤ) : ℤ :=
  (G.gradedFullyBlockedCochainComplex a).homologyEulerChar

/-- **Euler--Poincaré in one Alexander degree.** The alternating dimension of fully blocked grid
homology equals the alternating count of grid states. -/
@[simp]
theorem alexanderHomologyEulerChar_eq_alexanderEulerChar (a : ℤ) :
    G.alexanderHomologyEulerChar a = G.alexanderEulerChar (ZMod 2) a := by
  obtain ⟨lo, hi, hlo, hhi⟩ :=
    G.exists_isStrictlyBounded_gradedFullyBlockedFGCochainComplex a
  let K : CochainComplex (FGModuleCat (ZMod 2)) ℤ :=
    G.gradedFullyBlockedFGCochainComplex a
  have hloK : K.IsStrictlyGE lo := by simpa only [K] using hlo
  have hhiK : K.IsStrictlyLE hi := by simpa only [K] using hhi
  let _ : K.IsStrictlyGE lo := hloK
  let _ : K.IsStrictlyLE hi := hhiK
  have hEP := HomologicalComplex.eulerChar_forgetFG_eq_homologyEulerChar K lo hi
  have heuler :
      (((forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapHomologicalComplex _).obj
        K).eulerChar = G.alexanderEulerChar (ZMod 2) a := by
    simpa only [K] using G.eulerChar_gradedFullyBlockedCochainComplex a
  rw [alexanderHomologyEulerChar]
  exact hEP.symm.trans heuler

/-- Fully blocked grid homology has zero Euler characteristic in an Alexander degree containing
no grid state. -/
theorem alexanderHomologyEulerChar_eq_zero_of_notMem {a : ℤ}
    (ha : a ∉ G.alexanderSupport) : G.alexanderHomologyEulerChar a = 0 := by
  rw [G.alexanderHomologyEulerChar_eq_alexanderEulerChar,
    G.alexanderEulerChar_eq_zero_of_notMem (ZMod 2) ha]

/-- The graded Euler characteristic of fully blocked grid homology, assembled from its Alexander
degrees. The variable `T` is a square root of the usual Alexander variable, so degree `a` appears
with exponent `2a`. -/
noncomputable def gradedHomologyEulerChar : ℤ[T;T⁻¹] :=
  ∑ a ∈ G.alexanderSupport, G.alexanderHomologyEulerChar a • T (2 * a)

/-- The graded Euler characteristic computed from fully blocked grid homology equals the one
computed from grid states. -/
@[simp]
theorem gradedHomologyEulerChar_eq_gradedEulerChar :
    G.gradedHomologyEulerChar = G.gradedEulerChar (ZMod 2) := by
  rw [G.gradedEulerChar_eq_sum_alexanderSupport (ZMod 2)]
  apply Finset.sum_congr rfl
  intro a _
  rw [G.alexanderHomologyEulerChar_eq_alexanderEulerChar]

/-- **The graded Euler characteristic of fully blocked grid homology is the normalized grid
determinant.** -/
theorem gradedHomologyEulerChar_eq_smul_T_mul_det_weightMatrix :
    G.gradedHomologyEulerChar =
      (Equiv.Perm.sign G.1.O.toPerm * ((n : ℤ) + 1).negOnePow) •
        (T G.1.alexanderTwoShift * G.1.weightMatrix.det) := by
  rw [G.gradedHomologyEulerChar_eq_gradedEulerChar,
    G.gradedEulerChar_eq_smul_T_mul_det_weightMatrix]

end TauCeti.OddComponentGridDiagram
