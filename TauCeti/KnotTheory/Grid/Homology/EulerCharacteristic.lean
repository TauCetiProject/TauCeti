/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
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

* `TauCeti.OddComponentGridDiagram.alexanderHomologyEulerChar_eq_finsum_finrank`: the
  coefficient is the alternating dimension of the homology groups of the public graded complex.
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

/-- Under `ChainComplex.cochainComplexEquivalence`, cohomological degree `i` is homological
degree `-i`. -/
private theorem cochainComplexEquivalence_functor_obj_X {C : Type*} [Category* C]
    [HasZeroMorphisms C] (K : ChainComplex C ℤ) (i : ℤ) :
    ((ChainComplex.cochainComplexEquivalence C).functor.obj K).X i = K.X (-i) := by
  rw [ChainComplex.cochainComplexEquivalence, ComplexShape.Embedding.restrictionFunctor_obj,
    HomologicalComplex.restriction_X, ComplexShape.embeddingUpIntDownInt_f]

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
  rw [gradedFullyBlockedFGCochainComplex, cochainComplexEquivalence_functor_obj_X]
  exact G.gradedFullyBlockedFGComplex_X a (-i)

/-- The reindexed fully blocked cochain complex after forgetting the finite-dimensionality
witness on each homogeneous piece. -/
private noncomputable abbrev gradedFullyBlockedCochainComplex (a : ℤ) :
    CochainComplex (ModuleCat (ZMod 2)) ℤ :=
  ((forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapHomologicalComplex _).obj
    (G.gradedFullyBlockedFGCochainComplex a)

/-- Mapping a reindexed chain complex agrees with reindexing the mapped chain complex. -/
private noncomputable def mapCochainComplexEquivalenceIso
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : ChainComplex C ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ChainComplex.cochainComplexEquivalence C).functor.obj K) ≅
      (ChainComplex.cochainComplexEquivalence D).functor.obj
        ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K) :=
  Iso.refl _

/-- In each Maslov degree, forgetting the finite-dimensionality witness gives the corresponding
object of the public graded grid complex. -/
private noncomputable def gradedFullyBlockedComplexXIso (a m : ℤ) :
    (((forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapHomologicalComplex _).obj
        (G.gradedFullyBlockedFGComplex a)).X m ≅
      (G.gradedFullyBlockedComplex a).X m := by
  change ModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (m, a)) ≅ _
  exact eqToIso (G.gradedFullyBlockedComplex_X a m).symm

/-- The component identifications intertwine the finite-dimensional and public graded grid
differentials. -/
private theorem gradedFullyBlockedComplexXIso_hom_d (a m : ℤ) :
    (G.gradedFullyBlockedComplexXIso a (m + 1)).hom ≫
        (G.gradedFullyBlockedComplex a).d (m + 1) m =
      (((forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapHomologicalComplex _).obj
          (G.gradedFullyBlockedFGComplex a)).d (m + 1) m ≫
        (G.gradedFullyBlockedComplexXIso a m).hom := by
  rw [G.gradedFullyBlockedComplex_d]
  ext
  simp [gradedFullyBlockedComplexXIso, gradedFullyBlockedFGComplex,
    Functor.mapHomologicalComplex]
  rfl

/-- Forgetting the finite-dimensionality witnesses recovers the public graded grid complex. -/
private noncomputable def gradedFullyBlockedComplexIso (a : ℤ) :
    ((forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapHomologicalComplex _).obj
        (G.gradedFullyBlockedFGComplex a) ≅
      G.gradedFullyBlockedComplex a :=
  HomologicalComplex.Hom.isoOfComponents (G.gradedFullyBlockedComplexXIso a) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      exact G.gradedFullyBlockedComplexXIso_hom_d a j)

/-- The forgetful comparison commutes with reindexing Maslov degree as cohomological degree. -/
private noncomputable def gradedFullyBlockedCochainComplexIso (a : ℤ) :
    G.gradedFullyBlockedCochainComplex a ≅
      (ChainComplex.cochainComplexEquivalence (ModuleCat (ZMod 2))).functor.obj
        (G.gradedFullyBlockedComplex a) := by
  exact mapCochainComplexEquivalenceIso
      (forget₂ (FGModuleCat (ZMod 2)) (ModuleCat (ZMod 2)))
      (G.gradedFullyBlockedFGComplex a) ≪≫
    (ChainComplex.cochainComplexEquivalence (ModuleCat (ZMod 2))).functor.mapIso
      (G.gradedFullyBlockedComplexIso a)

/-- Reindexing the forgotten finite-dimensional complex identifies its cohomology in degree `i`
with the homology of the public grid complex in Maslov degree `-i`. -/
private theorem finrank_homology_gradedFullyBlockedCochainComplex (a i : ℤ) :
    Module.finrank (ZMod 2) ((G.gradedFullyBlockedCochainComplex a).homology i) =
      Module.finrank (ZMod 2)
        ((G.gradedFullyBlockedComplex a).homology ((Equiv.neg ℤ) i)) := by
  have hmap := (HomologicalComplex.homologyMapIso
    (G.gradedFullyBlockedCochainComplexIso a) i).toLinearEquiv.finrank_eq
  let e := ComplexShape.embeddingUpIntDownInt
  have hrestriction := ((G.gradedFullyBlockedComplex a).restrictionHomologyIso e
    (i - 1) i (i + 1) (by simp) (by simp)
    (i' := (Equiv.neg ℤ) (i - 1)) (j' := (Equiv.neg ℤ) i)
    (k' := (Equiv.neg ℤ) (i + 1))
    (by simp [e]) (by simp [e]) (by simp [e])
    (by simp; omega) (by simp; omega)).toLinearEquiv.finrank_eq
  exact hmap.trans hrestriction

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
  have hfinrank : Module.finrank (ZMod 2) (G.BigradedChainPiece (ZMod 2) (-i, a)) = 0 := by
    rw [G.finrank_bigradedChainPiece]
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro x _ hx
    exact h x (by rw [← G.bidegree_fst x, hx])
  have hsub : Subsingleton (G.BigradedChainPiece (ZMod 2) (-i, a)) :=
    Module.finrank_zero_iff.mp hfinrank
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

/-- The Euler characteristic in Alexander degree `a` is the alternating `finsum` of the
dimensions of the homology groups of the public Maslov-graded fully blocked complex. -/
theorem alexanderHomologyEulerChar_eq_finsum_finrank (a : ℤ) :
    G.alexanderHomologyEulerChar a =
      ∑ᶠ m : ℤ, (m.negOnePow : ℤ) *
        Module.finrank (ZMod 2) ((G.gradedFullyBlockedComplex a).homology m) := by
  rw [alexanderHomologyEulerChar]
  unfold HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  rw [← finsum_comp_equiv (Equiv.neg ℤ)
    (f := fun m : ℤ => (m.negOnePow : ℤ) *
      Module.finrank (ZMod 2) ((G.gradedFullyBlockedComplex a).homology m))]
  apply finsum_congr
  intro i
  simp only [Equiv.neg_apply, ComplexShape.eulerCharSignsUpInt_χ]
  rw [G.finrank_homology_gradedFullyBlockedCochainComplex a i, Int.negOnePow_neg]

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
