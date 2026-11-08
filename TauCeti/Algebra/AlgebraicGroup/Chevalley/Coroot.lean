/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Coroot

/-!
# Simple coroots of a Chevalley datum

The torus of a Chevalley datum `D` has character lattice `D.weightLattice`, not necessarily the
full weight lattice. The simple coroot at node `i` is restriction of the functional `μ ↦ μ i`
to this lattice. Consequently its coordinates in the chosen torus are
`fun j => s ^ (D.weightLatticeBasis j : Fin t.rank → ℤ) i`, rather than a single nontrivial
coordinate in general.

This file defines that parameter homomorphism and its values in `D.points A`. It identifies
those values with the rank-one words `n_i(s) n_i(1)⁻¹` in the numbered positive and negative
simple root subgroups, over every commutative ring. In particular this identifies the coroot
normalization without treating the full-weight parametrization as the actual torus.

The rank-one identity is supplied by the generic Kostant coroot theory in
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Coroot`;
the additional content here is its comparison with the coordinates of the datum's own torus.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Lemma 28(c).
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

noncomputable section

/-- The simple coroot at `i`, as a homomorphism into the torus parameters in the chosen basis
of the actual character lattice. -/
def simpleCorootParameter (i : Fin t.rank) (A : Type v) [CommRing A] :
    Aˣ →* (Fin t.rank → Aˣ) :=
  GeneralLinear.weightDiagonalUnits fun j => (D.weightLatticeBasis j : Fin t.rank → ℤ) i

@[simp]
theorem simpleCorootParameter_apply (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) (j : Fin t.rank) :
    D.simpleCorootParameter i A s j = s ^ (D.weightLatticeBasis j : Fin t.rank → ℤ) i :=
  GeneralLinear.weightDiagonalUnits_apply _ s j

/-- Evaluation of any character on a simple coroot is its pairing with that coroot. The
character is written in the chosen basis of the actual weight lattice. -/
theorem torusCharacter_simpleCorootParameter (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) (μ : D.weightLattice) :
    torusCharacter (D.simpleCorootParameter i A s) (D.weightLatticeBasis.repr μ) =
      s ^ (μ : Fin t.rank → ℤ) i := by
  have hcoord := congrArg (fun ν : D.weightLattice => (ν : Fin t.rank → ℤ) i)
    (D.weightLatticeBasis.sum_repr μ)
  simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
    smul_eq_mul] at hcoord
  rw [torusCharacter_def]
  simp only [simpleCorootParameter_apply, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  simpa only [mul_comm] using hcoord

/-- Each weight-basis character takes the expected value on the simple coroot. -/
@[simp]
theorem torusCharacter_simpleCorootParameter_coordinateWeight (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Aˣ) (j : Fin D.dim) :
    torusCharacter (D.simpleCorootParameter i A s) (D.coordinateWeight j) =
      s ^ D.weight j i := by
  rw [coordinateWeight_def]
  exact D.torusCharacter_simpleCorootParameter i A s ⟨D.weight j, D.weight_mem_weightLattice j⟩

/-- The simple coroot as a homomorphism into the points of the datum, obtained by evaluating
its actual torus at `simpleCorootParameter`. -/
def simpleCorootPoints (i : Fin t.rank) (A : Type v) [CommRing A] : Aˣ →* D.points A :=
  MonoidHom.codRestrict
    ((kostantTorusMatrix D.lattice D.basis D.coordinateWeight).comp (D.simpleCorootParameter i A))
    (D.points A) (fun _ => D.kostantTorusMatrix_mem_points A _)

/-- The simple coroot is a point of the datum's torus with the specified lattice coordinates. -/
theorem coe_simpleCorootPoints_eq_kostantTorusMatrix (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) :
    (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      kostantTorusMatrix D.lattice D.basis D.coordinateWeight (D.simpleCorootParameter i A s) := by
  rfl

/-- The simple coroot is the actual torus evaluated at its coroot parameter. -/
theorem simpleCorootPoints_eq_torusPoints (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) :
    D.simpleCorootPoints i A s = D.torusPoints A (D.simpleCorootParameter i A s) := by
  apply Subtype.ext
  rw [coe_torusPoints, coe_simpleCorootPoints_eq_kostantTorusMatrix]

/-- On a weight vector, the simple coroot acts by its weight's `i`-th coordinate. -/
@[simp]
theorem coe_simpleCorootPoints (i : Fin t.rank) (A : Type v) [CommRing A] (s : Aˣ) :
    (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      diagGL (fun j => s ^ D.weight j i) := by
  rw [coe_simpleCorootPoints_eq_kostantTorusMatrix, kostantTorusMatrix_apply]
  simp

/-- Simple coroot values commute with every scalar extension of the value ring. -/
theorem map_simpleCorootPoints {A : Type v} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin t.rank) (s : Aˣ) :
    Matrix.GeneralLinearGroup.map f (D.simpleCorootPoints i A s) =
      (D.simpleCorootPoints i B (Units.map f.toMonoidHom s) :
        Matrix.GeneralLinearGroup (Fin D.dim) B) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  simp [coe_simpleCorootPoints, diagGL_apply]

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-- The simple coroot value is the rank-one word `n_i(s) n_i(1)⁻¹`. Here `x` denotes the
existing numbered root-subgroup matrix, with its additive parameter read in `Multiplicative A`.
This holds over every commutative ring, without requiring that `s` have a square root. -/
theorem coe_simpleCorootPoints_eq_root_word (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) :
    let x := fun k (u : A) => kostantRootSubgroupMatrix (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice k
      (D.isNilpotent_representation_rootGenerator k) D.basis
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u))
    (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      x (.inl i) s * x (.inr i) (-((s⁻¹ : Aˣ) : A)) * x (.inl i) s *
        (x (.inl i) 1 * x (.inr i) (-1) * x (.inl i) 1)⁻¹ := by
  dsimp only
  have hneg : ∀ j, ⁅(t.lieBasis ht).h j, (t.lieBasis ht).rootGenerator (.inr i)⁆ =
      -((t.rootGeneratorWeight ht (.inl i) j : ℚ) •
        (t.lieBasis ht).rootGenerator (.inr i)) := by
    intro j
    rw [t.lie_lieBasis_h_rootGenerator ht, t.rootGeneratorWeight_inr,
      t.rootGeneratorWeight_inl, Int.cast_neg, neg_smul]
  have h := kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice D.basis D.weight D.isCartanWeightVector_basis
    (D.isSl2Triple_representation_rootGenerator i)
    (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i))
    (t.lie_lieBasis_h_rootGenerator ht (.inl i)) hneg (CommAlgCat.of ℤ A) s
  rw [kostantWeylGL_eq_kostantRootSubgroupParam_mul] at h
  have hm := congrArg (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) h
  simp only [map_mul,
    matrix_kostantRootSubgroupParam (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight,
    coe_kostantToralRootSubgroupPoints] at hm
  have hc : Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
      (kostantCoordinateCocharacter D.lattice D.basis D.weight A i s) =
        (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) := by
    rw [kostantCoordinateCocharacter_apply, coe_simpleCorootPoints]
    simp only [MulEquiv.toMonoidHom_eq_coe, basisMatrix_kostantTorusPoints,
      kostantTorusMatrix_apply, torusCharacter_mulSingle]
  rw [hc] at hm
  exact (eq_mul_inv_iff_mul_eq.mpr hm.symm)

end

end TauCeti.DynkinType.ChevalleyDatum
