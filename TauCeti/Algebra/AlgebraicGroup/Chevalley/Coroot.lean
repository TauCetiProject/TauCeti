/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Simple coroots in the torus of a Chevalley datum

The simple coroot at node `i` evaluates a weight `μ` as `μ i`. For a Chevalley datum `D`,
its coordinates in the actual torus are therefore `s ^ (D.weightLatticeBasis j : _) i`,
not in general `Pi.mulSingle i s`. This distinction matters for non-simply-connected data:
the simple coroot of adjoint type A₁ is the square map on its torus.

`simpleCorootParameter` gives these torus coordinates, and `simpleCoroot` is the resulting
homomorphism into the points of the datum. The theorem `simpleCoroot_eq_weylWord` identifies
it with Steinberg's word `nᵢ(s) nᵢ(1)⁻¹` over every commutative ring. In particular, this
identifies a specified cocharacter, not merely an element in the image of a torus.

The rank-one identity is supplied by
`UniversalEnvelopingAlgebra.kostantWeylParam_mul_inv_kostantWeylParam`.
The matrix comparison follows the existing doubled-minuscule E₆ calculation in
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.Weyl.Products`; the additional character calculation
here expresses that identity in the datum's own weight-lattice basis.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (i : Fin t.rank) (A : Type*) [CommRing A]

/-- The simple coroot at node `i`, in the coordinates of the datum's actual torus.
Its `j`-th coordinate pairs the `j`-th character-lattice basis vector with the simple coroot. -/
noncomputable def simpleCorootParameter : Aˣ →* (Fin t.rank → Aˣ) where
  toFun s j := s ^ (D.weightLatticeBasis j : Fin t.rank → ℤ) i
  map_one' := by ext; simp
  map_mul' s u := by ext; simp [mul_zpow]

/-- Coordinate evaluation of a simple coroot. -/
@[simp]
theorem simpleCorootParameter_apply (s : Aˣ) (j : Fin t.rank) :
    D.simpleCorootParameter i A s j = s ^ (D.weightLatticeBasis j : Fin t.rank → ℤ) i :=
  (rfl)

/-- Pairing a character, given in the weight-lattice basis, with a simple coroot. -/
@[simp]
theorem torusCharacter_simpleCorootParameter (s : Aˣ) (μ : Fin t.rank → ℤ) :
    torusCharacter (D.simpleCorootParameter i A s) μ =
      s ^ (∑ j, μ j * (D.weightLatticeBasis j : Fin t.rank → ℤ) i) := by
  simp only [torusCharacter_def, simpleCorootParameter_apply, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- In a weight basis, the simple coroot acts on a weight-`μ` vector by `s ^ μ i`.
This compares actual-torus coordinates with the full-weight parametrization. -/
theorem kostantTorusMatrix_simpleCorootParameter (s : Aˣ) :
    kostantTorusMatrix D.lattice D.basis D.coordinateWeight (D.simpleCorootParameter i A s) =
      kostantTorusMatrix D.lattice D.basis D.weight (Pi.mulSingle i s) := by
  rw [kostantTorusMatrix_apply, kostantTorusMatrix_apply]
  congr 1
  funext j
  rw [torusCharacter_mulSingle, torusCharacter_simpleCorootParameter]
  congr 1
  have h := congrFun (D.sum_coordinateWeight_smul j) i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

/-- The simple-coroot homomorphism into the points of a Chevalley datum, obtained by evaluating
its actual torus on `simpleCorootParameter`. It need not be injective. -/
noncomputable def simpleCoroot : Aˣ →* D.points A :=
  MonoidHom.codRestrict
    ((kostantTorusMatrix D.lattice D.basis D.coordinateWeight).comp
      (D.simpleCorootParameter i A)) (D.points A)
    (fun s => D.kostantTorusMatrix_mem_points A (D.simpleCorootParameter i A s))

/-- The matrix of a simple coroot in the datum's actual torus coordinates. -/
@[simp]
theorem coe_simpleCoroot (s : Aˣ) :
    (D.simpleCoroot i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      kostantTorusMatrix D.lattice D.basis D.coordinateWeight (D.simpleCorootParameter i A s) :=
  (rfl)

/-- A simple coroot is Steinberg's word `nᵢ(s) nᵢ(1)⁻¹`. The root maps in this formula are the
numbered positive and negative Kostant root maps, in the same matrix basis as the datum. -/
theorem simpleCoroot_eq_weylWord (s : Aˣ) :
    let x := fun k => kostantToralRootSubgroupPoints (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight k A
    (D.simpleCoroot i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      ((x (.inl i) (Multiplicative.ofAdd (s : A)) *
          x (.inr i) (Multiplicative.ofAdd (-((s⁻¹ : Aˣ) : A))) *
          x (.inl i) (Multiplicative.ofAdd (s : A))) *
        (x (.inl i) (Multiplicative.ofAdd (1 : A)) *
          x (.inr i) (Multiplicative.ofAdd (-1 : A)) *
          x (.inl i) (Multiplicative.ofAdd (1 : A)))⁻¹ :
        Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  dsimp only
  -- Faithfulness prevents the represented Cartan element from vanishing.
  have hT := ((t.lieBasis ht).sl2 i).map
    (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) (by
      intro hz
      apply ((t.lieBasis ht).sl2 i).h_ne_zero
      apply D.injective_representation_ι
      simpa using hz)
  have hneg : ∀ j, ⁅(t.lieBasis ht).h j, (t.lieBasis ht).rootGenerator (.inr i)⁆ =
      -((t.rootGeneratorWeight ht (.inl i) j : ℚ) • (t.lieBasis ht).rootGenerator (.inr i)) := by
    intro j
    rw [t.lie_lieBasis_h_rootGenerator ht]
    simp only [rootGeneratorWeight_inr, rootGeneratorWeight_inl, Int.cast_neg, neg_smul]
  have h := kostantWeylParam_mul_inv_kostantWeylParam
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i)) D.basis D.weight
    D.isCartanWeightVector_basis
    (by simpa only [LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using hT)
    (t.lie_lieBasis_h_rootGenerator ht (.inl i)) hneg
    (CommAlgCat.of ℤ A) s 1
  rw [kostantCoordinateCocharacter_apply, inv_one, mul_one] at h
  -- Write the rank-one identity in the lattice basis, then use actual-torus coordinates.
  have hm := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) h
  rw [MulEquiv.toMonoidHom_eq_coe, basisMatrix_kostantTorusPoints] at hm
  rw [coe_simpleCoroot, kostantTorusMatrix_simpleCorootParameter]
  symm
  simpa only [kostantWeylParam_def, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_kostantToralRootSubgroupPoints,
    basisMatrix_kostantRootSubgroupParam (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator D.basis A,
    Units.val_one, inv_one] using hm

end TauCeti.DynkinType.ChevalleyDatum
