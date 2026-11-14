/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Coroot
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Coroot words at every root of a Chevalley datum

For every numbered root `α`, its coroot defines a homomorphism from units into the actual
weight-lattice torus of a Chevalley datum. Its value is the root word
`n_α(s) n_α(1)⁻¹`, where `n_α` is `ChevalleyDatum.weylElement`. In particular these root words
are multiplicative in `s`, as required in Steinberg's presentation. The construction retains
arbitrary admissible lattices and arbitrary commutative value rings; it does not require that
the full-weight parametrization reach every actual torus point.

The all-root rank-one identity is transported from
`DynkinType.chevalleyRootSubgroup_mul_mul_eq_kostantTorusPoints_mul`. The torus coordinates
are restrictions of the native coroot functionals, not another enumeration of coroots.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 28(c), and
  Chapter 6, Theorem 8.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (α : Fin t.numRoots) (A : Type v) [CommRing A]

/-- The coroot of `α` restricted to the actual character lattice, in its chosen basis. -/
def corootParameter : Aˣ →* (Fin t.rank → Aˣ) :=
  GeneralLinear.weightDiagonalUnits fun j =>
    (t.simplyConnectedRootDatum ht).coroot' α (D.weightLatticeBasis j)

/-- The `j`-th torus coordinate is `s` raised to the coroot pairing with the `j`-th basis
character of the actual weight lattice. -/
@[simp]
theorem corootParameter_apply (s : Aˣ) (j : Fin t.rank) :
    D.corootParameter α A s j =
      s ^ (t.simplyConnectedRootDatum ht).coroot' α (D.weightLatticeBasis j) :=
  GeneralLinear.weightDiagonalUnits_apply _ s j

/-- The coroot parameter is restriction of its full-weight torus parameter. -/
theorem corootParameter_eq_fullWeightTorusRestriction (s : Aˣ) :
    D.corootParameter α A s = D.fullWeightTorusRestriction A
      (fun i => s ^ (t.simplyConnectedRootDatum ht).coroot α i) := by
  ext j
  simp only [corootParameter_apply, fullWeightTorusRestriction_apply,
    torusCharacter_def, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum,
    t.coroot'_simplyConnectedRootDatum_apply ht, dotProduct, mul_comm]

/-- Evaluating an actual lattice character on the coroot gives `s` raised to its native
pairing with that coroot. -/
@[simp]
theorem torusCharacter_corootParameter (s : Aˣ) (μ : D.weightLattice) :
    torusCharacter (D.corootParameter α A s) (D.weightLatticeBasis.repr μ) =
      s ^ (t.simplyConnectedRootDatum ht).coroot' α μ := by
  rw [D.corootParameter_eq_fullWeightTorusRestriction,
    D.torusCharacter_fullWeightTorusRestriction]
  simp only [torusCharacter_def, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum,
    t.coroot'_simplyConnectedRootDatum_apply ht, dotProduct, mul_comm]

/-- A weight-basis character on the coroot gives `s` raised to its native coroot pairing. -/
@[simp]
theorem torusCharacter_corootParameter_coordinateWeight (s : Aˣ) (j : Fin D.dim) :
    torusCharacter (D.corootParameter α A s) (D.coordinateWeight j) =
      s ^ (t.simplyConnectedRootDatum ht).coroot' α (D.weight j) := by
  rw [coordinateWeight_def]
  exact D.torusCharacter_corootParameter α A s ⟨_, D.weight_mem_weightLattice j⟩

/-- A root character on the coroot gives `s` raised to the corresponding Cartan integer. -/
@[simp]
theorem torusCharacter_corootParameter_coordinateRoot (s : Aˣ) (β : Fin t.numRoots) :
    torusCharacter (D.corootParameter α A s) (D.coordinateRoot β) =
      s ^ (t.simplyConnectedRootDatum ht).pairing β α := by
  rw [coordinateRoot_def, torusCharacter_corootParameter, RootPairing.root_coroot'_eq_pairing]

/-- The parameter of the opposite coroot is the inverse parameter homomorphism. -/
@[simp]
theorem corootParameter_reflectionPerm_self :
    D.corootParameter ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A =
      (D.corootParameter α A)⁻¹ := by
  ext s j
  simp [corootParameter_apply, RootPairing.coroot'_reflectionPerm_self]

/-- The all-root coroot parameter agrees with the existing simple-coroot parameter. -/
@[simp]
theorem corootParameter_simpleIndex (i : Fin t.rank) :
    D.corootParameter (t.simpleIndex ht i) A = D.simpleCorootParameter i A := by
  ext s j
  simp only [corootParameter_apply, simpleCorootParameter_apply,
    t.coroot'_simpleIndex_apply ht]

/-- The coroot cocharacter of any numbered root, valued in the datum's point group. -/
def corootPoints : Aˣ →* D.points A :=
  (D.torusPoints A).comp (D.corootParameter α A)

/-- A coroot point is its specified value in the actual torus. -/
theorem corootPoints_apply (s : Aˣ) :
    D.corootPoints α A s = D.torusPoints A (D.corootParameter α A s) :=
  (rfl)

/-- In the weight basis the coroot is diagonal, with `j`-th entry `s` raised to the native
pairing of `D.weight j` with the coroot. -/
@[simp]
theorem coe_corootPoints (s : Aˣ) :
    (D.corootPoints α A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      diagGL (fun j => s ^ (t.simplyConnectedRootDatum ht).coroot' α (D.weight j)) := by
  rw [corootPoints_apply, coe_torusPoints, kostantTorusMatrix_apply]
  simp only [coordinateWeight_def, torusCharacter_corootParameter]

/-- The all-root coroot cocharacter specializes to the existing simple coroot. -/
@[simp]
theorem corootPoints_simpleIndex (i : Fin t.rank) :
    D.corootPoints (t.simpleIndex ht i) A = D.simpleCorootPoints i A := by
  ext s
  rw [corootPoints_apply, corootParameter_simpleIndex, simpleCorootPoints_eq_torusPoints]

/-- The value of the opposite coroot is the inverse coroot value. -/
@[simp]
theorem corootPoints_reflectionPerm_self (s : Aˣ) :
    D.corootPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A s =
      (D.corootPoints α A s)⁻¹ := by
  simp only [corootPoints_apply, corootParameter_reflectionPerm_self,
    MonoidHom.inv_apply, map_inv]

attribute [local instance high] Algebra.toModule

/-- At every root, the coroot is Steinberg's root word `n_α(s) n_α(1)⁻¹`.
This holds over arbitrary commutative rings, including nonreduced rings. -/
theorem corootPoints_eq_weylElement_mul_inv (s : Aˣ) :
    D.corootPoints α A s = D.weylElement α A s * (D.weylElement α A 1)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  rw [Subgroup.coe_mul, corootPoints_apply, coe_torusPoints,
    corootParameter_eq_fullWeightTorusRestriction, ← kostantTorusMatrix_weight,
    ← basisMatrix_kostantTorusPoints, weylElement_def, weylElement_def]
  simp only [Subgroup.coe_mul, coe_rootSubgroupPoints, ← map_mul, inv_one, Units.val_one]
  exact congrArg (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom)
    (t.chevalleyRootSubgroup_mul_mul_eq_kostantTorusPoints_mul D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis D.weight
      D.isCartanWeightVector_basis α (CommAlgCat.of ℤ A) s).symm

/-- The torus-valued quotient of two Weyl words has the quotient of their unit parameters. -/
theorem weylElement_mul_inv_weylElement (s u : Aˣ) :
    D.weylElement α A s * (D.weylElement α A u)⁻¹ = D.corootPoints α A (s / u) := by
  have hs := D.corootPoints_eq_weylElement_mul_inv α A s
  have hu := D.corootPoints_eq_weylElement_mul_inv α A u
  rw [map_div, hs, hu, div_eq_mul_inv]
  group

/-- Steinberg's toral root words satisfy the multiplicativity relation at every root. -/
theorem weylElement_mul_mul_inv_weylElement_one (s u : Aˣ) :
    D.weylElement α A (s * u) * (D.weylElement α A 1)⁻¹ =
      (D.weylElement α A s * (D.weylElement α A 1)⁻¹) *
        (D.weylElement α A u * (D.weylElement α A 1)⁻¹) := by
  simp only [← corootPoints_eq_weylElement_mul_inv, map_mul]

/-- Conjugating by a coroot value rescales each root parameter by `s` raised to the
corresponding Cartan integer. -/
theorem corootPoints_conj_rootSubgroupPoints (β : Fin t.numRoots) (s : Aˣ) (u : A) :
    D.corootPoints α A s * D.rootSubgroupPoints β A (Multiplicative.ofAdd u) *
        (D.corootPoints α A s)⁻¹ =
      D.rootSubgroupPoints β A (Multiplicative.ofAdd
        (((s ^ (t.simplyConnectedRootDatum ht).pairing β α : Aˣ) : A) * u)) := by
  rw [corootPoints_apply, D.torusPoints_conj_rootSubgroupPoints, coordinateRoot_def,
    D.torusCharacter_corootParameter, RootPairing.root_coroot'_eq_pairing]

/-- Coroot values commute with arbitrary changes of the value ring. -/
@[simp↓]
theorem map_corootPoints {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (α : Fin t.numRoots) (s : Aˣ) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f (D.corootPoints α A s) =
      D.corootPoints α B (Units.map f.toMonoidHom s) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map, coe_corootPoints, coe_corootPoints]
  simp only [map_diagGL, map_zpow, RingHom.toMonoidHom_eq_coe]

end

end TauCeti.DynkinType.ChevalleyDatum
