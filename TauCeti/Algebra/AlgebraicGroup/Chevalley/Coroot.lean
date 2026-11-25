/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Coroots of a Chevalley datum

The coroot of a numbered root restricts to a functional on the actual character lattice
`D.weightLattice`. We use that functional in the chosen basis to parametrize the coroot in the
actual torus. This is also the restriction of its full-weight torus parameter; no surjectivity
of full-weight restriction is needed. At a simple root the functional is the corresponding
node coordinate, and products of these simple coroots give all restricted full-weight parameters.

The rank-one identification with Steinberg's words `n_α(s) n_α(1)⁻¹` is proved in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Weyl`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 28(c), and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section AllRoots

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

/-- The coroot parameter is the restriction of its full-weight torus parameter. -/
theorem corootParameter_eq_fullWeightTorusRestriction (s : Aˣ) :
    D.corootParameter α A s = D.fullWeightTorusRestriction A
      (fun i => s ^ (t.simplyConnectedRootDatum ht).coroot α i) := by
  ext j
  simp only [corootParameter_apply, fullWeightTorusRestriction_apply,
    torusCharacter_zpow, t.coroot'_simplyConnectedRootDatum_apply ht, dotProduct, mul_comm]

/-- Evaluating an actual lattice character on the coroot gives `s` raised to its native
pairing with that coroot. -/
@[simp]
theorem torusCharacter_corootParameter (s : Aˣ) (μ : D.weightLattice) :
    torusCharacter (D.corootParameter α A s) (D.weightLatticeBasis.repr μ) =
      s ^ (t.simplyConnectedRootDatum ht).coroot' α μ := by
  rw [D.corootParameter_eq_fullWeightTorusRestriction,
    D.torusCharacter_fullWeightTorusRestriction]
  simp only [torusCharacter_zpow, t.coroot'_simplyConnectedRootDatum_apply ht,
    dotProduct, mul_comm]

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

/-- The coroot of `α` as a homomorphism into the points of the datum, obtained by evaluating
its actual torus at `corootParameter`. -/
def corootPoints : Aˣ →* D.points A :=
  (D.torusPoints A).comp (D.corootParameter α A)

/-- A coroot point is its specified value in the actual torus. -/
theorem corootPoints_eq_torusPoints (s : Aˣ) :
    D.corootPoints α A s = D.torusPoints A (D.corootParameter α A s) := by
  rw [corootPoints, MonoidHom.comp_apply]

/-- A coroot point is the torus evaluated at the restriction of the full-weight parameter. -/
theorem corootPoints_apply (s : Aˣ) :
    D.corootPoints α A s = D.torusPoints A (D.fullWeightTorusRestriction A
      (fun i => s ^ (t.simplyConnectedRootDatum ht).coroot α i)) := by
  rw [corootPoints_eq_torusPoints, corootParameter_eq_fullWeightTorusRestriction]

/-- In the weight basis the coroot is diagonal, with `j`-th entry `s` raised to the native
pairing of `D.weight j` with the coroot. -/
@[simp]
theorem coe_corootPoints (s : Aˣ) :
    (D.corootPoints α A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      diagGL (fun j => s ^ (t.simplyConnectedRootDatum ht).coroot' α (D.weight j)) := by
  rw [corootPoints_eq_torusPoints, coe_torusPoints, kostantTorusMatrix_apply]
  simp only [torusCharacter_corootParameter_coordinateWeight]

/-- The value of the opposite coroot is the inverse coroot value. -/
@[simp]
theorem corootPoints_reflectionPerm_self (s : Aˣ) :
    D.corootPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A s =
      (D.corootPoints α A s)⁻¹ := by
  simp only [corootPoints_eq_torusPoints, corootParameter_reflectionPerm_self,
    MonoidHom.inv_apply, map_inv]

/-- Coroot values commute with arbitrary changes of the value ring. -/
@[simp↓]
theorem map_corootPoints {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (α : Fin t.numRoots) (s : Aˣ) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f (D.corootPoints α A s) =
      D.corootPoints α B (Units.map f.toMonoidHom s) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map, coe_corootPoints, coe_corootPoints]
  simp only [map_diagGL, map_zpow, RingHom.toMonoidHom_eq_coe]

end AllRoots

/-- The parameter of the coroot at the `i`-th simple root. -/
def simpleCorootParameter (i : Fin t.rank) (A : Type v) [CommRing A] :
    Aˣ →* (Fin t.rank → Aˣ) :=
  D.corootParameter (t.simpleIndex ht i) A

/-- A simple coroot parameter takes the unit to the power given by the node coordinate. -/
@[simp]
theorem simpleCorootParameter_apply (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) (j : Fin t.rank) :
    D.simpleCorootParameter i A s j = s ^ (D.weightLatticeBasis j : Fin t.rank → ℤ) i := by
  rw [simpleCorootParameter, corootParameter_apply, t.coroot'_simpleIndex_apply ht]

/-- A simple coroot parameter is the restriction of a single coordinate of the full-weight
torus. -/
theorem simpleCorootParameter_eq_fullWeightTorusRestriction (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Aˣ) :
    D.simpleCorootParameter i A s = D.fullWeightTorusRestriction A (Pi.mulSingle i s) := by
  ext j
  simp

/-- Evaluating a character on a simple coroot gives `s` raised to its node coordinate. -/
@[simp]
theorem torusCharacter_simpleCorootParameter (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) (μ : D.weightLattice) :
    torusCharacter (D.simpleCorootParameter i A s) (D.weightLatticeBasis.repr μ) =
      s ^ (μ : Fin t.rank → ℤ) i := by
  rw [simpleCorootParameter, torusCharacter_corootParameter, t.coroot'_simpleIndex_apply ht]

/-- Each weight-basis character evaluates to `s` raised to the weight's node coordinate. -/
@[simp]
theorem torusCharacter_simpleCorootParameter_coordinateWeight (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Aˣ) (j : Fin D.dim) :
    torusCharacter (D.simpleCorootParameter i A s) (D.coordinateWeight j) =
      s ^ D.weight j i := by
  rw [simpleCorootParameter, torusCharacter_corootParameter_coordinateWeight,
    t.coroot'_simpleIndex_apply ht]

/-- The coroot in the points of the datum at the `i`-th simple root. -/
def simpleCorootPoints (i : Fin t.rank) (A : Type v) [CommRing A] : Aˣ →* D.points A :=
  D.corootPoints (t.simpleIndex ht i) A

/-- At a simple root, the general coroot homomorphism specializes to the simple one. -/
theorem simpleCorootPoints_eq_corootPoints (i : Fin t.rank) (A : Type v) [CommRing A] :
    D.simpleCorootPoints i A = D.corootPoints (t.simpleIndex ht i) A := by
  rw [simpleCorootPoints]

/-- The simple coroot is the actual torus evaluated at its coroot parameter. -/
theorem simpleCorootPoints_eq_torusPoints (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) :
    D.simpleCorootPoints i A s = D.torusPoints A (D.simpleCorootParameter i A s) :=
  D.corootPoints_eq_torusPoints (t.simpleIndex ht i) A s

/-- A full-weight torus parameter is the product of the corresponding simple coroots in node
order. This identity holds over every commutative ring, even when restriction does not reach the
whole actual torus. -/
theorem torusPoints_fullWeightTorusRestriction_eq_prod_simpleCorootPoints
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    D.torusPoints A (D.fullWeightTorusRestriction A s) =
      (List.ofFn fun i => D.simpleCorootPoints i A (s i)).prod := by
  have hp : D.fullWeightTorusRestriction A s =
      (List.ofFn fun i => D.simpleCorootParameter i A (s i)).prod := by
    ext j
    simp [List.prod_ofFn, fullWeightTorusRestriction_apply, torusCharacter_def]
  rw [hp, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, simpleCorootPoints_eq_torusPoints]

/-- The diagonal entries of the simple coroot are `s` raised to the weights' node coordinates. -/
@[simp]
theorem coe_simpleCorootPoints (i : Fin t.rank) (A : Type v) [CommRing A] (s : Aˣ) :
    (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      diagGL (fun j => s ^ D.weight j i) := by
  simp only [simpleCorootPoints_eq_corootPoints, coe_corootPoints, t.coroot'_simpleIndex_apply ht]

/-- The coordinate cocharacter on lattice automorphisms is the simple coroot in the weight
basis. -/
theorem basisMatrix_kostantCoordinateCocharacter (i : Fin t.rank) (A : Type v) [CommRing A]
    (s : Aˣ) :
    Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv
      (kostantCoordinateCocharacter D.lattice D.basis D.weight A i s) =
        (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [kostantCoordinateCocharacter_apply, coe_simpleCorootPoints]
  simp only [basisMatrix_kostantTorusPoints, kostantTorusMatrix_apply, torusCharacter_mulSingle]

end

end TauCeti.DynkinType.ChevalleyDatum
