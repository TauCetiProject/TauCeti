/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Coordinate

/-!
# Simple coroots in the torus of a Chevalley datum

The simple coroot at node `i` evaluates a weight `μ` as `μ i`. For a Chevalley datum `D`,
its coordinates in the actual torus are therefore `s ^ (D.weightLatticeBasis j : _) i`,
not in general `Pi.mulSingle i s`. This distinction matters for non-simply-connected data:
the simple coroot of adjoint type A₁ is the square map on its torus.

`torusParameter` restricts full-weight torus points to the actual torus.
`simpleCorootParameter` specializes it to a single coordinate, and `simpleCoroot` is the resulting
homomorphism into the points of the datum. The theorem
`coe_simpleCoroot_eq_kostantWeylParam_mul_inv` identifies it with Steinberg's product
`nᵢ(s) nᵢ(1)⁻¹` over every commutative ring. In particular, this identifies a specified
cocharacter, not merely an element in the image of a torus.

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

/-- Restriction from the full-weight torus to the datum's actual torus, dual to the inclusion
of its character lattice. This map need not be surjective on ring-valued points. -/
noncomputable def torusParameter : (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  torusPointMap ((Submodule.subtype _) ∘ₗ D.weightLatticeBasis.equivFun.symm.toLinearMap)

/-- Each actual-torus coordinate evaluates the corresponding character-lattice basis vector. -/
@[simp]
theorem torusParameter_apply (s : Fin t.rank → Aˣ) (j : Fin t.rank) :
    D.torusParameter A s j = torusCharacter s (D.weightLatticeBasis j : Fin t.rank → ℤ) := by
  simp [torusParameter, torusPointMap_apply, Module.Basis.equivFun_symm_apply]

/-- Characters pull back from the actual torus by reconstruction in the character-lattice basis. -/
@[simp]
theorem torusCharacter_torusParameter (s : Fin t.rank → Aˣ) (μ : Fin t.rank → ℤ) :
    torusCharacter (D.torusParameter A s) μ =
      torusCharacter s (∑ j, μ j • (D.weightLatticeBasis j : Fin t.rank → ℤ)) := by
  simp [torusParameter, torusCharacter_torusPointMap, Module.Basis.equivFun_symm_apply]

/-- The full-weight torus acts by restriction to the datum's actual torus. -/
theorem kostantTorusMatrix_torusParameter (s : Fin t.rank → Aˣ) :
    kostantTorusMatrix D.lattice D.basis D.coordinateWeight (D.torusParameter A s) =
      kostantTorusMatrix D.lattice D.basis D.weight s := by
  simp only [kostantTorusMatrix_apply, torusCharacter_torusParameter,
    D.sum_coordinateWeight_smul]

/-- The simple coroot at node `i`, in the coordinates of the datum's actual torus.
Its `j`-th coordinate pairs the `j`-th character-lattice basis vector with the simple coroot. -/
noncomputable def simpleCorootParameter : Aˣ →* (Fin t.rank → Aˣ) :=
  (D.torusParameter A).comp (MonoidHom.mulSingle (fun _ : Fin t.rank => Aˣ) i)

/-- Coordinate evaluation of a simple coroot. -/
@[simp]
theorem simpleCorootParameter_apply (s : Aˣ) (j : Fin t.rank) :
    D.simpleCorootParameter i A s j = s ^ (D.weightLatticeBasis j : Fin t.rank → ℤ) i := by
  simp [simpleCorootParameter]

/-- Pairing a character, given in the weight-lattice basis, with a simple coroot. -/
@[simp]
theorem torusCharacter_simpleCorootParameter (s : Aˣ) (μ : Fin t.rank → ℤ) :
    torusCharacter (D.simpleCorootParameter i A s) μ =
      s ^ (∑ j, μ j * (D.weightLatticeBasis j : Fin t.rank → ℤ) i) := by
  simp [simpleCorootParameter, Finset.sum_apply]

/-- In a weight basis, the simple coroot acts on a weight-`μ` vector by `s ^ μ i`.
This compares actual-torus coordinates with the full-weight parametrization. -/
theorem kostantTorusMatrix_simpleCorootParameter (s : Aˣ) :
    kostantTorusMatrix D.lattice D.basis D.coordinateWeight (D.simpleCorootParameter i A s) =
      kostantTorusMatrix D.lattice D.basis D.weight (Pi.mulSingle i s) := by
  simpa only [simpleCorootParameter, MonoidHom.comp_apply, MonoidHom.mulSingle_apply] using
    D.kostantTorusMatrix_torusParameter A (Pi.mulSingle i s)

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
theorem coe_simpleCoroot_eq_kostantWeylParam_mul_inv (s : Aˣ) :
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
  have h := kostantRootSubgroupMatrix_mul_mul_mul_inv
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis D.weight
    D.isCartanWeightVector_basis (D.isSl2Triple_representation i)
    (t.lie_lieBasis_h_rootGenerator ht (.inl i))
    (t.lie_lieBasis_h_rootGenerator_inr_neg ht i) A s 1
  rw [coe_simpleCoroot, kostantTorusMatrix_simpleCorootParameter]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_kostantToralRootSubgroupPoints,
    inv_one, mul_one, Units.val_one] using h.symm

end TauCeti.DynkinType.ChevalleyDatum
