/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Restriction

/-!
# The actual torus and the full-weight parametrization of a Chevalley datum

A Chevalley datum `D` has character lattice `Λ(D)`, the integral span of its weights inside
`P = Fin t.rank → ℤ`. Its chosen basis identifies `Hom(Λ(D), Aˣ)` with `Fin t.rank → Aˣ`.
Reading the weights in `P` instead parametrizes only the image of restriction
`Hom(P, Aˣ) → Hom(Λ(D), Aˣ)`.

`ChevalleyDatum.fullWeightTorusRestriction` is this restriction map in the chosen coordinates.
The factorization `ChevalleyDatum.kostantTorusMatrix_weight` and the range criterion
`ChevalleyDatum.kostantTorusMatrix_mem_fullWeight_range_iff` compare the two matrix tori without
identifying them over an arbitrary ring. The kernel consists precisely of the characters of `P`
that annihilate `Λ(D)`. If the units are divisible, restriction is surjective and the two images
agree. This applies in particular over an algebraically closed field, but not in general over
`ℚ`.

The character evaluation and extension arguments use the general lattice-duality API
`TauCeti.torusCharacter_torusPointMap` and `TauCeti.torusPointMap_surjective_of_injective`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(c).
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The inclusion `Λ(D) ↪ P`, with the source written in the chosen basis of `Λ(D)`. -/
def weightLatticeEmbedding : Module.End ℤ (Fin t.rank → ℤ) :=
  D.weightLattice.subtype ∘ₗ D.weightLatticeBasis.equivFun.symm.toLinearMap

/-- Including the coordinates of a lattice element recovers its ambient weight. -/
@[simp]
theorem weightLatticeEmbedding_repr (μ : D.weightLattice) :
    D.weightLatticeEmbedding (D.weightLatticeBasis.repr μ) = (μ : Fin t.rank → ℤ) := by
  simp [weightLatticeEmbedding]

/-- The coordinate lattice inclusion has image exactly the weight lattice. -/
theorem range_weightLatticeEmbedding :
    LinearMap.range D.weightLatticeEmbedding = D.weightLattice := by
  rw [weightLatticeEmbedding, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-- The coordinate lattice inclusion sends a standard basis vector to the corresponding chosen
basis vector of `Λ(D)`, read in the full weight lattice. -/
@[simp]
theorem weightLatticeEmbedding_single (i : Fin t.rank) :
    D.weightLatticeEmbedding (Pi.single i 1) = (D.weightLatticeBasis i : Fin t.rank → ℤ) := by
  simp [weightLatticeEmbedding]

/-- Reconstructing a coordinate weight through the lattice inclusion recovers its original weight.
-/
@[simp]
theorem weightLatticeEmbedding_coordinateWeight (j : Fin D.dim) :
    D.weightLatticeEmbedding (D.coordinateWeight j) = D.weight j := by
  rw [← D.weightLatticeBasis.equivFun.apply_symm_apply (D.coordinateWeight j),
    Module.Basis.equivFun_apply, weightLatticeEmbedding_repr]
  simpa only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul] using
    D.sum_coordinateWeight_smul j

/-- The coordinate lattice inclusion is injective, even when the weight lattice is proper. -/
theorem weightLatticeEmbedding_injective : Function.Injective D.weightLatticeEmbedding :=
  Subtype.val_injective.comp D.weightLatticeBasis.equivFun.symm.injective

variable (A : Type*) [CommRing A]

/-- Restriction `Hom(P, Aˣ) → Hom(Λ(D), Aˣ)` in the chosen coordinates of the character lattice.
Its range need not be the whole torus over an arbitrary ring. -/
def fullWeightTorusRestriction : (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  torusPointMap D.weightLatticeEmbedding

/-- The restricted parameter at a basis vector is evaluation of that vector as a character of the
full weight lattice. -/
@[simp]
theorem fullWeightTorusRestriction_apply (s : Fin t.rank → Aˣ) (i : Fin t.rank) :
    D.fullWeightTorusRestriction A s i =
      torusCharacter s (D.weightLatticeBasis i : Fin t.rank → ℤ) := by
  simp [fullWeightTorusRestriction, torusPointMap_apply]

/-- Restriction is characterized by evaluation on every character of the actual weight lattice. -/
theorem torusCharacter_fullWeightTorusRestriction (s : Fin t.rank → Aˣ)
    (μ : D.weightLattice) :
    torusCharacter (D.fullWeightTorusRestriction A s) (D.weightLatticeBasis.equivFun μ) =
      torusCharacter s (μ : Fin t.rank → ℤ) := by
  rw [fullWeightTorusRestriction, torusCharacter_torusPointMap]
  simp only [Module.Basis.equivFun_apply, weightLatticeEmbedding_repr]

/-- The kernel of full-weight restriction is the group of characters that are trivial on `Λ(D)`;
these are exactly the characters that factor through `P / Λ(D)`. -/
theorem mem_ker_fullWeightTorusRestriction_iff (s : Fin t.rank → Aˣ) :
    s ∈ (D.fullWeightTorusRestriction A).ker ↔
      ∀ μ : D.weightLattice, torusCharacter s (μ : Fin t.rank → ℤ) = 1 := by
  rw [fullWeightTorusRestriction, mem_ker_torusPointMap_iff,
    Subtype.forall, ← D.range_weightLatticeEmbedding]
  simp only [LinearMap.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- **The full-weight parametrization factors through the actual torus.** Its weights are the
original weights, whereas the actual torus acts through their coordinates in `Λ(D)`. -/
theorem kostantTorusMatrix_weight (s : Fin t.rank → Aˣ) :
    kostantTorusMatrix D.lattice D.basis D.weight s =
      kostantTorusMatrix D.lattice D.basis D.coordinateWeight
        (D.fullWeightTorusRestriction A s) := by
  simpa only [fullWeightTorusRestriction, weightLatticeEmbedding_coordinateWeight] using
    (kostantTorusMatrix_torusPointMap D.lattice D.basis D.coordinateWeight
      D.weightLatticeEmbedding s).symm

/-- A point of the actual torus is reached by the full-weight parametrization if and only if its
parameter extends to the full weight lattice. This criterion does not assume divisible units. -/
theorem kostantTorusMatrix_mem_fullWeight_range_iff (s : Fin t.rank → Aˣ) :
    kostantTorusMatrix D.lattice D.basis D.coordinateWeight s ∈
        (kostantTorusMatrix D.lattice D.basis D.weight (A := A)).range ↔
      s ∈ (D.fullWeightTorusRestriction A).range := by
  simpa only [fullWeightTorusRestriction, weightLatticeEmbedding_coordinateWeight] using
    kostantTorusMatrix_mem_range_iff D.lattice D.basis D.coordinateWeight
      D.span_range_coordinateWeight_eq_top D.weightLatticeEmbedding s

/-- Divisible units let every character of `Λ(D)` extend to `P`, so full-weight restriction is
surjective. In particular this applies to algebraically closed fields. -/
theorem fullWeightTorusRestriction_surjective [RootableBy Aˣ ℕ] :
    Function.Surjective (D.fullWeightTorusRestriction A) :=
  torusPointMap_surjective_of_injective D.weightLatticeEmbedding_injective

/-- Over a ring with divisible units, the full-weight parametrization reaches every point of the
actual torus of a Chevalley datum. No equality over general rings is asserted. -/
theorem range_kostantTorusMatrix_weight_eq [RootableBy Aˣ ℕ] :
    (kostantTorusMatrix D.lattice D.basis D.weight (A := A)).range =
      (kostantTorusMatrix D.lattice D.basis D.coordinateWeight (A := A)).range := by
  simpa only [weightLatticeEmbedding_coordinateWeight] using
    range_kostantTorusMatrix_eq_of_injective D.lattice D.basis D.coordinateWeight
      (A := A) D.weightLatticeEmbedding_injective

end

end TauCeti.DynkinType.ChevalleyDatum
