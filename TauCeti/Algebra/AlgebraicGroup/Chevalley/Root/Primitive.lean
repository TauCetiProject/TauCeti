/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Module.Primitive.TensorProduct
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Primitive
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Primitive

/-!
# Primitive images of root operators on a Chevalley datum

On the admissible lattice of **any** Chevalley datum `D`, every numbered simple-root operator
(positive or negative) and every root operator in the Chevalley system has a primitive vector in
its image. Consequently, after scalar extension to an arbitrary commutative ring `A`, no root
operator has a nonzero scalar annihilator: `c • X_γ = 0` on `A ⊗[ℤ] D.lattice` forces `c = 0`.

These lattice-primitivity and scalar-faithfulness results hold across all valid Dynkin types and
isogeny types without assuming two-step root strings, supplying the integral input for closed
simple-root subgroups (`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Immersion`) and ordered
positive-root product uniqueness (`TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct`).

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.exists_isPrimitive_kostantRootOperator`: every signed
  simple-root operator on `D.lattice` hits a primitive vector.
* `TauCeti.DynkinType.ChevalleyDatum.exists_isPrimitive_chevalleySystem_apply`: every root vector
  of the Chevalley system maps some lattice vector to a primitive lattice vector.
* `ChevalleyDatum.smul_baseChange_kostantRootOperator_chevalleySystem_eq_zero_iff`:
  base-changed root operators of `D` have trivial scalar annihilators over every commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TauCeti.UniversalEnvelopingAlgebra

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-- Every positive or negative simple-root operator on the lattice of a Chevalley datum has a
primitive vector in its image. -/
theorem exists_isPrimitive_kostantRootOperator (i : Fin t.rank ⊕ Fin t.rank) :
    ∃ m : D.lattice, IsPrimitive
      (kostantRootOperator (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice i m) := by
  cases i with
  | inl j =>
    exact exists_isPrimitive_kostantRootOperator_of_isSl2Triple
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      D.basis D.span_range_basis_eq_top
      (D.isSl2Triple_representation_rootGenerator j)
      (wt := fun r => D.weight r j)
      (fun r => ((isCartanWeightVector_iff _ _).mp (D.isCartanWeightVector_basis r)) j)
      (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove
  | inr j =>
    exact exists_isPrimitive_kostantRootOperator_of_isSl2Triple
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      D.basis D.span_range_basis_eq_top
      (D.isSl2Triple_representation_rootGenerator j).symm
      (wt := fun r => -D.weight r j)
      (fun r => by
        rw [LinearMap.neg_apply,
          ((isCartanWeightVector_iff _ _).mp (D.isCartanWeightVector_basis r)) j,
          Int.cast_neg, neg_smul])
      (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove

end

/-- Every root vector in the Chevalley system maps some vector of `D.lattice` to a primitive
vector of `D.lattice`. -/
theorem exists_isPrimitive_chevalleySystem_apply (γ : Fin t.numRoots) :
    ∃ m w : D.lattice,
      D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))
        (m : D.carrier) = (w : D.carrier) ∧ IsPrimitive w := by
  refine exists_isPrimitive_chevalleySystem_apply_of_simple
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator (fun j => ?_) γ
  obtain ⟨m, hm⟩ := D.exists_isPrimitive_kostantRootOperator (.inl j)
  refine ⟨m, _, ?_, hm⟩
  simpa only [LieAlgebra.Basis.rootGenerator_inl] using
    (coe_kostantRootOperator_apply (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice (.inl j) m).symm

/-- Every all-root operator on the lattice of a Chevalley datum remains faithful after base change
to any commutative ring, including nonreduced rings and rings of small characteristic. -/
theorem smul_baseChange_kostantRootOperator_chevalleySystem_eq_zero_iff
    (γ : Fin t.numRoots) (A : Type v) [CommRing A] (c : A) :
    c • (kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      γ).baseChange A = 0 ↔ c = 0 := by
  obtain ⟨m, w, hmw, hw⟩ := D.exists_isPrimitive_chevalleySystem_apply γ
  have heq : kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ m = w := by
    apply Subtype.ext
    simpa only [coe_kostantRootOperator_apply] using hmw
  exact LinearMap.smul_baseChange_eq_zero_iff_of_isPrimitive _ m (heq.symm ▸ hw) A c

end TauCeti.DynkinType.ChevalleyDatum
