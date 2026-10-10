/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.Abelianization.Finite
import TauCeti.RepresentationTheory.Homological.TateCohomology.Finite
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Permutation.Basic
public import TauCeti.RepresentationTheory.Augmentation

/-!
# Herbrand quotient of the sum-zero permutation lattice

For a finite cyclic group `G` acting on a nonempty finite set `X`, the integral sum-zero
permutation lattice has Herbrand quotient `∏ ω, |G_ω| / |G|`. The denominator comes from the
trivial quotient in the augmentation sequence `0 → ker(sum) → ℤ[X] → ℤ → 0`.

This computes the lattice used in the logarithmic description of `S`-units: the permutation
basis indexes the places above `S`, the stabilizers are decomposition groups, and the sum-zero
hyperplane encodes the product formula. Comparing an `S`-unit lattice with this lattice still
requires an equivariant logarithmic comparison.

The calculation uses `herbrandQuotient_ofMulAction`,
`herbrandQuotient_eq_mul_of_shortExact` and `herbrandQuotient_trivial_int_eq_card`.
Finiteness in degree `-1` follows from the augmentation long exact sequence and the
identification `HNegTwoAddEquivAbelianization` of degree `-2` for the trivial integral module.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3.
* J. Tate, *Global class field theory*, in Cassels and Fröhlich, *Algebraic Number Theory*,
  Chapter VII.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits MulAction

namespace TauCeti.TateCohomology

variable {G X : Type} [Group G] [Fintype G] [MulAction G X]

/-- Degree-minus-one Tate cohomology of the integral sum-zero permutation module is finite.
No nonemptiness or finiteness of the permutation set or cyclicity of the group is required. -/
instance finite_tateCohomology_negOne_augmentationSubrepresentation :
    Finite (tateCohomology
      (Rep.of (augmentationSubrepresentation ℤ G X).toRepresentation) (-1)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : Subsingleton (MonoidAlgebra ℤ X) := MonoidAlgebra.coeff_injective.subsingleton
    have := Function.Injective.subsingleton (HNegOneIsoNormKernelQuotient
      (Rep.of (augmentationSubrepresentation ℤ G X).toRepresentation)).toLinearEquiv.injective
    infer_instance
  · have hS := permutationAugmentationSequence_shortExact ℤ G X
    rw [permutationAugmentationSequence_def] at hS
    have hzero : IsZero (tateCohomology (Rep.ofMulAction ℤ G X) (-1)) :=
      ModuleCat.isZero_of_subsingleton _
    have : Finite (tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :=
      Finite.of_equiv _ HNegTwoAddEquivAbelianization.toEquiv.symm
    apply finite_tateCohomology_X₁_of_shortExact_of_isZero_X₂ hS (-2)
    simpa only [Int.reduceNeg, Int.reduceAdd] using hzero

/-- For a finite cyclic group acting on a nonempty set, the integral sum-zero permutation module's
Herbrand quotient is that of the integral permutation module divided by the order of the group. -/
theorem herbrandQuotient_augmentationSubrepresentation_eq_div [Nonempty X] [IsCyclic G] :
    herbrandQuotient (Rep.of (augmentationSubrepresentation ℤ G X).toRepresentation) =
      herbrandQuotient (Rep.ofMulAction ℤ G X) / Nat.card G := by
  have hS := permutationAugmentationSequence_shortExact ℤ G X
  rw [permutationAugmentationSequence_def] at hS
  have h := herbrandQuotient_eq_mul_of_shortExact hS
  rw [herbrandQuotient_trivial_int_eq_card] at h
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card G ≠ 0))).2 h.symm

/-- The sum-zero permutation lattice has Herbrand quotient the product of orbit stabilizer
orders divided by the group order. The set must be nonempty for augmentation onto `ℤ`. -/
theorem herbrandQuotient_augmentationSubrepresentation [Nonempty X] [IsCyclic G]
    [Fintype (orbitRel.Quotient G X)] :
    herbrandQuotient (Rep.of (augmentationSubrepresentation ℤ G X).toRepresentation) =
      (∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G ω.out) : ℚ)) / Nat.card G := by
  rw [herbrandQuotient_augmentationSubrepresentation_eq_div, herbrandQuotient_ofMulAction]

end TauCeti.TateCohomology
