/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.LeadingMinors

/-!
# Weyl words in the matrix big cell

A Weyl word in a faithful Chevalley representation carries the weight space at `μ` to the
weight space at `w μ`. Its leading weight-block minors can therefore all be invertible only
when `w = 1`. Conversely, a word spelling the identity preserves every weight space, so all
these minors are units. This is the Weyl-representative test used to single out the open
Bruhat cell. It holds over every nontrivial commutative value ring, even when rational torus
points do not distinguish the weights.

The ordering can be any ordering of the distinct weights; basis vectors within a weight
space need not be permuted. The matrix argument uses
`TauCeti.UniversalEnvelopingAlgebra.isUnit_leading_weight_minors_iff`; the integral
weight-space transport uses `IsCartanWeightVector.kostantWeylRestrict` before scalar extension.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- A Weyl word has invertible leading weight-block minors exactly when the Weyl-group element
it spells is the identity. The equivalence `r` orders the distinct weights, keeping repeated
weights in a single block. The value ring may have arbitrary characteristic and nilpotents. -/
theorem isUnit_leading_weight_minors_weylWord_iff {β : Type*} [PartialOrder β] [DecidableLE β]
    (l : List (Fin t.rank)) (A : Type v) [CommRing A] [Nontrivial A]
    (r : Set.range D.weight ≃ β) :
    (∀ a, IsUnit ((Matrix.toSquareBlockProp
      ((((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A))
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ a).det)) ↔
      t.simplyConnectedWeylWordProd ht l = 1 := by
  rw [← D.map_toMatrix_weylWordLatticeEquiv l A,
    isUnit_leading_weight_minors_iff (t.lieBasis ht).h D.representation D.lattice D.basis D.weight
      D.isCartanWeightVector_basis (D.weylWordLatticeEquiv l)
      (fun μ => t.simplyConnectedWeylWordProd ht l • μ)
      (MulAction.injective _).injOn
      (fun j => D.isCartanWeightVector_weylWordLatticeEquiv l (D.isCartanWeightVector_basis j)) r]
  exact ⟨D.eq_one_of_forall_smul_weight_eq _, fun h j => by rw [h, one_smul]⟩

end TauCeti.DynkinType.ChevalleyDatum
