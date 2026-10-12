/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.StandardComodule
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# Torus weight lines of the type-D spin carrier

Restriction of the full spin representation to its weight torus is the direct sum of distinct
one-dimensional characters. Consequently every invariant submodule over a field is spanned by
the coordinate vectors it contains. Over an arbitrary commutative ring, every scaled coordinate
component of an invariant vector is still invariant.

These statements use the torus coaction, not its rational points, so they apply over finite
fields and in characteristic two. Together with the action of the simple root subgroups, they
reduce simplicity of the half-spin summands to connectivity of their weight graphs.

## Main results

* `TauCeti.TypeDSpinCarrier.single_smul_mem`: extraction of a scaled coordinate component.
* `TauCeti.TypeDSpinCarrier.toSubmodule_eq_sup_inf_halfSpinSubcomodule`: every invariant
  submodule splits along the two half-spin summands, over any commutative ring.
* `TauCeti.TypeDSpinCarrier.toSubmodule_eq_span`: coordinate description of every subcomodule
  over a field.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The character and restriction computations follow
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.StandardComodule`. Coordinate extraction uses
`TauCeti.Subcomodule.single_smul_mem_of_corestrict_eq_ofWeights` and its span counterpart.
-/

public section

namespace TauCeti.TypeDSpinCarrier

universe u

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

attribute [local instance] standardComodule

/-- Each scaled coordinate component of a vector in a spin subcomodule belongs to that
subcomodule, without a field or characteristic hypothesis. -/
theorem single_smul_mem
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    {v : Fin (dimension n) → R} (hv : v ∈ N) (a : Fin (dimension n)) :
    v a • Pi.single a 1 ∈ N :=
  Subcomodule.single_smul_mem_of_corestrict_eq_ofWeights
    (weightTorusToBaseChangeCoordinateMap n hn R).hom.toCoalgHom (basisCharacter n)
    (basisCharacter_injective n) (torusCorestrict_eq_ofWeights n hn R) N hv a

/-- Every invariant submodule splits along the even and odd half-spin summands. In particular,
invariant submodules cannot mix the two summands, even in characteristic two. -/
theorem toSubmodule_eq_sup_inf_halfSpinSubcomodule
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R)) :
    N.toSubmodule =
      (N.toSubmodule ⊓ (halfSpinSubcomodule n hn R 0).toSubmodule) ⊔
      (N.toSubmodule ⊓ (halfSpinSubcomodule n hn R 1).toSubmodule) := by
  classical
  apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro v hv
  rw [← Finset.univ_sum_single v]
  apply Submodule.sum_mem
  intro a _
  have hN : Pi.single a (v a) ∈ N := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using single_smul_mem n hn R N hv a
  have hspin : Pi.single a (v a) ∈
      halfSpinSubcomodule n hn R ((signSet n a).card : ZMod 2) := by
    rw [mem_halfSpinSubcomodule]
    intro b hb
    have hba : b ≠ a := by rintro rfl; exact hb rfl
    simp [hba]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) ((signSet n a).card : ZMod 2) with h | h
  · rw [h] at hspin
    exact Submodule.mem_sup_left ⟨hN, hspin⟩
  · rw [h] at hspin
    exact Submodule.mem_sup_right ⟨hN, hspin⟩

variable (k : Type u) [Field k]

/-- Over a field, every spin subcomodule is spanned by exactly the coordinate basis vectors
it contains. -/
theorem toSubmodule_eq_span
    (N : Subcomodule k (coordinateHopfAlgebra n hn k) (Fin (dimension n) → k)) :
    N.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin (dimension n))) ''
      {a | Pi.single a (1 : k) ∈ N}) :=
  Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (weightTorusToBaseChangeCoordinateMap n hn k).hom.toCoalgHom (basisCharacter n)
    (basisCharacter_injective n) (torusCorestrict_eq_ofWeights n hn k) N

end TauCeti.TypeDSpinCarrier
