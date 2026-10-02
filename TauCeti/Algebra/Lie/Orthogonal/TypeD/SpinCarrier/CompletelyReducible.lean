/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.TorusWeights
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.RootBasis
import TauCeti.Data.List.Involutive

/-!
# Complete reducibility of the type-D spin carrier representation

Over every field, the standard representation of the full-weight type-`Dₙ` spin carrier
is completely reducible. The distinct torus characters extract its coordinate lines, and
positive and negative simple-root points propagate each line through its entire half-spin
parity class. The coordinate lines absent from a subcomodule therefore form a union of
half-spin summands and give an invariant complement.

The torus coaction, rather than rational torus points, separates weights. Root moves have
integral-unit coefficients. Thus the result includes finite fields and characteristic two.
Together with faithfulness it allows elimination of normal smooth unipotent subgroups.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The coordinate-complement argument follows
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.CompletelyReducible`; signed root propagation follows
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.StandardComodule`.
-/

public section

open TauCeti.DynkinType
open scoped Matrix

namespace TauCeti.TypeDSpinCarrier

universe u

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

attribute [local instance] standardComodule

private theorem single_mem_of_root_move
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    (j : Fin n ⊕ Fin n) {a b : Fin (dimension n)} (c : ℤˣ)
    (hmove : ((rootSubgroupPoints n hn j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ Pi.single a 1 -
        Pi.single a 1 = ((c : ℤ) : R) • Pi.single b 1)
    (ha : Pi.single a 1 ∈ N) : Pi.single b 1 ∈ N := by
  have hsub := N.toSubmodule.sub_mem
    (points_mulVec_mem n hn R N (rootSubgroupPoints n hn j R
      (Multiplicative.ofAdd 1)) ha) ha
  rw [hmove] at hsub
  rcases Int.units_eq_one_or c with rfl | rfl <;> simpa using hsub

private theorem single_reflection_mem
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    (s : Finset (Fin n)) (i : Fin n)
    (hs : Pi.single (Fintype.equivFin (Finset (Fin n)) s) 1 ∈ N) :
    Pi.single (Fintype.equivFin (Finset (Fin n)) (typeDSpinReflection i s)) 1 ∈ N := by
  rcases typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one s i with hneg | hzero | hpos
  · obtain ⟨c, hc⟩ := exists_rootSubgroupPoints_inl_mulVec_single_sub n hn i
      (a := Fintype.equivFin (Finset (Fin n)) s)
      (a' := Fintype.equivFin (Finset (Fin n)) (typeDSpinReflection i s))
      (by simpa only [basisWeight, signSet, Equiv.symm_apply_apply] using hneg)
      (by simp [signSet]) R
    exact single_mem_of_root_move n hn R N (.inl i) c
      (by simpa only [toAdd_ofAdd, one_mul] using hc (Multiplicative.ofAdd 1)) hs
  · rwa [(typeDSpinReflection_eq_self_iff i s).2 hzero]
  · obtain ⟨c, hc⟩ := exists_rootSubgroupPoints_inr_mulVec_single_sub n hn i
      (a := Fintype.equivFin (Finset (Fin n)) s)
      (a' := Fintype.equivFin (Finset (Fin n)) (typeDSpinReflection i s))
      (by simpa only [basisWeight, signSet, Equiv.symm_apply_apply] using hpos)
      (by simp [signSet]) R
    exact single_mem_of_root_move n hn R N (.inr i) c
      (by simpa only [toAdd_ofAdd, one_mul] using hc (Multiplicative.ofAdd 1)) hs

/-- A spin subcomodule containing one coordinate line contains all coordinate lines in its
half-spin parity class. -/
theorem single_mem_of_parity_eq
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    {a b : Fin (dimension n)}
    (hab : ((signSet n a).card : ZMod 2) = (signSet n b).card)
    (hb : Pi.single b 1 ∈ N) : Pi.single a 1 ∈ N := by
  have hparity : Even (signSet n b).card ↔ Even (signSet n a).card := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even, hab]
  obtain ⟨l, hl⟩ := (exists_typeDSpinReflections_eq_iff (by omega : 2 ≤ n)
    (signSet n b) (signSet n a)).2 hparity
  have h := (predicate_foldl_iff_of_involutive
    (fun s ↦ Pi.single (Fintype.equivFin (Finset (Fin n)) s) (1 : R) ∈ N)
    typeDSpinReflection typeDSpinReflection_involutive
    (single_reflection_mem n hn R N) l (signSet n b)).2
      (by simpa [signSet] using hb)
  simpa [hl, signSet] using h

variable (k : Type u) [Field k]

/-- The standard representation of the full-weight type-`Dₙ` spin carrier is completely
reducible over every field, including characteristic two. -/
theorem isCompletelyReducible_standardComodule :
    Comodule.IsCompletelyReducible k (coordinateHopfAlgebra n hn k) (Fin (dimension n) → k) := by
  classical
  apply Comodule.IsCompletelyReducible.of_exists_isCompl
  intro N
  let s : Set (Fin (dimension n)) := {a | Pi.single a (1 : k) ∈ N}
  -- The absent coordinate lines form a union of the two preserved half-spin blocks.
  let M := (Pi.basisFun k (Fin (dimension n))).coordinateSpanSubcomodule sᶜ <|
    ((Pi.basisFun k (Fin (dimension n))).coordinateSpanIsStable_iff
      (C := coordinateHopfAlgebra n hn k) sᶜ).2 <| by
      intro a ha b hb
      have hab : basisParity n a ≠ basisParity n b := fun h ↦
        hb (single_mem_of_parity_eq n hn k N ((basisParity_eq_basisParity_iff n).1 h.symm)
          (Set.notMem_compl_iff.mp ha))
      rw [coefficientMatrix_basisFun]
      exact coordinateMap_X_eq_zero n hn k hab
  refine ⟨M, ?_⟩
  rw [Module.Basis.coordinateSpanSubcomodule_toSubmodule, toSubmodule_eq_span n hn k N]
  exact (Pi.basisFun k (Fin (dimension n))).linearIndependent.isCompl_span_image
    (Pi.basisFun k (Fin (dimension n))).span_eq isCompl_compl

end TauCeti.TypeDSpinCarrier
