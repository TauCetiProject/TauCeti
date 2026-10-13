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
The criterion `TauCeti.TypeDSpinCarrier.isCompletelyReducible_of_spinWeights_of_rootSubgroupPoints`
uses only the torus weights, numbered root actions, and parity of matrix coefficients, so it also
applies to the subgroup generated directly over the coefficient field.

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
    (N : Submodule R (Fin (dimension n) → R))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints n hn j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ v ∈ N)
    (j : Fin n ⊕ Fin n) {a b : Fin (dimension n)} (c : ℤˣ)
    (hmove : ((rootSubgroupPoints n hn j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ Pi.single a 1 -
        Pi.single a 1 = ((c : ℤ) : R) • Pi.single b 1)
    (ha : Pi.single a 1 ∈ N) : Pi.single b 1 ∈ N := by
  have hsub := N.sub_mem (hroot j _ ha) ha
  rw [hmove] at hsub
  rcases Int.units_eq_one_or c with rfl | rfl <;> simpa using hsub

private theorem single_reflection_mem
    (N : Submodule R (Fin (dimension n) → R))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints n hn j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ v ∈ N)
    (s : Finset (Fin n)) (i : Fin n)
    (hs : Pi.single (Fintype.equivFin (Finset (Fin n)) s) 1 ∈ N) :
    Pi.single (Fintype.equivFin (Finset (Fin n)) (typeDSpinReflection i s)) 1 ∈ N := by
  rcases typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one s i with hneg | hzero | hpos
  · obtain ⟨c, hc⟩ := exists_rootSubgroupPoints_inl_mulVec_single_sub n hn i
      (a := Fintype.equivFin (Finset (Fin n)) s)
      (a' := Fintype.equivFin (Finset (Fin n)) (typeDSpinReflection i s))
      (by simpa only [basisWeight, signSet, Equiv.symm_apply_apply] using hneg)
      (by simp [signSet]) R
    exact single_mem_of_root_move n hn R N hroot (.inl i) c
      (by simpa only [toAdd_ofAdd, one_mul] using hc (Multiplicative.ofAdd 1)) hs
  · rwa [(typeDSpinReflection_eq_self_iff i s).2 hzero]
  · obtain ⟨c, hc⟩ := exists_rootSubgroupPoints_inr_mulVec_single_sub n hn i
      (a := Fintype.equivFin (Finset (Fin n)) s)
      (a' := Fintype.equivFin (Finset (Fin n)) (typeDSpinReflection i s))
      (by simpa only [basisWeight, signSet, Equiv.symm_apply_apply] using hpos)
      (by simp [signSet]) R
    exact single_mem_of_root_move n hn R N hroot (.inr i) c
      (by simpa only [toAdd_ofAdd, one_mul] using hc (Multiplicative.ofAdd 1)) hs

/-- A submodule stable under the numbered spin root matrices containing one coordinate line
contains every coordinate line in its half-spin parity class. -/
theorem single_mem_of_parity_eq_of_rootSubgroupPoints
    (N : Submodule R (Fin (dimension n) → R))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints n hn j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ v ∈ N)
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
    (single_reflection_mem n hn R N hroot) l (signSet n b)).2
      (by simpa [signSet] using hb)
  simpa [hl, signSet] using h

variable (k : Type u) [Field k]

/-- A comodule with the distinct spin torus weights, the numbered root actions, and no
coefficients mixing half-spin parity is completely reducible. -/
theorem isCompletelyReducible_of_spinWeights_of_rootSubgroupPoints
    {H : Type*} [AddCommGroup H] [Module k H] [Coalgebra k H]
    [Comodule k H (Fin (dimension n) → k)]
    (τ : H →ₗc[k] (DiagonalizableGroup.coordinateRing k
      (SplitTorus.characterGroup (Fin n))).obj)
    (hτ : Comodule.Corestrict τ =
      Comodule.ofWeights (Pi.basisFun k (Fin (dimension n))) (basisCharacter n))
    (hroot : ∀ (N : Subcomodule k H (Fin (dimension n) → k)) j v, v ∈ N →
      ((rootSubgroupPoints n hn j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) k) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) k) *ᵥ v ∈ N)
    (hparity : ∀ a b, basisParity n a ≠ basisParity n b →
      Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin (dimension n))) a b = 0) :
    Comodule.IsCompletelyReducible k H (Fin (dimension n) → k) := by
  classical
  apply Comodule.IsCompletelyReducible.of_exists_isCompl
  intro N
  let s : Set (Fin (dimension n)) := {a | Pi.single a (1 : k) ∈ N}
  let M := (Pi.basisFun k (Fin (dimension n))).coordinateSpanSubcomodule sᶜ <|
    ((Pi.basisFun k (Fin (dimension n))).coordinateSpanIsStable_iff (C := H) sᶜ).2 <| by
      intro a ha b hb
      apply hparity
      intro h
      exact hb (single_mem_of_parity_eq_of_rootSubgroupPoints n hn k N.toSubmodule
        (hroot N) ((basisParity_eq_basisParity_iff n).1 h.symm) (Set.notMem_compl_iff.mp ha))
  refine ⟨M, ?_⟩
  rw [Module.Basis.coordinateSpanSubcomodule_toSubmodule,
    Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights τ (basisCharacter n)
      (basisCharacter_injective n) hτ N]
  exact (Pi.basisFun k (Fin (dimension n))).linearIndependent.isCompl_span_image
    (Pi.basisFun k (Fin (dimension n))).span_eq isCompl_compl

/-- The standard representation of the full-weight type-`Dₙ` spin carrier is completely
reducible over every field, including characteristic two. -/
theorem isCompletelyReducible_standardComodule :
    Comodule.IsCompletelyReducible k (coordinateHopfAlgebra n hn k) (Fin (dimension n) → k) :=
  isCompletelyReducible_of_spinWeights_of_rootSubgroupPoints n hn k
    (weightTorusToBaseChangeCoordinateMap n hn k).hom.toCoalgHom
    (torusCorestrict_eq_ofWeights n hn k)
    (fun N j _ hw ↦ points_mulVec_mem n hn k N
      (rootSubgroupPoints n hn j k (Multiplicative.ofAdd 1)) hw)
    (fun a b hab ↦ by
      rw [coefficientMatrix_basisFun]
      exact coordinateMap_X_eq_zero n hn k hab)

end TauCeti.TypeDSpinCarrier
