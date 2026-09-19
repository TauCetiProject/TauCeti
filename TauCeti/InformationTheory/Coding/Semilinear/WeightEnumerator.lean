/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.Semilinear.Basic
public import TauCeti.InformationTheory.Coding.WeightEnumerator

/-!
# Weight enumerators of semilinearly equivalent codes

Semilinearly equivalent codes have the same weight distribution, homogeneous weight enumerator,
and one-variable weight polynomial. These invariants allow comparison of codes after uniform
alphabet conjugation, coordinate scaling, and relabelling.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.7.
-/

public section

namespace TauCeti

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {R ι κ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ] [DecidableEq R]
  {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}

/-- Semilinearly equivalent codes have the same weight distribution. -/
theorem IsSemilinearEquivalent.weightDistribution_eq (h : IsSemilinearEquivalent C D)
    (w : ℕ) :
    (C : Set (ι → R)).weightDistribution w = (D : Set (κ → R)).weightDistribution w := by
  obtain ⟨σ, u, e, rfl⟩ := isSemilinearEquivalent_iff.mp h
  rw [Set.weightDistribution_def, Set.weightDistribution_def]
  exact Nat.card_congr
    (Equiv.subtypeEquiv (semilinearMonomialEquiv u e σ).toEquiv fun x ↦ by simp)

/-- Semilinearly equivalent codes have the same homogeneous weight enumerator. -/
theorem IsSemilinearEquivalent.weightEnumerator_eq (h : IsSemilinearEquivalent C D) :
    (C : Set (ι → R)).weightEnumerator = (D : Set (κ → R)).weightEnumerator := by
  have hcard : Fintype.card ι = Fintype.card κ := by
    obtain ⟨_, _, e, _⟩ := isSemilinearEquivalent_iff.mp h
    exact Fintype.card_congr e
  simp_rw [Set.weightEnumerator_def, hcard, h.weightDistribution_eq]

/-- Semilinearly equivalent codes have the same one-variable weight polynomial. -/
theorem IsSemilinearEquivalent.weightPolynomial_eq (h : IsSemilinearEquivalent C D) :
    (C : Set (ι → R)).weightPolynomial = (D : Set (κ → R)).weightPolynomial := by
  rw [← Set.aeval_weightEnumerator, ← Set.aeval_weightEnumerator, h.weightEnumerator_eq]

end TauCeti
