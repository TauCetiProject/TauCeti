/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.Additive.Equivalence
public import TauCeti.InformationTheory.Coding.Weight.Enumerator

/-!
# Weight enumerators under permutation equivalence of additive codes

Relabelling coordinates preserves the weight distribution and both weight enumerators of an
additive code. These invariants apply to arbitrary group alphabets, including discriminant
alphabets without a field structure. The enumerators are the existing set-of-words invariants.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.7.
-/

public section

namespace TauCeti.AdditiveCode

variable {A ι κ : Type*} [AddGroup A] [Fintype ι] [Fintype κ] [DecidableEq A]

/-- Relabelling preserves each weight multiplicity. -/
@[simp]
theorem weightDistribution_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) (w : ℕ) :
    (reindex C e : Set (κ → A)).weightDistribution w =
      (C : Set (ι → A)).weightDistribution w := by
  rw [Set.weightDistribution_def, Set.weightDistribution_def]
  exact Nat.card_congr (Equiv.subtypeEquiv
    (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).symm.toEquiv fun x ↦ by
      simp only [mem_reindex, SetLike.mem_coe]
      have hx : (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).symm.toEquiv x =
          x ∘ e.symm := rfl
      rw [hx, Equiv.hammingNorm_comp])

/-- Permutation-equivalent additive codes have identical weight distributions. -/
theorem IsPermutationEquivalent.weightDistribution_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) (w : ℕ) :
    (C : Set (ι → A)).weightDistribution w = (D : Set (κ → A)).weightDistribution w := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  exact (weightDistribution_reindex C e w).symm

/-- Relabelling preserves the homogeneous weight enumerator. -/
@[simp]
theorem weightEnumerator_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    (reindex C e : Set (κ → A)).weightEnumerator = (C : Set (ι → A)).weightEnumerator := by
  simp only [Set.weightEnumerator_def, Fintype.card_congr e, weightDistribution_reindex]

/-- Permutation-equivalent additive codes have identical homogeneous weight enumerators. -/
theorem IsPermutationEquivalent.weightEnumerator_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) :
    (C : Set (ι → A)).weightEnumerator = (D : Set (κ → A)).weightEnumerator := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  exact (weightEnumerator_reindex C e).symm

/-- Relabelling preserves the one-variable weight polynomial. -/
@[simp]
theorem weightPolynomial_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    (reindex C e : Set (κ → A)).weightPolynomial = (C : Set (ι → A)).weightPolynomial := by
  simp only [Set.weightPolynomial_def, Fintype.card_congr e, weightDistribution_reindex]

/-- Permutation-equivalent additive codes have identical one-variable weight polynomials. -/
theorem IsPermutationEquivalent.weightPolynomial_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) :
    (C : Set (ι → A)).weightPolynomial = (D : Set (κ → A)).weightPolynomial := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  exact (weightPolynomial_reindex C e).symm

end TauCeti.AdditiveCode
