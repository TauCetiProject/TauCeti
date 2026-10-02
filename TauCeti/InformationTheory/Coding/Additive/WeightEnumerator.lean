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

Permutation equivalence follows Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.6.
For weight enumerators see their §7.2 and MacWilliams and Sloane, *The Theory of Error-Correcting
Codes*, Chapter 5, §2, as in the set-level enumerator module.
-/

public section

namespace TauCeti.AdditiveCode

variable {A ι κ : Type*} [AddGroup A] [Fintype ι] [Fintype κ] [DecidableEq A]

/-- Relabelling preserves each weight multiplicity. -/
@[simp↓]
theorem weightDistribution_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) (w : ℕ) :
    (reindex C e : Set (κ → A)).weightDistribution w =
      (C : Set (ι → A)).weightDistribution w := by
  rw [coe_reindex]
  have hcomp : ⇑(Equiv.arrowCongr e.symm (Equiv.refl A)) = (· ∘ e) := by
    ext x j
    simp
  have hf (x : ι → A) :
      hammingNorm (Equiv.arrowCongr e.symm (Equiv.refl A) x) = hammingNorm x := by
    rw [hcomp]
    exact Equiv.hammingNorm_comp e x
  simpa only [hcomp] using
    weightDistribution_image (C : Set (ι → A)) (Equiv.arrowCongr e.symm (Equiv.refl A)) hf w

/-- Permutation-equivalent additive codes have identical weight distributions. -/
theorem IsPermutationEquivalent.weightDistribution_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) (w : ℕ) :
    (C : Set (ι → A)).weightDistribution w = (D : Set (κ → A)).weightDistribution w := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  exact (weightDistribution_reindex C e w).symm

/-- Relabelling preserves the homogeneous weight enumerator. -/
@[simp↓]
theorem weightEnumerator_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    (reindex C e : Set (κ → A)).weightEnumerator = (C : Set (ι → A)).weightEnumerator := by
  rw [coe_reindex]
  have hcomp : ⇑(Equiv.arrowCongr e.symm (Equiv.refl A)) = (· ∘ e) := by
    ext x j
    simp
  have hf (x : ι → A) :
      hammingNorm (Equiv.arrowCongr e.symm (Equiv.refl A) x) = hammingNorm x := by
    rw [hcomp]
    exact Equiv.hammingNorm_comp e x
  simpa only [hcomp] using
    weightEnumerator_image (C : Set (ι → A)) (Equiv.arrowCongr e.symm (Equiv.refl A)) hf
      (Fintype.card_congr e.symm)

/-- Permutation-equivalent additive codes have identical homogeneous weight enumerators. -/
theorem IsPermutationEquivalent.weightEnumerator_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) :
    (C : Set (ι → A)).weightEnumerator = (D : Set (κ → A)).weightEnumerator := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  exact (weightEnumerator_reindex C e).symm

/-- Relabelling preserves the one-variable weight polynomial. -/
@[simp↓]
theorem weightPolynomial_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    (reindex C e : Set (κ → A)).weightPolynomial = (C : Set (ι → A)).weightPolynomial := by
  rw [coe_reindex]
  have hcomp : ⇑(Equiv.arrowCongr e.symm (Equiv.refl A)) = (· ∘ e) := by
    ext x j
    simp
  have hf (x : ι → A) :
      hammingNorm (Equiv.arrowCongr e.symm (Equiv.refl A) x) = hammingNorm x := by
    rw [hcomp]
    exact Equiv.hammingNorm_comp e x
  simpa only [hcomp] using
    weightPolynomial_image (C : Set (ι → A)) (Equiv.arrowCongr e.symm (Equiv.refl A)) hf
      (Fintype.card_congr e.symm)

/-- Permutation-equivalent additive codes have identical one-variable weight polynomials. -/
theorem IsPermutationEquivalent.weightPolynomial_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) :
    (C : Set (ι → A)).weightPolynomial = (D : Set (κ → A)).weightPolynomial := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  exact (weightPolynomial_reindex C e).symm

end TauCeti.AdditiveCode
