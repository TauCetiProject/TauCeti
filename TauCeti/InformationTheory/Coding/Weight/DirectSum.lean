/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.Weight.Enumerator
public import TauCeti.InformationTheory.Coding.DirectSum

/-!
# Weight enumerators of concatenated codes

Concatenating words on disjoint coordinate types adds their Hamming weights. For any two finite
sets of words, the homogeneous and one-variable weight enumerators of their concatenation are
the products of the enumerators of the two sets, and its weight distribution is their convolution.
No additive or scalar closure, or finiteness of the alphabet, is needed. Thus these formulas apply
to additive codes as well as linear codes. The linear direct-sum formulas are specializations.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.6 and §7.2,
and MacWilliams and Sloane, *The Theory of Error-Correcting Codes*, Chapter 5, §2.
-/

public section

open MvPolynomial Finset

namespace Set

variable {ι κ A : Type*} [Fintype ι] [Fintype κ] [Zero A] [DecidableEq A]
  {C : Set (ι → A)} {D : Set (κ → A)}

/-- Concatenating two finite sets of words multiplies their homogeneous weight enumerators. -/
theorem weightEnumerator_sumElim (hC : C.Finite) (hD : D.Finite) :
    ((fun p : (ι → A) × (κ → A) ↦ Sum.elim p.1 p.2) '' (C ×ˢ D)).weightEnumerator =
      C.weightEnumerator * D.weightEnumerator := by
  classical
  let e := (Equiv.sumArrowEquivProdArrow ι κ A).symm
  have he : (fun p : (ι → A) × (κ → A) ↦ Sum.elim p.1 p.2) = e := by
    funext p i
    rcases p with ⟨x, y⟩
    cases i <;> simp [e]
  rw [he, weightEnumerator_eq_sum ((hC.prod hD).image e), weightEnumerator_eq_sum hC,
    weightEnumerator_eq_sum hD, Set.Finite.toFinset_image e (hC.prod hD),
    ← Set.Finite.toFinset_prod hC hD,
    Finset.sum_image (fun _ _ _ _ h ↦ e.injective h), Finset.sum_product,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hsub : Fintype.card ι + Fintype.card κ - (hammingNorm x + hammingNorm y) =
      (Fintype.card ι - hammingNorm x) + (Fintype.card κ - hammingNorm y) := by
    have : hammingNorm x ≤ Fintype.card ι := hammingNorm_le_card_fintype
    have : hammingNorm y ≤ Fintype.card κ := hammingNorm_le_card_fintype
    omega
  rw [← he, TauCeti.hammingNorm_sumElim, Fintype.card_sum, hsub]
  ring

/-- Concatenating two finite sets of words multiplies their one-variable weight enumerators. -/
theorem weightPolynomial_sumElim (hC : C.Finite) (hD : D.Finite) :
    ((fun p : (ι → A) × (κ → A) ↦ Sum.elim p.1 p.2) '' (C ×ˢ D)).weightPolynomial =
      C.weightPolynomial * D.weightPolynomial := by
  simp only [← aeval_weightEnumerator, weightEnumerator_sumElim hC hD, map_mul]

/-- The weight distribution of a concatenation is the convolution of the two distributions. -/
theorem weightDistribution_sumElim (hC : C.Finite) (hD : D.Finite) (w : ℕ) :
    ((fun p : (ι → A) × (κ → A) ↦ Sum.elim p.1 p.2) '' (C ×ˢ D)).weightDistribution w =
      ∑ p ∈ Finset.antidiagonal w, C.weightDistribution p.1 * D.weightDistribution p.2 := by
  have h := congrArg (Polynomial.coeff · w) (weightPolynomial_sumElim hC hD)
  simp only [coeff_weightPolynomial, Polynomial.coeff_mul] at h
  exact_mod_cast h

end Set

namespace Submodule

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [Semiring R] [DecidableEq R]

/-- The weight enumerator of a direct sum of codes is the product of their weight
enumerators. -/
theorem weightEnumerator_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    [Finite C] [Finite D] :
    (directSum C D : Set (ι ⊕ κ → R)).weightEnumerator =
      (C : Set (ι → R)).weightEnumerator * (D : Set (κ → R)).weightEnumerator := by
  have hset : (directSum C D : Set (ι ⊕ κ → R)) =
      (fun p : (ι → R) × (κ → R) ↦ Sum.elim p.1 p.2) ''
        ((C : Set (ι → R)) ×ˢ (D : Set (κ → R))) := by
    ext x
    simp only [mem_directSum_iff, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨(fun i ↦ x (.inl i), fun j ↦ x (.inr j)), h, Sum.elim_comp_inl_inr x⟩
    · rintro ⟨⟨y, z⟩, h, rfl⟩
      exact h
  rw [hset]
  exact Set.weightEnumerator_sumElim (Set.toFinite _) (Set.toFinite _)

/-- The one-variable weight enumerator of a direct sum of codes is the product of their
one-variable weight enumerators. -/
theorem weightPolynomial_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    [Finite C] [Finite D] :
    (directSum C D : Set (ι ⊕ κ → R)).weightPolynomial =
      (C : Set (ι → R)).weightPolynomial * (D : Set (κ → R)).weightPolynomial := by
  simp only [← Set.aeval_weightEnumerator, weightEnumerator_directSum, map_mul]

/-- The weight distribution of a direct sum of codes is the convolution of their weight
distributions: `A_w(C ⊕ D) = ∑_{i + j = w} A_i(C) A_j(D)`. -/
theorem weightDistribution_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    [Finite C] [Finite D] (w : ℕ) :
    (directSum C D : Set (ι ⊕ κ → R)).weightDistribution w =
      ∑ p ∈ Finset.antidiagonal w,
        (C : Set (ι → R)).weightDistribution p.1 * (D : Set (κ → R)).weightDistribution p.2 := by
  have h := congrArg (Polynomial.coeff · w) (weightPolynomial_directSum C D)
  simp only [Set.coeff_weightPolynomial, Polynomial.coeff_mul] at h
  exact_mod_cast h

end Submodule
