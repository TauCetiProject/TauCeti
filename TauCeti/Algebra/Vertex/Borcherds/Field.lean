/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.NthProduct
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Int.PascalRecurrence
import TauCeti.RingTheory.Binomial.PascalSum

/-!
# Field-level Borcherds identity

For any two mutually local vertex operators `A` and `B` over an arbitrary commutative ring `R`
(requiring neither `TauCeti.FormalVertexAxioms` nor `[HasUniqueDiv V]`), their `n`-th products
`VertexOperator.nthProduct` satisfy the three-parameter **Borcherds identity**:
`∑ᶠ i : ℕ, (m choose i) • ((A_{(n+i)} B)_{(m+r-i)}) v =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • (A_{(m+n-i)} (B_{(r+i)} v) - (-1)ⁿ B_{(n+r-i)} (A_{(m+i)} v))`.

The proof follows from the Pascal recurrence on `(m, n, r)` via
`TauCeti.eq_zero_of_pascal_recurrence`, with the `m = 0` iterate formula
(`VertexOperator.ncoeff_nthProduct_apply_eq_finsum`) and the `n = 0` commutator formula
(`VertexOperator.IsLocalOfOrder.lie_ncoeff_eq_sum_nthProduct`) as base cases.

## Main results

* `VertexOperator.IsLocalOfOrder.borcherds_finsum`: the field-level Borcherds identity in
  `finsum` form over any commutative ring.

## References

* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), 143–195, §2.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.8.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

section BorcherdsField

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem IsLocalOfOrder.exists_nthProduct_add_cutoff {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (s : ℤ) :
    ∃ K : ℕ, ∀ i : ℕ, K ≤ i → nthProduct (s + i) A B = 0 :=
  ⟨(N - s).toNat, fun i hi ↦ h.nthProduct_eq_zero (by omega)⟩

private def borcherdsLHSTerm (A B : VertexOperator R V) (v : V) (m n r : ℤ) (i : ℕ) : V :=
  ((nthProduct (n + i) A B)[[m + r - i]]) v

private def borcherdsLHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • borcherdsLHSTerm A B v m n r i

private def borcherdsRHSTerm₁ (A B : VertexOperator R V) (v : V) (m n r : ℤ) (i : ℕ) : V :=
  (A[[m + n - i]]) ((B[[r + i]]) v)

private def borcherdsRHSTerm₂ (A B : VertexOperator R V) (v : V) (m n r : ℤ) (i : ℕ) : V :=
  (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)

private def borcherdsRHSWeighted₁ (A B : VertexOperator R V) (v : V) (m n r : ℤ) (i : ℕ) : V :=
  ((-1 : ℤ) ^ i * Ring.choose n i) • borcherdsRHSTerm₁ A B v m n r i

private def borcherdsRHSWeighted₂ (A B : VertexOperator R V) (v : V) (m n r : ℤ) (i : ℕ) : V :=
  ((-1 : ℤ) ^ i * Ring.choose n i) • borcherdsRHSTerm₂ A B v m n r i

private def borcherdsRHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    (borcherdsRHSTerm₁ A B v m n r i - borcherdsRHSTerm₂ A B v m n r i)

private theorem borcherdsLHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hM : ∀ i : ℕ, M ≤ i → nthProduct (n + i) A B = 0) :
    borcherdsLHS A B v m n r =
      ∑ i ∈ range M, Ring.choose m i • borcherdsLHSTerm A B v m n r i := by
  unfold borcherdsLHS
  exact TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by
    simp [borcherdsLHSTerm, hM i hi]

private theorem borcherdsRHS_eq_sub (A B : VertexOperator R V) (v : V) (m n r : ℤ) :
    borcherdsRHS A B v m n r =
      (∑ᶠ i : ℕ, borcherdsRHSWeighted₁ A B v m n r i) -
        ∑ᶠ i : ℕ, borcherdsRHSWeighted₂ A B v m n r i := by
  obtain ⟨K₁, hK₁⟩ := B.exists_forall_ncoeff_add_apply_eq_zero v r
  obtain ⟨K₂, hK₂⟩ := A.exists_forall_ncoeff_add_apply_eq_zero v m
  have h₁ : Function.HasFiniteSupport (borcherdsRHSWeighted₁ A B v m n r) :=
    TauCeti.hasFiniteSupport_of_forall_eq_zero K₁ fun i hi ↦ by
      simp [borcherdsRHSWeighted₁, borcherdsRHSTerm₁, hK₁ i hi]
  have h₂ : Function.HasFiniteSupport (borcherdsRHSWeighted₂ A B v m n r) :=
    TauCeti.hasFiniteSupport_of_forall_eq_zero K₂ fun i hi ↦ by
      simp [borcherdsRHSWeighted₂, borcherdsRHSTerm₂, hK₂ i hi]
  simp only [borcherdsRHS, smul_sub]
  exact finsum_sub_distrib h₁ h₂

private theorem negOnePow_smul_add_one {M : Type*} [AddCommGroup M] (n : ℤ) (x : M) :
    (n.negOnePow : ℤ) • x = -(((n + 1).negOnePow : ℤ) • x) := by
  rw [Int.negOnePow_succ, Units.val_neg, neg_smul, neg_neg]

private theorem borcherdsLHS_add_one {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    borcherdsLHS A B v (m + 1) n r =
      borcherdsLHS A B v m n (r + 1) + borcherdsLHS A B v m (n + 1) r := by
  obtain ⟨K, hK⟩ := h.exists_nthProduct_add_cutoff n
  have hu : Function.HasFiniteSupport (borcherdsLHSTerm A B v (m + 1) n r) :=
    TauCeti.hasFiniteSupport_of_forall_eq_zero K fun i hi ↦ by
      simp [borcherdsLHSTerm, hK i hi]
  have h₁ (i : ℕ) :
      borcherdsLHSTerm A B v (m + 1) n r i = borcherdsLHSTerm A B v m n (r + 1) i := by
    simp only [borcherdsLHSTerm]
    rw [show m + 1 + r - (i : ℤ) = m + (r + 1) - i by omega]
  have h₂ (i : ℕ) :
      borcherdsLHSTerm A B v (m + 1) n r (i + 1) = borcherdsLHSTerm A B v m (n + 1) r i := by
    simp only [borcherdsLHSTerm, Nat.cast_add, Nat.cast_one]
    rw [show n + ((i : ℤ) + 1) = n + 1 + i by omega,
      show m + 1 + r - ((i : ℤ) + 1) = m + r - i by omega]
  have hsum := TauCeti.Ring.finsum_choose_add_one_smul (R := ℤ) m hu
  rw [finsum_congr fun i ↦ congrArg (Ring.choose m i • ·) (h₁ i),
    finsum_congr fun i ↦ congrArg (Ring.choose m i • ·) (h₂ i)] at hsum
  exact hsum

private theorem borcherdsRHS_add_one (A B : VertexOperator R V) (v : V) (m n r : ℤ) :
    borcherdsRHS A B v (m + 1) n r =
      borcherdsRHS A B v m n (r + 1) + borcherdsRHS A B v m (n + 1) r := by
  obtain ⟨K₁, hK₁⟩ := B.exists_forall_ncoeff_add_apply_eq_zero v r
  obtain ⟨K₂, hK₂⟩ := A.exists_forall_ncoeff_add_apply_eq_zero v m
  have hu₁ : Function.HasFiniteSupport (borcherdsRHSTerm₁ A B v (m + 1) n r) :=
    TauCeti.hasFiniteSupport_of_forall_eq_zero K₁ fun i hi ↦ by
      simp [borcherdsRHSTerm₁, hK₁ i hi]
  have hu₂ : Function.HasFiniteSupport (borcherdsRHSTerm₂ A B v m n (r + 1)) :=
    TauCeti.hasFiniteSupport_of_forall_eq_zero K₂ fun i hi ↦ by
      simp [borcherdsRHSTerm₂, hK₂ i hi]
  have h₁ := TauCeti.Ring.finsum_neg_one_pow_mul_choose_smul (R := ℤ) n hu₁
  have h₂ := TauCeti.Ring.finsum_neg_one_pow_mul_choose_smul (R := ℤ) n hu₂
  have h₁_shift (i : ℕ) :
      borcherdsRHSTerm₁ A B v (m + 1) n r (i + 1) = borcherdsRHSTerm₁ A B v m n (r + 1) i := by
    simp only [borcherdsRHSTerm₁, Nat.cast_add, Nat.cast_one]
    rw [show m + 1 + n - ((i : ℤ) + 1) = m + n - i by omega,
      show r + ((i : ℤ) + 1) = r + 1 + i by omega]
  have h₁_inc (i : ℕ) :
      borcherdsRHSTerm₁ A B v (m + 1) n r i = borcherdsRHSTerm₁ A B v m (n + 1) r i := by
    simp only [borcherdsRHSTerm₁]
    rw [show m + 1 + n - (i : ℤ) = m + (n + 1) - i by omega]
  have h₂_shift (i : ℕ) :
      borcherdsRHSTerm₂ A B v m n (r + 1) (i + 1) = borcherdsRHSTerm₂ A B v (m + 1) n r i := by
    simp only [borcherdsRHSTerm₂, Nat.cast_add, Nat.cast_one]
    rw [show n + (r + 1) - ((i : ℤ) + 1) = n + r - i by omega,
      show m + ((i : ℤ) + 1) = m + 1 + i by omega]
  have h₂_inc (i : ℕ) :
      ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) • borcherdsRHSTerm₂ A B v m n (r + 1) i =
        -(((-1 : ℤ) ^ i * Ring.choose (n + 1) i) • borcherdsRHSTerm₂ A B v m (n + 1) r i) := by
    simp only [borcherdsRHSTerm₂]
    rw [show n + (r + 1) - (i : ℤ) = n + 1 + r - i by omega, negOnePow_smul_add_one, smul_neg]
  rw [finsum_congr fun i ↦ congrArg (((-1 : ℤ) ^ i * Ring.choose n i) • ·) (h₁_shift i),
    finsum_congr fun i ↦ congrArg (((-1 : ℤ) ^ i * Ring.choose (n + 1) i) • ·) (h₁_inc i)] at h₁
  rw [finsum_congr fun i ↦ congrArg (((-1 : ℤ) ^ i * Ring.choose n i) • ·) (h₂_shift i),
    finsum_congr h₂_inc, finsum_neg_distrib] at h₂
  rw [borcherdsRHS_eq_sub, borcherdsRHS_eq_sub, borcherdsRHS_eq_sub]
  simp only [borcherdsRHSWeighted₁, borcherdsRHSWeighted₂]
  rw [h₁, h₂]
  abel

private theorem borcherds_eq_of_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {v : V}
    (h0n : ∀ q s : ℤ, borcherdsLHS A B v 0 q s = borcherdsRHS A B v 0 q s)
    (hm0 : ∀ p s : ℤ, borcherdsLHS A B v p 0 s = borcherdsRHS A B v p 0 s)
    (m n r : ℤ) : borcherdsLHS A B v m n r = borcherdsRHS A B v m n r := by
  refine sub_eq_zero.mp <| TauCeti.eq_zero_of_pascal_recurrence
    (fun p q s ↦ borcherdsLHS A B v p q s - borcherdsRHS A B v p q s)
    (fun p q s ↦ ?_) (fun q s ↦ sub_eq_zero.mpr (h0n q s))
    (fun p s ↦ sub_eq_zero.mpr (hm0 p s)) m n r
  simp only [borcherdsLHS_add_one h, borcherdsRHS_add_one]
  abel

private theorem borcherds_eq {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    borcherdsLHS A B v m n r = borcherdsRHS A B v m n r := by
  refine borcherds_eq_of_zero h (fun q s ↦ ?_) (fun p s ↦ ?_) m n r
  · rw [borcherdsLHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    simpa [borcherdsRHS, borcherdsLHSTerm, borcherdsRHSTerm₁, borcherdsRHSTerm₂] using
      ncoeff_nthProduct_apply_eq_finsum A B q s v
  · rw [borcherdsRHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    have hL : borcherdsLHS A B v p 0 s = (⁅A[[p]], B[[s]]⁆) v := by
      rw [h.lie_ncoeff_eq_sum_nthProduct p s, LinearMap.sum_apply,
        borcherdsLHS_eq_sum (M := N) fun i hi ↦ h.nthProduct_eq_zero (by omega)]
      exact sum_congr rfl fun i _ ↦ by
        simp only [zero_add, LinearMap.smul_apply, borcherdsLHSTerm]
    simpa [borcherdsRHSTerm₁, borcherdsRHSTerm₂, Ring.lie_def, mul_apply_eq_comp] using hL

/-- **Field-level Borcherds identity** in `finsum` form, over any commutative ring: for mutually
local fields `A, B` (local of order `N`), any `v : V`, and all integers `m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) ((A_{(n+i)} B)_{(m+r-i)}) v =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (A₍ₘ₊ₙ₋ᵢ₎ (B₍ᵣ₊ᵢ₎ v) - (-1)ⁿ B₍ₙ₊ᵣ₋ᵢ₎ (A₍ₘ₊ᵢ₎ v))`. -/
theorem IsLocalOfOrder.borcherds_finsum {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[m + n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  simpa only [borcherdsLHS, borcherdsRHS, borcherdsLHSTerm, borcherdsRHSTerm₁,
    borcherdsRHSTerm₂] using borcherds_eq h v m n r

end BorcherdsField

end VertexOperator
