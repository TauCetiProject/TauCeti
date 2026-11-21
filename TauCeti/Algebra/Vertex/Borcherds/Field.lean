/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.NthProduct
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Int.PascalRecurrence
import TauCeti.RingTheory.Binomial

/-!
# Field-level Borcherds identity

For any two mutually local vertex operators `A` and `B` over an arbitrary commutative ring `R`
(requiring neither `TauCeti.FormalVertexAxioms` nor `[HasUniqueDiv V]`), their `n`-th products
`VertexOperator.nthProduct` satisfy the three-parameter **Borcherds identity**:
`∑ᶠ i : ℕ, (m choose i) • ((A_{(n+i)} B)_{(m+r-i)}) v =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • (A_{(m+n-i)} (B_{(r+i)} v) - (-1)ⁿ B_{(n+r-i)} (A_{(m+i)} v))`.

The proof proceeds by two-way Pascal recurrence on `m` starting from the `m = 0` iterate formula
(`VertexOperator.ncoeff_nthProduct_apply`), together with the `n = 0` commutator formula
(`VertexOperator.IsLocalOfOrder.lie_ncoeff_eq_sum_nthProduct`) and diagonal shifting for negative
`m, n`.

## Main results

* `VertexOperator.IsLocalOfOrder.borcherds_finsum`: the field-level Borcherds identity in
  `finsum` form over any commutative ring.
* `VertexOperator.IsLocalOfOrder.borcherds`: explicit finite-cutoff form of the field-level
  Borcherds identity.

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

private theorem hasFiniteSupport_of_forall_eq_zero {M : Type*} [Zero M] {f : ℕ → M} (K : ℕ)
    (hf : ∀ i : ℕ, K ≤ i → f i = 0) : Function.HasFiniteSupport f :=
  (Finset.finite_toSet (range K)).subset fun i hi ↦ by
    simpa only [mem_coe, mem_range] using lt_of_not_ge fun hle ↦ hi (hf i hle)

private def borcherdsLHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v

private def borcherdsRHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    ((A[[m + n - i]]) ((B[[r + i]]) v) -
      (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v))

private theorem borcherdsLHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hM : ∀ i : ℕ, M ≤ i → nthProduct (n + i) A B = 0) :
    borcherdsLHS A B v m n r =
      ∑ i ∈ range M, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v := by
  unfold borcherdsLHS
  exact TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hM i hi]

private theorem borcherdsRHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hB : ∀ i : ℕ, M ≤ i → (B[[r + i]]) v = 0) (hA : ∀ i : ℕ, M ≤ i → (A[[m + i]]) v = 0) :
    borcherdsRHS A B v m n r =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[m + n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  unfold borcherdsRHS
  exact TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hB i hi, hA i hi]

private theorem borcherdsRHS_eq_sub (A B : VertexOperator R V) (v : V) (m n r : ℤ) :
    borcherdsRHS A B v m n r =
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + i]]) v)) -
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v) := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  have h₁ : Function.HasFiniteSupport fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + i]]) v) :=
    hasFiniteSupport_of_forall_eq_zero ((N₂ : ℤ) - r).toNat fun i hi ↦ by
      simp [hN₂ (r + i) (by omega)]
  have h₂ : Function.HasFiniteSupport fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n i) •
        (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v) :=
    hasFiniteSupport_of_forall_eq_zero ((N₃ : ℤ) - m).toNat fun i hi ↦ by
      simp [hN₃ (m + i) (by omega)]
  simp only [borcherdsRHS, smul_sub]
  exact finsum_sub_distrib h₁ h₂

private theorem borcherdsLHS_add_one {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    borcherdsLHS A B v (m + 1) n r =
      borcherdsLHS A B v m n (r + 1) + borcherdsLHS A B v m (n + 1) r := by
  have hu : Function.HasFiniteSupport fun i : ℕ ↦
      ((nthProduct (n + i) A B)[[m + 1 + r - i]]) v :=
    hasFiniteSupport_of_forall_eq_zero ((N : ℤ) - n).toNat fun i hi ↦ by
      simp [h.nthProduct_eq_zero (n := n + i) (by omega)]
  rw [borcherdsLHS, borcherdsLHS, borcherdsLHS,
    TauCeti.Ring.finsum_choose_add_one_smul (R := ℤ) m hu]
  congr 1
  · exact finsum_congr fun i ↦ by rw [show m + 1 + r - (i : ℤ) = m + (r + 1) - i by omega]
  · exact finsum_congr fun i ↦ by
      rw [show n + ((i + 1 : ℕ) : ℤ) = n + 1 + i by omega,
        show m + 1 + r - ((i + 1 : ℕ) : ℤ) = m + r - i by omega]

private theorem borcherdsRHS_add_one (A B : VertexOperator R V) (v : V) (m n r : ℤ) :
    borcherdsRHS A B v (m + 1) n r =
      borcherdsRHS A B v m n (r + 1) + borcherdsRHS A B v m (n + 1) r := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  have hu₁ : Function.HasFiniteSupport fun i : ℕ ↦ (A[[m + 1 + n - i]]) ((B[[r + i]]) v) :=
    hasFiniteSupport_of_forall_eq_zero ((N₂ : ℤ) - r).toNat fun i hi ↦ by
      simp [hN₂ (r + i) (by omega)]
  have hu₂ : Function.HasFiniteSupport fun i : ℕ ↦
      (n.negOnePow : ℤ) • (B[[n + (r + 1) - i]]) ((A[[m + i]]) v) :=
    hasFiniteSupport_of_forall_eq_zero ((N₃ : ℤ) - m).toNat fun i hi ↦ by
      simp [hN₃ (m + i) (by omega)]
  have h₁ := TauCeti.Ring.finsum_neg_one_pow_mul_choose_smul (R := ℤ) n hu₁
  have h₂ := TauCeti.Ring.finsum_neg_one_pow_mul_choose_smul (R := ℤ) n hu₂
  rw [show (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (A[[m + 1 + n - ((i + 1 : ℕ) : ℤ)]]) ((B[[r + ((i + 1 : ℕ) : ℤ)]]) v)) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (A[[m + n - i]]) ((B[[r + 1 + i]]) v) from finsum_congr fun i ↦ by
      rw [show m + 1 + n - ((i + 1 : ℕ) : ℤ) = m + n - i by omega,
        show r + ((i + 1 : ℕ) : ℤ) = r + 1 + i by omega],
    show (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) •
        (A[[m + 1 + n - (i : ℤ)]]) ((B[[r + i]]) v)) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) •
        (A[[m + (n + 1) - i]]) ((B[[r + i]]) v) from finsum_congr fun i ↦ by
      rw [show m + 1 + n - (i : ℤ) = m + (n + 1) - i by omega] ] at h₁
  rw [show (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (n.negOnePow : ℤ) • (B[[n + (r + 1) - ((i + 1 : ℕ) : ℤ)]])
          ((A[[m + ((i + 1 : ℕ) : ℤ)]]) v)) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + 1 + i]]) v) from finsum_congr fun i ↦ by
      rw [show n + (r + 1) - ((i + 1 : ℕ) : ℤ) = n + r - i by omega,
        show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by omega],
    show (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) •
        (n.negOnePow : ℤ) • (B[[n + (r + 1) - (i : ℤ)]]) ((A[[m + i]]) v)) =
      - ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) •
        ((n + 1).negOnePow : ℤ) • (B[[n + 1 + r - (i : ℤ)]]) ((A[[m + i]]) v) from by
      rw [← finsum_neg_distrib]
      exact finsum_congr fun i ↦ by
        rw [Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg, neg_neg,
          show n + 1 + r - (i : ℤ) = n + (r + 1) - i by omega] ] at h₂
  rw [borcherdsRHS_eq_sub, borcherdsRHS_eq_sub, borcherdsRHS_eq_sub, h₁, h₂]
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
  suffices borcherdsLHS A B v m n r = borcherdsRHS A B v m n r by
    simpa only [borcherdsLHS, borcherdsRHS] using this
  refine borcherds_eq_of_zero h (fun q s ↦ ?_) (fun p s ↦ ?_) m n r
  · rw [borcherdsLHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    simpa [borcherdsRHS] using ncoeff_nthProduct_apply A B q s v
  · rw [borcherdsRHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    have hL : borcherdsLHS A B v p 0 s = (⁅A[[p]], B[[s]]⁆) v := by
      rw [h.lie_ncoeff_eq_sum_nthProduct p s, LinearMap.sum_apply,
        borcherdsLHS_eq_sum (M := N) fun i hi ↦ h.nthProduct_eq_zero (by omega)]
      exact sum_congr rfl fun i _ ↦ by simp only [zero_add, LinearMap.smul_apply]
    simpa [Ring.lie_def, mul_apply_eq_comp] using hL

/-- **Field-level Borcherds identity** with explicit finite cutoff `M`, over any commutative ring:
all three mode expressions vanish for `i ≥ M`, and the finite sums over `Finset.range M` agree. -/
theorem IsLocalOfOrder.borcherds {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    ∃ M : ℕ,
      (∀ i : ℕ, M ≤ i → ((nthProduct (n + i) A B)[[m + r - i]]) v = 0) ∧
      (∀ i : ℕ, M ≤ i →
        (A[[m + n - i]]) ((B[[r + i]]) v) = 0 ∧ (B[[n + r - i]]) ((A[[m + i]]) v) = 0) ∧
      (∑ i ∈ range M, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v) =
        ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
          ((A[[m + n - i]]) ((B[[r + i]]) v) -
            (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M := max ((N : ℤ) - n).toNat (max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat)
  have hcut (i : ℕ) (hi : M ≤ i) : nthProduct (n + i) A B = 0 :=
    h.nthProduct_eq_zero (by omega)
  refine ⟨M, fun i hi ↦ by simp [hcut i hi],
    fun i hi ↦ ⟨by simp [hN₂ (r + i) (by omega)], by simp [hN₃ (m + i) (by omega)]⟩, ?_⟩
  rw [← borcherdsLHS_eq_sum hcut,
    ← borcherdsRHS_eq_sum (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  simpa only [borcherdsLHS, borcherdsRHS] using h.borcherds_finsum v m n r

end BorcherdsField

end VertexOperator
