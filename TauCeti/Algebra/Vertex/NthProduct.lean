/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.HasseDeriv
public import TauCeti.Algebra.Vertex.ResidueProduct
public import TauCeti.Algebra.Vertex.NormalOrder
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Data.Nat.Choose.Sum
import TauCeti.RingTheory.Binomial
import Mathlib.Tactic.Module

/-!
# Integer residue products of vertex operators

For any integer `n : ℤ`, the `n`-th product `A₍ₙ₎ B` (`VertexOperator.nthProduct n A B`) of two
fields `A, B : VertexOperator R V` over a commutative ring `R` combines:

* for `0 ≤ n`, the singular residue product `nonnegResidueProduct n.toNat A B`;
* for `n < 0`, say `n = -k - 1`, the normal-ordered Hasse-derivative product
  `normalOrder (hasseDeriv k A) B`.

Using Hasse derivatives avoids dividing by `k!`, so `nthProduct` is `R`-bilinear over every
commutative ring and needs no mutual-locality hypothesis.

On any vector `v`, both branches satisfy the single finite-sum mode formula
`((nthProduct n A B)[[m]]) v =`
`∑ i < K, (-1)^i (n choose i) (A₍ₙ₋ᵢ₎ B₍ₘ₊ᵢ₎ v - (-1)ⁿ B₍ₙ₊ₘ₋ᵢ₎ A₍ᵢ₎ v)`
once `K` exceeds the truncation cutoffs of `A` and `B` on `v` (`ncoeff_nthProduct_apply_eq_sum`);
specializing this expansion evaluates `nthProduct n A B` on a vacuum vector
(`ncoeff_nthProduct_apply_of_nonneg` and `ncoeff_neg_one_nthProduct_apply`).
Formal differentiation acts as a derivation (`derivative_nthProduct`) and satisfies
`(∂A)₍ₙ₎ B = -n A₍ₙ₋₁₎ B` (`nthProduct_derivative_left`); together with the general endomorphism
derivation rule `lie_ncoeff_nthProduct_eq_add`, this implies translation covariance of all `n`-th
products (`lie_ncoeff_nthProduct`).

## Main definitions

* `VertexOperator.nthProduct`: the `R`-bilinear `n`-th product on `VertexOperator R V` for `n : ℤ`.

## Main results

* `VertexOperator.ncoeff_nthProduct_apply_eq_sum`: unified mode formula for all `n, m : ℤ`.
* `VertexOperator.nthProduct_derivative_left`: `(∂A)₍ₙ₎ B = -n • A₍ₙ₋₁₎ B`.
* `VertexOperator.derivative_nthProduct`: `∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`.
* `VertexOperator.lie_ncoeff_nthProduct_eq_add`, `VertexOperator.lie_ncoeff_nthProduct`:
  endomorphism derivations and translation covariance of `nthProduct n A B`.
* `VertexOperator.ncoeff_nthProduct_apply_of_nonneg`,
  `VertexOperator.ncoeff_neg_one_nthProduct_apply`: evaluation of `nthProduct n A B` on a vacuum
  vector.
* `VertexOperator.IsLocalOfOrder.lie_ncoeff_eq_sum_nthProduct`: the commutator formula for local
  fields in terms of `nthProduct`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.1 and §4.4.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3–§2.4 and §3.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §2.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The `R`-bilinear `n`-th product `A₍ₙ₎ B` of two fields for any `n : ℤ`: the nonnegative residue
product for `0 ≤ n`, and `normalOrder (hasseDeriv (-n - 1).toNat A) B` for `n < 0`. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V :=
  if 0 ≤ n then
    nonnegResidueProduct n.toNat
  else
    normalOrderₗ.comp (hasseDeriv (-n - 1).toNat)

/-- For `0 ≤ n`, `nthProduct n` is `nonnegResidueProduct n.toNat`. -/
theorem nthProduct_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    nthProduct (R := R) (V := V) n = nonnegResidueProduct n.toNat := by
  simp [nthProduct, hn]

/-- On natural numbers, `nthProduct ↑n` is `nonnegResidueProduct n`. -/
@[simp]
theorem nthProduct_natCast (n : ℕ) :
    nthProduct (R := R) (V := V) (n : ℤ) = nonnegResidueProduct n := by
  rw [nthProduct_of_nonneg (Nat.cast_nonneg n), Int.toNat_natCast]

/-- On nonnegative integer numerals, `nthProduct ofNat(n)` is `nonnegResidueProduct n`. -/
@[simp]
theorem nthProduct_ofNat (n : ℕ) :
    nthProduct (R := R) (V := V) ofNat(n) = nonnegResidueProduct (OfNat.ofNat n) :=
  nthProduct_natCast n

/-- At `0`, `nthProduct 0` is `nonnegResidueProduct 0`. -/
theorem nthProduct_zero :
    nthProduct (R := R) (V := V) 0 = nonnegResidueProduct 0 :=
  nthProduct_natCast 0

/-- At `1`, `nthProduct 1` is `nonnegResidueProduct 1`. -/
theorem nthProduct_one :
    nthProduct (R := R) (V := V) 1 = nonnegResidueProduct 1 :=
  nthProduct_natCast 1

/-- For `n < 0`, `nthProduct n A B` is `normalOrder (hasseDeriv (-n - 1).toNat A) B`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B = normalOrder (hasseDeriv (-n - 1).toNat A) B := by
  simp [nthProduct, hn.not_ge]

/-- At `-1`, `nthProduct (-1)` is `normalOrderₗ`. -/
@[simp]
theorem nthProduct_neg_one :
    nthProduct (R := R) (V := V) (-1) = normalOrderₗ := by
  simp [nthProduct]

/-- At `-k - 1` for `k : ℕ`, `nthProduct (-k - 1) A B = normalOrder (hasseDeriv k A) B`. -/
theorem nthProduct_neg_natCast_sub_one (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDeriv k A) B := by
  rw [nthProduct_of_neg (by omega)]
  have hk : (-(-(k : ℤ) - 1) - 1).toNat = k := by omega
  rw [hk]

namespace IsLocalOfOrder

/-- Mutual locality of order `N` kills every `n`-th product with `N ≤ n`. -/
theorem nthProduct_eq_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {n : ℤ} (hn : (N : ℤ) ≤ n) :
    nthProduct n A B = 0 := by
  rw [nthProduct_of_nonneg (by omega)]
  exact h.nonnegResidueProduct_eq_zero (by omega)

/-- **Operator product commutator formula.** If `A` and `B` are local of order `N`, the commutator
of their modes is `⁅A₍ₘ₎, B₍ₙ₎⁆ = ∑ j < N, (m choose j) (A₍ⱼ₎ B)₍ₘ₊ₙ₋ⱼ₎`. -/
theorem lie_ncoeff_eq_sum_nthProduct {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (m n : ℤ) :
    ⁅A[[m]], B[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (nthProduct (j : ℤ) A B)[[m + n - j]] := by
  have hc := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm m) n
  rw [Finset.sum_apply, Finset.sum_apply, commutatorDistribution_apply] at hc
  rw [Ring.lie_def, hc]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [nthProduct_natCast, FormalDistribution.deltaTerm_apply,
    ncoeff_nonnegResidueProduct_eq_residue]

end IsLocalOfOrder

/-! ### Unified mode expansion -/

private theorem ncoeff_nonnegResidueProduct_apply_eq_sum (p : ℕ) (A B : VertexOperator R V)
    (m : ℤ) (v : V) {K : ℕ} (hA : ∀ i : ℕ, K ≤ i → (A[[(i : ℤ)]]) v = 0)
    (hB : ∀ i : ℕ, K ≤ i → (B[[m + i]]) v = 0) :
    ((nonnegResidueProduct p A B)[[m]]) v =
      ∑ i ∈ range K, (-1 : ℤ) ^ i • Ring.choose (p : ℤ) i •
        ((A[[(p : ℤ) - i]]) ((B[[m + i]]) v) -
          Int.negOnePow (p : ℤ) • (B[[(p : ℤ) + m - i]]) ((A[[(i : ℤ)]]) v)) := by
  have hL := FormalDistribution.sum_antidiagonal_choose_eq_sum_range_left p
    (fun x y ↦ (A[[x]]) ((B[[y]]) v)) 0 m (K := K) fun i hi ↦ by simp [hB i hi]
  have hR := FormalDistribution.sum_antidiagonal_choose_eq_sum_range_right p
    (fun x y ↦ (B[[y]]) ((A[[x]]) v)) 0 m (K := K) fun i hi ↦ by simp [hA i hi]
  simp only [zero_add] at hL hR
  rw [ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp, smul_sub,
    sum_sub_distrib]
  rw [hL, hR, ← sum_sub_distrib]

/-- **Unified mode expansion of `nthProduct`.** For any `n, m : ℤ` and any cutoff `K` beyond which
`A[[i]] v = 0` and `B[[m + i]] v = 0`, the mode `(nthProduct n A B)[[m]] v` is given by the single
finite binomial sum over `range K`. -/
theorem ncoeff_nthProduct_apply_eq_sum (n : ℤ) (A B : VertexOperator R V) (m : ℤ) (v : V)
    {K : ℕ} (hA : ∀ i : ℕ, K ≤ i → (A[[(i : ℤ)]]) v = 0)
    (hB : ∀ i : ℕ, K ≤ i → (B[[m + i]]) v = 0) :
    ((nthProduct n A B)[[m]]) v =
      ∑ i ∈ range K, (-1 : ℤ) ^ i • Ring.choose n i •
        ((A[[n - i]]) ((B[[m + i]]) v) -
          Int.negOnePow n • (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simpa only [nthProduct_natCast] using ncoeff_nonnegResidueProduct_apply_eq_sum p A B m v hA hB
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_natCast_sub_one, ncoeff_normalOrder,
      normalOrderCoeff_eq_sum (hasseDeriv k A) B m v hB (Q := k + K) (fun j hj ↦ by
        rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply,
          show (j : ℤ) - k = ((j - k : ℕ) : ℤ) by omega, hA (j - k) (by omega),
          smul_zero, smul_zero])]
    rw [sum_range_add]
    have hzero : ∑ x ∈ range k, (B[[m - x - 1]]) (((hasseDeriv k A)[[(x : ℤ)]]) v) = 0 := by
      refine sum_eq_zero fun x hx ↦ ?_
      simp [ncoeff_hasseDeriv, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (mem_range.mp hx)]
    rw [hzero, zero_add]
    simp_rw [smul_sub, sum_sub_distrib]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    · refine sum_congr rfl fun i _ ↦ ?_
      rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul, smul_smul,
        TauCeti.Ring.neg_one_pow_mul_choose_neg_natCast_sub_one_comm (R := ℤ) k i,
        show -(i : ℤ) - 1 - k = -(k : ℤ) - 1 - i by omega]
    · refine sum_congr rfl fun i _ ↦ ?_
      have hsign : (-(k : ℤ) - 1).negOnePow = -((k : ℤ).negOnePow) := by
        rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, Int.negOnePow_neg, Int.negOnePow_succ]
      have hchoose := TauCeti.Ring.neg_one_pow_mul_choose_neg_natCast_sub_one (R := ℤ) k i
      have hidx₁ : m - ((k + i : ℕ) : ℤ) - 1 = -(k : ℤ) - 1 + m - i := by push_cast; omega
      have hidx₂ : ((k + i : ℕ) : ℤ) - k = (i : ℤ) := by push_cast; omega
      rw [ncoeff_hasseDeriv, hidx₁, hidx₂, Ring.choose_natCast, Nat.choose_symm_add, ← hchoose,
        LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, map_zsmul, hsign,
        Units.neg_smul, Units.smul_def, Int.coe_negOnePow_natCast]
      module

/-! ### Derivatives and translation covariance -/

/-- Differentiating the first factor of an `n`-th product gives `(∂A)₍ₙ₎ B = -n • A₍ₙ₋₁₎ B`,
for all `n : ℤ` and over any commutative ring. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    cases k with
    | zero =>
      rw [Nat.cast_zero, neg_zero, zero_smul, nthProduct_zero]
      refine ext_ncoeff fun m ↦ ?_
      simp [ncoeff_nonnegResidueProduct]
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [nthProduct_natCast, hk, nthProduct_natCast]
      refine ext_ncoeff fun m ↦ ?_
      rw [ncoeff_nonnegResidueProduct, map_zsmul, Pi.smul_apply, ncoeff_nonnegResidueProduct]
      have hterm : ∀ ij ∈ antidiagonal (k + 1),
          (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
            ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
              B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
          -((k + 1).choose ij.1 • ij.1 • (-1 : ℤ) ^ ij.2 •
            (A[[(ij.1 : ℤ) - 1]] * B[[m + ij.2]] -
              B[[m + ij.2]] * A[[(ij.1 : ℤ) - 1]])) := by
        intro ij _
        rw [ncoeff_derivative, smul_mul_assoc, mul_smul_comm, ← smul_sub]
        simp only [← natCast_zsmul]
        module
      rw [sum_congr rfl hterm, sum_neg_distrib,
        sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ j •
          (A[[(i : ℤ) - 1]] * B[[m + j]] - B[[m + j]] * A[[(i : ℤ) - 1]])) k,
        neg_zsmul, natCast_zsmul]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have hk₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have hk₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [nthProduct_neg_natCast_sub_one, hk₁, hk₂, nthProduct_neg_natCast_sub_one,
      hasseDeriv_derivative, ← Nat.cast_smul_eq_nsmul R, normalOrder_smul_left,
      Nat.cast_smul_eq_nsmul R, natCast_zsmul]

private theorem sum_antidiagonal_choose_succ_tail (k : ℕ) (A B : VertexOperator R V) (m : ℤ) :
    ∑ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]]) =
      -((k + 1) • ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
  rw [← Nat.sum_antidiagonal_swap]
  have hswap : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.swap.1 • (-1 : ℤ) ^ ij.swap.2 • ij.swap.2 •
        (A[[(ij.swap.1 : ℤ)]] * B[[m - 1 + ij.swap.2]] -
          B[[m - 1 + ij.swap.2]] * A[[(ij.swap.1 : ℤ)]]) =
      (k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ ij.1 •
        (A[[(ij.2 : ℤ)]] * B[[m - 1 + ij.1]] - B[[m - 1 + ij.1]] * A[[(ij.2 : ℤ)]])) := by
    intro ij hij
    rw [Prod.fst_swap, Prod.snd_swap,
      Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm,
      smul_comm ((-1 : ℤ) ^ ij.1) ij.1]
  rw [sum_congr rfl hswap,
    sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ i •
      (A[[(j : ℤ)]] * B[[m - 1 + i]] - B[[m - 1 + i]] * A[[(j : ℤ)]])) k,
    ← Nat.sum_antidiagonal_swap (n := k)]
  have hswap₂ : ∀ ij ∈ antidiagonal k,
      k.choose ij.swap.1 • (-1 : ℤ) ^ (ij.swap.1 + 1) •
        (A[[(ij.swap.2 : ℤ)]] * B[[m - 1 + ↑(ij.swap.1 + 1)]] -
          B[[m - 1 + ↑(ij.swap.1 + 1)]] * A[[(ij.swap.2 : ℤ)]]) =
      -(k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
    intro ij hij
    have hidx : m - 1 + ((ij.2 + 1 : ℕ) : ℤ) = m + ij.2 := by push_cast; omega
    rw [Prod.fst_swap, Prod.snd_swap,
      Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm, hidx, pow_succ]
    module
  rw [sum_congr rfl hswap₂, sum_neg_distrib, smul_neg]

private theorem ncoeff_nonnegResidueProduct_derivative_right_succ (k : ℕ)
    (A B : VertexOperator R V) (m : ℤ) :
    (nonnegResidueProduct (k + 1) A (derivative B))[[m]] =
      (-m) • (nonnegResidueProduct (k + 1) A B)[[m - 1]] +
        ((k + 1 : ℕ) : ℤ) • (nonnegResidueProduct k A B)[[m]] := by
  rw [ncoeff_nonnegResidueProduct (k + 1) A (derivative B) m,
    ncoeff_nonnegResidueProduct (k + 1) A B (m - 1),
    ncoeff_nonnegResidueProduct k A B m]
  have hsplit : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * (derivative B)[[m + ij.2]] -
          (derivative B)[[m + ij.2]] * A[[(ij.1 : ℤ)]]) =
      (-m) • ((k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]])) -
      (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]]) := by
    intro ij _
    have hidx : m + (ij.2 : ℤ) - 1 = m - 1 + ij.2 := by omega
    rw [ncoeff_derivative, hidx, mul_smul_comm, smul_mul_assoc, ← smul_sub]
    simp only [← natCast_zsmul]
    module
  rw [sum_congr rfl hsplit, sum_sub_distrib, ← smul_sum,
    sum_antidiagonal_choose_succ_tail, sub_neg_eq_add, natCast_zsmul]

/-- **Leibniz rule for `nthProduct`.** Formal differentiation is a derivation of every integer
`n`-th product: `∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    cases k with
    | zero =>
      rw [Nat.cast_zero, nthProduct_derivative_left, neg_zero, zero_smul, zero_add,
        nthProduct_zero]
      refine ext_ncoeff fun m ↦ ?_
      simp only [ncoeff_derivative, ncoeff_nonnegResidueProduct, Nat.antidiagonal_zero,
        sum_singleton, Nat.choose_self, one_smul, pow_zero, Nat.cast_zero, add_zero]
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [nthProduct_derivative_left, hk, nthProduct_natCast, nthProduct_natCast]
      refine ext_ncoeff fun m ↦ ?_
      rw [ncoeff_derivative, map_add, Pi.add_apply, map_zsmul, Pi.smul_apply,
        ncoeff_nonnegResidueProduct_derivative_right_succ]
      simp only [neg_zsmul]
      rw [add_comm (-(m • _)) _, neg_add_cancel_left]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_natCast_sub_one, nthProduct_neg_natCast_sub_one,
      nthProduct_neg_natCast_sub_one, derivative_normalOrder, derivative_hasseDeriv,
      hasseDeriv_derivative]

/-- Differentiating the second factor of an `n`-th product gives
`A₍ₙ₎ (∂B) = ∂(A₍ₙ₎ B) + n • A₍ₙ₋₁₎ B`. -/
theorem nthProduct_derivative_right (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n A (derivative B) =
      derivative (nthProduct n A B) + n • nthProduct (n - 1) A B := by
  rw [derivative_nthProduct, nthProduct_derivative_left, neg_zsmul]
  abel

/-- **Derivation rule for `nthProduct` under mode commutators.** If an endomorphism `T` acts on
the modes of `A` and `B` by `⁅T, A[[k]]⁆ = A'[[k]]` and `⁅T, B[[k]]⁆ = B'[[k]]` for fields `A'`
and `B'`, then
`⁅T, (nthProduct n A B)[[m]]⁆ = (nthProduct n A' B)[[m]] + (nthProduct n A B')[[m]]`. -/
theorem lie_ncoeff_nthProduct_eq_add {T : Module.End R V} {A A' B B' : VertexOperator R V}
    (hA : ∀ k : ℤ, ⁅T, A[[k]]⁆ = A'[[k]]) (hB : ∀ k : ℤ, ⁅T, B[[k]]⁆ = B'[[k]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ =
      (nthProduct n A' B)[[m]] + (nthProduct n A B')[[m]] := by
  ext v
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P', hP'⟩ := B'.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q', hQ'⟩ := A'.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨PT, hPT⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨QT, hQT⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let K := max (max (max P Q) (max P' Q')) (max PT QT) + m.natAbs
  rw [LinearMap.add_apply, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    mul_apply_eq_comp,
    ncoeff_nthProduct_apply_eq_sum n A B m (T v) (K := K)
      (fun i hi ↦ hQT _ (by omega)) (fun i hi ↦ hPT _ (by omega)),
    ncoeff_nthProduct_apply_eq_sum n A B m v (K := K)
      (fun i hi ↦ hQ _ (by omega)) (fun i hi ↦ hP _ (by omega)),
    ncoeff_nthProduct_apply_eq_sum n A' B m v (K := K)
      (fun i hi ↦ hQ' _ (by omega)) (fun i hi ↦ hP _ (by omega)),
    ncoeff_nthProduct_apply_eq_sum n A B' m v (K := K)
      (fun i hi ↦ hQ _ (by omega)) (fun i hi ↦ hP' _ (by omega)),
    map_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hcomm (X Y : Module.End R V) :
      T ((X * Y) v) - (X * Y) (T v) = (⁅T, X⁆ * Y + X * ⁅T, Y⁆) v := by
    simp [Ring.lie_def, mul_apply_eq_comp, sub_eq_add_neg, add_assoc]
  rw [map_zsmul, map_zsmul, ← smul_sub, ← smul_sub, ← smul_add, ← smul_add]
  congr 2
  have h₁ := hcomm (A[[n - i]]) (B[[m + i]])
  have h₂ := hcomm (B[[n + m - i]]) (A[[(i : ℤ)]])
  rw [hA, hB] at h₁ h₂
  simp only [mul_apply_eq_comp, LinearMap.add_apply] at h₁ h₂
  simp only [Units.smul_def]
  rw [map_sub, map_zsmul, sub_sub_sub_comm, h₁, ← smul_sub, h₂, smul_add]
  abel

/-- **Translation covariance of `nthProduct`.** If an endomorphism `T` acts as `∂_z` on `A` and
`B` by commutation, it acts as `∂_z` on every `n`-th product `nthProduct n A B`. -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ k : ℤ, ⁅T, A[[k]]⁆ = (derivative A)[[k]])
    (hB : ∀ k : ℤ, ⁅T, B[[k]]⁆ = (derivative B)[[k]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  rw [lie_ncoeff_nthProduct_eq_add hA hB, derivative_nthProduct, map_add, Pi.add_apply]

/-! ### Action on a vacuum vector -/

/-- If all nonnegative modes of `A` and `B` annihilate `vac`, then so do all nonnegative modes of
`nthProduct n A B`. -/
theorem ncoeff_nthProduct_apply_of_nonneg {A B : VertexOperator R V} {vac : V}
    (hA : ∀ k : ℤ, 0 ≤ k → (A[[k]]) vac = 0) (hB : ∀ k : ℤ, 0 ≤ k → (B[[k]]) vac = 0)
    (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ((nthProduct n A B)[[m]]) vac = 0 := by
  rw [ncoeff_nthProduct_apply_eq_sum n A B m vac (K := 0)
    (fun i _ ↦ hA i (Nat.cast_nonneg i)) (fun i _ ↦ hB (m + i) (by omega))]
  simp

/-- If all nonnegative modes of `A` and `B` annihilate `vac`, then the `(-1)`-st mode of
`nthProduct n A B` on `vac` is `A₍ₙ₎ (B₍₋₁₎ vac)`. -/
theorem ncoeff_neg_one_nthProduct_apply {A B : VertexOperator R V} {vac : V}
    (hA : ∀ k : ℤ, 0 ≤ k → (A[[k]]) vac = 0) (hB : ∀ k : ℤ, 0 ≤ k → (B[[k]]) vac = 0)
    (n : ℤ) :
    ((nthProduct n A B)[[-1]]) vac = (A[[n]]) ((B[[-1]]) vac) := by
  rw [ncoeff_nthProduct_apply_eq_sum n A B (-1) vac (K := 1)
    (fun i _ ↦ hA i (Nat.cast_nonneg i)) (fun i hi ↦ hB (-1 + i) (by omega))]
  simp [hA 0 le_rfl]

end VertexOperator
