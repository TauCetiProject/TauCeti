/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import TauCeti.Algebra.Vertex.Dong
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Field `n`-th products and formal calculus

For two fields `A(z)` and `B(w)` on an `R`-module `V`, the singular products (`n ≥ 0`) are the
nonnegative residue products `Res_z (z - w)ⁿ [A(z), B(w)]`, while over a `ℚ`-algebra `R` the
regular products (`n = -k - 1 < 0`) are the divided-power normal-ordered derivatives

`A(w)₍₋ₖ₋₁₎ B(w) = (k!)⁻¹ : (∂_w^k A(w)) B(w) :`.

Together these form the bilinear family `VertexOperator.nthProduct n` indexed by all `n : ℤ`.

We first establish over an arbitrary commutative ring `R` (with no characteristic assumption):
* the Leibniz rules `∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)` for nonnegative residue products and for
  normal ordering (`VertexOperator.derivative_nonnegResidueProduct`,
  `VertexOperator.derivative_normalOrder`), together with `(∂A)₍ₖ₊₁₎ B = -(k + 1) (A₍ₖ₎ B)`;
* preservation of translation covariance `[T, A[[m]]] = (∂A)[[m]]` under differentiation,
  nonnegative residue products, and normal ordering, plus the creation recursion
  `k! • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac)` and automatic annihilation of `vac` by
  nonnegative modes when `V` has unique additive divisibility
  (`VertexOperator.ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative`);
* preservation of the vacuum annihilation condition `∀ m ≥ 0, A[[m]] v = 0`, and evaluation of the
  `(-1)`-mode on such a vector `v`.

Over a `ℚ`-algebra `R`, these combine with `TauCeti.Algebra.Vertex.Dong` to give the full calculus
of `VertexOperator.nthProduct`: translation identities, Leibniz rule, translation covariance,
evaluation on vacuum-like vectors `((A₍ₙ₎ B)[[-1]]) v = A[[n]] (B[[-1]] v)`, and Dong's lemma
(`VertexOperator.IsLocalOfOrder.nthProduct_left`, `VertexOperator.IsLocalOfOrder.nthProduct_right`).

## Main definitions

* `VertexOperator.nthProduct`: the bilinear `n`-th product of fields for `n : ℤ` over a
  `ℚ`-algebra.

## Main results

* `VertexOperator.derivative_nonnegResidueProduct`, `VertexOperator.derivative_normalOrder`,
  `VertexOperator.derivative_nthProduct`: Leibniz rules for formal differentiation.
* `VertexOperator.nthProduct_derivative_left`, `VertexOperator.nthProduct_derivative_right`:
  interaction of `nthProduct` with formal differentiation.
* `VertexOperator.lie_ncoeff_nthProduct`: `nthProduct` preserves translation covariance.
* `VertexOperator.ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative`: under `HasUniqueDiv V`,
  translation covariance and `T vac = 0` force `B[[m]] vac = 0` for `m ≥ 0`.
* `VertexOperator.ncoeff_nthProduct_apply_of_nonneg`,
  `VertexOperator.ncoeff_neg_one_nthProduct_apply`: action of `nthProduct` on vectors killed by
  nonnegative modes.
* `VertexOperator.IsLocalOfOrder.nthProduct_left`,
  `VertexOperator.IsLocalOfOrder.nthProduct_right`: Dong's lemma for all integer-indexed field
  products.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.1–§3.3 and §4.4.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3–§2.4.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### Formal derivatives of residue and normal-ordered products -/

/-- The `0`-th residue product with a derivative on the left vanishes: `Res_z ∂_z A(z) = 0`. -/
@[simp]
theorem nonnegResidueProduct_zero_derivative_left (A B : VertexOperator R V) :
    nonnegResidueProduct 0 (derivative A) B = 0 := by
  refine ext_ncoeff fun m ↦ ?_
  simp

/-- Differentiating the left factor in the `(k + 1)`-st residue product lowers the product index:
`Res_z (z - w)^{k+1} [∂_z A(z), B(w)] = -(k + 1) Res_z (z - w)^k [A(z), B(w)]`. -/
theorem nonnegResidueProduct_succ_derivative_left (k : ℕ) (A B : VertexOperator R V) :
    nonnegResidueProduct (k + 1) (derivative A) B =
      -((k + 1) • nonnegResidueProduct k A B) := by
  refine ext_ncoeff fun m ↦ ?_
  simp only [ncoeff_nonnegResidueProduct, map_neg, map_nsmul, Pi.neg_apply, Pi.smul_apply]
  have hterm : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
          B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
      -((k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ) - 1]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ) - 1]]))) := by
    intro ij _
    rw [ncoeff_derivative, neg_zsmul, natCast_zsmul]
    simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_sub]
    module
  rw [sum_congr rfl hterm, sum_neg_distrib,
    sum_antidiagonal_choose_succ_nsmul_nsmul
      (fun i j ↦ (-1 : ℤ) ^ j • (A[[(i : ℤ) - 1]] * B[[m + j]] - B[[m + j]] * A[[(i : ℤ) - 1]])) k]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

/-- **Leibniz rule** for nonnegative residue products:
`∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`. -/
theorem derivative_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V) :
    derivative (nonnegResidueProduct n A B) =
      nonnegResidueProduct n (derivative A) B + nonnegResidueProduct n A (derivative B) := by
  cases n with
  | zero =>
    refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
    simp [smul_sub]
  | succ k =>
    rw [nonnegResidueProduct_succ_derivative_left]
    refine ext_ncoeff fun m ↦ ?_
    rw [ncoeff_derivative (nonnegResidueProduct (k + 1) A B)]
    simp only [map_add, map_neg, map_nsmul, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, ncoeff_nonnegResidueProduct]
    -- Split `-(m + ij.2)` in `(∂B)[[m + ij.2]]` into `-m` and `-ij.2`.
    have hsplit : ∀ ij ∈ antidiagonal (k + 1),
        (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * (derivative B)[[m + ij.2]] -
            (derivative B)[[m + ij.2]] * A[[(ij.1 : ℤ)]]) =
        (-m) • ((k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]])) -
        (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • (ij.2 : ℤ) •
          (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]]) := by
      intro ij _
      have hm : m + (ij.2 : ℤ) - 1 = m - 1 + ij.2 := by omega
      rw [ncoeff_derivative, hm]
      simp only [smul_mul_assoc, mul_smul_comm]
      module
    -- The `-ij.2` weighted sum equals `-(k + 1)` times the order-`k` residue product.
    have hweighted : ∑ ij ∈ antidiagonal (k + 1),
        (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • (ij.2 : ℤ) •
          (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]]) =
        -((k + 1) • ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
      rw [← Nat.sum_antidiagonal_swap]
      have hswap : ∀ ij ∈ antidiagonal (k + 1),
          (k + 1).choose ij.swap.1 • (-1 : ℤ) ^ ij.swap.2 • (ij.swap.2 : ℤ) •
            (A[[(ij.swap.1 : ℤ)]] * B[[m - 1 + ij.swap.2]] -
              B[[m - 1 + ij.swap.2]] * A[[(ij.swap.1 : ℤ)]]) =
          (k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ ij.1 •
            (A[[(ij.2 : ℤ)]] * B[[m - 1 + ij.1]] - B[[m - 1 + ij.1]] * A[[(ij.2 : ℤ)]])) := by
        intro ij hij
        rw [Prod.fst_swap, Prod.snd_swap,
          Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm, natCast_zsmul]
        module
      rw [sum_congr rfl hswap,
        sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ i •
          (A[[(j : ℤ)]] * B[[m - 1 + i]] - B[[m - 1 + i]] * A[[(j : ℤ)]])) k,
        ← Nat.sum_antidiagonal_swap]
      have hback : ∀ ij ∈ antidiagonal k,
          k.choose ij.swap.1 • (-1 : ℤ) ^ (ij.swap.1 + 1) •
            (A[[(ij.swap.2 : ℤ)]] * B[[m - 1 + ↑(ij.swap.1 + 1)]] -
              B[[m - 1 + ↑(ij.swap.1 + 1)]] * A[[(ij.swap.2 : ℤ)]]) =
          -(k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
            (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
        intro ij hij
        have hm : m - 1 + ((ij.2 + 1 : ℕ) : ℤ) = m + ij.2 := by omega
        rw [Prod.fst_swap, Prod.snd_swap,
          Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm, hm, pow_succ]
        module
      rw [sum_congr rfl hback, sum_neg_distrib, smul_neg]
    rw [sum_congr rfl hsplit, sum_sub_distrib, ← smul_sum, hweighted]
    abel

/-- **Leibniz rule** for normal ordering:
`∂(:AB:) = :(∂A)B: + :A(∂B):`. -/
theorem derivative_normalOrder (A B : VertexOperator R V) :
    derivative (normalOrder A B) =
      normalOrder (derivative A) B + normalOrder A (derivative B) := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ ?_
  simp only [ncoeff_derivative, map_add, Pi.add_apply, ncoeff_normalOrder,
    LinearMap.smul_apply, LinearMap.add_apply]
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := P₀ + (n - 1).natAbs
  have hBnm1 : ∀ i : ℕ, P ≤ i → (B[[n - 1 + i]]) v = 0 := fun i hi ↦ hP₀ (n - 1 + i) (by omega)
  have hBn : ∀ i : ℕ, P ≤ i → (B[[n + i]]) v = 0 := fun i hi ↦ hP₀ (n + i) (by omega)
  have hdBn : ∀ i : ℕ, P + 1 ≤ i → ((derivative B)[[n + i]]) v = 0 := by
    intro i hi
    have hm : n + (i : ℤ) - 1 = n - 1 + i := by omega
    rw [ncoeff_derivative, hm, LinearMap.smul_apply, hBnm1 i (by omega), smul_zero]
  have hA : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0 := fun i hi ↦ hQ i (by omega)
  have hdA : ∀ i : ℕ, Q + 1 ≤ i → ((derivative A)[[(i : ℤ)]]) v = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : ((j + 1 : ℕ) : ℤ) - 1 = j := by omega
    rw [ncoeff_derivative, hj, LinearMap.smul_apply, hA j (by omega), smul_zero]
  rw [normalOrderCoeff_eq_sum A B (n - 1) v (P := P + 1) (Q := Q)
        (fun i hi ↦ hBnm1 i (by omega)) hA,
      normalOrderCoeff_eq_sum (derivative A) B n v (P := P) (Q := Q + 1) hBn hdA,
      normalOrderCoeff_eq_sum A (derivative B) n v (P := P + 1) (Q := Q) hdBn hA]
  -- Match the negative-mode sums (length `P + 1` via `sum_range_succ'`).
  have hleft :
      (∑ j ∈ range P, ((derivative A)[[-(j : ℤ) - 1]]) ((B[[n + j]]) v)) +
        (∑ i ∈ range (P + 1), (A[[-(i : ℤ) - 1]]) (((derivative B)[[n + i]]) v)) =
      (-n) • ∑ i ∈ range (P + 1), (A[[-(i : ℤ) - 1]]) ((B[[n - 1 + i]]) v) := by
    rw [sum_range_succ' (fun i ↦ (A[[-(i : ℤ) - 1]]) (((derivative B)[[n + i]]) v)) P,
      sum_range_succ' (fun i ↦ (A[[-(i : ℤ) - 1]]) ((B[[n - 1 + i]]) v)) P, smul_add,
      ← add_assoc, ← sum_add_distrib]
    have h0 : (A[[-(0 : ℕ) - 1]]) (((derivative B)[[n + (0 : ℕ)]]) v) =
        (-n) • (A[[-(0 : ℕ) - 1]]) ((B[[n - 1 + (0 : ℕ)]]) v) := by
      simp [ncoeff_derivative]
    have hstep : ∀ j ∈ range P,
        ((derivative A)[[-(j : ℤ) - 1]]) ((B[[n + j]]) v) +
          (A[[-(j + 1 : ℕ) - 1]]) (((derivative B)[[n + (j + 1 : ℕ)]]) v) =
        (-n) • (A[[-(j + 1 : ℕ) - 1]]) ((B[[n - 1 + (j + 1 : ℕ)]]) v) := by
      intro j _
      have h₁ : -(j : ℤ) - 1 - 1 = -((j + 1 : ℕ) : ℤ) - 1 := by omega
      have h₂ : n + (j : ℤ) = n - 1 + ((j + 1 : ℕ) : ℤ) := by omega
      have h₃ : n + ((j + 1 : ℕ) : ℤ) - 1 = n - 1 + ((j + 1 : ℕ) : ℤ) := by omega
      rw [ncoeff_derivative, ncoeff_derivative, h₁, h₂, h₃]
      simp only [LinearMap.smul_apply, map_zsmul]
      module
    rw [h0, sum_congr rfl hstep, ← smul_sum]
  -- Match the nonnegative-mode sums (length `Q + 1` via `sum_range_succ'`).
  have hright :
      (∑ i ∈ range (Q + 1), (B[[n - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) +
        (∑ j ∈ range Q, ((derivative B)[[n - j - 1]]) ((A[[(j : ℤ)]]) v)) =
      (-n) • ∑ j ∈ range Q, (B[[n - 1 - j - 1]]) ((A[[(j : ℤ)]]) v) := by
    rw [sum_range_succ' (fun i ↦ (B[[n - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) Q]
    have h0 : (B[[n - (0 : ℕ) - 1]]) (((derivative A)[[(0 : ℕ)]]) v) = 0 := by
      simp [ncoeff_derivative]
    rw [h0, add_zero, ← sum_add_distrib, smul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    have h₁ : ((j + 1 : ℕ) : ℤ) - 1 = j := by omega
    have h₂ : n - ((j + 1 : ℕ) : ℤ) - 1 = n - 1 - j - 1 := by omega
    have h₃ : n - (j : ℤ) - 1 - 1 = n - 1 - j - 1 := by omega
    rw [ncoeff_derivative, ncoeff_derivative, h₁, h₂, h₃]
    simp only [LinearMap.smul_apply, map_zsmul]
    module
  rw [smul_add, ← hleft, ← hright]
  abel

/-! ### Translation covariance -/

/-- Differentiation preserves translation covariance `[T, A[[m]]] = (∂A)[[m]]`. -/
theorem lie_ncoeff_derivative {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (m : ℤ) :
    ⁅T, (derivative A)[[m]]⁆ = (derivative (derivative A))[[m]] := by
  ext v
  simp only [ncoeff_derivative, ← hA (m - 1), Ring.lie_def, LinearMap.sub_apply,
    mul_apply_eq_comp, LinearMap.smul_apply, map_zsmul, smul_sub]

/-- Iterated differentiation preserves translation covariance. -/
theorem lie_ncoeff_iterate_derivative {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, ((derivative (R := R) (V := V))^[k] A)[[m]]⁆ =
      (derivative ((derivative (R := R) (V := V))^[k] A))[[m]] := by
  induction k generalizing m with
  | zero => exact hA m
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using lie_ncoeff_derivative ih m

/-- Nonnegative residue products preserve translation covariance. -/
theorem lie_ncoeff_nonnegResidueProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n : ℕ) (m : ℤ) :
    ⁅T, (nonnegResidueProduct n A B)[[m]]⁆ = (derivative (nonnegResidueProduct n A B))[[m]] := by
  rw [derivative_nonnegResidueProduct, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct, Ring.lie_def, mul_sum, sum_mul,
    ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [← hA ij.1, ← hB (m + ij.2)]
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub, ← smul_add]
  congr 2
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- Normal ordering preserves translation covariance. -/
theorem lie_ncoeff_normalOrder {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    ⁅T, (normalOrder A B)[[m]]⁆ = (derivative (normalOrder A B))[[m]] := by
  rw [derivative_normalOrder]
  ext v
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, map_add, Pi.add_apply,
    LinearMap.add_apply, ncoeff_normalOrder]
  -- Choose common finite truncation cutoffs `P`, `Q` valid on both `v` and `T v`.
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let P := max P₁ P₂ + (m - 1).natAbs
  let Q := max Q₁ Q₂ + 1
  have hBv : ∀ i : ℕ, P ≤ i → (B[[m + i]]) v = 0 := fun i hi ↦ hP₁ (m + i) (by omega)
  have hBTv : ∀ i : ℕ, P ≤ i → (B[[m + i]]) (T v) = 0 := fun i hi ↦ hP₂ (m + i) (by omega)
  have hdBv : ∀ i : ℕ, P ≤ i → ((derivative B)[[m + i]]) v = 0 := by
    intro i hi
    rw [← hB (m + i), Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      hBv i hi, hBTv i hi, map_zero, sub_zero]
  have hAv : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0 := fun i hi ↦ hQ₁ i (by omega)
  have hATv : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) (T v) = 0 := fun i hi ↦ hQ₂ i (by omega)
  have hdAv : ∀ i : ℕ, Q ≤ i → ((derivative A)[[(i : ℤ)]]) v = 0 := by
    intro i hi
    rw [← hA i, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      hAv i hi, hATv i hi, map_zero, sub_zero]
  rw [normalOrderCoeff_eq_sum A B m v hBv hAv,
      normalOrderCoeff_eq_sum A B m (T v) hBTv hATv,
      normalOrderCoeff_eq_sum (derivative A) B m v hBv hdAv,
      normalOrderCoeff_eq_sum A (derivative B) m v hdBv hAv,
      map_add, map_sum, map_sum]
  -- Apply the derivation identity `[T, X Y] = [T, X] Y + X [T, Y]` termwise to each finite sum.
  have hleft :
      (∑ i ∈ range P, T ((A[[-(i : ℤ) - 1]]) ((B[[m + i]]) v))) -
        (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[m + i]]) (T v))) =
      (∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) +
        ∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← hA (-(i : ℤ) - 1), ← hB (m + i)]
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
    abel
  have hright :
      (∑ i ∈ range Q, T ((B[[m - i - 1]]) ((A[[(i : ℤ)]]) v))) -
        (∑ i ∈ range Q, (B[[m - i - 1]]) ((A[[(i : ℤ)]]) (T v))) =
      (∑ i ∈ range Q, (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) +
        ∑ i ∈ range Q, ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← hA i, ← hB (m - i - 1)]
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
    abel
  have hrearr :
      ((∑ i ∈ range P, T ((A[[-(i : ℤ) - 1]]) ((B[[m + i]]) v))) +
        ∑ i ∈ range Q, T ((B[[m - i - 1]]) ((A[[(i : ℤ)]]) v))) -
      ((∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[m + i]]) (T v))) +
        ∑ i ∈ range Q, (B[[m - i - 1]]) ((A[[(i : ℤ)]]) (T v))) =
      ((∑ i ∈ range P, T ((A[[-(i : ℤ) - 1]]) ((B[[m + i]]) v))) -
        ∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[m + i]]) (T v))) +
      ((∑ i ∈ range Q, T ((B[[m - i - 1]]) ((A[[(i : ℤ)]]) v))) -
        ∑ i ∈ range Q, (B[[m - i - 1]]) ((A[[(i : ℤ)]]) (T v))) := by abel
  rw [hrearr, hleft, hright]
  abel

/-- Creation recursion without division for any field `B` covariant with an operator `T`
satisfying `T vac = 0`: `k! • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac)`. -/
theorem factorial_smul_ncoeff_apply_of_lie_eq_derivative
    {T : Module.End R V} {B : VertexOperator R V} {vac : V}
    (hT : T vac = 0) (hcov : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]]) (k : ℕ) :
    k.factorial • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := LinearMap.congr_fun (hcov (-(k : ℤ) - 1)) vac
    have h₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    have h₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hT, map_zero,
      sub_zero, ncoeff_derivative, LinearMap.smul_apply, h₁, h₂, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- When `V` has unique additive divisibility (`HasUniqueDiv V`), any field `B` covariant with an
operator `T` satisfying `T vac = 0` annihilates `vac` in all nonnegative modes
(`B(z) vac ∈ V[[z]]`). -/
theorem ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative [HasUniqueDiv V]
    {T : Module.End R V} {B : VertexOperator R V} {vac : V}
    (hT : T vac = 0) (hcov : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]])
    {m : ℤ} (hm : 0 ≤ m) :
    (B[[m]]) vac = 0 := by
  -- Descending induction from lower truncation via `-(k + 1) • B[[k]] vac = T (B[[k + 1]] vac)`.
  lift m to ℕ using hm
  have hstep : ∀ k : ℕ, (B[[((k + 1 : ℕ) : ℤ)]]) vac = 0 → (B[[(k : ℤ)]]) vac = 0 := by
    intro k hk
    have h := LinearMap.congr_fun (hcov (k + 1 : ℕ)) vac
    have hsub : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
    rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hk, hT,
      map_zero, map_zero, sub_zero, ncoeff_derivative, LinearMap.smul_apply, hsub, neg_zsmul,
      natCast_zsmul, eq_neg_iff_add_eq_zero, zero_add] at h
    exact (smul_eq_zero.mp h).resolve_left (Nat.succ_ne_zero k)
  have hdesc : ∀ d k : ℕ, (B[[((k + d : ℕ) : ℤ)]]) vac = 0 → (B[[(k : ℤ)]]) vac = 0 := by
    intro d
    induction d with
    | zero => intro k hk; simpa using hk
    | succ d ih =>
      intro k hk
      have hadd : k + (d + 1) = (k + 1) + d := by omega
      exact hstep k (ih (k + 1) (hadd ▸ hk))
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  exact hdesc N m (hN (m + N : ℕ) (by omega))

/-! ### Action on vectors killed by nonnegative modes -/

/-- Differentiation preserves annihilation of a vector by all nonnegative modes. -/
theorem ncoeff_derivative_apply_of_nonneg {A : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) {m : ℤ} (hm : 0 ≤ m) :
    ((derivative A)[[m]]) v = 0 := by
  rcases hm.eq_or_lt with rfl | hpos
  · simp
  · rw [ncoeff_derivative, LinearMap.smul_apply, hA (m - 1) (by omega), smul_zero]

/-- Iterated differentiation preserves annihilation of a vector by all nonnegative modes. -/
theorem ncoeff_iterate_derivative_apply_of_nonneg {A : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) (k : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    (((derivative (R := R) (V := V))^[k] A)[[m]]) v = 0 := by
  induction k generalizing m with
  | zero => exact hA m hm
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using
      ncoeff_derivative_apply_of_nonneg (fun _ ↦ ih) hm

/-- Nonnegative residue products preserve annihilation of a vector by all nonnegative modes. -/
theorem ncoeff_nonnegResidueProduct_apply_of_nonneg {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) (n : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    ((nonnegResidueProduct n A B)[[m]]) v = 0 := by
  rw [ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
  refine sum_eq_zero fun ij _ ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
    hA ij.1 (Nat.cast_nonneg _), hB (m + ij.2) (by omega), map_zero, sub_zero, smul_zero]

/-- On a vector killed by nonnegative modes of `A` and `B`, the `(-1)`-mode of
`nonnegResidueProduct n A B` acts as `A[[n]] ∘ B[[-1]]`. -/
theorem ncoeff_neg_one_nonnegResidueProduct_apply {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) (n : ℕ) :
    ((nonnegResidueProduct n A B)[[-1]]) v = (A[[(n : ℤ)]]) ((B[[-1]]) v) := by
  rw [ncoeff_nonnegResidueProduct, LinearMap.sum_apply,
    sum_eq_single (n, 0) (fun ij hij hne ↦ ?_) (by simp)]
  · simp [hA n (Nat.cast_nonneg _)]
  · have hj : ij.2 ≠ 0 := fun hj ↦ hne (Prod.ext (by simpa [hj] using mem_antidiagonal.1 hij) hj)
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
      hA ij.1 (Nat.cast_nonneg _), hB (-1 + ij.2) (by omega), map_zero, sub_zero, smul_zero]

/-- Normal ordering preserves annihilation of a vector by all nonnegative modes. -/
theorem ncoeff_normalOrder_apply_of_nonneg {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) {m : ℤ} (hm : 0 ≤ m) :
    ((normalOrder A B)[[m]]) v = 0 := by
  rw [ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B m v (P := 0) (Q := 0)
      (fun i _ ↦ hB (m + i) (by omega)) (fun i _ ↦ hA i (Nat.cast_nonneg _))]
  simp

/-- On a vector killed by nonnegative modes of `A` and `B`, the `(-1)`-mode of `:AB:` acts as
`A[[-1]] ∘ B[[-1]]`. -/
theorem ncoeff_neg_one_normalOrder_apply {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) :
    ((normalOrder A B)[[-1]]) v = (A[[-1]]) ((B[[-1]]) v) := by
  rw [ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B (-1) v (P := 1) (Q := 0)
      (fun i hi ↦ hB (-1 + i) (by omega)) (fun i _ ↦ hA i (Nat.cast_nonneg _))]
  simp

end CommRing

/-! ### Integer-indexed `n`-th products over a `ℚ`-algebra -/

section RatAlgebra

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]

/-- The bilinear `n`-th product `A(w)₍ₙ₎ B(w)` of fields for `n : ℤ`:
`nonnegResidueProduct n.toNat A B` for `0 ≤ n`, and
`(k!)⁻¹ • normalOrder (∂^k A) B` for `n = -k - 1 < 0`. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V :=
  if 0 ≤ n then
    nonnegResidueProduct n.toNat
  else
    algebraMap ℚ R ((-n - 1).toNat.factorial : ℚ)⁻¹ •
      normalOrderₗ.comp ((derivative : Module.End R (VertexOperator R V)) ^ (-n - 1).toNat)

/-- Nonnegative `n`-th products are the nonnegative residue products. -/
theorem nthProduct_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    (nthProduct n : VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V) =
      nonnegResidueProduct n.toNat := by
  simp [nthProduct, hn]

/-- Negative `n`-th products (`n < 0`) are divided-power normal-ordered derivatives of order
`(-n - 1).toNat`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B =
      algebraMap ℚ R ((-n - 1).toNat.factorial : ℚ)⁻¹ •
        normalOrder ((derivative (R := R) (V := V))^[(-n - 1).toNat] A) B := by
  unfold nthProduct
  split_ifs with h
  · omega
  · simp [pow_apply_eq_iterate]

/-- At a natural number index, `nthProduct` is `nonnegResidueProduct`. -/
@[simp]
theorem nthProduct_natCast (n : ℕ) :
    (nthProduct (n : ℤ) : VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V) =
      nonnegResidueProduct n := by
  simp [nthProduct]

/-- The `0`-th product is `nonnegResidueProduct 0`. -/
@[simp]
theorem nthProduct_zero :
    (nthProduct (0 : ℤ) : VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V) =
      nonnegResidueProduct 0 := by
  simp [nthProduct]

/-- Negative `n`-th products at index `-k - 1` (`k : ℕ`):
`A₍₋ₖ₋₁₎ B = (k!)⁻¹ • :(∂^k A) B:`. -/
theorem nthProduct_neg_apply (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-k - 1) A B =
      algebraMap ℚ R (k.factorial : ℚ)⁻¹ •
        normalOrder ((derivative (R := R) (V := V))^[k] A) B := by
  rw [nthProduct_of_neg (by omega)]
  have hk : (-(-(k : ℤ) - 1) - 1).toNat = k := by omega
  rw [hk]

/-- The `(-1)`-st product is the normal-ordered product. -/
@[simp]
theorem nthProduct_neg_one :
    (nthProduct (-1 : ℤ) : VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V) =
      normalOrderₗ :=
  LinearMap.ext fun A ↦ LinearMap.ext fun B ↦ by
    simpa using nthProduct_neg_apply (R := R) (V := V) 0 A B

/-- Differentiating the left factor in an `n`-th product scales and shifts the index:
`(∂A)₍ₙ₎ B = -n (A₍ₙ₋₁₎ B)`. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    have hm1 : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    have hneg : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    rw [nthProduct_neg_apply, hm1, nthProduct_neg_apply, hneg, natCast_zsmul,
      ← Function.iterate_succ_apply, ← Nat.cast_smul_eq_nsmul R, ← map_natCast (algebraMap ℚ R),
      smul_smul, ← map_mul]
    congr 2
    rw [Nat.factorial_succ]
    push_cast
    have hfac : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  · lift n to ℕ using hn
    cases n with
    | zero => simp
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
      rw [nthProduct_natCast, hk, nthProduct_natCast, nonnegResidueProduct_succ_derivative_left,
        neg_zsmul, natCast_zsmul]

/-- **Leibniz rule** for all integer-indexed `n`-th products:
`∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_apply, nthProduct_neg_apply, nthProduct_neg_apply, map_smul,
      derivative_normalOrder, smul_add,
      ← Function.iterate_succ_apply' (derivative (R := R) (V := V)) k A,
      Function.iterate_succ_apply]
  · lift n to ℕ using hn
    simp [derivative_nonnegResidueProduct]

/-- Differentiating the right factor in an `n`-th product:
`A₍ₙ₎ (∂B) = ∂(A₍ₙ₎ B) + n (A₍ₙ₋₁₎ B)`. -/
theorem nthProduct_derivative_right (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n A (derivative B) = derivative (nthProduct n A B) + n • nthProduct (n - 1) A B := by
  rw [derivative_nthProduct, nthProduct_derivative_left, neg_zsmul]
  abel

/-- All `n`-th products preserve translation covariance. -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_apply, map_smul, map_smul, Pi.smul_apply, map_smul, Pi.smul_apply,
      Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub, ← Ring.lie_def,
      lie_ncoeff_normalOrder (lie_ncoeff_iterate_derivative hA k) hB]
  · lift n to ℕ using hn
    simpa using lie_ncoeff_nonnegResidueProduct hA hB n m

/-- All `n`-th products preserve annihilation of a vector by nonnegative modes. -/
theorem ncoeff_nthProduct_apply_of_nonneg {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ((nthProduct n A B)[[m]]) v = 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_apply, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      ncoeff_normalOrder_apply_of_nonneg
        (fun _ ↦ ncoeff_iterate_derivative_apply_of_nonneg hA k) hB hm,
      smul_zero]
  · lift n to ℕ using hn
    simpa using ncoeff_nonnegResidueProduct_apply_of_nonneg hA hB n hm

/-- On a vector `v` killed by nonnegative modes of `A` and `B`, the `(-1)`-mode of `A₍ₙ₎ B` acts
as `A[[n]] ((B[[-1]]) v)`. -/
theorem ncoeff_neg_one_nthProduct_apply {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) (n : ℤ) :
    ((nthProduct n A B)[[-1]]) v = (A[[n]]) ((B[[-1]]) v) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_apply, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      ncoeff_neg_one_normalOrder_apply
        (fun _ ↦ ncoeff_iterate_derivative_apply_of_nonneg hA k) hB,
      ncoeff_neg_one_iterate_derivative, LinearMap.smul_apply,
      ← Nat.cast_smul_eq_nsmul R, ← map_natCast (algebraMap ℚ R), smul_smul, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero), map_one, one_smul]
  · lift n to ℕ using hn
    simpa using ncoeff_neg_one_nonnegResidueProduct_apply hA hB n

/-- **Dong's lemma** for all integer-indexed `n`-th products (left argument). -/
theorem IsLocalOfOrder.nthProduct_left {A B C : VertexOperator R V} {r s t : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hAC : A.IsLocalOfOrder C s) (hBC : B.IsLocalOfOrder C t)
    (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (r + s + t + 2 * (-n).toNat) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_apply]
    refine (IsLocalOfOrder.smul_left _
      ((hAB.iterate_derivative_left k).normalOrder_left
        (hAC.iterate_derivative_left k) hBC)).mono ?_
    omega
  · lift n to ℕ using hn
    have h0 : (-(n : ℤ)).toNat = 0 := by omega
    simpa [h0] using hAB.nonnegResidueProduct_left hAC hBC n

/-- **Dong's lemma** for all integer-indexed `n`-th products (right argument). -/
theorem IsLocalOfOrder.nthProduct_right {A B C : VertexOperator R V} {r s t : ℕ}
    (hAB : A.IsLocalOfOrder B s) (hAC : A.IsLocalOfOrder C t) (hBC : B.IsLocalOfOrder C r)
    (n : ℤ) :
    A.IsLocalOfOrder (nthProduct n B C) (r + s + t + 2 * (-n).toNat) :=
  (hBC.nthProduct_left hAB.symm hAC.symm n).symm

end RatAlgebra

end VertexOperator
