/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Dong
public import TauCeti.Algebra.Vertex.Derivative
public import Mathlib.Algebra.Ring.NegOnePow
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Nat.Choose.Sum
import TauCeti.RingTheory.Binomial
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Integer `n`-th products of vertex operators

Over any commutative ring `R`, `VertexOperator.nthProduct n` combines nonnegative residue products
(`n ≥ 0`) with normal-ordered Hasse derivatives (`:(∂_z^{(-n-1)} A) B:` for `n < 0`).

## Main definitions and results

* `VertexOperator.nthProduct`: the `R`-bilinear `n`-th product `A_{(n)} B` for `n : ℤ`.
* `VertexOperator.nthProduct_id_left`, `nthProduct_id_right`: unit laws with `VertexOperator.id`.
* `VertexOperator.IsLocalOfOrder.nthProduct_left`, `nthProduct_right`: Dong's lemma.
* `VertexOperator.derivative_nthProduct`, `nthProduct_derivative_left`: Leibniz & derivative rules.
* `VertexOperator.lie_ncoeff_nthProduct`: `nthProduct` preserves translation covariance.
* `VertexOperator.ncoeff_nthProduct_apply_eq_zero_of_nonneg`, `ncoeff_neg_one_nthProduct_apply`:
  vacuum annihilation and `(-1)`-mode rules.
* `VertexOperator.ncoeff_nthProduct_apply`: field-level mode iterate (`m = 0` Borcherds) formula.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.1, §3.3 and §4.4.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §2.2–2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3–2.4 and §3.1.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Integer `n`-th products of vertex operators -/

/-- The `R`-bilinear `n`-th product `A_{(n)} B` of two vertex operators for `n : ℤ`: the
nonnegative residue product `Res_x (x - z)ⁿ [A(x), B(z)]` when `n ≥ 0`, and the normal-ordered
product `:(∂_z^{(-n-1)} A(z)) B(z):` when `n < 0`. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V :=
  if 0 ≤ n then nonnegResidueProduct n.toNat
  else normalOrderₗ.comp (hasseDeriv (-n - 1).toNat)

/-- For `n ≥ 0`, `nthProduct n` is `nonnegResidueProduct n.toNat`. -/
theorem nthProduct_of_nonneg {n : ℤ} (hn : 0 ≤ n) (A B : VertexOperator R V) :
    nthProduct n A B = nonnegResidueProduct n.toNat A B := by simp [nthProduct, hn]

/-- For `n < 0`, `nthProduct n` is `:∂_z^{(-n-1)} A(z) B(z):`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B = normalOrder (hasseDeriv (-n - 1).toNat A) B := by
  simp [nthProduct, not_le.mpr hn]

@[simp] theorem nthProduct_natCast (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (k : ℤ) A B = nonnegResidueProduct k A B := by simp [nthProduct]
@[simp] theorem nthProduct_zero (A B : VertexOperator R V) :
    nthProduct 0 A B = nonnegResidueProduct 0 A B := by simp [nthProduct]
@[simp] theorem nthProduct_neg_succ (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDeriv k A) B := by
  rw [nthProduct_of_neg (by omega), show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]
@[simp] theorem nthProduct_neg_one (A B : VertexOperator R V) :
    nthProduct (-1) A B = normalOrder A B := by simpa using nthProduct_neg_succ 0 A B

/-- Left `n`-th products with the identity field vanish except at `n = -1`, where they act as the
identity. -/
theorem nthProduct_id_left (n : ℤ) (B : VertexOperator R V) :
    nthProduct n (VertexOperator.id R V) B = if n = -1 then B else 0 := by
  rcases le_or_gt 0 n with hn | hn
  · simp [nthProduct_of_nonneg hn, show n ≠ -1 by omega]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    cases k with
    | zero => simp
    | succ k =>
      rw [nthProduct_neg_succ, hasseDeriv_succ_id, normalOrder_zero_left]
      split_ifs <;> [omega; rfl]

/-- Right `n`-th products with the identity field vanish for `n ≥ 0` and yield the `(-n - 1)`-st
Hasse derivative for `n < 0`. -/
theorem nthProduct_id_right (n : ℤ) (A : VertexOperator R V) :
    nthProduct n A (VertexOperator.id R V) = if 0 ≤ n then 0 else hasseDeriv (-n - 1).toNat A := by
  rcases le_or_gt 0 n with hn | hn
  · simp [nthProduct_of_nonneg hn, hn]
  · simp [nthProduct_of_neg hn, not_le.mpr hn]

/-- **Dong's lemma** for all integer `n`-th products (left form). -/
theorem IsLocalOfOrder.nthProduct_left {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) := by
  rcases le_or_gt 0 n with hn | hn
  · exact nthProduct_of_nonneg hn A B ▸ (hAB.nonnegResidueProduct_left hBC hAC n.toNat).mono
      (by omega)
  · exact nthProduct_of_neg hn A B ▸ ((hAB.hasseDeriv_left _).normalOrder_left hBC
      (hAC.hasseDeriv_left _)).mono (by omega)

/-- **Dong's lemma** for all integer `n`-th products (right form). -/
theorem IsLocalOfOrder.nthProduct_right {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hCA : C.IsLocalOfOrder A r₃) (hCB : C.IsLocalOfOrder B r₂)
    (hAB : A.IsLocalOfOrder B r₁) (n : ℤ) :
    C.IsLocalOfOrder (nthProduct n A B) (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) :=
  (hAB.nthProduct_left hCB.symm hCA.symm n).symm

/-! ### Derivatives of residue, normal-ordered and `n`-th products -/

@[simp] theorem nonnegResidueProduct_zero_derivative_left (A B : VertexOperator R V) :
    nonnegResidueProduct 0 (derivative A) B = 0 := ext_ncoeff fun _ ↦ by simp

/-- Differentiating the left factor of the `(k + 1)`-st residue product gives `-(k + 1)` times the
`k`-th residue product. -/
theorem nonnegResidueProduct_succ_derivative_left (k : ℕ) (A B : VertexOperator R V) :
    nonnegResidueProduct (k + 1) (derivative A) B =
      -((k + 1 : ℕ) : ℤ) • nonnegResidueProduct k A B :=
  ext_ncoeff fun m ↦ by
    let c (i j : ℤ) := A[[i]] * B[[j]] - B[[j]] * A[[i]]
    simp only [neg_smul, map_neg, Pi.neg_apply, map_zsmul, Pi.smul_apply,
      ncoeff_nonnegResidueProduct]
    rw [sum_congr rfl fun ij _ ↦ show (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
            B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
          -((k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ ij.2 • c ((ij.1 : ℤ) - 1) (m + ij.2))) by
        rw [ncoeff_derivative]
        simp only [c, smul_mul_assoc, mul_smul_comm, ← natCast_zsmul]; module,
      sum_neg_distrib,
      sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ j • c ((i : ℤ) - 1) (m + j)) k,
      natCast_zsmul]
    congr 2; exact sum_congr rfl fun ij _ ↦ by simp [c]

/-- Differentiating the left factor of an `n`-th product multiplies by `-n` and lowers `n` by
one. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by omega,
      nthProduct_neg_succ, show -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) by omega, natCast_zsmul,
      hasseDeriv_derivative, ← normalOrderₗ_apply, map_nsmul, LinearMap.smul_apply,
      normalOrderₗ_apply]
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 1 : ℕ) := ⟨n.toNat - 1, by omega⟩
    rw [nthProduct_natCast, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega, nthProduct_natCast,
      nonnegResidueProduct_succ_derivative_left]

/-- Formal differentiation is a derivation of each nonnegative residue product. -/
theorem derivative_nonnegResidueProduct (k : ℕ) (A B : VertexOperator R V) :
    derivative (nonnegResidueProduct k A B) =
      nonnegResidueProduct k (derivative A) B + nonnegResidueProduct k A (derivative B) := by
  cases k with
  | zero =>
    exact ext_ncoeff fun m ↦ by
      simp only [ncoeff_derivative, nonnegResidueProduct_zero_derivative_left, zero_add,
        ncoeff_nonnegResidueProduct, Nat.antidiagonal_zero, sum_singleton, Nat.choose_self,
        Nat.cast_zero, add_zero, pow_zero, one_smul, smul_sub, mul_smul_comm, smul_mul_assoc]
  | succ k =>
    refine ext_ncoeff fun m ↦ ?_
    let c (i j : ℤ) := A[[i]] * B[[j]] - B[[j]] * A[[i]]
    rw [ncoeff_derivative, nonnegResidueProduct_succ_derivative_left]
    simp only [map_add, Pi.add_apply, neg_smul, map_neg, Pi.neg_apply, map_zsmul, Pi.smul_apply,
      ncoeff_nonnegResidueProduct]
    have hsplit : ∀ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * (derivative B)[[m + ij.2]] -
          (derivative B)[[m + ij.2]] * A[[(ij.1 : ℤ)]]) =
        (-m) • ((k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • c ij.1 (m - 1 + ij.2)) +
        (k + 1).choose ij.1 • ij.2 • ((-1 : ℤ) ^ (ij.2 - 1) •
          c ij.1 (m + (ij.2 - 1 : ℕ))) := fun ij _ ↦ by
      rw [ncoeff_derivative, show m + (ij.2 : ℤ) - 1 = m - 1 + ij.2 by omega]
      simp only [c, mul_smul_comm, smul_mul_assoc]
      rcases eq_or_ne ij.2 0 with hj | hj
      · simp only [hj, Nat.cast_zero, add_zero, pow_zero, one_smul, zero_smul]; module
      · obtain ⟨j, hj'⟩ : ∃ j, ij.2 = j + 1 := ⟨ij.2 - 1, by omega⟩
        rw [hj', Nat.add_sub_cancel, show m - 1 + ((j + 1 : ℕ) : ℤ) = m + j by omega, pow_succ,
          ← natCast_zsmul]; module
    rw [sum_congr rfl hsplit, sum_add_distrib, ← smul_sum,
      sum_antidiagonal_choose_succ_nsmul_snd_nsmul
        (fun i j ↦ (-1 : ℤ) ^ (j - 1) • c i (m + (j - 1 : ℕ))) k, ← natCast_zsmul]
    simp only [Nat.add_sub_cancel, c]; module

/-- Formal differentiation is a derivation of normal ordering. -/
theorem derivative_normalOrder (A B : VertexOperator R V) :
    derivative (normalOrder A B) =
      normalOrder (derivative A) B + normalOrder A (derivative B) := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := ((P₀ : ℤ) - (m - 1)).toNat
  have hL (K : ℕ) (hK : ∀ i, K ≤ i → (B[[m - 1 + i]]) v = 0) :
      (∑ i ∈ range K, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) +
      (∑ i ∈ range K, (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v)) =
      (-m) • ∑ i ∈ range K, (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
    rw [show (∑ i ∈ range K, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) =
        ∑ i ∈ range K, (i : ℤ) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) by
      cases K with
      | zero => simp
      | succ p =>
        rw [sum_range_succ, show m + (p : ℤ) = m - 1 + ((p + 1 : ℕ) : ℤ) by omega,
          hK (p + 1) (by omega), map_zero, add_zero, sum_range_succ' _ p, Nat.cast_zero,
          zero_smul, add_zero]
        exact sum_congr rfl fun i _ ↦ by
          rw [ncoeff_derivative, LinearMap.smul_apply,
            show -(-(i : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) by omega,
            show -(i : ℤ) - 1 - 1 = -((i + 1 : ℕ) : ℤ) - 1 by omega,
            show m + (i : ℤ) = m - 1 + ((i + 1 : ℕ) : ℤ) by omega],
      ← sum_add_distrib, smul_sum]
    exact sum_congr rfl fun i _ ↦ by
      rw [ncoeff_derivative, LinearMap.smul_apply, map_zsmul,
        show m + (i : ℤ) - 1 = m - 1 + i by omega, ← add_smul]; congr 1; omega
  have hR : (∑ i ∈ range (Q + 1), (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) +
      (∑ i ∈ range Q, ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v)) =
      (-m) • ∑ i ∈ range Q, (B[[m - 1 - i - 1]]) ((A[[(i : ℤ)]]) v) := by
    rw [sum_range_succ', Nat.cast_zero, ncoeff_derivative, neg_zero, zero_smul,
      LinearMap.zero_apply, map_zero, add_zero, ← sum_add_distrib, smul_sum]
    exact sum_congr rfl fun i _ ↦ by
      rw [ncoeff_derivative, ncoeff_derivative, LinearMap.smul_apply, LinearMap.smul_apply,
        map_zsmul, show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by omega,
        show m - ((i + 1 : ℕ) : ℤ) - 1 = m - 1 - i - 1 by omega,
        show m - (i : ℤ) - 1 - 1 = m - 1 - i - 1 by omega, ← add_smul]; congr 1; omega
  simp only [ncoeff_derivative, LinearMap.smul_apply, map_add, Pi.add_apply, LinearMap.add_apply,
    ncoeff_normalOrder]
  rw [normalOrderCoeff_eq_sum A B (m - 1) v (P := P) (Q := Q)
      (fun _ _ ↦ hP₀ _ (by omega)) (fun _ _ ↦ hQ _ (by omega)),
    normalOrderCoeff_eq_sum (derivative A) B m v (P := P) (Q := Q + 1) (fun _ _ ↦ hP₀ _ (by omega))
      (fun _ _ ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hQ _ (by omega), smul_zero]),
    normalOrderCoeff_eq_sum A (derivative B) m v (P := P) (Q := Q)
      (fun _ _ ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hP₀ _ (by omega), smul_zero])
      (fun _ _ ↦ hQ _ (by omega)),
    smul_add, ← hL P (fun _ _ ↦ hP₀ _ (by omega)), ← hR]; abel

/-- Formal differentiation is a derivation of every integer `n`-th product. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  rcases le_or_gt 0 n with hn | hn
  · simp only [nthProduct_of_nonneg hn, derivative_nonnegResidueProduct]
  · simp only [nthProduct_of_neg hn, derivative_normalOrder, derivative_hasseDeriv_comm]

/-! ### Translation covariance of `n`-th products -/

/-- Nonnegative residue products preserve translation covariance. -/
theorem lie_ncoeff_nonnegResidueProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, (nonnegResidueProduct k A B)[[m]]⁆ = (derivative (nonnegResidueProduct k A B))[[m]] := by
  simp only [derivative_nonnegResidueProduct, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ← Ring.lie_def, lie_sum, ← sum_add_distrib]
  exact sum_congr rfl fun ij _ ↦ by simp only [lie_nsmul, lie_zsmul, leibniz_lie, hA, hB, smul_add]

/-- Normal ordering preserves translation covariance. -/
theorem lie_ncoeff_normalOrder {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    ⁅T, (normalOrder A B)[[m]]⁆ = (derivative (normalOrder A B))[[m]] := by
  ext v
  have hsum (N : ℕ) (X Y dX dY : ℕ → Module.End R V) (hX : ∀ i, ⁅T, X i⁆ = dX i)
      (hY : ∀ i, ⁅T, Y i⁆ = dY i) :
      (∑ i ∈ range N, T (X i (Y i v))) - (∑ i ∈ range N, X i (Y i (T v))) =
      (∑ i ∈ range N, dX i (Y i v)) + (∑ i ∈ range N, X i (dY i v)) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by
      rw [← hX i, ← hY i]
      simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]; abel
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let P := (max ((P₁ : ℤ) + 1) P₂ - m).toNat; let Q := max (Q₁ + 1) Q₂
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, derivative_normalOrder,
    map_add, Pi.add_apply, LinearMap.add_apply, ncoeff_normalOrder]
  rw [normalOrderCoeff_eq_sum A B m v (P := P) (Q := Q)
      (fun _ _ ↦ hP₁ _ (by omega)) (fun _ _ ↦ hQ₁ _ (by omega)),
    normalOrderCoeff_eq_sum A B m (T v) (P := P) (Q := Q)
      (fun _ _ ↦ hP₂ _ (by omega)) (fun _ _ ↦ hQ₂ _ (by omega)),
    normalOrderCoeff_eq_sum (derivative A) B m v (P := P) (Q := Q) (fun _ _ ↦ hP₁ _ (by omega))
      (fun _ _ ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hQ₁ _ (by omega), smul_zero]),
    normalOrderCoeff_eq_sum A (derivative B) m v (P := P) (Q := Q)
      (fun _ _ ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hP₁ _ (by omega), smul_zero])
      (fun _ _ ↦ hQ₁ _ (by omega))]
  simp only [map_add, map_sum, add_sub_add_comm,
    hsum P _ _ _ _ (fun _ ↦ hA _) (fun _ ↦ hB _),
    hsum Q _ _ _ _ (fun _ ↦ hB _) (fun _ ↦ hA _)]; abel

/-- Every integer `n`-th product preserves translation covariance. -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  rcases le_or_gt 0 n with hn | hn
  · exact nthProduct_of_nonneg hn A B ▸ lie_ncoeff_nonnegResidueProduct hA hB n.toNat m
  · exact nthProduct_of_neg hn A B ▸ lie_ncoeff_normalOrder (lie_ncoeff_hasseDeriv hA _) hB m

/-! ### Vacuum evaluation of `n`-th products -/

/-- If `vac` is annihilated by nonnegative modes of `A` and `B`, it is annihilated by nonnegative
modes of `nthProduct n A B` for every `n : ℤ`. -/
theorem ncoeff_nthProduct_apply_eq_zero_of_nonneg {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0)
    (n : ℤ) {m : ℤ} (hm : 0 ≤ m) : ((nthProduct n A B)[[m]]) vac = 0 := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    exact sum_eq_zero fun ij _ ↦ by simp [hA ij.1 (Nat.cast_nonneg _), hB (m + ij.2) (by omega)]
  · rw [nthProduct_of_neg hn, ncoeff_normalOrder, normalOrderCoeff_apply,
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by simp [hB (m + i) (by omega)],
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDeriv_apply_eq_zero_of_nonneg hA _ (Nat.cast_nonneg i), map_zero],
      add_zero]

/-- If `vac` is annihilated by nonnegative modes of `A` and `B`, then the `(-1)`-st mode of
`nthProduct n A B` on `vac` is `A₍ₙ₎ (B₍₋₁₎ vac)` for every `n : ℤ`. -/
theorem ncoeff_neg_one_nthProduct_apply {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0)
    (n : ℤ) : ((nthProduct n A B)[[-1]]) vac = (A[[n]]) ((B[[-1]]) vac) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    rw [nthProduct_natCast, ncoeff_nonnegResidueProduct, LinearMap.sum_apply, sum_eq_single (n, 0)]
    · simp [hA n (Nat.cast_nonneg _)]
    · intro ij hij hne
      have hj : ij.2 ≠ 0 := fun hj ↦ hne (Prod.ext (by simpa [hj] using mem_antidiagonal.mp hij) hj)
      simp [hA ij.1 (Nat.cast_nonneg _), hB (-1 + ij.2) (by omega)]
    · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, ncoeff_normalOrder, normalOrderCoeff_apply, add_comm,
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDeriv_apply_eq_zero_of_nonneg hA k (Nat.cast_nonneg i), map_zero],
      zero_add, finsum_eq_single _ 0]
    · rw [Nat.cast_zero, neg_zero, zero_sub, add_zero, ncoeff_neg_one_hasseDeriv]
    · intro i hi; simp [hB (-1 + i) (by omega)]

/-! ### Mode iterate formula for `n`-th products -/

/-- **Mode iterate formula** (`m = 0` case of the Borcherds identity) for any two vertex operators
over a commutative ring:
`((A_{(n)} B)_{(r)}) v = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (A₍ₙ₋ᵢ₎ (B₍ᵣ₊ᵢ₎ v) - (-1)ⁿ B₍ₙ₊ᵣ₋ᵢ₎ (A₍ᵢ₎ v))`
for all `A, B : VertexOperator R V`, `n, r : ℤ`, and `v : V`. -/
theorem ncoeff_nthProduct_apply (A B : VertexOperator R V) (n r : ℤ) (v : V) :
    ((nthProduct n A B)[[r]]) v =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[(i : ℤ)]]) v)) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    rw [TauCeti.finsum_eq_sum_range_of_zero (N := n + 1) fun i hi ↦ by
        simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hi],
      nthProduct_natCast, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp, smul_sub,
      sum_sub_distrib, Int.coe_negOnePow_natCast, Ring.choose_natCast]
    congr 1
    · rw [← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      exact sum_congr rfl fun i hi ↦ by
        rw [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm (Nat.lt_succ_iff.mp (mem_range.mp hi)),
          show ((n - i : ℕ) : ℤ) = (n : ℤ) - i by have := mem_range.mp hi; omega,
          ← natCast_zsmul, smul_smul, mul_comm]
    · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      exact sum_congr rfl fun i hi ↦ by
        have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
        have hpow : (-1 : ℤ) ^ (n - i) = (-1 : ℤ) ^ i * (-1 : ℤ) ^ n := by
          conv_rhs => rw [← Nat.sub_add_cancel hle]
          rw [pow_add, mul_left_comm, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
        rw [show r + ((n - i : ℕ) : ℤ) = (n : ℤ) + r - i by omega, hpow,
          ← natCast_zsmul, smul_smul, smul_smul]; congr 1; ring
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨Q₀, hQ₀⟩ := A.exists_forall_ncoeff_apply_eq_zero v
    let M := max ((P₀ : ℤ) - r).toNat Q₀
    rw [TauCeti.finsum_eq_sum_range_of_zero (N := M) fun i hi ↦ by
        simp [hP₀ (r + i) (by omega), hQ₀ i (by omega)],
      nthProduct_neg_succ, ncoeff_normalOrder,
      normalOrderCoeff_eq_sum _ _ r v (P := M) (Q := k + M) (fun _ _ ↦ hP₀ _ (by omega))
        (fun j _ ↦ by rw [ncoeff_hasseDeriv, LinearMap.smul_apply,
          show (j : ℤ) - k = ((j - k : ℕ) : ℤ) by omega, hQ₀ _ (by omega), smul_zero])]
    simp only [smul_sub, sum_sub_distrib]; rw [sub_eq_add_neg]; congr 1
    · exact sum_congr rfl fun i _ ↦ by
        rw [ncoeff_hasseDeriv, LinearMap.smul_apply,
          TauCeti.Ring.neg_one_pow_mul_choose_neg_succ (R := ℤ) i k,
          TauCeti.Ring.neg_one_pow_mul_choose_neg_succ (R := ℤ) k i, Nat.add_comm i k,
          Nat.choose_symm_add, show -(i : ℤ) - 1 - k = -(k : ℤ) - 1 - i by omega]
    · have hsign : -(((-(k : ℤ) - 1).negOnePow : ℤ)) = (-1 : ℤ) ^ k := by
        rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, Int.negOnePow_neg, Int.negOnePow_succ,
          Units.val_neg, neg_neg, Int.coe_negOnePow_natCast]
      rw [sum_range_add, sum_eq_zero fun j hj ↦ by
          simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (mem_range.mp hj)],
        zero_add, ← sum_neg_distrib]
      exact sum_congr rfl fun i _ ↦ by
        rw [ncoeff_hasseDeriv, LinearMap.smul_apply, map_zsmul, Ring.choose_natCast,
          TauCeti.Ring.neg_one_pow_mul_choose_neg_succ (R := ℤ) k i,
          show ((k + i : ℕ) : ℤ) - k = (i : ℤ) by omega,
          show r - ((k + i : ℕ) : ℤ) - 1 = (-(k : ℤ) - 1) + r - i by omega, smul_smul, ← neg_smul]
        congr 1; linear_combination -(((k + i).choose k : ℤ)) * hsign

end VertexOperator
