/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Dong
public import TauCeti.Algebra.Vertex.Derivative
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Hasse derivatives and integer `n`-th products of vertex operators

For a field `A(z) = ∑ₙ A₍ₙ₎ z^{-n-1}` on an `R`-module `V`, its `k`-th Hasse derivative
`∂_z^{(k)} A(z)` has modes `((-1)ᵏ (n choose k)) • A₍ₙ₋ₖ₎` (`VertexOperator.hasseDerivative`),
satisfying `k! • ∂_z^{(k)} A = ∂_zᵏ A` over any commutative ring `R`. Combining nonnegative residue
products (`n ≥ 0`) with normal ordering of Hasse derivatives (`:(∂_z^{(k)} A) B:` for `n = -k - 1`)
defines the `R`-bilinear integer `n`-th product `VertexOperator.nthProduct`, which preserves mutual
locality, translation covariance, and vacuum annihilation while satisfying the Leibniz and
left-derivative rules.

## Main definitions

* `VertexOperator.id`: the identity field `Id_V z⁰`, with modes `δ_{n,-1} • 1`.
* `VertexOperator.hasseDerivative`: the `k`-th divided-power derivative `∂_z^{(k)}` on fields.
* `VertexOperator.nthProduct`: the `R`-bilinear `n`-th product `A_{(n)} B` for `n : ℤ`.

## Main results

* `VertexOperator.IsLocalOfOrder.hasseDerivative_left`,
  `VertexOperator.IsLocalOfOrder.nthProduct_left`: Hasse derivatives and `nthProduct` preserve
  mutual locality.
* `VertexOperator.IsLocalOfOrder.lie_ncoeff`: mode commutator formula for mutually local fields.
* `VertexOperator.derivative_nthProduct`, `VertexOperator.nthProduct_derivative_left`: Leibniz and
  left-derivative rules for `nthProduct`.
* `VertexOperator.lie_ncoeff_nthProduct`: `nthProduct` preserves translation covariance.
* `VertexOperator.ncoeff_nthProduct_apply_of_nonneg`,
  `VertexOperator.ncoeff_neg_one_nthProduct_apply`,
  `VertexOperator.ncoeff_apply_eq_zero_of_nonneg_of_lie`: vacuum annihilation and `(-1)`-mode rules.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.1, §3.3 and §4.4.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §2.2–2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3–2.4 and §3.1.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### The identity vertex operator -/

private theorem bddBelow_support_id (v : V) :
    BddBelow (Function.support fun k : ℤ ↦ ((if k = 0 then (1 : Module.End R V) else 0)) v) :=
  ⟨0, fun _ hk ↦ not_lt.mp fun h ↦ hk (by simp [h.ne])⟩

/-- The identity field `Id_V z⁰`, whose `(-1)`-st normalized mode is `1` and all other modes are
`0`. -/
protected def id (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] : VertexOperator R V :=
  of_coeff (fun k ↦ if k = 0 then 1 else 0) bddBelow_support_id

/-- The normalized modes of `VertexOperator.id` are `δ_{n,-1}`. -/
theorem ncoeff_id (n : ℤ) : (VertexOperator.id R V)[[n]] = if n = -1 then 1 else 0 := by
  rw [VertexOperator.id, ncoeff_of_coeff]
  simp [show (-n - 1 = 0) ↔ (n = -1) by omega]

@[simp] theorem ncoeff_neg_one_id : (VertexOperator.id R V)[[-1]] = 1 := by simp [ncoeff_id]

@[simp] theorem ncoeff_id_of_ne {n : ℤ} (hn : n ≠ -1) : (VertexOperator.id R V)[[n]] = 0 := by
  simp [ncoeff_id, hn]

@[simp] theorem derivative_id : derivative (VertexOperator.id R V) = 0 :=
  ext_ncoeff fun n ↦ by
    rw [ncoeff_derivative, ncoeff_id, map_zero, Pi.zero_apply]
    split_ifs with h <;> [simp [show n = 0 by omega]; simp]

/-- The identity field commutes with every field, hence is local of order `0`. -/
theorem IsLocalOfOrder.id_left (B : VertexOperator R V) :
    (VertexOperator.id R V).IsLocalOfOrder B 0 := by
  rw [isLocalOfOrder_iff]; intro m n; simp only [Nat.antidiagonal_zero, sum_singleton,
    Nat.choose_self, Nat.cast_zero, add_zero, pow_zero, one_smul, ncoeff_id]
  split_ifs <;> simp

/-- Every field is local of order `0` with the identity field. -/
theorem IsLocalOfOrder.id_right (A : VertexOperator R V) :
    A.IsLocalOfOrder (VertexOperator.id R V) 0 :=
  (IsLocalOfOrder.id_left A).symm

@[simp] theorem nonnegResidueProduct_id_left (n : ℕ) (B : VertexOperator R V) :
    nonnegResidueProduct n (VertexOperator.id R V) B = 0 :=
  (IsLocalOfOrder.id_left B).nonnegResidueProduct_eq_zero (Nat.zero_le n)

@[simp] theorem normalOrder_id_left (B : VertexOperator R V) :
    normalOrder (VertexOperator.id R V) B = B := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ ?_
  have hR : (∑ᶠ i : ℕ, (B[[n - i - 1]]) (((VertexOperator.id R V)[[(i : ℤ)]]) v)) = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun i ↦ by rw [ncoeff_id_of_ne (by omega)]; simp
  rw [ncoeff_normalOrder, normalOrderCoeff_apply, hR, add_zero, finsum_eq_single _ 0]
  · simp
  · intro i hi; rw [ncoeff_id_of_ne (by omega), LinearMap.zero_apply]

/-! ### Hasse derivatives of vertex operators -/

/-- The `k`-th Hasse (divided-power) derivative `∂_z^{(k)}` of a vertex operator, defined over any
commutative ring by `(∂_z^{(k)} A)₍ₙ₎ = (-1)ᵏ (n choose k) • A₍ₙ₋ₖ₎`. -/
def hasseDerivative (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A := of_coeff
    (fun m ↦ ((-1 : ℤ) ^ k * Ring.choose (-m - 1) k) • A[[-m - 1 - k]]) fun v ↦ by
      obtain ⟨N, hN⟩ := A.exists_forall_ncoeff_apply_eq_zero v
      exact ⟨-(N : ℤ) - 1 - k, fun m hm ↦ not_lt.mp fun h ↦
        hm (by simp [hN (-m - 1 - k) (by omega)])⟩
  map_add' A B := ext_ncoeff fun n ↦ by simp [smul_add]
  map_smul' r A := ext_ncoeff fun n ↦ by simp [smul_comm]

/-- The normalized modes of the `k`-th Hasse derivative are `(-1)ᵏ (n choose k) • A₍ₙ₋ₖ₎`. -/
@[simp] theorem ncoeff_hasseDerivative (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDerivative k A)[[n]] = ((-1 : ℤ) ^ k * Ring.choose n k) • A[[n - k]] := by
  simp only [hasseDerivative, LinearMap.coe_mk, AddHom.coe_mk, ncoeff_of_coeff,
    show -(-n - 1) - 1 = n by omega]

/-- The `0`-th Hasse derivative is the identity. -/
@[simp] theorem hasseDerivative_zero (A : VertexOperator R V) : hasseDerivative 0 A = A :=
  ext_ncoeff fun _ ↦ by simp

/-- The `1`-st Hasse derivative is the formal derivative. -/
@[simp] theorem hasseDerivative_one (A : VertexOperator R V) : hasseDerivative 1 A = derivative A :=
  ext_ncoeff fun _ ↦ by simp

/-- The `(-1)`-st mode of `∂_z^{(k)} A` is `A₍₋ₖ₋₁₎`. -/
theorem ncoeff_neg_one_hasseDerivative (k : ℕ) (A : VertexOperator R V) :
    (hasseDerivative k A)[[-1]] = A[[-(k : ℤ) - 1]] := by
  have hc : Ring.choose (-1 : ℤ) k = (-1 : ℤ) ^ k := by
    simpa [show (1 : ℤ) + k - 1 = k by omega, Int.negOnePow_def, Units.smul_def,
      Ring.choose_natCast, Nat.choose_self] using Ring.choose_neg (1 : ℤ) k
  rw [ncoeff_hasseDerivative, hc, ← mul_pow, show (-1 : ℤ) * -1 = 1 by ring, one_pow, one_smul,
    show (-1 : ℤ) - k = -(k : ℤ) - 1 by omega]

@[simp] theorem hasseDerivative_id_succ (k : ℕ) :
    hasseDerivative (k + 1) (VertexOperator.id R V) = 0 :=
  ext_ncoeff fun n ↦ by
    rw [ncoeff_hasseDerivative, map_zero, Pi.zero_apply, ncoeff_id]
    split_ifs with h
    · rw [show n = (k : ℤ) by omega, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]; simp
    · simp

/-- Differentiating the `k`-th Hasse derivative gives `(k + 1)` times the `(k + 1)`-st. -/
theorem derivative_hasseDerivative (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDerivative k A) = (k + 1) • hasseDerivative (k + 1) A :=
  ext_ncoeff fun n ↦ by
    have hc := Ring.choose_smul_choose n (show 1 ≤ k + 1 by omega)
    rw [Nat.choose_one_right, Nat.cast_one, Ring.choose_one_right, Nat.add_sub_cancel,
      nsmul_eq_mul] at hc
    rw [ncoeff_derivative, ncoeff_hasseDerivative, map_nsmul, Pi.smul_apply, ncoeff_hasseDerivative,
      show n - 1 - (k : ℤ) = n - ↑(k + 1) by omega, smul_smul, ← natCast_zsmul, smul_smul]
    congr 1; rw [pow_succ]; linear_combination ((-1 : ℤ) ^ k) * hc

/-- Taking the `k`-th Hasse derivative of `∂A` also gives `(k + 1)` times the `(k + 1)`-st. -/
theorem hasseDerivative_derivative (k : ℕ) (A : VertexOperator R V) :
    hasseDerivative k (derivative A) = (k + 1) • hasseDerivative (k + 1) A :=
  ext_ncoeff fun n ↦ by
    have hc := Ring.choose_smul_choose n (show k ≤ k + 1 by omega)
    rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
      nsmul_eq_mul] at hc
    rw [ncoeff_hasseDerivative, ncoeff_derivative, map_nsmul, Pi.smul_apply, ncoeff_hasseDerivative,
      show n - (k : ℤ) - 1 = n - ↑(k + 1) by omega, smul_smul, ← natCast_zsmul, smul_smul]
    congr 1; rw [pow_succ]; linear_combination ((-1 : ℤ) ^ k) * hc

/-- Formal differentiation commutes with every Hasse derivative. -/
theorem derivative_hasseDerivative_comm (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDerivative k A) = hasseDerivative k (derivative A) := by
  rw [derivative_hasseDerivative, hasseDerivative_derivative]

/-- Multiplying the `k`-th Hasse derivative by `k!` recovers the `k`-th iterated derivative,
without any division assumption on `R`. -/
theorem factorial_smul_hasseDerivative (k : ℕ) (A : VertexOperator R V) :
    k.factorial • hasseDerivative k A = (derivative^[k]) A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, map_nsmul, derivative_hasseDerivative, ← mul_smul,
      Nat.factorial_succ, mul_comm]

private theorem eq_inv_smul_of_nsmul [Algebra ℚ R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : n ≠ 0) {x y : M} (h : n • x = y) : x = algebraMap ℚ R (n : ℚ)⁻¹ • y := by
  rw [← h, ← Nat.cast_smul_eq_nsmul R, ← map_natCast (algebraMap ℚ R), smul_smul, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast hn), map_one, one_smul]

/-- Over a `ℚ`-algebra, the `k`-th Hasse derivative is `(k!)⁻¹ • ∂_zᵏ A`. -/
theorem hasseDerivative_eq_smul_iterate_derivative [Algebra ℚ R] (k : ℕ) (A : VertexOperator R V) :
    hasseDerivative k A = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (derivative^[k]) A :=
  eq_inv_smul_of_nsmul k.factorial_ne_zero (factorial_smul_hasseDerivative k A)

/-- Taking the `k`-th Hasse derivative in the first variable increases a locality bound by `k`,
over any commutative ring. -/
theorem IsLocalOfOrder.hasseDerivative_left {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (k : ℕ) : (hasseDerivative k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  have hexp : (hasseDerivative k A).commutatorDistribution B = ∑ j ∈ range N,
      FormalDistribution.deltaTerm (k + j) (fun r ↦ ((-1 : ℤ) ^ k * ((k + j).choose k : ℤ)) •
        FormalDistribution.residue ((FormalDistribution.mulSub ^ j)
          (A.commutatorDistribution B)) r) := by
    funext m n
    have hsum := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm (m - k)) n
    simp only [Finset.sum_apply, FormalDistribution.deltaTerm_apply] at hsum ⊢
    rw [commutatorDistribution_apply, ncoeff_hasseDerivative, smul_mul_assoc, mul_smul_comm,
      ← smul_sub, ← commutatorDistribution_apply, hsum, smul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    have hc := Ring.choose_smul_choose m (Nat.le_add_right k j)
    rw [Nat.add_sub_cancel_left, nsmul_eq_mul] at hc
    rw [smul_smul, smul_smul, show m - (k : ℤ) + n - j = m + n - ↑(k + j) by omega]
    congr 1; linear_combination (-1 : ℤ) ^ k * hc.symm
  rw [hexp, map_sum]
  exact sum_eq_zero fun j hj ↦
    FormalDistribution.mulSub_pow_deltaTerm_eq_zero (by have := mem_range.mp hj; omega) _

/-- Taking the `k`-th Hasse derivative in the second variable increases a locality bound by `k`. -/
theorem IsLocalOfOrder.hasseDerivative_right {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (k : ℕ) : A.IsLocalOfOrder (hasseDerivative k B) (N + k) :=
  (h.symm.hasseDerivative_left k).symm

/-- Hasse derivatives of orders `k` and `l` of local fields are local of order `N + k + l`. -/
theorem IsLocalOfOrder.hasseDerivative {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    (hasseDerivative k A).IsLocalOfOrder (hasseDerivative l B) (N + k + l) :=
  (h.hasseDerivative_left k).hasseDerivative_right l

/-! ### Integer `n`-th products of vertex operators -/

/-- The `R`-bilinear `n`-th product `A_{(n)} B` of two vertex operators for `n : ℤ`: the
nonnegative residue product `Res_x (x - z)ⁿ [A(x), B(z)]` when `n ≥ 0`, and the normal-ordered
product `:(∂_z^{(-n-1)} A(z)) B(z):` when `n < 0`. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V :=
  if 0 ≤ n then nonnegResidueProduct n.toNat
  else normalOrderₗ.comp (hasseDerivative (-n - 1).toNat)

/-- For `n ≥ 0`, `nthProduct n` is the nonnegative residue product
`nonnegResidueProduct n.toNat`. -/
theorem nthProduct_of_nonneg {n : ℤ} (hn : 0 ≤ n) (A B : VertexOperator R V) :
    nthProduct n A B = nonnegResidueProduct n.toNat A B := by simp [nthProduct, hn]

/-- For `n < 0`, `nthProduct n` is `:∂_z^{(-n-1)} A(z) B(z):`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B = normalOrder (hasseDerivative (-n - 1).toNat A) B := by
  simp [nthProduct, not_le.mpr hn]

@[simp] theorem nthProduct_natCast (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (k : ℤ) A B = nonnegResidueProduct k A B := by simp [nthProduct]

@[simp] theorem nthProduct_zero (A B : VertexOperator R V) :
    nthProduct 0 A B = nonnegResidueProduct 0 A B := by simp [nthProduct]

@[simp] theorem nthProduct_neg_succ (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDerivative k A) B := by
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
      rw [nthProduct_neg_succ, hasseDerivative_id_succ, normalOrder_zero_left]
      split_ifs <;> [omega; rfl]

/-- **Dong's lemma** for all integer `n`-th products (left form). -/
theorem IsLocalOfOrder.nthProduct_left {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn]
    exact (hAB.nonnegResidueProduct_left hBC hAC n.toNat).mono (by omega)
  · rw [nthProduct_of_neg hn]
    exact ((hAB.hasseDerivative_left _).normalOrder_left hBC
      (hAC.hasseDerivative_left _)).mono (by omega)

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
    rw [ncoeff_nonnegResidueProduct, map_zsmul, Pi.smul_apply, neg_smul,
      ncoeff_nonnegResidueProduct]
    have e : ∀ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
          B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
        -((k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ ij.2 • c ((ij.1 : ℤ) - 1) (m + ij.2))) :=
      fun ij _ ↦ by rw [ncoeff_derivative]; simp only [c, smul_mul_assoc, mul_smul_comm,
        ← natCast_zsmul]; module
    rw [sum_congr rfl e, sum_neg_distrib,
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
      hasseDerivative_derivative, ← normalOrderₗ_apply, map_nsmul, LinearMap.smul_apply,
      normalOrderₗ_apply]
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 1 : ℕ) := ⟨n.toNat - 1, by omega⟩
    rw [nthProduct_natCast, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega, nthProduct_natCast,
      nonnegResidueProduct_succ_derivative_left]

private theorem sum_antidiagonal_choose_succ_snd {M : Type*} [AddCommGroup M]
    (f : ℕ → ℕ → M) (k : ℕ) :
    ∑ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.1 • (ij.2 : ℤ) • ((-1 : ℤ) ^ (ij.2 - 1) • f ij.1 (ij.2 - 1)) =
    ((k + 1 : ℕ) : ℤ) • ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 • f ij.1 ij.2 := by
  rw [← Nat.sum_antidiagonal_swap,
    sum_congr rfl fun ij hij ↦ by
      rw [Prod.fst_swap, Prod.snd_swap,
        ← Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm, natCast_zsmul],
    sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ (i - 1) • f j (i - 1)) k,
    natCast_zsmul, ← Nat.sum_antidiagonal_swap (n := k)]
  exact congrArg _ <| sum_congr rfl fun ij hij ↦ by
    rw [Prod.fst_swap, Prod.snd_swap, Nat.add_sub_cancel,
      ← Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]

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
    rw [ncoeff_derivative, ncoeff_nonnegResidueProduct, map_add, Pi.add_apply,
      nonnegResidueProduct_succ_derivative_left, map_zsmul, Pi.smul_apply, neg_smul,
      ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct]
    have hsplit : ∀ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * (derivative B)[[m + ij.2]] -
          (derivative B)[[m + ij.2]] * A[[(ij.1 : ℤ)]]) =
        (-m) • ((k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • c ij.1 (m - 1 + ij.2)) +
        (k + 1).choose ij.1 • (ij.2 : ℤ) • ((-1 : ℤ) ^ (ij.2 - 1) •
          c ij.1 (m + (ij.2 - 1 : ℕ))) := fun ij _ ↦ by
      rw [ncoeff_derivative, show m + (ij.2 : ℤ) - 1 = m - 1 + ij.2 by omega]
      simp only [c, mul_smul_comm, smul_mul_assoc]
      rcases eq_or_ne ij.2 0 with hj | hj
      · simp only [hj, Nat.cast_zero, add_zero, pow_zero, one_smul, zero_smul]; module
      · obtain ⟨j, hj'⟩ : ∃ j, ij.2 = j + 1 := ⟨ij.2 - 1, by omega⟩
        rw [hj', Nat.add_sub_cancel, show m - 1 + ((j + 1 : ℕ) : ℤ) = m + j by omega, pow_succ]
        module
    rw [sum_congr rfl hsplit, sum_add_distrib, ← smul_sum,
      sum_antidiagonal_choose_succ_snd (fun i j ↦ c i (m + j)) k]; dsimp only [c]; module

private theorem derivative_normalOrder_left_sum (A B : VertexOperator R V) (m : ℤ) (v : V)
    (P : ℕ) (hcut : ∀ i, P ≤ i → (B[[m - 1 + i]]) v = 0) :
    (∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) +
      (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v)) =
    (-m) • ∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
  have h₁ : (∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) =
      ∑ i ∈ range P, (i : ℤ) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
    cases P with
    | zero => simp
    | succ p =>
      rw [sum_range_succ, show m + (p : ℤ) = m - 1 + ((p + 1 : ℕ) : ℤ) by omega,
        hcut (p + 1) (by omega), map_zero, add_zero, sum_range_succ' _ p, Nat.cast_zero,
        zero_smul, add_zero]
      exact sum_congr rfl fun i _ ↦ by
        rw [ncoeff_derivative, LinearMap.smul_apply,
          show -(-(i : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) by omega,
          show -(i : ℤ) - 1 - 1 = -((i + 1 : ℕ) : ℤ) - 1 by omega,
          show m + (i : ℤ) = m - 1 + ((i + 1 : ℕ) : ℤ) by omega]
  rw [h₁, ← sum_add_distrib, smul_sum]
  exact sum_congr rfl fun i _ ↦ by
    rw [ncoeff_derivative, LinearMap.smul_apply, map_zsmul,
      show m + (i : ℤ) - 1 = m - 1 + i by omega, ← add_smul]; congr 1; omega

private theorem derivative_normalOrder_right_sum (A B : VertexOperator R V) (m : ℤ) (v : V)
    (Q : ℕ) :
    (∑ i ∈ range (Q + 1), (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) +
      (∑ i ∈ range Q, ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v)) =
    (-m) • ∑ i ∈ range Q, (B[[m - 1 - i - 1]]) ((A[[(i : ℤ)]]) v) := by
  have h₁ : (∑ i ∈ range (Q + 1), (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) =
      ∑ i ∈ range Q, (-(i : ℤ) - 1) • (B[[m - 1 - i - 1]]) ((A[[(i : ℤ)]]) v) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, ncoeff_derivative, neg_zero, zero_smul, LinearMap.zero_apply,
      map_zero, add_zero]
    exact sum_congr rfl fun i _ ↦ by
      rw [LinearMap.smul_apply, map_zsmul, show -((i + 1 : ℕ) : ℤ) = -(i : ℤ) - 1 by omega,
        show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by omega,
        show m - ((i + 1 : ℕ) : ℤ) - 1 = m - 1 - i - 1 by omega]
  rw [h₁, ← sum_add_distrib, smul_sum]
  exact sum_congr rfl fun i _ ↦ by
    rw [ncoeff_derivative, LinearMap.smul_apply, show m - (i : ℤ) - 1 - 1 = m - 1 - i - 1 by omega,
      ← add_smul]; congr 1; omega

/-- Formal differentiation is a derivation of normal ordering. -/
theorem derivative_normalOrder (A B : VertexOperator R V) :
    derivative (normalOrder A B) =
      normalOrder (derivative A) B + normalOrder A (derivative B) := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := ((P₀ : ℤ) - (m - 1)).toNat
  have cutB (i : ℕ) (hi : P ≤ i) : (B[[m - 1 + i]]) v = 0 := hP₀ _ (by omega)
  have cutA (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ _ (by omega)
  rw [ncoeff_derivative, LinearMap.smul_apply, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B (m - 1) v cutB cutA,
    map_add, Pi.add_apply, LinearMap.add_apply, ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum (derivative A) B m v (P := P) (Q := Q + 1)
      (fun _ _ ↦ hP₀ _ (by omega))
      (fun i hi ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hQ _ (by omega), smul_zero]),
    normalOrderCoeff_eq_sum A (derivative B) m v (P := P) (Q := Q)
      (fun i hi ↦ by
        rw [ncoeff_derivative, LinearMap.smul_apply, hP₀ _ (by omega), smul_zero]) cutA,
    smul_add, ← derivative_normalOrder_left_sum A B m v P cutB,
    ← derivative_normalOrder_right_sum A B m v Q]; abel

/-- Formal differentiation is a derivation of every integer `n`-th product. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  rcases le_or_gt 0 n with hn | hn
  · simp only [nthProduct_of_nonneg hn, derivative_nonnegResidueProduct]
  · simp only [nthProduct_of_neg hn, derivative_normalOrder, derivative_hasseDerivative_comm]

/-! ### Translation covariance of Hasse derivatives and `n`-th products -/

/-- Hasse derivatives preserve translation covariance. -/
theorem lie_ncoeff_hasseDerivative {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, (hasseDerivative k A)[[m]]⁆ = (derivative (hasseDerivative k A))[[m]] := by
  rw [ncoeff_hasseDerivative, derivative_hasseDerivative_comm, ncoeff_hasseDerivative, ← hA]
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Nonnegative residue products preserve translation covariance. -/
theorem lie_ncoeff_nonnegResidueProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, (nonnegResidueProduct k A B)[[m]]⁆ = (derivative (nonnegResidueProduct k A B))[[m]] := by
  have hjac (X Y : Module.End R V) : T * (X * Y - Y * X) - (X * Y - Y * X) * T =
      (⁅T, X⁆ * Y + X * ⁅T, Y⁆) - (⁅T, Y⁆ * X + Y * ⁅T, X⁆) := by
    simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]; abel
  rw [derivative_nonnegResidueProduct, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct, Ring.lie_def, mul_sum, sum_mul,
    ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, ← smul_sub, ← smul_sub,
    ← smul_add, ← smul_add]
  congr 2; rw [hjac, hA, hB]; abel

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
      have h₁ := LinearMap.congr_fun (hX i) (Y i v); have h₂ := LinearMap.congr_fun (hY i) v
      simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp] at h₁ h₂
      rw [← h₁, ← h₂, map_sub]; abel
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let P := (max ((P₁ : ℤ) + 1) P₂ - m).toNat; let Q := max (Q₁ + 1) Q₂
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    derivative_normalOrder, map_add, Pi.add_apply, LinearMap.add_apply, ncoeff_normalOrder,
    ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B m v (P := P) (Q := Q)
      (fun _ _ ↦ hP₁ _ (by omega)) (fun _ _ ↦ hQ₁ _ (by omega)),
    normalOrderCoeff_eq_sum A B m (T v) (P := P) (Q := Q)
      (fun _ _ ↦ hP₂ _ (by omega)) (fun _ _ ↦ hQ₂ _ (by omega)),
    normalOrderCoeff_eq_sum (derivative A) B m v (P := P) (Q := Q) (fun _ _ ↦ hP₁ _ (by omega))
      (fun _ _ ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hQ₁ _ (by omega), smul_zero]),
    normalOrderCoeff_eq_sum A (derivative B) m v (P := P) (Q := Q)
      (fun _ _ ↦ by rw [ncoeff_derivative, LinearMap.smul_apply, hP₁ _ (by omega), smul_zero])
      (fun _ _ ↦ hQ₁ _ (by omega)),
    map_add, map_sum, map_sum,
    show ∀ a b c d : V, (a + b) - (c + d) = (a - c) + (b - d) from fun _ _ _ _ ↦ by abel,
    hsum P _ _ _ _ (fun _ ↦ hA _) (fun _ ↦ hB _), hsum Q _ _ _ _ (fun _ ↦ hB _) (fun _ ↦ hA _)]
  abel

/-- Every integer `n`-th product preserves translation covariance. -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn]; exact lie_ncoeff_nonnegResidueProduct hA hB n.toNat m
  · rw [nthProduct_of_neg hn]; exact lie_ncoeff_normalOrder (lie_ncoeff_hasseDerivative hA _) hB m

/-! ### Vacuum evaluation of Hasse derivatives and `n`-th products -/

/-- If `vac` is annihilated by nonnegative modes of `A`, it is also annihilated by nonnegative
modes of every Hasse derivative of `A`. -/
theorem ncoeff_hasseDerivative_apply_of_nonneg {A : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (k : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    ((hasseDerivative k A)[[m]]) vac = 0 := by
  rw [ncoeff_hasseDerivative, LinearMap.smul_apply]
  rcases lt_or_ge m k with hlt | hge
  · lift m to ℕ using hm
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [hA (m - k) (by omega), smul_zero]

/-- If `vac` is annihilated by nonnegative modes of `A` and `B`, it is annihilated by nonnegative
modes of `nthProduct n A B` for every `n : ℤ`. -/
theorem ncoeff_nthProduct_apply_of_nonneg {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0)
    (n : ℤ) {m : ℤ} (hm : 0 ≤ m) : ((nthProduct n A B)[[m]]) vac = 0 := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    exact sum_eq_zero fun ij _ ↦ by simp [hA ij.1 (Nat.cast_nonneg _), hB (m + ij.2) (by omega)]
  · rw [nthProduct_of_neg hn, ncoeff_normalOrder, normalOrderCoeff_apply,
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by simp [hB (m + i) (by omega)],
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDerivative_apply_of_nonneg hA _ (Nat.cast_nonneg i), map_zero],
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
    have hR : (∑ᶠ i : ℕ, (B[[-1 - i - 1]]) (((hasseDerivative k A)[[(i : ℤ)]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDerivative_apply_of_nonneg hA k (Nat.cast_nonneg i), map_zero]
    rw [nthProduct_neg_succ, ncoeff_normalOrder, normalOrderCoeff_apply, hR, add_zero,
      finsum_eq_single _ 0]
    · rw [Nat.cast_zero, neg_zero, zero_sub, add_zero, ncoeff_neg_one_hasseDerivative]
    · intro i hi; simp [hB (-1 + i) (by omega)]

/-- If `T vac = 0` and `B` is translation-covariant with respect to `T`, then
`T (B₍ₘ₎ vac) = -m B₍ₘ₋₁₎ vac` for every integer `m`. -/
theorem apply_ncoeff_apply_of_lie {T : Module.End R V} {vac : V} {B : VertexOperator R V}
    (hT : T vac = 0) (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    T ((B[[m]]) vac) = (-m) • (B[[m - 1]]) vac := by
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, hT, map_zero, sub_zero,
    ncoeff_derivative, LinearMap.smul_apply] using LinearMap.congr_fun (hcov m) vac

/-- If `T vac = 0` and `B` is translation-covariant with respect to `T`, then
`k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)` without any division hypothesis on `R`. -/
theorem factorial_smul_ncoeff_neg_succ_apply_of_lie {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    k.factorial • (B[[-(k : ℤ) - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := apply_ncoeff_apply_of_lie hT hcov (-(k : ℤ) - 1)
    rw [show -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) by omega,
      show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by omega, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul, smul_comm]

/-- **Commutator formula for mutually local vertex operators.** If `A` and `B` are local of order
`N`, then `[A₍ₘ₎, B₍ₙ₎] = ∑_{j < N} (m choose j) (A_{(j)} B)₍ₘ₊ₙ₋ⱼ₎` over any commutative ring. -/
theorem IsLocalOfOrder.lie_ncoeff {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (m n : ℤ) :
    ⁅A[[m]], B[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (nonnegResidueProduct j A B)[[m + n - j]] := by
  have hexp := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm m) n
  simp only [commutatorDistribution_apply, Finset.sum_apply, FormalDistribution.deltaTerm_apply,
    FormalDistribution.residue_apply, FormalDistribution.mulSub_pow_apply, zero_add] at hexp
  rw [Ring.lie_def, hexp]
  exact sum_congr rfl fun j _ ↦ by rw [ncoeff_nonnegResidueProduct]

/-- Over a `ℚ`-algebra, if `T vac = 0` and `B` is translation-covariant with respect to `T`,
then all nonnegative modes of `B` annihilate `vac`. -/
theorem ncoeff_apply_eq_zero_of_nonneg_of_lie [Algebra ℚ R] {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) {m : ℤ} (hm : 0 ≤ m) :
    (B[[m]]) vac = 0 := by
  lift m to ℕ using hm
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  suffices hstep : ∀ d k : ℕ, N - d ≤ k → (B[[(k : ℤ)]]) vac = 0 from hstep N m (by omega)
  intro d; induction d with
  | zero => exact fun k hk ↦ hN k (by exact_mod_cast hk)
  | succ d ih =>
    intro k hk; have hrec := apply_ncoeff_apply_of_lie hT hcov ((k + 1 : ℕ) : ℤ)
    rw [ih (k + 1) (by omega), map_zero, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega,
      neg_smul, eq_comm, neg_eq_zero, natCast_zsmul] at hrec
    simpa [smul_zero] using eq_inv_smul_of_nsmul (R := R) (Nat.succ_ne_zero k) hrec

/-- Over a `ℚ`-algebra, if `T vac = 0` and `B` is translation-covariant with respect to `T`,
then `B₍₋ₖ₋₁₎ vac = (k!)⁻¹ • Tᵏ (B₍₋₁₎ vac)`. -/
theorem ncoeff_neg_succ_apply_of_lie [Algebra ℚ R] {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    (B[[-(k : ℤ) - 1]]) vac = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (T ^ k) ((B[[-1]]) vac) :=
  eq_inv_smul_of_nsmul k.factorial_ne_zero (factorial_smul_ncoeff_neg_succ_apply_of_lie hT hcov k)

end VertexOperator
