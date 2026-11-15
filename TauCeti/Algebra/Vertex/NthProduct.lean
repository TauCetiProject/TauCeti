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

For a field `A(z) = ∑ₙ A₍ₙ₎ z^{-n-1}` on an `R`-module `V`, its `k`-th Hasse (divided-power)
derivative `∂_z^{(k)} A(z)` has normalized modes `((-1)ᵏ (n choose k)) • A₍ₙ₋ₖ₎`
(`VertexOperator.hasseDerivative`), using integer binomial coefficients `Ring.choose` so that no
division or characteristic assumption on `R` is required. It satisfies `k! • ∂_z^{(k)} A = ∂_zᵏ A`,
and preserves mutual locality while increasing an order bound by `k`.

Combining nonnegative residue products for `n ≥ 0` with normal ordering of Hasse derivatives for
`n < 0` defines the `R`-bilinear integer `n`-th product (`VertexOperator.nthProduct`)

* `A(z)_{(n)} B(z) = Res_x (x - z)ⁿ [A(x), B(z)]` for `n ≥ 0`,
* `A(z)_{(-k-1)} B(z) = :(∂_z^{(k)} A(z)) B(z):` for `k : ℕ`.

By Dong's lemma and locality of Hasse derivatives, `nthProduct n` preserves mutual locality for
every integer `n`. Formal differentiation acts as a derivation of `nthProduct n`, differentiates the
left factor by `(∂A)_{(n)} B = -n A_{(n-1)} B`, preserves translation covariance, and evaluates on a
vacuum vector `vac` annihilated by nonnegative modes via `(A_{(n)} B)₍₋₁₎ vac = A₍ₙ₎ (B₍₋₁₎ vac)`.

## Main definitions

* `VertexOperator.id`: the identity vertex operator `Id_V z⁰`, with modes `δ_{n,-1} • 1`.
* `VertexOperator.hasseDerivative`: the `k`-th divided-power derivative `∂_z^{(k)}` on fields.
* `VertexOperator.nthProduct`: the `R`-bilinear `n`-th product `A_{(n)} B` for `n : ℤ`.

## Main results

* `VertexOperator.IsLocalOfOrder.hasseDerivative_left`,
  `VertexOperator.IsLocalOfOrder.nthProduct_left`: Hasse derivatives and all integer `n`-th products
  preserve mutual locality over an arbitrary commutative ring.
* `VertexOperator.IsLocalOfOrder.lie_ncoeff`: commutator formula for modes of mutually local fields.
* `VertexOperator.derivative_nthProduct`, `VertexOperator.nthProduct_derivative_left`: the Leibniz
  and left-derivative rules for `nthProduct`.
* `VertexOperator.lie_ncoeff_nthProduct`: `nthProduct` preserves translation covariance.
* `VertexOperator.ncoeff_nthProduct_apply_of_nonneg`,
  `VertexOperator.ncoeff_neg_one_nthProduct_apply`,
  `VertexOperator.ncoeff_apply_eq_zero_of_nonneg_of_lie`: vacuum annihilation and `(-1)`-mode
  evaluation for translation-covariant fields and `nthProduct`.

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
  ⟨0, fun k hk ↦ not_lt.mp fun h ↦ hk (by simp [h.ne])⟩

/-- The identity field `Id_V z⁰`, whose `(-1)`-st normalized mode is `1` and all other modes are
`0`. -/
protected def id (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] : VertexOperator R V :=
  of_coeff (fun k ↦ if k = 0 then 1 else 0) bddBelow_support_id

/-- The normalized modes of `VertexOperator.id` are `δ_{n,-1}`. -/
theorem ncoeff_id (n : ℤ) : (VertexOperator.id R V)[[n]] = if n = -1 then 1 else 0 := by
  rw [VertexOperator.id, ncoeff_of_coeff]
  have e : (-n - 1 = 0) ↔ (n = -1) := by omega
  simp [e]

@[simp]
theorem ncoeff_neg_one_id : (VertexOperator.id R V)[[-1]] = 1 := by
  simp [ncoeff_id]

@[simp]
theorem ncoeff_id_of_ne {n : ℤ} (hn : n ≠ -1) : (VertexOperator.id R V)[[n]] = 0 := by
  simp [ncoeff_id, hn]

@[simp]
theorem derivative_id : derivative (VertexOperator.id R V) = 0 := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_derivative, ncoeff_id, map_zero, Pi.zero_apply]
  split_ifs with h
  · have hn : n = 0 := by omega
    simp [hn]
  · simp

/-- The identity field commutes with every field, hence is local of order `0`. -/
theorem IsLocalOfOrder.id_left (B : VertexOperator R V) :
    (VertexOperator.id R V).IsLocalOfOrder B 0 := by
  rw [isLocalOfOrder_iff]
  intro m n
  simp only [Nat.antidiagonal_zero, sum_singleton, Nat.choose_self, Nat.cast_zero, add_zero,
    pow_zero, one_smul, ncoeff_id]
  split_ifs <;> simp

/-- Every field is local of order `0` with the identity field. -/
theorem IsLocalOfOrder.id_right (A : VertexOperator R V) :
    A.IsLocalOfOrder (VertexOperator.id R V) 0 :=
  (IsLocalOfOrder.id_left A).symm

@[simp]
theorem nonnegResidueProduct_id_left (n : ℕ) (B : VertexOperator R V) :
    nonnegResidueProduct n (VertexOperator.id R V) B = 0 :=
  (IsLocalOfOrder.id_left B).nonnegResidueProduct_eq_zero (Nat.zero_le n)

@[simp]
theorem normalOrder_id_left (B : VertexOperator R V) :
    normalOrder (VertexOperator.id R V) B = B := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ ?_
  rw [ncoeff_normalOrder, normalOrderCoeff_apply]
  have hright : (∑ᶠ i : ℕ, (B[[n - i - 1]]) (((VertexOperator.id R V)[[(i : ℤ)]]) v)) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    rw [ncoeff_id_of_ne (by omega), LinearMap.zero_apply, map_zero]
  rw [hright, add_zero, finsum_eq_single _ 0]
  · simp
  · intro i hi
    rw [ncoeff_id_of_ne (by omega), LinearMap.zero_apply]

/-! ### Hasse derivatives of vertex operators -/

private theorem bddBelow_support_hasseDerivative (k : ℕ) (A : VertexOperator R V) (v : V) :
    BddBelow (Function.support fun m : ℤ ↦
      (((-1 : ℤ) ^ k * Ring.choose (-m - 1) k) • A[[-m - 1 - k]]) v) := by
  obtain ⟨N, hN⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  refine ⟨-(N : ℤ) - 1 - k, fun m hm ↦ ?_⟩
  by_contra! hlt
  exact hm (by simp [hN (-m - 1 - k) (by omega)])

/-- The `k`-th Hasse (divided-power) derivative `∂_z^{(k)}` of a vertex operator, defined over any
commutative ring by `(∂_z^{(k)} A)₍ₙ₎ = (-1)ᵏ (n choose k) • A₍ₙ₋ₖ₎`. -/
def hasseDerivative (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A := of_coeff
    (fun m ↦ ((-1 : ℤ) ^ k * Ring.choose (-m - 1) k) • A[[-m - 1 - k]])
    (bddBelow_support_hasseDerivative k A)
  map_add' A B := ext_ncoeff fun n ↦ by simp [smul_add]
  map_smul' r A := ext_ncoeff fun n ↦ by simp [smul_comm]

/-- The normalized modes of the `k`-th Hasse derivative are `(-1)ᵏ (n choose k) • A₍ₙ₋ₖ₎`. -/
@[simp]
theorem ncoeff_hasseDerivative (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDerivative k A)[[n]] = ((-1 : ℤ) ^ k * Ring.choose n k) • A[[n - k]] := by
  simp only [hasseDerivative, LinearMap.coe_mk, AddHom.coe_mk, ncoeff_of_coeff]
  have e : -(-n - 1) - 1 = n := by omega
  rw [e]

/-- The `0`-th Hasse derivative is the identity. -/
@[simp]
theorem hasseDerivative_zero (A : VertexOperator R V) : hasseDerivative 0 A = A :=
  ext_ncoeff fun n ↦ by simp

/-- The `1`-st Hasse derivative is the formal derivative. -/
@[simp]
theorem hasseDerivative_one (A : VertexOperator R V) : hasseDerivative 1 A = derivative A :=
  ext_ncoeff fun n ↦ by simp

/-- The `(-1)`-st mode of `∂_z^{(k)} A` is `A₍₋ₖ₋₁₎`. -/
theorem ncoeff_neg_one_hasseDerivative (k : ℕ) (A : VertexOperator R V) :
    (hasseDerivative k A)[[-1]] = A[[-(k : ℤ) - 1]] := by
  rw [ncoeff_hasseDerivative]
  have hchoose : Ring.choose (-1 : ℤ) k = (-1 : ℤ) ^ k := by
    have h := Ring.choose_neg (1 : ℤ) k
    rw [show (1 : ℤ) + k - 1 = (k : ℤ) by omega, Ring.choose_natCast, Nat.choose_self,
      Nat.cast_one, Int.negOnePow_def, Units.smul_def, zsmul_one] at h
    exact h
  have hpow : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  have hidx : (-1 : ℤ) - k = -(k : ℤ) - 1 := by omega
  rw [hchoose, hpow, one_smul, hidx]

@[simp]
theorem hasseDerivative_id_succ (k : ℕ) :
    hasseDerivative (k + 1) (VertexOperator.id R V) = 0 := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_hasseDerivative, map_zero, Pi.zero_apply, ncoeff_id]
  split_ifs with h
  · have hn : n = (k : ℤ) := by omega
    rw [hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k), Nat.cast_zero,
      mul_zero, zero_smul]
  · simp

/-- Differentiating the `k`-th Hasse derivative gives `(k + 1)` times the `(k + 1)`-st. -/
theorem derivative_hasseDerivative (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDerivative k A) = (k + 1) • hasseDerivative (k + 1) A := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_derivative, ncoeff_hasseDerivative, map_nsmul, Pi.smul_apply, ncoeff_hasseDerivative]
  have hchoose := Ring.choose_smul_choose n (show 1 ≤ k + 1 by omega)
  rw [Nat.choose_one_right, Nat.cast_one, Ring.choose_one_right, Nat.add_sub_cancel,
    nsmul_eq_mul] at hchoose
  have hidx : n - 1 - (k : ℤ) = n - ↑(k + 1) := by omega
  rw [hidx, smul_smul, ← natCast_zsmul, smul_smul]
  congr 1
  rw [pow_succ]
  linear_combination ((-1 : ℤ) ^ k) * hchoose

/-- Taking the `k`-th Hasse derivative of `∂A` also gives `(k + 1)` times the `(k + 1)`-st. -/
theorem hasseDerivative_derivative (k : ℕ) (A : VertexOperator R V) :
    hasseDerivative k (derivative A) = (k + 1) • hasseDerivative (k + 1) A := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_hasseDerivative, ncoeff_derivative, map_nsmul, Pi.smul_apply, ncoeff_hasseDerivative]
  have hchoose := Ring.choose_smul_choose n (show k ≤ k + 1 by omega)
  rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
    nsmul_eq_mul] at hchoose
  have hidx : n - (k : ℤ) - 1 = n - ↑(k + 1) := by omega
  rw [hidx, smul_smul, ← natCast_zsmul, smul_smul]
  congr 1
  rw [pow_succ]
  linear_combination ((-1 : ℤ) ^ k) * hchoose

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

/-- Over a `ℚ`-algebra, the `k`-th Hasse derivative is `(k!)⁻¹ • ∂_zᵏ A`. -/
theorem hasseDerivative_eq_smul_iterate_derivative [Algebra ℚ R] (k : ℕ) (A : VertexOperator R V) :
    hasseDerivative k A = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (derivative^[k]) A := by
  rw [← factorial_smul_hasseDerivative, ← Nat.cast_smul_eq_nsmul R,
    ← map_natCast (algebraMap ℚ R), smul_smul, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast k.factorial_ne_zero), map_one, one_smul]

/-- Taking the `k`-th Hasse derivative in the first variable increases a locality bound by `k`,
over any commutative ring. -/
theorem IsLocalOfOrder.hasseDerivative_left {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (k : ℕ) :
    (hasseDerivative k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  let c : ℕ → ℤ → Module.End R V := fun j ↦
    FormalDistribution.residue ((FormalDistribution.mulSub ^ j) (A.commutatorDistribution B))
  have hexp : (hasseDerivative k A).commutatorDistribution B =
      ∑ j ∈ range N, FormalDistribution.deltaTerm (k + j)
        (fun r ↦ ((-1 : ℤ) ^ k * ((k + j).choose k : ℤ)) • c j r) := by
    funext m n
    have hsum := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm (m - k)) n
    simp only [Finset.sum_apply, FormalDistribution.deltaTerm_apply] at hsum
    rw [commutatorDistribution_apply, ncoeff_hasseDerivative, smul_mul_assoc, mul_smul_comm,
      ← smul_sub, ← commutatorDistribution_apply, hsum, smul_sum]
    simp only [Finset.sum_apply, FormalDistribution.deltaTerm_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_smul, smul_smul]
    have hchoose := Ring.choose_smul_choose m (Nat.le_add_right k j)
    rw [Nat.add_sub_cancel_left, nsmul_eq_mul] at hchoose
    have hidx : m - (k : ℤ) + n - j = m + n - ↑(k + j) := by omega
    rw [hidx]
    congr 1
    linear_combination (-1 : ℤ) ^ k * hchoose.symm
  rw [hexp, map_sum]
  exact sum_eq_zero fun j hj ↦
    FormalDistribution.mulSub_pow_deltaTerm_eq_zero (by have := mem_range.mp hj; omega) _

/-- Taking the `k`-th Hasse derivative in the second variable increases a locality bound by `k`. -/
theorem IsLocalOfOrder.hasseDerivative_right {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (k : ℕ) :
    A.IsLocalOfOrder (hasseDerivative k B) (N + k) :=
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
    nthProduct n A B = nonnegResidueProduct n.toNat A B := by
  simp [nthProduct, hn]

/-- For `n < 0`, `nthProduct n` is `:∂_z^{(-n-1)} A(z) B(z):`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B = normalOrder (hasseDerivative (-n - 1).toNat A) B := by
  simp [nthProduct, not_le.mpr hn]

@[simp]
theorem nthProduct_natCast (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (k : ℤ) A B = nonnegResidueProduct k A B := by
  simp [nthProduct]

@[simp]
theorem nthProduct_zero (A B : VertexOperator R V) :
    nthProduct 0 A B = nonnegResidueProduct 0 A B := by
  simp [nthProduct]

@[simp]
theorem nthProduct_neg_succ (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDerivative k A) B := by
  rw [nthProduct_of_neg (by omega)]
  have e : (-(-(k : ℤ) - 1) - 1).toNat = k := by omega
  rw [e]

@[simp]
theorem nthProduct_neg_one (A B : VertexOperator R V) :
    nthProduct (-1) A B = normalOrder A B := by
  simpa using nthProduct_neg_succ 0 A B

/-- Left `n`-th products with the identity field vanish except at `n = -1`, where they act as the
identity. -/
theorem nthProduct_id_left (n : ℤ) (B : VertexOperator R V) :
    nthProduct n (VertexOperator.id R V) B = if n = -1 then B else 0 := by
  rcases le_or_gt 0 n with hn | hn
  · have hne : n ≠ -1 := by omega
    simp [nthProduct_of_nonneg hn, hne]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ]
    cases k with
    | zero => simp
    | succ k =>
      have hne : -((k + 1 : ℕ) : ℤ) - 1 ≠ -1 := by omega
      rw [hasseDerivative_id_succ, normalOrder_zero_left]
      simp only [hne, ↓reduceIte]

/-- **Dong's lemma** for all integer `n`-th products (left form). -/
theorem IsLocalOfOrder.nthProduct_left {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn]
    exact (hAB.nonnegResidueProduct_left hBC hAC n.toNat).mono (by omega)
  · rw [nthProduct_of_neg hn]
    let k := (-n - 1).toNat
    exact ((hAB.hasseDerivative_left k).normalOrder_left hBC
      (hAC.hasseDerivative_left k)).mono (by omega)

/-- **Dong's lemma** for all integer `n`-th products (right form). -/
theorem IsLocalOfOrder.nthProduct_right {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hCA : C.IsLocalOfOrder A r₃) (hCB : C.IsLocalOfOrder B r₂)
    (hAB : A.IsLocalOfOrder B r₁) (n : ℤ) :
    C.IsLocalOfOrder (nthProduct n A B) (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) :=
  (hAB.nthProduct_left hCB.symm hCA.symm n).symm

/-! ### Derivatives of residue, normal-ordered and `n`-th products -/

@[simp]
theorem nonnegResidueProduct_zero_derivative_left (A B : VertexOperator R V) :
    nonnegResidueProduct 0 (derivative A) B = 0 := by
  refine ext_ncoeff fun m ↦ ?_
  simp

/-- Differentiating the left factor of the `(k + 1)`-st residue product gives `-(k + 1)` times the
`k`-th residue product. -/
theorem nonnegResidueProduct_succ_derivative_left (k : ℕ) (A B : VertexOperator R V) :
    nonnegResidueProduct (k + 1) (derivative A) B =
      -((k + 1 : ℕ) : ℤ) • nonnegResidueProduct k A B := by
  refine ext_ncoeff fun m ↦ ?_
  rw [ncoeff_nonnegResidueProduct, map_zsmul, Pi.smul_apply, neg_smul,
    ncoeff_nonnegResidueProduct]
  have e : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
          B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
      -((k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ) - 1]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ) - 1]]))) := by
    intro ij _
    rw [ncoeff_derivative]
    simp only [smul_mul_assoc, mul_smul_comm, ← natCast_zsmul]
    module
  rw [sum_congr rfl e, sum_neg_distrib,
    sum_antidiagonal_choose_succ_nsmul_nsmul
      (fun i j ↦ (-1 : ℤ) ^ j • (A[[(i : ℤ) - 1]] * B[[m + j]] - B[[m + j]] * A[[(i : ℤ) - 1]])) k,
    natCast_zsmul]
  congr 2
  refine sum_congr rfl fun ij _ ↦ ?_
  have hidx : ((ij.1 + 1 : ℕ) : ℤ) - 1 = (ij.1 : ℤ) := by omega
  rw [hidx]

/-- Differentiating the left factor of an `n`-th product multiplies by `-n` and lowers `n` by
one. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have hidx : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    have hcoef : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    rw [nthProduct_neg_succ, hidx, nthProduct_neg_succ, hcoef, natCast_zsmul,
      hasseDerivative_derivative, ← normalOrderₗ_apply, map_nsmul, LinearMap.smul_apply,
      normalOrderₗ_apply]
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 1 : ℕ) := ⟨n.toNat - 1, by omega⟩
    have hidx : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    rw [nthProduct_natCast, hidx, nthProduct_natCast, nonnegResidueProduct_succ_derivative_left]

private theorem nonnegResidueProduct_succ_derivative_tail (k : ℕ) (A B : VertexOperator R V)
    (m : ℤ) :
    ∑ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • (ij.2 : ℤ) • ((-1 : ℤ) ^ (ij.2 - 1) •
      (A[[(ij.1 : ℤ)]] * B[[m + (ij.2 - 1 : ℕ)]] -
        B[[m + (ij.2 - 1 : ℕ)]] * A[[(ij.1 : ℤ)]])) =
    ((k + 1 : ℕ) : ℤ) • ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]]) := by
  rw [← Nat.sum_antidiagonal_swap]
  have eswap : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.swap.1 • (ij.swap.2 : ℤ) • ((-1 : ℤ) ^ (ij.swap.2 - 1) •
        (A[[(ij.swap.1 : ℤ)]] * B[[m + (ij.swap.2 - 1 : ℕ)]] -
          B[[m + (ij.swap.2 - 1 : ℕ)]] * A[[(ij.swap.1 : ℤ)]])) =
      (k + 1).choose ij.1 • ij.1 • ((-1 : ℤ) ^ (ij.1 - 1) •
        (A[[(ij.2 : ℤ)]] * B[[m + (ij.1 - 1 : ℕ)]] -
          B[[m + (ij.1 - 1 : ℕ)]] * A[[(ij.2 : ℤ)]])) := by
    intro ij hij
    rw [Prod.fst_swap, Prod.snd_swap,
      Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm, natCast_zsmul]
  rw [sum_congr rfl eswap,
    sum_antidiagonal_choose_succ_nsmul_nsmul
      (fun i j ↦ (-1 : ℤ) ^ (i - 1) •
        (A[[(j : ℤ)]] * B[[m + (i - 1 : ℕ)]] - B[[m + (i - 1 : ℕ)]] * A[[(j : ℤ)]])) k,
    natCast_zsmul, ← Nat.sum_antidiagonal_swap (n := k)]
  congr 1
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [Prod.fst_swap, Prod.snd_swap, Nat.add_sub_cancel,
    Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]

/-- Formal differentiation is a derivation of each nonnegative residue product. -/
theorem derivative_nonnegResidueProduct (k : ℕ) (A B : VertexOperator R V) :
    derivative (nonnegResidueProduct k A B) =
      nonnegResidueProduct k (derivative A) B + nonnegResidueProduct k A (derivative B) := by
  cases k with
  | zero =>
    refine ext_ncoeff fun m ↦ ?_
    rw [ncoeff_derivative, map_add, Pi.add_apply, nonnegResidueProduct_zero_derivative_left,
      map_zero, Pi.zero_apply, zero_add, ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct]
    simp only [Nat.antidiagonal_zero, sum_singleton, Nat.choose_self, Nat.cast_zero, add_zero,
      pow_zero, one_smul, ncoeff_derivative, smul_sub, mul_smul_comm, smul_mul_assoc]
  | succ k =>
    refine ext_ncoeff fun m ↦ ?_
    rw [ncoeff_derivative, ncoeff_nonnegResidueProduct, map_add, Pi.add_apply,
      nonnegResidueProduct_succ_derivative_left, map_zsmul, Pi.smul_apply, neg_smul,
      ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct]
    have hsplit : ∀ ij ∈ antidiagonal (k + 1),
        (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * (derivative B)[[m + ij.2]] -
            (derivative B)[[m + ij.2]] * A[[(ij.1 : ℤ)]]) =
        (-m) • ((k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]])) +
        (k + 1).choose ij.1 • (ij.2 : ℤ) • ((-1 : ℤ) ^ (ij.2 - 1) •
          (A[[(ij.1 : ℤ)]] * B[[m + (ij.2 - 1 : ℕ)]] -
            B[[m + (ij.2 - 1 : ℕ)]] * A[[(ij.1 : ℤ)]])) := by
      intro ij _
      rw [ncoeff_derivative, show m + (ij.2 : ℤ) - 1 = m - 1 + ij.2 by omega]
      simp only [mul_smul_comm, smul_mul_assoc]
      rcases eq_or_ne ij.2 0 with hj | hj
      · simp only [hj, Nat.cast_zero, add_zero, pow_zero, one_smul, zero_smul]
        module
      · have hpow : (-1 : ℤ) ^ ij.2 = -((-1 : ℤ) ^ (ij.2 - 1)) := by
          conv_lhs => rw [show ij.2 = (ij.2 - 1) + 1 by omega, pow_succ]
          ring
        have hsub : m - 1 + (ij.2 : ℤ) = m + ((ij.2 - 1 : ℕ) : ℤ) := by omega
        rw [hsub, hpow]
        module
    rw [sum_congr rfl hsplit, sum_add_distrib, ← smul_sum,
      nonnegResidueProduct_succ_derivative_tail]
    module

private theorem derivative_normalOrder_left_sum (A B : VertexOperator R V) (m : ℤ) (v : V)
    (P : ℕ) (hcut : ∀ i, P ≤ i → (B[[m - 1 + i]]) v = 0) :
    (∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) +
      (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v)) =
    (-m) • ∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
  have h₁ : (∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) =
      ∑ i ∈ range P, (i : ℤ) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
    rcases eq_or_ne P 0 with hP | hP
    · rw [hP]; simp
    · obtain ⟨p, hp⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
      rw [hp, sum_range_succ, show m + (p : ℤ) = m - 1 + ((p + 1 : ℕ) : ℤ) by omega,
        hcut (p + 1) (by omega), map_zero, add_zero, sum_range_succ' _ p, Nat.cast_zero,
        zero_smul, add_zero]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [ncoeff_derivative, LinearMap.smul_apply]
      have e₁ : -(-(i : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) := by omega
      have e₂ : -(i : ℤ) - 1 - 1 = -((i + 1 : ℕ) : ℤ) - 1 := by omega
      have e₃ : m + (i : ℤ) = m - 1 + ((i + 1 : ℕ) : ℤ) := by omega
      rw [e₁, e₂, e₃]
  have h₂ : (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v)) =
      ∑ i ∈ range P, (-(m + i)) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [ncoeff_derivative, LinearMap.smul_apply, map_zsmul,
      show m + (i : ℤ) - 1 = m - 1 + i by omega]
  rw [h₁, h₂, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← add_smul]
  congr 1
  omega

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
    refine sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smul_apply, map_zsmul]
    have e₁ : -((i + 1 : ℕ) : ℤ) = -(i : ℤ) - 1 := by omega
    have e₂ : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by omega
    have e₃ : m - ((i + 1 : ℕ) : ℤ) - 1 = m - 1 - i - 1 := by omega
    rw [e₁, e₂, e₃]
  have h₂ : (∑ i ∈ range Q, ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v)) =
      ∑ i ∈ range Q, (-(m - i - 1)) • (B[[m - 1 - i - 1]]) ((A[[(i : ℤ)]]) v) := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [ncoeff_derivative, LinearMap.smul_apply,
      show m - (i : ℤ) - 1 - 1 = m - 1 - i - 1 by omega]
  rw [h₁, h₂, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← add_smul]
  congr 1
  omega

/-- Formal differentiation is a derivation of normal ordering. -/
theorem derivative_normalOrder (A B : VertexOperator R V) :
    derivative (normalOrder A B) =
      normalOrder (derivative A) B + normalOrder A (derivative B) := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₀, hQ₀⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := ((P₀ : ℤ) - (m - 1)).toNat
  let Q := Q₀
  have cutB_shift (i : ℕ) (hi : P ≤ i) : (B[[m - 1 + i]]) v = 0 := hP₀ _ (by omega)
  have cutB (i : ℕ) (hi : P ≤ i) : (B[[m + i]]) v = 0 := hP₀ _ (by omega)
  have cutdB (i : ℕ) (hi : P ≤ i) : ((derivative B)[[m + i]]) v = 0 := by
    rw [ncoeff_derivative, LinearMap.smul_apply, show m + (i : ℤ) - 1 = m - 1 + i by omega,
      cutB_shift i hi, smul_zero]
  have cutA (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ₀ _ (by omega)
  have cutdA (i : ℕ) (hi : Q + 1 ≤ i) : ((derivative A)[[(i : ℤ)]]) v = 0 := by
    rw [ncoeff_derivative, LinearMap.smul_apply, show (i : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) by omega,
      cutA (i - 1) (by omega), smul_zero]
  rw [ncoeff_derivative, LinearMap.smul_apply, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B (m - 1) v cutB_shift cutA,
    map_add, Pi.add_apply, LinearMap.add_apply, ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum (derivative A) B m v cutB cutdA,
    normalOrderCoeff_eq_sum A (derivative B) m v cutdB cutA,
    smul_add, ← derivative_normalOrder_left_sum A B m v P cutB_shift,
    ← derivative_normalOrder_right_sum A B m v Q]
  abel

/-- Formal differentiation is a derivation of every integer `n`-th product. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn, nthProduct_of_nonneg hn, nthProduct_of_nonneg hn,
      derivative_nonnegResidueProduct]
  · rw [nthProduct_of_neg hn, nthProduct_of_neg hn, nthProduct_of_neg hn,
      derivative_normalOrder, derivative_hasseDerivative_comm]

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
    ⁅T, (nonnegResidueProduct k A B)[[m]]⁆ =
      (derivative (nonnegResidueProduct k A B))[[m]] := by
  have hjac (X Y : Module.End R V) :
      T * (X * Y - Y * X) - (X * Y - Y * X) * T =
        (⁅T, X⁆ * Y + X * ⁅T, Y⁆) - (⁅T, Y⁆ * X + Y * ⁅T, X⁆) := by
    simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]
    abel
  rw [derivative_nonnegResidueProduct, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct, Ring.lie_def, mul_sum, sum_mul,
    ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, ← smul_sub, ← smul_sub,
    ← smul_add, ← smul_add]
  congr 2
  rw [hjac, hA, hB]
  abel

/-- Normal ordering preserves translation covariance. -/
theorem lie_ncoeff_normalOrder {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    ⁅T, (normalOrder A B)[[m]]⁆ = (derivative (normalOrder A B))[[m]] := by
  have hcomm (X Y dX dY : Module.End R V) (hX : ⁅T, X⁆ = dX) (hY : ⁅T, Y⁆ = dY) (v : V) :
      T (X (Y v)) - X (Y (T v)) = dX (Y v) + X (dY v) := by
    have h₁ := LinearMap.congr_fun hX (Y v)
    have h₂ := LinearMap.congr_fun hY v
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp] at h₁ h₂
    rw [← h₁, ← h₂, map_sub]
    abel
  ext v
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨P₃, hP₃⟩ := (derivative B).exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q₃, hQ₃⟩ := (derivative A).exists_forall_ncoeff_apply_eq_zero v
  let P := (max (max (P₁ : ℤ) P₂) P₃ - m).toNat
  let Q := max (max Q₁ Q₂) Q₃
  have cutBv (i : ℕ) (hi : P ≤ i) : (B[[m + i]]) v = 0 := hP₁ _ (by omega)
  have cutBTv (i : ℕ) (hi : P ≤ i) : (B[[m + i]]) (T v) = 0 := hP₂ _ (by omega)
  have cutdBv (i : ℕ) (hi : P ≤ i) : ((derivative B)[[m + i]]) v = 0 := hP₃ _ (by omega)
  have cutAv (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ₁ _ (by omega)
  have cutATv (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) (T v) = 0 := hQ₂ _ (by omega)
  have cutdAv (i : ℕ) (hi : Q ≤ i) : ((derivative A)[[(i : ℤ)]]) v = 0 := hQ₃ _ (by omega)
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    derivative_normalOrder, map_add, Pi.add_apply, LinearMap.add_apply,
    ncoeff_normalOrder, ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B m v cutBv cutAv,
    normalOrderCoeff_eq_sum A B m (T v) cutBTv cutATv,
    normalOrderCoeff_eq_sum (derivative A) B m v cutBv cutdAv,
    normalOrderCoeff_eq_sum A (derivative B) m v cutdBv cutAv,
    map_add, map_sum, map_sum]
  have hL :
      (∑ i ∈ range P, T ((A[[-(i : ℤ) - 1]]) ((B[[m + i]]) v))) -
        (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[m + i]]) (T v))) =
      (∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) +
        (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v)) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ hcomm _ _ _ _ (hA _) (hB _) v
  have hR :
      (∑ i ∈ range Q, T ((B[[m - i - 1]]) ((A[[(i : ℤ)]]) v))) -
        (∑ i ∈ range Q, (B[[m - i - 1]]) ((A[[(i : ℤ)]]) (T v))) =
      (∑ i ∈ range Q, ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v)) +
        (∑ i ∈ range Q, (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ hcomm _ _ _ _ (hB _) (hA _) v
  have rearrange (a b c d : V) : (a + b) - (c + d) = (a - c) + (b - d) := by abel
  rw [rearrange, hL, hR]
  abel

/-- Every integer `n`-th product preserves translation covariance. -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn]
    exact lie_ncoeff_nonnegResidueProduct hA hB n.toNat m
  · rw [nthProduct_of_neg hn]
    exact lie_ncoeff_normalOrder (lie_ncoeff_hasseDerivative hA _) hB m

/-! ### Vacuum evaluation of Hasse derivatives and `n`-th products -/

/-- If `vac` is annihilated by nonnegative modes of `A`, it is also annihilated by nonnegative
modes of every Hasse derivative of `A`. -/
theorem ncoeff_hasseDerivative_apply_of_nonneg {A : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (k : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    ((hasseDerivative k A)[[m]]) vac = 0 := by
  rw [ncoeff_hasseDerivative, LinearMap.smul_apply]
  rcases lt_or_ge m k with hlt | hge
  · lift m to ℕ using hm
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero,
      zero_smul]
  · rw [hA (m - k) (by omega), smul_zero]

/-- If `vac` is annihilated by nonnegative modes of `A` and `B`, it is annihilated by nonnegative
modes of `nthProduct n A B` for every `n : ℤ`. -/
theorem ncoeff_nthProduct_apply_of_nonneg {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0) (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ((nthProduct n A B)[[m]]) vac = 0 := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    refine sum_eq_zero fun ij _ ↦ ?_
    simp [hA ij.1 (Nat.cast_nonneg _), hB (m + ij.2) (by omega)]
  · rw [nthProduct_of_neg hn, ncoeff_normalOrder, normalOrderCoeff_apply]
    have hL : (∑ᶠ i : ℕ, ((hasseDerivative (-n - 1).toNat A)[[-(i : ℤ) - 1]])
        ((B[[m + i]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by simp [hB (m + i) (by omega)]
    have hR : (∑ᶠ i : ℕ, (B[[m - i - 1]])
        (((hasseDerivative (-n - 1).toNat A)[[(i : ℤ)]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDerivative_apply_of_nonneg hA (-n - 1).toNat (Nat.cast_nonneg i), map_zero]
    rw [hL, hR, add_zero]

/-- If `vac` is annihilated by nonnegative modes of `A` and `B`, then the `(-1)`-st mode of
`nthProduct n A B` on `vac` is `A₍ₙ₎ (B₍₋₁₎ vac)` for every `n : ℤ`. -/
theorem ncoeff_neg_one_nthProduct_apply {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0)
    (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0) (n : ℤ) :
    ((nthProduct n A B)[[-1]]) vac = (A[[n]]) ((B[[-1]]) vac) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    rw [nthProduct_natCast, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    rw [sum_eq_single (n, 0)]
    · simp [hA n (Nat.cast_nonneg _)]
    · intro ij hij hne
      have hj : ij.2 ≠ 0 := fun hj ↦
        hne (Prod.ext (by simpa [hj] using mem_antidiagonal.mp hij) hj)
      simp [hA ij.1 (Nat.cast_nonneg _), hB (-1 + ij.2) (by omega)]
    · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, ncoeff_normalOrder, normalOrderCoeff_apply]
    have hR : (∑ᶠ i : ℕ, (B[[-1 - i - 1]]) (((hasseDerivative k A)[[(i : ℤ)]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDerivative_apply_of_nonneg hA k (Nat.cast_nonneg i), map_zero]
    rw [hR, add_zero, finsum_eq_single _ 0]
    · rw [Nat.cast_zero, neg_zero, zero_sub, add_zero, ncoeff_neg_one_hasseDerivative]
    · intro i hi
      simp [hB (-1 + i) (by omega)]

/-- If `T vac = 0` and `B` is translation-covariant with respect to `T`, then
`T (B₍ₘ₎ vac) = -m B₍ₘ₋₁₎ vac` for every integer `m`. -/
theorem apply_ncoeff_apply_of_lie {T : Module.End R V} {vac : V} {B : VertexOperator R V}
    (hT : T vac = 0) (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    T ((B[[m]]) vac) = (-m) • (B[[m - 1]]) vac := by
  have h := LinearMap.congr_fun (hcov m) vac
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, hT, map_zero, sub_zero,
    ncoeff_derivative, LinearMap.smul_apply] using h

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
    have h₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    have h₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    rw [h₁, h₂, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- **Commutator formula for mutually local vertex operators.** If `A` and `B` are local of order
`N`, then `[A₍ₘ₎, B₍ₙ₎] = ∑_{j < N} (m choose j) (A_{(j)} B)₍ₘ₊ₙ₋ⱼ₎` over any commutative ring. -/
theorem IsLocalOfOrder.lie_ncoeff {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (m n : ℤ) :
    ⁅A[[m]], B[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (nonnegResidueProduct j A B)[[m + n - j]] := by
  have hexp := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm m) n
  simp only [commutatorDistribution_apply, Finset.sum_apply,
    FormalDistribution.deltaTerm_apply, FormalDistribution.residue_apply,
    FormalDistribution.mulSub_pow_apply, zero_add] at hexp
  rw [Ring.lie_def, hexp]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [ncoeff_nonnegResidueProduct]

/-- Over a `ℚ`-algebra, if `T vac = 0` and `B` is translation-covariant with respect to `T`,
then all nonnegative modes of `B` annihilate `vac`. -/
theorem ncoeff_apply_eq_zero_of_nonneg_of_lie [Algebra ℚ R] {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) {m : ℤ} (hm : 0 ≤ m) :
    (B[[m]]) vac = 0 := by
  lift m to ℕ using hm
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  suffices hstep : ∀ d k : ℕ, N - d ≤ k → (B[[(k : ℤ)]]) vac = 0 from
    hstep N m (by omega)
  intro d
  induction d with
  | zero =>
    intro k hk
    exact hN k (by exact_mod_cast hk)
  | succ d ih =>
    intro k hk
    have hrec := apply_ncoeff_apply_of_lie hT hcov ((k + 1 : ℕ) : ℤ)
    rw [ih (k + 1) (by omega), map_zero, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega,
      neg_smul, eq_comm, neg_eq_zero, natCast_zsmul] at hrec
    have hne : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    rw [← Nat.cast_smul_eq_nsmul R, ← map_natCast (algebraMap ℚ R)] at hrec
    have hinv := congrArg (algebraMap ℚ R ((k + 1 : ℕ) : ℚ)⁻¹ • ·) hrec
    simpa only [smul_zero, smul_smul, ← map_mul, inv_mul_cancel₀ hne,
      map_one, one_smul] using hinv

/-- Over a `ℚ`-algebra, if `T vac = 0` and `B` is translation-covariant with respect to `T`,
then `B₍₋ₖ₋₁₎ vac = (k!)⁻¹ • Tᵏ (B₍₋₁₎ vac)`. -/
theorem ncoeff_neg_succ_apply_of_lie [Algebra ℚ R] {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    (B[[-(k : ℤ) - 1]]) vac = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (T ^ k) ((B[[-1]]) vac) := by
  rw [← factorial_smul_ncoeff_neg_succ_apply_of_lie hT hcov k, ← Nat.cast_smul_eq_nsmul R,
    ← map_natCast (algebraMap ℚ R), smul_smul, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast k.factorial_ne_zero), map_one, one_smul]

end VertexOperator
