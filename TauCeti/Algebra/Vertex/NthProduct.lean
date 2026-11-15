/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import TauCeti.Algebra.Vertex.NormalOrder
public import TauCeti.Algebra.Vertex.ResidueProduct
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Algebra.Vertex.FormalDistribution
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Module

/-!
# Hasse derivatives and `n`-th products of fields

For fields `A(z)` and `B(w)` on an `R`-module `V` (`VertexOperator R V`), the operator product
expansion attaches an `n`-th product field `(A₍ₙ₎ B)(w)` to every integer `n : ℤ`:

* for `n ≥ 0`, `(A₍ₙ₎ B)(w) = Res_z (z - w)ⁿ [A(z), B(w)]` (`VertexOperator.nonnegResidueProduct`);
* for `n = -k - 1 < 0`, `(A₍₋ₖ₋₁₎ B)(w) = :(∂_w^{(k)} A(w)) B(w):`, formed using the `k`-th Hasse
  (divided-power) derivative `∂_w^{(k)}` (`VertexOperator.hasseDeriv`) and normal ordering
  (`VertexOperator.normalOrder`).

Using `LaurentSeries.hasseDeriv`, both cases are defined over an arbitrary commutative ring `R`,
with no characteristic-zero or division hypothesis. In normalized modes they satisfy a single
binomial expansion for all `n, r : ℤ`:

`((A₍ₙ₎ B)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) A₍ₙ₋ᵢ₎ (B₍ᵣ₊ᵢ₎ c) -
  ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (-1)ⁿ B₍ₙ₊ᵣ₋ᵢ₎ (A₍ᵢ₎ c)`

(`VertexOperator.ncoeff_nthProduct_apply`), which is the `m = 0` specialization of the Borcherds
identity without assuming locality. We also define the identity field `VertexOperator.identity`,
prove that Hasse differentiation preserves mutual locality (increasing the order bound by `k`), and
establish the Leibniz rules `(∂A)₍ₙ₎ B = -n (A₍ₙ₋₁₎ B)`,
`∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)` and translation covariance of `A₍ₙ₎ B`.

## Main definitions

* `VertexOperator.identity`: the identity field `id_V z⁰`, with modes `δ_{n,-1}`.
* `VertexOperator.hasseDeriv`: the `k`-th divided-power derivative `∂^{(k)}` of a field.
* `VertexOperator.nthProduct`: the bilinear `n`-th product `(A, B) ↦ A₍ₙ₎ B` for all `n : ℤ`.

## Main results

* `VertexOperator.IsLocalOfOrder.hasseDeriv_left`: `∂^{(k)} A` is local to `B` of order `N + k`.
* `VertexOperator.nthProduct_derivative_left`: `(∂A)₍ₙ₎ B = -n • A₍ₙ₋₁₎ B`.
* `VertexOperator.derivative_nthProduct`: `∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`.
* `VertexOperator.ncoeff_nthProduct_apply`: the unified binomial mode formula for `(A₍ₙ₎ B)₍ᵣ₎`.
* `VertexOperator.lie_ncoeff_nthProduct`: translation covariance passes to all `n`-th products.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.3 and §3.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §2.
* G. Mason, *Vertex rings and Pierce bundles*, Contemp. Math. 695 (2017), 45–55.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4 and §3.1.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### The identity field -/

private theorem bddBelow_support_identity (x : V) :
    BddBelow (Function.support fun k : ℤ ↦ (if k = 0 then (1 : Module.End R V) else 0) x) :=
  ⟨0, fun k hk ↦ not_lt.1 fun h ↦ hk (by simp [h.ne])⟩

/-- The identity field `id_V z⁰`, whose only nonzero coefficient is `1` in degree `0`
(normalized mode `-1`). -/
def identity : VertexOperator R V :=
  of_coeff (fun k ↦ if k = 0 then 1 else 0) bddBelow_support_identity

/-- The normalized modes of the identity field are `δ_{n, -1}`. -/
@[simp]
theorem ncoeff_identity (n : ℤ) :
    (identity : VertexOperator R V)[[n]] = if n = -1 then 1 else 0 := by
  rw [identity, ncoeff_of_coeff]
  split_ifs <;> first | rfl | omega

/-- The unnormalized Laurent coefficients of the identity field are `δ_{k, 0}`. -/
theorem coeff_identity (k : ℤ) :
    HVertexOperator.coeff (identity : VertexOperator R V) k = if k = 0 then 1 else 0 := by
  rw [coeff_eq_ncoeff, ncoeff_identity]
  split_ifs <;> first | rfl | omega

/-- The formal derivative of the identity field is zero. -/
@[simp]
theorem derivative_identity : derivative (identity : VertexOperator R V) = 0 := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_derivative, ncoeff_identity, map_zero, Pi.zero_apply]
  split_ifs with h
  · have hn : n = 0 := by omega
    simp [hn]
  · simp

/-- The identity field is mutually local of every order with any field on the right. -/
theorem isLocalOfOrder_identity_left (B : VertexOperator R V) (N : ℕ) :
    (identity : VertexOperator R V).IsLocalOfOrder B N := by
  refine isLocalOfOrder_iff.2 fun m n ↦ sum_eq_zero fun ij _ ↦ ?_
  rw [ncoeff_identity]
  split_ifs <;> simp

/-- Any field is mutually local of every order with the identity field on the right. -/
theorem isLocalOfOrder_identity_right (A : VertexOperator R V) (N : ℕ) :
    A.IsLocalOfOrder (identity : VertexOperator R V) N :=
  (isLocalOfOrder_identity_left A N).symm

/-- Normal ordering with `identity` on the left is the identity on fields. -/
@[simp]
theorem normalOrder_identity_left (B : VertexOperator R V) : normalOrder identity B = B := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ ?_
  rw [ncoeff_normalOrder, normalOrderCoeff_apply]
  have h₂ : (∑ᶠ i : ℕ, (B[[n - i - 1]]) (((identity : VertexOperator R V)[[(i : ℤ)]]) v)) = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun i ↦ by simp [show (i : ℤ) ≠ -1 by omega]
  rw [h₂, add_zero, finsum_eq_single _ 0]
  · simp
  · intro i hi
    simp [show -(i : ℤ) - 1 ≠ -1 by omega]

/-- Normal ordering with `identity` on the right is the identity on fields. -/
@[simp]
theorem normalOrder_identity_right (A : VertexOperator R V) : normalOrder A identity = A := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ ?_
  rw [ncoeff_normalOrder, normalOrderCoeff_apply]
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have h₂ : (∑ᶠ i : ℕ, ((identity : VertexOperator R V)[[-(k : ℤ) - 1 - i - 1]])
        ((A[[(i : ℤ)]]) v)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        simp [show -(k : ℤ) - 1 - i - 1 ≠ -1 by omega]
    rw [h₂, add_zero, finsum_eq_single _ k]
    · simp [show -(k : ℤ) - 1 + k = -1 by omega]
    · intro i hi
      simp [show -(k : ℤ) - 1 + i ≠ -1 by omega]
  · lift n to ℕ using hn
    have h₁ : (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) (((identity : VertexOperator R V)[[n + i]]) v)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by simp [show (n : ℤ) + i ≠ -1 by omega]
    rw [h₁, zero_add, finsum_eq_single _ n]
    · simp
    · intro i hi
      simp [show (n : ℤ) - i - 1 ≠ -1 by omega]

/-- All nonnegative residue products with `identity` on the left vanish. -/
@[simp]
theorem nonnegResidueProduct_identity_left (n : ℕ) (B : VertexOperator R V) :
    nonnegResidueProduct n identity B = 0 := by
  refine ext_ncoeff fun m ↦ ?_
  rw [ncoeff_nonnegResidueProduct, map_zero, Pi.zero_apply]
  exact sum_eq_zero fun ij _ ↦ by simp [show (ij.1 : ℤ) ≠ -1 by omega]

/-- All nonnegative residue products with `identity` on the right vanish. -/
@[simp]
theorem nonnegResidueProduct_identity_right (n : ℕ) (A : VertexOperator R V) :
    nonnegResidueProduct n A identity = 0 := by
  refine ext_ncoeff fun m ↦ ?_
  rw [ncoeff_nonnegResidueProduct, map_zero, Pi.zero_apply]
  refine sum_eq_zero fun ij _ ↦ ?_
  rw [ncoeff_identity]
  split_ifs <;> simp

/-! ### Hasse (divided-power) derivatives of fields -/

/-- The `k`-th divided-power (Hasse) derivative `∂^{(k)}` of a field, defined coefficientwise via
`LaurentSeries.hasseDeriv`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R
    ((HahnModule.ofLinearEquiv R).toLinearMap ∘ₗ LaurentSeries.hasseDeriv R k ∘ₗ
      (HahnModule.ofLinearEquiv R).symm.toLinearMap)

/-- The unnormalized Laurent coefficients of `∂^{(k)} A`. -/
theorem coeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (hasseDeriv k A) n =
      Ring.choose (n + k) k • HVertexOperator.coeff A (n + k) := by
  ext v
  rw [HVertexOperator.coeff_apply_apply, LinearMap.smul_apply, HVertexOperator.coeff_apply_apply]
  simp [hasseDeriv]

/-- The normalized modes of `∂^{(k)} A` are `(∂^{(k)} A)₍ₙ₎ = (-1)ᵏ (n choose k) A₍ₙ₋ₖ₎`. -/
@[simp]
theorem ncoeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDeriv k A)[[n]] = ((-1 : ℤ) ^ k * Ring.choose n k) • A[[n - k]] := by
  rw [ncoeff_apply, coeff_hasseDeriv, coeff_eq_ncoeff]
  have h₁ : -n - 1 + (k : ℤ) = -(n + 1 - k) := by omega
  have h₂ : n + 1 - (k : ℤ) + k - 1 = n := by omega
  have h₃ : -(-n - 1 + (k : ℤ)) - 1 = n - k := by omega
  rw [h₃, h₁, Ring.choose_neg, h₂, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul]

/-- The `(-1)`-st mode of `∂^{(k)} A` recovers `A₍₋ₖ₋₁₎`. -/
theorem ncoeff_neg_one_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    (hasseDeriv k A)[[-1]] = A[[-k - 1]] := by
  rw [ncoeff_apply, coeff_hasseDeriv, show -(-1 : ℤ) - 1 + k = k by omega,
    Ring.choose_natCast, Nat.choose_self, Nat.cast_one, one_smul, coeff_eq_ncoeff]

/-- The `0`-th Hasse derivative is the identity linear map on fields. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv (R := R) (V := V) 0 = LinearMap.id := by
  ext A : 1
  exact ext_ncoeff fun n ↦ by simp

/-- Applying `hasseDeriv 0` leaves a field unchanged. -/
theorem hasseDeriv_zero_apply (A : VertexOperator R V) : hasseDeriv 0 A = A := by
  simp

/-- The `1`-st Hasse derivative equals `VertexOperator.derivative`. -/
theorem hasseDeriv_one :
    hasseDeriv (R := R) (V := V) 1 = derivative := by
  ext A : 1
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_hasseDeriv, ncoeff_derivative, pow_one, Ring.choose_one_right, Nat.cast_one]
  congr 1
  ring

/-- Applying `hasseDeriv 1` equals `derivative A`. -/
theorem hasseDeriv_one_apply (A : VertexOperator R V) : hasseDeriv 1 A = derivative A := by
  rw [← hasseDeriv_one]

/-- Positive Hasse derivatives of the identity field vanish. -/
@[simp]
theorem hasseDeriv_succ_identity (k : ℕ) :
    hasseDeriv (k + 1) (identity : VertexOperator R V) = 0 := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_hasseDeriv, ncoeff_identity, map_zero, Pi.zero_apply]
  split_ifs with h
  · have hn : n = k := by omega
    rw [hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k),
      Nat.cast_zero, mul_zero, zero_smul]
  · simp

/-- Composition law `∂^{(k)} (∂^{(l)} A) = ((k + l) choose k) ∂^{(k + l)} A`. -/
theorem hasseDeriv_hasseDeriv (k l : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (hasseDeriv l A) = (k + l).choose k • hasseDeriv (k + l) A := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_hasseDeriv, ncoeff_hasseDeriv, map_nsmul, Pi.smul_apply, ncoeff_hasseDeriv,
    smul_smul, ← natCast_zsmul, smul_smul, show n - (k : ℤ) - l = n - ↑(k + l) by omega]
  have hc : Ring.choose n k * Ring.choose (n - k) l =
      ((k + l).choose k : ℤ) * Ring.choose n (k + l) := by
    have h := Ring.choose_smul_choose n (Nat.le_add_right k l)
    rw [Nat.add_sub_cancel_left, nsmul_eq_mul] at h
    exact h.symm
  congr 1
  calc ((-1 : ℤ) ^ k * Ring.choose n k) * ((-1 : ℤ) ^ l * Ring.choose (n - k) l)
      = (-1 : ℤ) ^ (k + l) * (Ring.choose n k * Ring.choose (n - k) l) := by rw [pow_add]; ring
    _ = ↑((k + l).choose k) * ((-1 : ℤ) ^ (k + l) * Ring.choose n (k + l)) := by rw [hc]; ring

/-- Ordinary differentiation commutes with Hasse differentiation. -/
theorem derivative_hasseDeriv_comm (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDeriv k A) = hasseDeriv k (derivative A) := by
  rw [← hasseDeriv_one_apply, ← hasseDeriv_one_apply, hasseDeriv_hasseDeriv,
    hasseDeriv_hasseDeriv, Nat.add_comm 1 k, Nat.choose_one_right, Nat.choose_symm_add,
    Nat.choose_one_right]

/-- The `k`-th iterate of `derivative` is `k!` times `hasseDeriv k`. -/
theorem iterate_derivative_eq_factorial_smul_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    (derivative (R := R) (V := V))^[k] A = k.factorial • hasseDeriv k A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, ← hasseDeriv_one_apply,
      hasseDeriv_hasseDeriv, Nat.add_comm 1 k, Nat.choose_one_right, smul_smul, mul_comm,
      ← Nat.factorial_succ]

namespace IsLocalOfOrder

open TauCeti

/-- Taking the `k`-th Hasse derivative of the first field increases a locality bound by `k`, over
any commutative ring. -/
theorem hasseDeriv_left {A B : VertexOperator R V} {N : ℕ} (h : A.IsLocalOfOrder B N) (k : ℕ) :
    (hasseDeriv k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  let D : ℕ → ℤ → Module.End R V := fun j ↦
    FormalDistribution.residue ((FormalDistribution.mulSub ^ j) (A.commutatorDistribution B))
  have hexp : (hasseDeriv k A).commutatorDistribution B =
      ∑ j ∈ range N, FormalDistribution.deltaTerm (k + j)
        (fun s ↦ ((-1 : ℤ) ^ k * (k + j).choose k) • D j s) := by
    ext m n : 2
    have hm := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm (m - k)) n
    have hcomm : ((hasseDeriv k A).commutatorDistribution B) m n =
        ((-1 : ℤ) ^ k * Ring.choose m k) • (A.commutatorDistribution B (m - k) n) := by
      simp only [commutatorDistribution_apply, ncoeff_hasseDeriv, smul_mul_assoc, mul_smul_comm,
        smul_sub]
    rw [hcomm, hm, Finset.sum_apply, Finset.sum_apply, Finset.smul_sum, Finset.sum_apply,
      Finset.sum_apply]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [FormalDistribution.deltaTerm_apply]
    have hidx : m - (k : ℤ) + n - j = m + n - ↑(k + j) := by omega
    have hchoose : Ring.choose m k * Ring.choose (m - k) j =
        ((k + j).choose k : ℤ) * Ring.choose m (k + j) := by
      have hc := Ring.choose_smul_choose m (Nat.le_add_right k j)
      rw [Nat.add_sub_cancel_left, nsmul_eq_mul] at hc
      exact hc.symm
    rw [hidx, smul_smul, mul_assoc ((-1 : ℤ) ^ k), hchoose, smul_smul]
    congr 1
    ring
  rw [hexp, map_sum]
  exact sum_eq_zero fun j hj ↦
    FormalDistribution.mulSub_pow_deltaTerm_eq_zero (by have := mem_range.1 hj; omega) _

/-- Taking the `k`-th Hasse derivative of the second field increases a locality bound by `k`. -/
theorem hasseDeriv_right {A B : VertexOperator R V} {N : ℕ} (h : A.IsLocalOfOrder B N) (k : ℕ) :
    A.IsLocalOfOrder (hasseDeriv k B) (N + k) :=
  (h.symm.hasseDeriv_left k).symm

/-- Hasse derivatives of orders `k` and `l` of local fields are local of order `N + k + l`. -/
theorem hasseDeriv {A B : VertexOperator R V} {N : ℕ} (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    (VertexOperator.hasseDeriv k A).IsLocalOfOrder
      (VertexOperator.hasseDeriv l B) (N + k + l) :=
  (h.hasseDeriv_left k).hasseDeriv_right l

end IsLocalOfOrder

/-! ### Derivatives of normal-ordered and residue products -/

private theorem sum_derivative_normalOrder_left (A B : VertexOperator R V) (r : ℤ) (v : V) (M : ℕ)
    (hBM : ∀ i : ℕ, M ≤ i → (B[[r - 1 + i]]) v = 0) :
    (∑ i ∈ range M, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[r + i]]) v)) +
      (∑ j ∈ range M, (A[[-(j : ℤ) - 1]]) (((derivative B)[[r + j]]) v)) =
    (-r) • ∑ j ∈ range M, (A[[-(j : ℤ) - 1]]) ((B[[r - 1 + j]]) v) := by
  have hL₀ : ∑ j ∈ range M, (A[[-(j : ℤ) - 1]]) ((B[[r - 1 + j]]) v) =
      ∑ j ∈ range (M + 1), (A[[-(j : ℤ) - 1]]) ((B[[r - 1 + j]]) v) := by
    rw [sum_range_succ, hBM M le_rfl, map_zero, add_zero]
  have hL₁ : ∑ i ∈ range M, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[r + i]]) v) =
      ∑ j ∈ range (M + 1), (j : ℤ) • (A[[-(j : ℤ) - 1]]) ((B[[r - 1 + j]]) v) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_smul, add_zero]
    refine sum_congr rfl fun i _ ↦ ?_
    have h₁ : -(-(i : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    have h₂ : -(i : ℤ) - 1 - 1 = -((i + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    have h₃ : r - 1 + ((i + 1 : ℕ) : ℤ) = r + i := by push_cast; ring
    rw [ncoeff_derivative, LinearMap.smul_apply, h₁, h₂, h₃]
  have hL₂ : ∑ j ∈ range M, (A[[-(j : ℤ) - 1]]) (((derivative B)[[r + j]]) v) =
      ∑ j ∈ range (M + 1), (-(r + j)) • (A[[-(j : ℤ) - 1]]) ((B[[r - 1 + j]]) v) := by
    rw [sum_range_succ, hBM M le_rfl, map_zero, smul_zero, add_zero]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [ncoeff_derivative, LinearMap.smul_apply, map_zsmul,
      show r + (j : ℤ) - 1 = r - 1 + j by omega]
  rw [hL₀, hL₁, hL₂, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← add_zsmul]
  exact congrArg (· • _) (by ring)

private theorem sum_derivative_normalOrder_right (A B : VertexOperator R V) (r : ℤ) (v : V)
    (M : ℕ) :
    (∑ i ∈ range (M + 1), (B[[r - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) +
      (∑ j ∈ range M, ((derivative B)[[r - j - 1]]) ((A[[(j : ℤ)]]) v)) =
    (-r) • ∑ j ∈ range M, (B[[r - 1 - j - 1]]) ((A[[(j : ℤ)]]) v) := by
  have hR₁ : ∑ i ∈ range (M + 1), (B[[r - i - 1]]) (((derivative A)[[(i : ℤ)]]) v) =
      ∑ j ∈ range M, (-(j + 1 : ℤ)) • (B[[r - 1 - j - 1]]) ((A[[(j : ℤ)]]) v) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, ncoeff_derivative, neg_zero, zero_smul, LinearMap.zero_apply,
      map_zero, add_zero]
    refine sum_congr rfl fun j _ ↦ ?_
    have h₁ : ((j + 1 : ℕ) : ℤ) - 1 = j := by push_cast; ring
    have h₂ : r - ((j + 1 : ℕ) : ℤ) - 1 = r - 1 - j - 1 := by push_cast; ring
    rw [h₁, h₂, LinearMap.smul_apply, map_zsmul]
    exact congrArg (· • _) (by push_cast; ring)
  have hR₂ : ∑ j ∈ range M, ((derivative B)[[r - j - 1]]) ((A[[(j : ℤ)]]) v) =
      ∑ j ∈ range M, (-(r - j - 1)) • (B[[r - 1 - j - 1]]) ((A[[(j : ℤ)]]) v) := by
    refine sum_congr rfl fun j _ ↦ ?_
    rw [ncoeff_derivative, LinearMap.smul_apply,
      show r - (j : ℤ) - 1 - 1 = r - 1 - j - 1 by omega]
  rw [hR₁, hR₂, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← add_zsmul]
  exact congrArg (· • _) (by ring)

/-- **Leibniz rule for normal ordering**: `∂(:AB:) = :(∂A)B: + :A(∂B):`. -/
theorem derivative_normalOrder (A B : VertexOperator R V) :
    derivative (normalOrder A B) =
      normalOrder (derivative A) B + normalOrder A (derivative B) := by
  refine ext_ncoeff fun r ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M : ℕ := max (P + r.natAbs + 2) (Q + 2)
  have hBM (i : ℕ) (hi : M ≤ i) : (B[[r - 1 + i]]) v = 0 := hP _ (by omega)
  have hBM' (i : ℕ) (hi : M ≤ i) : (B[[r + i]]) v = 0 := hP _ (by omega)
  have hBderM (i : ℕ) (hi : M ≤ i) : ((derivative B)[[r + i]]) v = 0 := by
    rw [ncoeff_derivative, LinearMap.smul_apply,
      show r + (i : ℤ) - 1 = r - 1 + i by omega, hBM i hi, smul_zero]
  have hAM (i : ℕ) (hi : M ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ _ (by omega)
  have hAderM (i : ℕ) (hi : M + 1 ≤ i) : ((derivative A)[[(i : ℤ)]]) v = 0 := by
    rw [ncoeff_derivative, LinearMap.smul_apply, hQ _ (by omega), smul_zero]
  rw [ncoeff_derivative, LinearMap.smul_apply, map_add, Pi.add_apply, LinearMap.add_apply,
    ncoeff_normalOrder, ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B (r - 1) v hBM hAM,
    normalOrderCoeff_eq_sum (derivative A) B r v hBM' hAderM,
    normalOrderCoeff_eq_sum A (derivative B) r v hBderM hAM, smul_add,
    ← sum_derivative_normalOrder_left A B r v M hBM,
    ← sum_derivative_normalOrder_right A B r v M]
  abel

/-- The `0`-th residue product with a derivative on the left vanishes: `(∂A)₍₀₎ B = 0`. -/
@[simp]
theorem nonnegResidueProduct_zero_derivative_left (A B : VertexOperator R V) :
    nonnegResidueProduct 0 (derivative A) B = 0 := by
  refine ext_ncoeff fun m ↦ ?_
  simp

/-- Differentiating the first factor of a nonnegative residue product shifts the index down:
`((∂A)₍ₖ₊₁₎ B) = -(k + 1) (A₍ₖ₎ B)`. -/
theorem nonnegResidueProduct_succ_derivative_left (k : ℕ) (A B : VertexOperator R V) :
    nonnegResidueProduct (k + 1) (derivative A) B =
      -((k + 1 : ℕ) : ℤ) • nonnegResidueProduct k A B := by
  refine ext_ncoeff fun m ↦ ?_
  rw [ncoeff_nonnegResidueProduct, map_zsmul, Pi.smul_apply, neg_zsmul, natCast_zsmul,
    ncoeff_nonnegResidueProduct]
  have e : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
          B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
      -((k + 1).choose ij.1 • ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ) - 1]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ) - 1]])) := by
    intro ij _
    rw [ncoeff_derivative]
    simp only [smul_mul_assoc, mul_smul_comm, ← natCast_zsmul]
    module
  rw [sum_congr rfl e, sum_neg_distrib,
    sum_antidiagonal_choose_succ_nsmul_nsmul
      (fun i j ↦ (-1 : ℤ) ^ j • (A[[(i : ℤ) - 1]] * B[[m + j]] - B[[m + j]] * A[[(i : ℤ) - 1]])) k]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

private theorem sum_antidiagonal_choose_succ_commutator_shift (k : ℕ) (m : ℤ)
    (A B : VertexOperator R V) :
    ∑ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • ij.2 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2 - 1]] - B[[m + ij.2 - 1]] * A[[(ij.1 : ℤ)]]) =
      -((k + 1) • ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
  rw [← Nat.sum_antidiagonal_swap]
  have eswap : ∀ ij ∈ antidiagonal (k + 1),
      (k + 1).choose ij.swap.1 • ij.swap.2 • (-1 : ℤ) ^ ij.swap.2 •
        (A[[(ij.swap.1 : ℤ)]] * B[[m + ij.swap.2 - 1]] -
          B[[m + ij.swap.2 - 1]] * A[[(ij.swap.1 : ℤ)]]) =
      (k + 1).choose ij.1 • ij.1 • (-1 : ℤ) ^ ij.1 •
        (A[[(ij.2 : ℤ)]] * B[[m + ij.1 - 1]] - B[[m + ij.1 - 1]] * A[[(ij.2 : ℤ)]]) := by
    intro ij hij
    rw [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]
  rw [sum_congr rfl eswap,
    sum_antidiagonal_choose_succ_nsmul_nsmul
      (fun i j ↦ (-1 : ℤ) ^ i •
        (A[[(j : ℤ)]] * B[[m + i - 1]] - B[[m + i - 1]] * A[[(j : ℤ)]])) k,
    ← Nat.sum_antidiagonal_swap]
  have ef : ∀ ij ∈ antidiagonal k,
      k.choose ij.swap.1 • (-1 : ℤ) ^ (ij.swap.1 + 1) •
        (A[[(ij.swap.2 : ℤ)]] * B[[m + ↑(ij.swap.1 + 1) - 1]] -
          B[[m + ↑(ij.swap.1 + 1) - 1]] * A[[(ij.swap.2 : ℤ)]]) =
      -(k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
    intro ij hij
    rw [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm,
      pow_succ, show m + ((ij.2 + 1 : ℕ) : ℤ) - 1 = m + ij.2 by omega]
    simp only [← natCast_zsmul]
    module
  rw [sum_congr rfl ef, sum_neg_distrib, smul_neg]

/-- **Leibniz rule for nonnegative residue products**:
`∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`. -/
theorem derivative_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V) :
    derivative (nonnegResidueProduct n A B) =
      nonnegResidueProduct n (derivative A) B + nonnegResidueProduct n A (derivative B) := by
  refine ext_ncoeff fun m ↦ ?_
  rw [ncoeff_derivative, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct]
  cases n with
  | zero =>
    simp only [Nat.antidiagonal_zero, sum_singleton, Nat.choose_zero_right, pow_zero, one_smul,
      Nat.cast_zero, add_zero, ncoeff_derivative, neg_zero, zero_smul,
      sub_self, zero_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  | succ k =>
    have e₂ : ∀ ij ∈ antidiagonal (k + 1),
        (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * (derivative B)[[m + ij.2]] -
            (derivative B)[[m + ij.2]] * A[[(ij.1 : ℤ)]]) =
        (-m) • ((k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m - 1 + ij.2]] - B[[m - 1 + ij.2]] * A[[(ij.1 : ℤ)]])) -
        (k + 1).choose ij.1 • ij.2 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m + ij.2 - 1]] - B[[m + ij.2 - 1]] * A[[(ij.1 : ℤ)]]) := by
      intro ij _
      rw [ncoeff_derivative, show m + (ij.2 : ℤ) - 1 = m - 1 + ij.2 by omega]
      simp only [smul_mul_assoc, mul_smul_comm]
      module
    rw [sum_congr rfl e₂, sum_sub_distrib, ← smul_sum]
    have h₁ : ∑ ij ∈ antidiagonal (k + 1), (k + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
          B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
        -((k + 1) • ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]])) := by
      have h : (nonnegResidueProduct (k + 1) (derivative A) B)[[m]] =
          (-((k + 1 : ℕ) : ℤ) • nonnegResidueProduct k A B)[[m]] := by
        rw [nonnegResidueProduct_succ_derivative_left]
      rwa [ncoeff_nonnegResidueProduct, map_zsmul, Pi.smul_apply, neg_zsmul, natCast_zsmul,
        ncoeff_nonnegResidueProduct] at h
    rw [h₁, sum_antidiagonal_choose_succ_commutator_shift]
    abel

/-! ### The `n`-th product of fields (`n : ℤ`) -/

/-- The bilinear `n`-th product `(A, B) ↦ A₍ₙ₎ B` of fields for any integer `n : ℤ`:
for `n ≥ 0` it is the residue commutator product `nonnegResidueProduct n.toNat`, and for
`n = -k - 1 < 0` it is the normal-ordered product `:(∂^{(k)} A) B:`. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V :=
  if 0 ≤ n then nonnegResidueProduct n.toNat
  else normalOrderₗ.comp (hasseDeriv (-n - 1).toNat)

/-- For `0 ≤ n`, `nthProduct n` agrees with `nonnegResidueProduct n.toNat`. -/
theorem nthProduct_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    nthProduct (R := R) (V := V) n = nonnegResidueProduct n.toNat := by
  simp [nthProduct, hn]

/-- On a natural number `n : ℕ`, `nthProduct (n : ℤ)` is `nonnegResidueProduct n`. -/
@[simp]
theorem nthProduct_natCast (n : ℕ) :
    nthProduct (R := R) (V := V) (n : ℤ) = nonnegResidueProduct n := by
  simp [nthProduct]

/-- The `0`-th product `nthProduct 0` is `nonnegResidueProduct 0`. -/
@[simp]
theorem nthProduct_zero :
    nthProduct (R := R) (V := V) 0 = nonnegResidueProduct 0 := by
  simp [nthProduct]

/-- For `n < 0`, `nthProduct n A B` is the normal-ordered product `:∂^{(-n-1)} A · B:`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B = normalOrder (hasseDeriv (-n - 1).toNat A) B := by
  simp [nthProduct, hn.not_ge]

/-- The `(-1)`-st product `A₍₋₁₎ B` is the normal-ordered product `:AB:`. -/
@[simp]
theorem nthProduct_neg_one (A B : VertexOperator R V) :
    nthProduct (-1) A B = normalOrder A B := by
  simp [nthProduct]

/-- The `(-k - 1)`-st product `A₍₋ₖ₋₁₎ B` is `:(∂^{(k)} A) B:`. -/
theorem nthProduct_neg_succ (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDeriv k A) B := by
  rw [nthProduct_of_neg (by omega)]
  have hk : (-(-(k : ℤ) - 1) - 1).toNat = k := by omega
  rw [hk]

/-- Left unit law for `nthProduct`: `1₍ₙ₎ B` equals `B` at `n = -1` and `0` otherwise. -/
@[simp]
theorem nthProduct_identity_left (n : ℤ) (B : VertexOperator R V) :
    nthProduct n identity B = if n = -1 then B else 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [nthProduct_of_neg hn]
    rcases eq_or_ne n (-1) with rfl | hne
    · simp
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, (-n - 1).toNat = k + 1 := ⟨(-n - 1).toNat - 1, by omega⟩
      simp [hk, hne]
  · rw [nthProduct_of_nonneg hn, nonnegResidueProduct_identity_left]
    simp [show n ≠ -1 by omega]

/-- Right evaluation on `identity` at negative indices: `A₍₋ₖ₋₁₎ 1 = ∂^{(k)} A`. -/
@[simp]
theorem nthProduct_neg_succ_identity_right (k : ℕ) (A : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A identity = hasseDeriv k A := by
  rw [nthProduct_neg_succ, normalOrder_identity_right]

/-- Locality of order `N` annihilates all `n`-th products with `N ≤ n`. -/
theorem IsLocalOfOrder.nthProduct_eq_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {n : ℤ} (hn : (N : ℤ) ≤ n) :
    nthProduct n A B = 0 := by
  have hn₀ : 0 ≤ n := by omega
  rw [nthProduct_of_nonneg hn₀]
  exact h.nonnegResidueProduct_eq_zero (by omega)

/-- Differentiating the first field in an `n`-th product satisfies `(∂A)₍ₙ₎ B = -n • A₍ₙ₋₁₎ B`
for every `n : ℤ`. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have h₁ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    have h₂ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [nthProduct_neg_succ, h₁, nthProduct_neg_succ, h₂, natCast_zsmul, ← hasseDeriv_one_apply,
      hasseDeriv_hasseDeriv, Nat.choose_symm_add, Nat.choose_one_right, ← normalOrderₗ_apply,
      map_nsmul, LinearMap.smul_apply, normalOrderₗ_apply]
  · lift n to ℕ using hn
    cases n with
    | zero => simp
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [nthProduct_natCast, hk, nthProduct_natCast]
      exact nonnegResidueProduct_succ_derivative_left k A B

/-- **Leibniz rule for `n`-th products**: `∂(A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)` for every `n : ℤ`. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, nthProduct_neg_succ, nthProduct_neg_succ, derivative_normalOrder,
      derivative_hasseDeriv_comm]
  · lift n to ℕ using hn
    simp only [nthProduct_natCast]
    exact derivative_nonnegResidueProduct n A B

/-! ### Unified mode expansion of `nthProduct` -/

/-- Support cutoff for the left sum in a Borcherds / `nthProduct` right-hand side. -/
theorem support_nthProduct_left_subset (A B : VertexOperator R V) (m n r : ℤ) (c : V)
    {P : ℕ} (hP : ∀ i : ℕ, P ≤ i → (B[[r + i]]) c = 0) :
    (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + i]]) c)) ⊆ range P := by
  intro i hi
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (by simp [hP i h])

/-- Support cutoff for the right sum in a Borcherds / `nthProduct` right-hand side. -/
theorem support_nthProduct_right_subset (A B : VertexOperator R V) (m n r : ℤ) (c : V)
    {Q : ℕ} (hQ : ∀ i : ℕ, Q ≤ i → (A[[m + i]]) c = 0) :
    (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
        (B[[n + r - i]]) ((A[[m + i]]) c)) ⊆ range Q := by
  intro i hi
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (by simp [hQ i h])

/-- Reindexing the rank-`n` binomial commutator sum on `antidiagonal n` into the difference of
two `finsum`s of Borcherds shape. -/
theorem sum_antidiagonal_commutator_eq_sub_finsum (n : ℕ) (m r : ℤ)
    (A B : VertexOperator R V) (c : V) :
    ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((A[[m + ij.1]]) ((B[[r + ij.2]]) c) - (B[[r + ij.2]]) ((A[[m + ij.1]]) c)) =
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (n : ℤ) i) •
          (A[[m + (n : ℤ) - i]]) ((B[[r + i]]) c)) -
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (n : ℤ) i * ((n : ℤ).negOnePow : ℤ)) •
          (B[[(n : ℤ) + r - i]]) ((A[[m + i]]) c) := by
  have hsub₁ : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose (n : ℤ) i) • (A[[m + (n : ℤ) - i]]) ((B[[r + i]]) c)) ⊆
      range (n + 1) := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    apply hi
    dsimp only
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero,
      mul_zero, zero_smul]
  have hsub₂ : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose (n : ℤ) i * ((n : ℤ).negOnePow : ℤ)) •
        (B[[(n : ℤ) + r - i]]) ((A[[m + i]]) c)) ⊆ range (n + 1) := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    apply hi
    dsimp only
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero,
      mul_zero, zero_mul, zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hsub₁, finsum_eq_sum_of_support_subset _ hsub₂]
  simp only [smul_sub, sum_sub_distrib]
  congr 1
  · refine sum_nbij' Prod.snd (fun i ↦ (n - i, i)) ?_ ?_ ?_ ?_ ?_
    · intro ij hij
      have := mem_antidiagonal.1 hij
      exact mem_range.2 (by omega)
    · intro i hi
      have := mem_range.1 hi
      exact mem_antidiagonal.2 (by omega)
    · intro ij hij
      have := mem_antidiagonal.1 hij
      exact Prod.ext (by omega) rfl
    · intro _ _
      rfl
    · intro ij hij
      have h := mem_antidiagonal.1 hij
      have hi1 : m + (ij.1 : ℤ) = m + (n : ℤ) - ij.2 := by omega
      rw [← h, Nat.choose_symm_add, h, Ring.choose_natCast, hi1, mul_comm, mul_zsmul,
        natCast_zsmul]
  · refine sum_nbij' Prod.fst (fun i ↦ (i, n - i)) ?_ ?_ ?_ ?_ ?_
    · intro ij hij
      have := mem_antidiagonal.1 hij
      exact mem_range.2 (by omega)
    · intro i hi
      have := mem_range.1 hi
      exact mem_antidiagonal.2 (by omega)
    · intro ij hij
      have := mem_antidiagonal.1 hij
      exact Prod.ext rfl (by omega)
    · intro _ _
      rfl
    · intro ij hij
      have h := mem_antidiagonal.1 hij
      have hj : r + (ij.2 : ℤ) = (n : ℤ) + r - ij.1 := by omega
      have hsign : (-1 : ℤ) ^ ij.2 = (-1 : ℤ) ^ ij.1 * ((n : ℤ).negOnePow : ℤ) := by
        rw [Int.coe_negOnePow_natCast, ← h, pow_add, ← mul_assoc, ← mul_pow,
          show (-1 : ℤ) * -1 = 1 by rfl, one_pow, one_mul]
      rw [← natCast_zsmul, Ring.choose_natCast, hj, hsign, smul_smul]
      congr 1
      ring

private theorem neg_one_pow_mul_choose_neg_succ (k i : ℕ) :
    (-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i = ((k + i).choose i : ℤ) := by
  rw [show (-(k : ℤ) - 1) = -(k + 1 : ℤ) by omega, Ring.choose_neg,
    show (k : ℤ) + 1 + i - 1 = ((k + i : ℕ) : ℤ) by push_cast; ring,
    Ring.choose_natCast, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul, ← mul_assoc,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **Unified mode formula for `nthProduct`.** For any fields `A` and `B` (without assuming
locality) and all `n, r : ℤ`, `((A₍ₙ₎ B)₍ᵣ₎) c` is given by the `m = 0` Borcherds binomial sums. -/
theorem ncoeff_nthProduct_apply (n r : ℤ) (A B : VertexOperator R V) (c : V) :
    ((nthProduct n A B)[[r]]) c =
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[n - i]]) ((B[[r + i]]) c)) -
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
          (B[[n + r - i]]) ((A[[(i : ℤ)]]) c) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, ncoeff_normalOrder, normalOrderCoeff_apply]
    have h₁ : (∑ᶠ i : ℕ, ((hasseDeriv k A)[[-(i : ℤ) - 1]]) ((B[[r + i]]) c)) =
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
          (A[[-(k : ℤ) - 1 - i]]) ((B[[r + i]]) c) := by
      refine finsum_congr fun i ↦ ?_
      rw [ncoeff_hasseDeriv, LinearMap.smul_apply,
        show -(i : ℤ) - 1 - k = -(k : ℤ) - 1 - i by omega,
        neg_one_pow_mul_choose_neg_succ i k, neg_one_pow_mul_choose_neg_succ k i,
        Nat.add_comm i k, Nat.choose_symm_add]
    obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero c
    have h₂ : (∑ᶠ j : ℕ, (B[[r - j - 1]]) (((hasseDeriv k A)[[(j : ℤ)]]) c)) =
        -∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i *
          ((-(k : ℤ) - 1).negOnePow : ℤ)) • (B[[-(k : ℤ) - 1 + r - i]]) ((A[[(i : ℤ)]]) c) := by
      have hsub₁ : (Function.support fun j : ℕ ↦
          (B[[r - j - 1]]) (((hasseDeriv k A)[[(j : ℤ)]]) c)) ⊆ range (k + Q) := by
        intro j hj
        simp only [mem_coe, mem_range]
        by_contra! h
        apply hj
        dsimp only
        rw [ncoeff_hasseDeriv, LinearMap.smul_apply, hQ _ (by omega), smul_zero, map_zero]
      have hsub₂ := support_nthProduct_right_subset A B 0 (-(k : ℤ) - 1) r c
        (Q := Q) (fun i hi ↦ by simpa using hQ i (by omega))
      simp only [zero_add] at hsub₂
      rw [finsum_eq_sum_of_support_subset _ hsub₁, finsum_eq_sum_of_support_subset _ hsub₂,
        sum_range_add]
      have hlow : ∑ j ∈ range k, (B[[r - j - 1]]) (((hasseDeriv k A)[[(j : ℤ)]]) c) = 0 := by
        refine sum_eq_zero fun j hj ↦ ?_
        rw [ncoeff_hasseDeriv, Ring.choose_natCast,
          Nat.choose_eq_zero_of_lt (mem_range.1 hj), Nat.cast_zero, mul_zero, zero_smul,
          LinearMap.zero_apply, map_zero]
      rw [hlow, zero_add, ← Finset.sum_neg_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [ncoeff_hasseDeriv, Ring.choose_natCast, LinearMap.smul_apply, map_zsmul,
        show ((k + i : ℕ) : ℤ) - k = (i : ℤ) by push_cast; ring,
        show r - ((k + i : ℕ) : ℤ) - 1 = -(k : ℤ) - 1 + r - i by push_cast; ring, ← neg_zsmul]
      congr 1
      have hsign : ((-(k : ℤ) - 1).negOnePow : ℤ) = -((-1 : ℤ) ^ k) := by
        rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring, Int.negOnePow_neg,
          Int.coe_negOnePow_natCast, pow_succ, mul_neg_one]
      rw [neg_one_pow_mul_choose_neg_succ k i, Nat.choose_symm_add, hsign]
      ring
    rw [h₁, h₂, ← sub_eq_add_neg]
  · lift n to ℕ using hn
    rw [nthProduct_natCast, ncoeff_nonnegResidueProduct]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp]
    simpa only [zero_add] using sum_antidiagonal_commutator_eq_sub_finsum n 0 r A B c

/-! ### Action of `hasseDeriv` and `nthProduct` on pole-free vectors -/

/-- If all nonnegative modes of `A` kill `vac`, the same holds for `∂^{(k)} A`. -/
theorem ncoeff_hasseDeriv_apply_eq_zero_of_nonneg {A : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (k : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    ((hasseDeriv k A)[[m]]) vac = 0 := by
  lift m to ℕ using hm
  rw [ncoeff_hasseDeriv, Ring.choose_natCast, LinearMap.smul_apply]
  rcases lt_or_ge m k with hlt | hge
  · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero, zero_smul]
  · rw [hA _ (by omega), smul_zero]

/-- If all nonnegative modes of `A` and `B` kill `vac`, then all nonnegative modes of `A₍ₙ₎ B`
kill `vac` as well. -/
theorem ncoeff_nthProduct_apply_eq_zero_of_nonneg {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0)
    (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ((nthProduct n A B)[[m]]) vac = 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, ncoeff_normalOrder, normalOrderCoeff_apply]
    have h₁ : (∑ᶠ i : ℕ, ((hasseDeriv k A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by rw [hB _ (by omega), map_zero]
    have h₂ : (∑ᶠ i : ℕ, (B[[m - i - 1]]) (((hasseDeriv k A)[[(i : ℤ)]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDeriv_apply_eq_zero_of_nonneg hA k (Nat.cast_nonneg i), map_zero]
    rw [h₁, h₂, add_zero]
  · lift n to ℕ using hn
    rw [nthProduct_natCast, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    refine sum_eq_zero fun ij _ ↦ ?_
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp]
    rw [hB _ (by omega), hA _ (Nat.cast_nonneg ij.1), map_zero, map_zero, sub_self, smul_zero,
      smul_zero]

/-- If all nonnegative modes of `A` and `B` kill `vac`, then `((A₍ₙ₎ B)₍₋₁₎) vac = A₍ₙ₎ (B₍₋₁₎ vac)`
for every `n : ℤ`. -/
theorem ncoeff_neg_one_nthProduct_apply {A B : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) vac = 0)
    (n : ℤ) :
    ((nthProduct n A B)[[-1]]) vac = (A[[n]]) ((B[[-1]]) vac) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, ncoeff_normalOrder, normalOrderCoeff_apply]
    have h₂ : (∑ᶠ i : ℕ, (B[[-1 - i - 1]]) (((hasseDeriv k A)[[(i : ℤ)]]) vac)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun i ↦ by
        rw [ncoeff_hasseDeriv_apply_eq_zero_of_nonneg hA k (Nat.cast_nonneg i), map_zero]
    rw [h₂, add_zero, finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, neg_zero, zero_sub, add_zero]
      rw [ncoeff_neg_one_hasseDeriv]
    · intro i hi
      rw [hB _ (by omega), map_zero]
  · lift n to ℕ using hn
    rw [nthProduct_natCast, ncoeff_nonnegResidueProduct, LinearMap.sum_apply,
      sum_eq_single (n, 0)]
    · simp [hA _ (Nat.cast_nonneg n)]
    · intro ij hij hne
      have hj : ij.2 ≠ 0 := fun hj ↦
        hne (Prod.ext (by simpa [hj] using mem_antidiagonal.1 hij) hj)
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp]
      rw [hB _ (by omega), hA _ (Nat.cast_nonneg ij.1), map_zero, map_zero, sub_self, smul_zero,
        smul_zero]
    · simp

/-! ### Translation covariance of `hasseDeriv` and field products -/

/-- Translation covariance is preserved by Hasse differentiation. -/
theorem lie_ncoeff_hasseDeriv {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, (hasseDeriv k A)[[m]]⁆ = (derivative (hasseDeriv k A))[[m]] := by
  have hzsmul (z : ℤ) (u : Module.End R V) : ⁅T, z • u⁆ = z • ⁅T, u⁆ := by
    simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [ncoeff_hasseDeriv, hzsmul, hA, ncoeff_derivative, ncoeff_derivative, ncoeff_hasseDeriv,
    show m - 1 - (k : ℤ) = m - k - 1 by omega, smul_smul, smul_smul]
  congr 1
  -- Both scalar coefficients reduce to `(-1)^(k+1) * (k + 1) * (m choose (k + 1))`.
  have h₁ : Ring.choose m k * (m - k) = ((k + 1 : ℕ) : ℤ) * Ring.choose m (k + 1) := by
    have hc := Ring.choose_smul_choose m (Nat.le_add_right k 1)
    rw [Nat.add_sub_cancel_left, Ring.choose_one_right, Nat.choose_symm_add,
      Nat.choose_one_right, nsmul_eq_mul] at hc
    exact hc.symm
  have h₂ : m * Ring.choose (m - 1) k = ((k + 1 : ℕ) : ℤ) * Ring.choose m (k + 1) := by
    have hc := Ring.choose_add_smul_choose (m - 1) k 1
    rw [show m - 1 + (1 : ℕ) = m by omega, Ring.choose_one_right, Nat.choose_one_right,
      nsmul_eq_mul] at hc
    exact hc.symm
  calc ((-1 : ℤ) ^ k * Ring.choose m k) * -(m - k)
      = -((-1 : ℤ) ^ k * (Ring.choose m k * (m - k))) := by ring
    _ = -((-1 : ℤ) ^ k * (((k + 1 : ℕ) : ℤ) * Ring.choose m (k + 1))) := by rw [h₁]
    _ = -((-1 : ℤ) ^ k * (m * Ring.choose (m - 1) k)) := by rw [h₂]
    _ = (-m) * ((-1 : ℤ) ^ k * Ring.choose (m - 1) k) := by ring

/-- Translation covariance is preserved by normal ordering. -/
theorem lie_ncoeff_normalOrder {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (r : ℤ) :
    ⁅T, (normalOrder A B)[[r]]⁆ = (derivative (normalOrder A B))[[r]] := by
  have hcomp (u w : Module.End R V) (v : V) :
      T (u (w v)) = (⁅T, u⁆) (w v) + u ((⁅T, w⁆) v) + u (w (T v)) := by
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
    abel
  ext v
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P', hP'⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q', hQ'⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let M : ℕ := max (max P P' + r.natAbs + 2) (max Q Q' + 2)
  have hBv (i : ℕ) (hi : M ≤ i) : (B[[r + i]]) v = 0 := hP _ (by omega)
  have hBTv (i : ℕ) (hi : M ≤ i) : (B[[r + i]]) (T v) = 0 := hP' _ (by omega)
  have hBder (i : ℕ) (hi : M ≤ i) : ((derivative B)[[r + i]]) v = 0 := by
    rw [ncoeff_derivative, LinearMap.smul_apply, hP _ (by omega), smul_zero]
  have hAv (i : ℕ) (hi : M ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ _ (by omega)
  have hATv (i : ℕ) (hi : M ≤ i) : (A[[(i : ℤ)]]) (T v) = 0 := hQ' _ (by omega)
  have hAder (i : ℕ) (hi : M ≤ i) : ((derivative A)[[(i : ℤ)]]) v = 0 := by
    rw [ncoeff_derivative, LinearMap.smul_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp
    · rw [hQ _ (by omega), smul_zero]
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    derivative_normalOrder, map_add, Pi.add_apply, LinearMap.add_apply,
    ncoeff_normalOrder, ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B r v hBv hAv,
    normalOrderCoeff_eq_sum A B r (T v) hBTv hATv,
    normalOrderCoeff_eq_sum (derivative A) B r v hBv hAder,
    normalOrderCoeff_eq_sum A (derivative B) r v hBder hAv,
    map_add, map_sum, map_sum]
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [hcomp, hcomp, hA, hB, hB, hA]
  abel

/-- Translation covariance is preserved by nonnegative residue products. -/
theorem lie_ncoeff_nonnegResidueProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n : ℕ) (r : ℤ) :
    ⁅T, (nonnegResidueProduct n A B)[[r]]⁆ =
      (derivative (nonnegResidueProduct n A B))[[r]] := by
  have hlie_sum (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → Module.End R V) :
      ⁅T, ∑ x ∈ s, f x⁆ = ∑ x ∈ s, ⁅T, f x⁆ := by
    simp only [Ring.lie_def, mul_sum, sum_mul, ← sum_sub_distrib]
  have hnsmul (k : ℕ) (u : Module.End R V) : ⁅T, k • u⁆ = k • ⁅T, u⁆ := by
    simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]
  have hzsmul (z : ℤ) (u : Module.End R V) : ⁅T, z • u⁆ = z • ⁅T, u⁆ := by
    simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]
  have hjac (u w : Module.End R V) :
      ⁅T, u * w - w * u⁆ = (⁅T, u⁆ * w - w * ⁅T, u⁆) + (u * ⁅T, w⁆ - ⁅T, w⁆ * u) := by
    simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]
    abel
  rw [derivative_nonnegResidueProduct, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct, hlie_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [hnsmul, hzsmul, ← smul_add, ← smul_add]
  congr 2
  rw [hjac, hA, hB]

/-- Translation covariance is preserved by all `n`-th products (`n : ℤ`). -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n r : ℤ) :
    ⁅T, (nthProduct n A B)[[r]]⁆ = (derivative (nthProduct n A B))[[r]] := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ]
    exact lie_ncoeff_normalOrder (fun m ↦ lie_ncoeff_hasseDeriv hA k m) hB r
  · lift n to ℕ using hn
    rw [nthProduct_natCast]
    exact lie_ncoeff_nonnegResidueProduct hA hB n r

end VertexOperator
