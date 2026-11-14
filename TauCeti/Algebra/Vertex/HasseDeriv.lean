/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import TauCeti.Algebra.Vertex.FormalDistribution

/-!
# Hasse derivatives of vertex operators

The `k`-th Hasse (divided-power) derivative `∂_z^{(k)} A(z)` of a field `A : VertexOperator R V`
acts on Laurent coefficients by `(∂_z^{(k)} A).coeff n = Ring.choose (n + k) k • A.coeff (n + k)`.
Unlike `∂_z^k A / k!`, it is defined over any commutative ring `R` without dividing by factorials.

In normalized mode indexing `A(z) = ∑ₙ A₍ₙ₎ z^{-n-1}`, upper negation of integer binomial
coefficients gives `(∂_z^{(k)} A)₍ₙ₎ = (-1)ᵏ (n choose k) A₍ₙ₋ₖ₎`; in particular
`(∂_z^{(k)} A)₍₋₁₎ = A₍₋ₖ₋₁₎`, which allows negative residue products of fields to be defined
uniformly as `A₍₋ₖ₋₁₎ B = :(∂_z^{(k)} A) B:` in every characteristic.

Hasse differentiation preserves mutual locality over any commutative ring: if `A` and `B` are
mutually local of order `N`, then `∂_z^{(k)} A` and `∂_z^{(l)} B` are mutually local of order
`N + k + l`. The proof rewrites the commutator distribution via the formal delta expansion
`VertexOperator.IsLocalOfOrder.commutatorDistribution_eq_sum_deltaTerm` and absorbs the binomial
factors with `Ring.choose_smul_choose`.

## Main definitions

* `VertexOperator.hasseDeriv`: the `k`-th Hasse derivative as an `R`-linear map on
  `VertexOperator R V`.

## Main results

* `VertexOperator.ncoeff_hasseDeriv`: `(hasseDeriv k A)[[n]] = (-1) ^ k • choose n k • A[[n - k]]`.
* `VertexOperator.ncoeff_neg_one_hasseDeriv`: `(hasseDeriv k A)[[-1]] = A[[-k - 1]]`.
* `VertexOperator.hasseDeriv_comp`:
  `hasseDeriv k (hasseDeriv l A) = (k + l).choose k • hasseDeriv (k + l) A`.
* `VertexOperator.iterate_derivative_eq_factorial_smul_hasseDeriv`:
  `derivative^[k] A = k! • hasseDeriv k A`.
* `VertexOperator.IsLocalOfOrder.hasseDeriv_left`, `VertexOperator.IsLocalOfOrder.hasseDeriv_right`,
  `VertexOperator.IsLocalOfOrder.hasseDeriv`: Hasse derivatives preserve mutual locality.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3.
* H. Li, *Vertex algebras and vertex Poisson algebras*, Commun. Contemp. Math. 6 (2004), §2.
* G. Mason, *Vertex rings and Pierce bundles*, Contemp. Math. 711 (2018), §2.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The `k`-th Hasse (divided-power) derivative `∂_z^{(k)}` on fields `VertexOperator R V`,
transported from `LaurentSeries.hasseDeriv` across `HahnModule.ofLinearEquiv`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R
    ((HahnModule.ofLinearEquiv R).toLinearMap ∘ₗ LaurentSeries.hasseDeriv R k ∘ₗ
      (HahnModule.ofLinearEquiv R).symm.toLinearMap)

/-- Evaluating `hasseDeriv k A` at a vector applies `LaurentSeries.hasseDeriv R k` to its Laurent
series. -/
@[simp]
theorem of_symm_hasseDeriv_apply (k : ℕ) (A : VertexOperator R V) (v : V) :
    (HahnModule.of R).symm (hasseDeriv k A v) =
      LaurentSeries.hasseDeriv R k ((HahnModule.of R).symm (A v)) := by
  simp [hasseDeriv]

/-- The `k`-th Hasse derivative shifts unnormalized Laurent coefficients down by `k`, weighted by
`Ring.choose (n + k) k`. -/
theorem coeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (hasseDeriv k A) n =
      Ring.choose (n + k) k • HVertexOperator.coeff A (n + k) := by
  ext v
  rw [HVertexOperator.coeff_apply_apply, LinearMap.smul_apply, HVertexOperator.coeff_apply_apply,
    of_symm_hasseDeriv_apply, LaurentSeries.hasseDeriv_coeff]

/-- The normalized modes of the `k`-th Hasse derivative are
`(∂_z^{(k)} A)₍ₙ₎ = (-1)ᵏ (n choose k) A₍ₙ₋ₖ₎`. -/
@[simp]
theorem ncoeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDeriv k A)[[n]] = (-1 : ℤ) ^ k • Ring.choose n k • A[[n - k]] := by
  rw [ncoeff_apply, coeff_hasseDeriv, coeff_eq_ncoeff]
  have h₁ : -n - 1 + (k : ℤ) = -(n - k + 1) := by omega
  have h₂ : n - (k : ℤ) + 1 + k - 1 = n := by omega
  rw [h₁, neg_neg, add_sub_cancel_right, Ring.choose_neg, h₂, Units.smul_def,
    Int.coe_negOnePow_natCast, smul_assoc]

/-- The `(-1)`-st mode of the `k`-th Hasse derivative is `A₍₋ₖ₋₁₎`. -/
theorem ncoeff_neg_one_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    (hasseDeriv k A)[[-1]] = A[[-(k : ℤ) - 1]] := by
  rw [ncoeff_apply, coeff_hasseDeriv, coeff_eq_ncoeff]
  have h₁ : -(-1 : ℤ) - 1 + (k : ℤ) = (k : ℤ) := by omega
  rw [h₁, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, one_smul]

/-- The `0`-th Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero : hasseDeriv (R := R) (V := V) 0 = LinearMap.id := by
  ext A v n
  simp

/-- The `1`-st Hasse derivative is the ordinary formal derivative. -/
@[simp]
theorem hasseDeriv_one : hasseDeriv (R := R) (V := V) 1 = derivative := by
  ext A v n
  simp [LaurentSeries.derivative_apply]

/-- Composing Hasse derivatives of orders `k` and `l` gives `(k + l).choose k` times the
`(k + l)`-th Hasse derivative. -/
theorem hasseDeriv_comp (k l : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (hasseDeriv l A) = (k + l).choose k • hasseDeriv (k + l) A := by
  ext v n
  rw [← Nat.cast_smul_eq_nsmul R]
  simp [LaurentSeries.hasseDeriv_comp, ← Nat.cast_smul_eq_nsmul R]

/-- Differentiating the `k`-th Hasse derivative gives `k + 1` times the `(k + 1)`-st Hasse
derivative. -/
theorem derivative_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDeriv k A) = (k + 1) • hasseDeriv (k + 1) A := by
  rw [← hasseDeriv_one, hasseDeriv_comp, Nat.add_comm 1 k, Nat.choose_one_right]

/-- The `k`-th Hasse derivative of `∂_z A` is `k + 1` times the `(k + 1)`-st Hasse derivative. -/
theorem hasseDeriv_derivative (k : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (derivative A) = (k + 1) • hasseDeriv (k + 1) A := by
  rw [← hasseDeriv_one, hasseDeriv_comp, Nat.choose_symm_add, Nat.choose_one_right]

/-- The `k`-th iterated derivative equals `k!` times the `k`-th Hasse derivative. -/
theorem iterate_derivative_eq_factorial_smul_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    (derivative (R := R) (V := V))^[k] A = k.factorial • hasseDeriv k A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, derivative_hasseDeriv, Nat.factorial_succ,
      mul_nsmul, smul_comm]

namespace IsLocalOfOrder

variable {A B : VertexOperator R V} {N : ℕ}

/-- Taking the `k`-th Hasse derivative of the first field increases a locality bound by `k`, over
any commutative ring. -/
theorem hasseDeriv_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    (hasseDeriv k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  let C : ℕ → ℤ → Module.End R V := fun j ↦
    FormalDistribution.residue ((FormalDistribution.mulSub ^ j) (A.commutatorDistribution B))
  -- Rewrite the commutator via the delta expansion of `[A(z), B(w)]` and absorb `choose m k`.
  have hexp : (hasseDeriv k A).commutatorDistribution B =
      ∑ j ∈ range N, FormalDistribution.deltaTerm (j + k)
        ((-1 : ℤ) ^ k • ((j + k).choose k) • C j) := by
    refine funext fun m ↦ funext fun n ↦ ?_
    have hc := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm (m - k)) n
    rw [Finset.sum_apply, Finset.sum_apply] at hc ⊢
    rw [commutatorDistribution_apply] at hc ⊢
    rw [ncoeff_hasseDeriv, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      ← smul_sub, ← smul_sub, hc, smul_sum, smul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [FormalDistribution.deltaTerm_apply, FormalDistribution.deltaTerm_apply,
      Pi.smul_apply, Pi.smul_apply]
    have hchoose := Ring.choose_smul_choose m (Nat.le_add_left k j)
    rw [Nat.add_sub_cancel, nsmul_eq_mul] at hchoose
    have hidx : m - (k : ℤ) + n - j = m + n - (j + k : ℕ) := by push_cast; omega
    rw [hidx, ← natCast_zsmul, smul_smul, smul_smul, smul_smul, smul_smul]
    exact congrArg (· • C j (m + n - (j + k : ℕ))) (by linear_combination -((-1 : ℤ) ^ k) * hchoose)
  rw [hexp, map_sum]
  exact sum_eq_zero fun j hj ↦ FormalDistribution.mulSub_pow_deltaTerm_eq_zero
    (Nat.add_lt_add_right (mem_range.mp hj) k) _

/-- Taking the `k`-th Hasse derivative of the second field increases a locality bound by `k`, over
any commutative ring. -/
theorem hasseDeriv_right (h : A.IsLocalOfOrder B N) (k : ℕ) :
    A.IsLocalOfOrder (hasseDeriv k B) (N + k) :=
  (h.symm.hasseDeriv_left k).symm

/-- Hasse derivatives of orders `k` and `l` of local fields are local of order `N + k + l`. -/
theorem hasseDeriv (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    (hasseDeriv k A).IsLocalOfOrder (hasseDeriv l B) (N + k + l) :=
  ((h.hasseDeriv_left k).symm.hasseDeriv_left l).symm

end IsLocalOfOrder

end VertexOperator
