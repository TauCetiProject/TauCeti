/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import Mathlib.RingTheory.Binomial
-- Proof-only: delta expansions of local commutators and module ring tactics.
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Tactic.Module

/-!
# Hasse derivatives of vertex operators

The `k`-th Hasse (divided-power) derivative `∂_z^(k)` of a field is defined over any commutative
ring, without dividing by `k!`: on unnormalized Laurent coefficients it sends `A.coeff (n + k)` to
`choose (n + k) k • A.coeff (n + k)`, and in normalized mode indexing its modes are
`(∂_z^(k) A)₍ₙ₎ = (-1)ᵏ • choose n k • A₍ₙ₋ₖ₎`.

Over any ring, `k! • ∂_z^(k) A` recovers the `k`-fold ordinary derivative `∂_z^[k] A`, and Hasse
differentiation preserves mutual locality, increasing a locality bound by the derivative order.
These divided-power derivatives govern the negative `n`-th products of fields via
`A₍₋ₖ₋₁₎ B = :(∂_z^(k) A) B:`.

## Main definitions

* `VertexOperator.hasseDeriv`: the `k`-th Hasse derivative of a field as an `R`-linear map.

## Main results

* `VertexOperator.ncoeff_hasseDeriv`:
  `(hasseDeriv k A)[[n]] = (-1)ᵏ • Ring.choose n k • A[[n - k]]`.
* `VertexOperator.factorial_nsmul_hasseDeriv`: `k! • hasseDeriv k A = derivative^[k] A`.
* `VertexOperator.IsLocalOfOrder.hasseDeriv_left`, `VertexOperator.IsLocalOfOrder.hasseDeriv_right`,
  `VertexOperator.IsLocalOfOrder.hasseDeriv`: Hasse differentiation preserves mutual locality.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §3.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §2.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2 and §3.1.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The `k`-th Hasse (divided-power) derivative of fields, defined coefficientwise on Laurent
series by `(hasseDeriv k A).coeff n = Ring.choose (n + k) k • A.coeff (n + k)`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R
    ((HahnModule.ofLinearEquiv R).toLinearMap ∘ₗ
      LaurentSeries.hasseDeriv R k ∘ₗ
      (HahnModule.ofLinearEquiv R).symm.toLinearMap)

-- As with Mathlib's coefficient API, this is not a simp lemma: the simp normal form
-- uses normalized coefficients instead.
/-- Hasse differentiation shifts the unnormalized Laurent coefficients down by `k` with binomial
weights. -/
theorem coeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (hasseDeriv k A) n =
      Ring.choose (n + k) k • HVertexOperator.coeff A (n + k) := by
  ext v
  simp only [hasseDeriv, LinearMap.compRight_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    HVertexOperator.coeff_apply_apply, LinearMap.smul_apply, HahnModule.ofLinearEquiv_apply,
    HahnModule.ofLinearEquiv_symm_apply, Equiv.symm_apply_apply, LaurentSeries.hasseDeriv_coeff]

/-- The normalized modes of the `k`-th Hasse derivative are
`(∂_z^(k) A)₍ₙ₎ = (-1)ᵏ • choose n k • A₍ₙ₋ₖ₎`. -/
@[simp]
theorem ncoeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDeriv k A)[[n]] = (-1 : ℤ) ^ k • Ring.choose n k • A[[n - k]] := by
  simp only [ncoeff_apply, coeff_hasseDeriv]
  have h₁ : -n - 1 + (k : ℤ) = -(n + 1 - k) := by omega
  have h₂ : n + 1 - (k : ℤ) + k - 1 = n := by omega
  have h₃ : -n - 1 + (k : ℤ) = -(n - k) - 1 := by omega
  rw [h₁, Ring.choose_neg, h₂, Units.smul_def, Int.coe_negOnePow_natCast, smul_assoc, ← h₁, h₃]

/-- The zeroth Hasse derivative is the identity on fields. -/
theorem hasseDeriv_zero (A : VertexOperator R V) : hasseDeriv 0 A = A := by
  refine ext_ncoeff fun n ↦ ?_
  simp

/-- The zeroth Hasse derivative as a linear map is the identity. -/
@[simp]
theorem hasseDeriv_zero_eq_id :
    hasseDeriv (R := R) (V := V) 0 = LinearMap.id :=
  LinearMap.ext hasseDeriv_zero

/-- The first Hasse derivative is the ordinary formal derivative. -/
theorem hasseDeriv_one (A : VertexOperator R V) : hasseDeriv 1 A = derivative A := by
  refine ext_ncoeff fun n ↦ ?_
  simp [neg_smul]

/-- The first Hasse derivative as a linear map is `VertexOperator.derivative`. -/
theorem hasseDeriv_one_eq_derivative :
    hasseDeriv (R := R) (V := V) 1 = derivative :=
  LinearMap.ext hasseDeriv_one

/-- Composing Hasse derivatives of orders `j` and `k` multiplies the `(j + k)`-th Hasse derivative
by `choose (j + k) j`. -/
theorem choose_nsmul_hasseDeriv_add (j k : ℕ) (A : VertexOperator R V) :
    (j + k).choose j • hasseDeriv (j + k) A = hasseDeriv j (hasseDeriv k A) := by
  refine ext_ncoeff fun n ↦ ?_
  simp only [map_nsmul, Pi.smul_apply, ncoeff_hasseDeriv]
  have hchoose := Ring.choose_smul_choose n (Nat.le_add_right j k)
  rw [Nat.add_sub_cancel_left] at hchoose
  have hsub : n - (j : ℤ) - k = n - ↑(j + k) := by omega
  rw [hsub, ← natCast_zsmul, pow_add, smul_comm ((-1 : ℤ) ^ k), ← mul_smul (Ring.choose n j),
    ← hchoose, nsmul_eq_mul]
  module

/-- Scaling the `k`-th Hasse derivative by `k!` recovers the `k`-fold ordinary derivative. -/
theorem factorial_nsmul_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    k.factorial • hasseDeriv k A = (derivative (R := R) (V := V))^[k] A := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    have h1 : (k + 1).choose k = k + 1 := Nat.choose_succ_self_right k
    rw [Function.iterate_succ_apply, ← hasseDeriv_one A, ← ih, ← map_nsmul,
      ← choose_nsmul_hasseDeriv_add k 1 A, h1, smul_smul, mul_comm, ← Nat.factorial_succ,
      map_nsmul]

namespace IsLocalOfOrder

variable {A B : VertexOperator R V} {N : ℕ}

/-- Taking the `k`-th Hasse derivative of the first field increases a locality bound by `k`. -/
theorem hasseDeriv_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    (VertexOperator.hasseDeriv k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  let C : ℕ → ℤ → Module.End R V := fun j ↦
    TauCeti.FormalDistribution.residue
      ((TauCeti.FormalDistribution.mulSub ^ j) (A.commutatorDistribution B))
  -- Expand `[A(z), B(w)]` in delta derivatives and absorb `choose m k` via `choose_smul_choose`.
  have hexp : (VertexOperator.hasseDeriv k A).commutatorDistribution B =
      ∑ j ∈ range N, TauCeti.FormalDistribution.deltaTerm (j + k)
        (fun s ↦ (-1 : ℤ) ^ k • (j + k).choose k • C j s) := by
    refine funext fun m ↦ funext fun n ↦ ?_
    have hAB := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm (m - k)) n
    simp only [commutatorDistribution_apply, ncoeff_hasseDeriv, smul_mul_assoc,
      mul_smul_comm, ← smul_sub] at hAB ⊢
    rw [hAB]
    simp only [Finset.sum_apply, TauCeti.FormalDistribution.deltaTerm_apply, smul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    have hchoose := Ring.choose_smul_choose m (Nat.le_add_left k j)
    rw [Nat.add_sub_cancel] at hchoose
    have hidx : m - (k : ℤ) + n - j = m + n - ↑(j + k) := by omega
    rw [hidx, ← mul_smul (Ring.choose m k), ← hchoose, nsmul_eq_mul, ← natCast_zsmul]
    dsimp only [C]
    module
  rw [hexp, map_sum]
  exact sum_eq_zero fun j hj ↦
    TauCeti.FormalDistribution.mulSub_pow_deltaTerm_eq_zero
      (Nat.add_lt_add_right (mem_range.mp hj) k) _

/-- Taking the `k`-th Hasse derivative of the second field increases a locality bound by `k`. -/
theorem hasseDeriv_right (h : A.IsLocalOfOrder B N) (k : ℕ) :
    A.IsLocalOfOrder (VertexOperator.hasseDeriv k B) (N + k) :=
  (h.symm.hasseDeriv_left k).symm

/-- Hasse derivatives of orders `k` and `l` of local fields are local of order `N + k + l`. -/
theorem hasseDeriv (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    (VertexOperator.hasseDeriv k A).IsLocalOfOrder
      (VertexOperator.hasseDeriv l B) (N + k + l) :=
  ((h.hasseDeriv_left k).hasseDeriv_right l)

end IsLocalOfOrder

end VertexOperator
