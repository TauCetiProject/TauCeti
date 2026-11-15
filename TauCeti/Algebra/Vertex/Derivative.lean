/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
public import TauCeti.Algebra.Vertex.FormalDistribution
public import TauCeti.RingTheory.LaurentSeries.HahnModuleDerivative
import Mathlib.Tactic.Module

/-!
# Formal and Hasse derivatives of vertex operators

The formal derivative and Hasse (divided-power) derivatives of a field are again fields: the `k`-th
Hasse derivative lowers the Laurent order bound by at most `k`, and in normalized mode indexing its
coefficients are `(D^[k] A)[[n]] = (-1)ᵏ (n choose k) • A[[n - k]]`, while
`(∂A)[[n]] = -n • A[[n - 1]]`. Both constructions are linear over any commutative coefficient ring,
with `(∂)^[k] A = k! • D^[k] A` and no characteristic-zero assumption.

Differentiation and Hasse differentiation preserve mutual locality over any commutative ring: taking
Hasse derivatives of orders `k` and `l` in the two variables increases a locality bound by `k + l`.
These are the formal-calculus identities used for negative `n`-th products, translation-covariant
fields, and reconstruction of vertex algebras.

## Main definitions

* `VertexOperator.derivative`: formal derivative `∂` of fields.
* `VertexOperator.hasseDeriv`: `k`-th Hasse (divided-power) derivative `D^[k]` of fields.

## Main results

* `VertexOperator.ncoeff_derivative`, `VertexOperator.ncoeff_hasseDeriv`: normalized mode formulas
  for `∂A` and `D^[k] A`.
* `VertexOperator.hasseDeriv_comp`, `VertexOperator.derivative_iterate`: composition law
  `D^[k] (D^[l] A) = ((k + l) choose k) • D^[k + l] A` and `(∂)^[k] A = k! • D^[k] A`.
* `VertexOperator.IsLocalOfOrder.hasseDeriv_left`, `VertexOperator.IsLocalOfOrder.hasseDeriv`:
  Hasse derivatives preserve mutual locality over any commutative ring.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §2.
-/

public section

noncomputable section

open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Formal differentiation of fields, defined on Laurent coefficients by
`(∂A).coeff n = (n + 1) • A.coeff (n + 1)`. -/
def derivative : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R (HahnModule.derivative R)

/-- Applying the derivative of a field differentiates its value as a Laurent series. -/
@[simp]
theorem derivative_apply (A : VertexOperator R V) (v : V) :
    derivative A v = HahnModule.derivative R (A v) := (rfl)

-- As with Mathlib's coefficient API, this is not a simp lemma: the simp normal form
-- uses normalized coefficients instead.
/-- Differentiation shifts the unnormalized Laurent coefficients down by one. -/
theorem coeff_derivative (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (derivative A) n = (n + 1) • HVertexOperator.coeff A (n + 1) := by
  ext v
  simpa only [derivative, LinearMap.compRight_apply, LinearMap.comp_apply,
    HVertexOperator.coeff_apply_apply, LinearMap.smul_apply] using
    HahnModule.coeff_derivative (A v) n

/-- The normalized modes of the derivative are `(∂A)₍ₙ₎ = -n A₍ₙ₋₁₎`. -/
@[simp]
theorem ncoeff_derivative (A : VertexOperator R V) (n : ℤ) :
    (derivative A)[[n]] = (-n) • A[[n - 1]] := by
  simp only [ncoeff_apply, coeff_derivative]
  have h₁ : -n - 1 + 1 = -n := by omega
  have h₂ : -(n - 1) - 1 = -n := by omega
  rw [h₁, h₂]

/-- The formal derivative of the identity field vanishes. -/
@[simp]
theorem derivative_idField : derivative (idField : VertexOperator R V) = 0 := by
  refine ext_ncoeff fun n ↦ ?_
  rw [ncoeff_derivative, ncoeff_idField]
  split_ifs with h
  · have hn : n = 0 := by omega
    subst hn
    simp
  · simp

/-- The `k`-th Hasse (divided-power) derivative of fields, defined on Laurent coefficients by
`(D^[k] A).coeff n = Ring.choose (n + k) k • A.coeff (n + k)`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R
    ((HahnModule.ofLinearEquiv R).toLinearMap ∘ₗ LaurentSeries.hasseDeriv R k ∘ₗ
      (HahnModule.ofLinearEquiv R).symm.toLinearMap)

/-- Reading `hasseDeriv k A v` through `HahnModule.of` gives the Laurent Hasse derivative. -/
@[simp]
theorem of_symm_hasseDeriv_apply (k : ℕ) (A : VertexOperator R V) (v : V) :
    (HahnModule.of R).symm (hasseDeriv k A v) =
      LaurentSeries.hasseDeriv R k ((HahnModule.of R).symm (A v)) := by
  simp [hasseDeriv]

/-- The `k`-th Hasse derivative shifts unnormalized Laurent coefficients down by `k` with binomial
weights. -/
theorem coeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (hasseDeriv k A) n =
      Ring.choose (n + k) k • HVertexOperator.coeff A (n + k) := by
  ext v
  simp only [HVertexOperator.coeff_apply_apply, of_symm_hasseDeriv_apply,
    LaurentSeries.hasseDeriv_coeff, LinearMap.smul_apply]

/-- The normalized modes of the `k`-th Hasse derivative are
`(D^[k] A)₍ₙ₎ = (-1)ᵏ (n choose k) A₍ₙ₋ₖ₎`. -/
@[simp]
theorem ncoeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDeriv k A)[[n]] = (-1 : ℤ) ^ k • Ring.choose n k • A[[n - k]] := by
  rw [ncoeff_apply, coeff_hasseDeriv, ncoeff_apply]
  have h₁ : -n - 1 + (k : ℤ) = -(n - k + 1) := by omega
  have h₂ : -(n - (k : ℤ)) - 1 = -(n - k + 1) := by omega
  have h₃ : n - (k : ℤ) + 1 + k - 1 = n := by omega
  rw [h₁, h₂, Ring.choose_neg, h₃, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
    mul_smul]

/-- Evaluating the `(-1)`-mode of `hasseDeriv k A` recovers `A₍₋ₖ₋₁₎`. -/
theorem ncoeff_neg_one_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    (hasseDeriv k A)[[-1]] = A[[-(k : ℤ) - 1]] := by
  rw [ncoeff_hasseDeriv, show (-1 : ℤ) = -(1 : ℤ) from rfl, Ring.choose_neg,
    show (1 : ℤ) + k - 1 = (k : ℤ) by ring, Ring.choose_natCast, Nat.choose_self,
    Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul, Nat.cast_one, mul_one, smul_smul,
    ← pow_add, ← two_mul, Even.neg_one_pow ⟨k, two_mul k⟩, one_smul,
    show -(1 : ℤ) - k = -(k : ℤ) - 1 by ring]

/-- If nonnegative modes of `A` annihilate `v`, so do nonnegative modes of `hasseDeriv k A`. -/
theorem ncoeff_hasseDeriv_apply_eq_zero_of_nonneg (k : ℕ) {A : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) {m : ℤ} (hm : 0 ≤ m) :
    ((hasseDeriv k A)[[m]]) v = 0 := by
  lift m to ℕ using hm
  rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, Ring.choose_natCast]
  rcases lt_or_ge m k with hlt | hge
  · simp [Nat.choose_eq_zero_of_lt hlt]
  · simp [hA _ (by omega : (0 : ℤ) ≤ (m : ℤ) - k)]

/-- The zeroth Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero : hasseDeriv (R := R) (V := V) 0 = LinearMap.id := by
  refine LinearMap.ext fun A ↦ LinearMap.ext fun v ↦ (HahnModule.of R).symm.injective ?_
  simp

/-- The first Hasse derivative is the formal derivative. -/
@[simp]
theorem hasseDeriv_one : hasseDeriv (R := R) (V := V) 1 = derivative := by
  refine LinearMap.ext fun A ↦ LinearMap.ext fun v ↦ (HahnModule.of R).symm.injective ?_
  simp [LaurentSeries.derivative_apply]

/-- Composition of Hasse derivatives: `D^[k] (D^[l] A) = ((k + l) choose k) • D^[k + l] A`. -/
theorem hasseDeriv_comp (k l : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (hasseDeriv l A) = (k + l).choose k • hasseDeriv (k + l) A := by
  refine HVertexOperator.coeff_inj (funext fun n ↦ ?_)
  rw [coeff_hasseDeriv, coeff_hasseDeriv, map_nsmul, Pi.smul_apply, coeff_hasseDeriv, Nat.cast_add,
    smul_smul, mul_comm, ← Ring.choose_add_smul_choose (n + k), add_assoc, Nat.choose_symm_add,
    smul_assoc]

/-- Formal differentiation of the `k`-th Hasse derivative gives `(k + 1) • D^[k + 1] A`. -/
theorem derivative_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDeriv k A) = (k + 1) • hasseDeriv (k + 1) A := by
  simpa [← hasseDeriv_one, add_comm 1 k, Nat.choose_one_right] using hasseDeriv_comp 1 k A

/-- The `k`-th Hasse derivative commutes with the formal derivative. -/
theorem hasseDeriv_derivative (k : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (derivative A) = (k + 1) • hasseDeriv (k + 1) A := by
  simpa [← hasseDeriv_one, Nat.choose_symm_add, Nat.choose_one_right] using hasseDeriv_comp k 1 A

/-- Iterated formal differentiation equals `k!` times the `k`-th Hasse derivative. -/
theorem derivative_iterate (k : ℕ) (A : VertexOperator R V) :
    (derivative (R := R) (V := V))^[k] A = k.factorial • hasseDeriv k A := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, derivative_hasseDeriv,
      Nat.factorial_succ, mul_nsmul, smul_comm]

private def hasseDerivDist {M : Type*} [AddCommGroup M] (k : ℕ) :
    AddMonoid.End (TauCeti.FormalDistribution M) where
  toFun c m n := (-1 : ℤ) ^ k • Ring.choose m k • c (m - k) n
  map_zero' := by ext m n; simp
  map_add' c d := by ext m n; simp [smul_add]

@[simp]
private theorem hasseDerivDist_apply {M : Type*} [AddCommGroup M] (k : ℕ)
    (c : TauCeti.FormalDistribution M) (m n : ℤ) :
    hasseDerivDist k c m n = (-1 : ℤ) ^ k • Ring.choose m k • c (m - k) n := (rfl)

private theorem mulSub_hasseDerivDist_succ {M : Type*} [AddCommGroup M] (k : ℕ)
    (c : TauCeti.FormalDistribution M) :
    TauCeti.FormalDistribution.mulSub (hasseDerivDist (k + 1) c) =
      hasseDerivDist (k + 1) (TauCeti.FormalDistribution.mulSub c) - hasseDerivDist k c := by
  ext m n
  simp only [TauCeti.FormalDistribution.mulSub_apply, hasseDerivDist_apply, Pi.sub_apply]
  have h₁ : m + 1 - ↑(k + 1) = m - (k : ℤ) := by omega
  have h₂ : m - ↑(k + 1) + 1 = m - (k : ℤ) := by omega
  rw [h₁, h₂, Ring.choose_succ_succ, pow_succ, add_smul, smul_sub]
  module

private theorem mulSub_pow_hasseDerivDist_eq_zero {M : Type*} [AddCommGroup M] :
    ∀ (s N k : ℕ) (c : TauCeti.FormalDistribution M),
      N + k = s → (TauCeti.FormalDistribution.mulSub ^ N) c = 0 →
        (TauCeti.FormalDistribution.mulSub ^ (N + k)) (hasseDerivDist k c) = 0
  | _, N, 0, c, _, hc => by
    have hc0 : hasseDerivDist 0 c = c := by ext m n; simp
    simpa [hc0] using hc
  | _, 0, k + 1, c, _, hc => by
    have hc0 : c = 0 := by simpa using hc
    simp [hc0]
  | _ + 1, N + 1, k + 1, c, _, hc => by
    have hexp : N + 1 + (k + 1) = (N + k + 1) + 1 := by omega
    rw [hexp, pow_succ, AddMonoid.End.coe_mul, Function.comp_apply,
      mulSub_hasseDerivDist_succ, map_sub]
    have h₁ : (TauCeti.FormalDistribution.mulSub ^ (N + (k + 1)))
        (hasseDerivDist (k + 1) (TauCeti.FormalDistribution.mulSub c)) = 0 :=
      mulSub_pow_hasseDerivDist_eq_zero (N + k + 1) N (k + 1) _ (by omega)
        (by simpa [pow_succ] using hc)
    have h₂ : (TauCeti.FormalDistribution.mulSub ^ (N + 1 + k)) (hasseDerivDist k c) = 0 :=
      mulSub_pow_hasseDerivDist_eq_zero (N + k + 1) (N + 1) k c (by omega) hc
    have he₁ : N + k + 1 = N + (k + 1) := by omega
    have he₂ : N + k + 1 = N + 1 + k := by omega
    rw [he₁, h₁, ← he₁, he₂, h₂, sub_zero]

namespace IsLocalOfOrder

variable {A B : VertexOperator R V} {N : ℕ}

/-- Taking the `k`-th Hasse derivative in the first variable increases a locality bound by `k`,
over any commutative ring. -/
theorem hasseDeriv_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    (VertexOperator.hasseDeriv k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero] at h ⊢
  have hcomm : (VertexOperator.hasseDeriv k A).commutatorDistribution B =
      hasseDerivDist k (A.commutatorDistribution B) := by
    ext m n : 2
    simp only [commutatorDistribution_apply, ncoeff_hasseDeriv, hasseDerivDist_apply,
      smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hcomm]
  exact mulSub_pow_hasseDerivDist_eq_zero (N + k) N k _ rfl h

/-- Taking the `k`-th Hasse derivative in the second variable increases a locality bound by `k`,
over any commutative ring. -/
theorem hasseDeriv_right (h : A.IsLocalOfOrder B N) (k : ℕ) :
    A.IsLocalOfOrder (VertexOperator.hasseDeriv k B) (N + k) :=
  (h.symm.hasseDeriv_left k).symm

/-- Hasse derivatives of orders `k` and `l` of local fields are local of order at most
`N + k + l`. -/
theorem hasseDeriv (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    (VertexOperator.hasseDeriv k A).IsLocalOfOrder
      (VertexOperator.hasseDeriv l B) (N + k + l) :=
  ((h.hasseDeriv_left k).hasseDeriv_right l)

/-- Differentiating the first field increases a locality bound by one. -/
theorem derivative_left (h : A.IsLocalOfOrder B N) :
    (derivative A).IsLocalOfOrder B (N + 1) := by
  simpa using h.hasseDeriv_left 1

/-- Differentiating the second field increases a locality bound by one. -/
theorem derivative_right (h : A.IsLocalOfOrder B N) :
    A.IsLocalOfOrder (derivative B) (N + 1) :=
  h.symm.derivative_left.symm

/-- Iterated differentiation in the first variable preserves locality. -/
theorem iterate_derivative_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    ((derivative (R := R) (V := V))^[k] A).IsLocalOfOrder B (N + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa [Function.iterate_succ_apply', Nat.add_assoc] using ih.derivative_left

/-- Derivatives of orders `k` and `l` of local fields are local of order at most `N + k + l`. -/
theorem iterate_derivative (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    ((derivative (R := R) (V := V))^[k] A).IsLocalOfOrder
      ((derivative (R := R) (V := V))^[l] B) (N + k + l) :=
  ((h.iterate_derivative_left k).symm.iterate_derivative_left l).symm

end IsLocalOfOrder

end VertexOperator
