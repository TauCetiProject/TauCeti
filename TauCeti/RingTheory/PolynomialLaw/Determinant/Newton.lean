/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.AdjoinRoot

/-!
# Newton identities for determinants

`TauCeti.Determinant.mul_charCoeff_eq_sum_trace_pow` relates the characteristic coefficients
of a Chenevier determinant to the traces of powers over any commutative ring.
`TauCeti.Determinant.rid_toFun_one_add_sum_inr_tmul` computes
its dual-number evaluation at first order.
The main ingredients are the scalar-extension formula `Determinant.toFun_tmul_add_tmul_one`
and Mathlib's square-zero Taylor formula `Polynomial.aeval_add_of_sq_eq_zero` and geometric
sum identity `mul_neg_geom_sum`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, Example 1.11(ii)](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

open TensorProduct Polynomial Finset TrivSqZeroExt
open scoped DualNumber

namespace TauCeti.Determinant

section CommSemiring

variable {A : Type*} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}

/-- The determinant at a single infinitesimal direction has linear term given by the trace. -/
theorem rid_toFun_inr_tmul_add_one {B : Type*} [CommSemiring B] [Algebra A B]
    (D : Determinant A R d) (b : B) (x : R) :
    Algebra.TensorProduct.rid A A B[ε] (D.toLaw.toFun B[ε] (inr b ⊗ₜ x + 1)) =
      1 + inr (b * algebraMap A B (D.trace x)) := by
  rw [Algebra.TensorProduct.one_def, D.toFun_tmul_add_tmul_one, map_sum]
  simp only [one_pow, mul_one, Algebra.TensorProduct.rid_tmul, Algebra.smul_def,
    TrivSqZeroExt.algebraMap_eq_inl']
  rcases d with _ | d
  · simp
  rw [← Finset.sum_subset (Finset.range_mono (Nat.le_add_left 2 d))]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one,
      zero_add, D.charCoeff_zero, _root_.map_one, inl_one, _root_.mul_one, inr_mul_inl,
      op_smul_eq_smul, smul_eq_mul, D.trace_apply, mul_comm]
  · intro i _ hi
    have hi₂ : 2 ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
    have hsq : (inr b : B[ε]) ^ 2 = 0 := by rw [pow_two, inr_mul_inr]
    rw [pow_eq_zero_of_le hi₂ hsq, mul_zero]

/-- Over the dual numbers of an `A`-algebra `B`, the determinant at
`1 + ∑ i ∈ s, (ε bᵢ) ⊗ xᵢ` is `1 + ε ∑ i ∈ s, bᵢ Tr(xᵢ)`. -/
theorem rid_toFun_one_add_sum_inr_tmul {B ι : Type*} [CommSemiring B] [Algebra A B]
    (D : Determinant A R d) (s : Finset ι) (b : ι → B) (x : ι → R) :
    Algebra.TensorProduct.rid A A B[ε] (D.toLaw.toFun B[ε] (1 + ∑ i ∈ s, inr (b i) ⊗ₜ x i)) =
      1 + inr (∑ i ∈ s, b i * algebraMap A B (D.trace (x i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [D.isMultiplicative.toFun_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hmul :
        (1 + (inr (b i) : B[ε]) ⊗ₜ[A] x i) *
            (1 + ∑ j ∈ s, inr (b j) ⊗ₜ x j) =
          1 + ((inr (b i) : B[ε]) ⊗ₜ[A] x i + ∑ j ∈ s, inr (b j) ⊗ₜ x j) := by
      have hzero : ((inr (b i) : B[ε]) ⊗ₜ[A] x i) * (∑ j ∈ s, inr (b j) ⊗ₜ x j) = 0 := by
        calc _ = ∑ j ∈ s, ((inr (b i) : B[ε]) ⊗ₜ[A] x i) * (inr (b j) ⊗ₜ x j) :=
              Finset.mul_sum s _ ((inr (b i) : B[ε]) ⊗ₜ[A] x i)
          _ = 0 := by simp only [Algebra.TensorProduct.tmul_mul_tmul, inr_mul_inr,
            zero_tmul, Finset.sum_const_zero]
      rw [add_mul, mul_add ((inr (b i) : B[ε]) ⊗ₜ[A] x i), hzero]
      simp only [one_mul (1 + ∑ j ∈ s, (inr (b j) : B[ε]) ⊗ₜ[A] x j),
        mul_one ((inr (b i) : B[ε]) ⊗ₜ[A] x i), add_zero]
      abel
    rw [← hmul, D.isMultiplicative.toFun_mul, _root_.map_mul, add_comm (1 : B[ε] ⊗[A] R),
      D.rid_toFun_inr_tmul_add_one, ih]
    simp only [add_mul, mul_add, mul_one, one_mul, inr_mul_inr, add_zero, inr_add]
    abel

end CommSemiring

variable {A : Type*} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}

/-- At an element of nilpotence index at most `n`, the derivative of the generating polynomial
for the characteristic coefficients is its product with the truncated signed trace series. -/
private theorem aeval_derivative_sum_charCoeff {B : Type*} [CommRing B] [Algebra A B]
    (D : Determinant A R d) (x : R) {z : B} {n : ℕ} (hz : z ^ n = 0) :
    aeval z (derivative (∑ i ∈ range (d + 1), C (D.charCoeff i x) * X ^ i)) =
      aeval z (∑ i ∈ range (d + 1), C (D.charCoeff i x) * X ^ i) *
        aeval z (∑ j ∈ range n, C ((-1) ^ j * D.trace (x ^ (j + 1))) * X ^ j) := by
  let P : A[X] := ∑ i ∈ range (d + 1), C (D.charCoeff i x) * X ^ i
  let Q : A[X] := ∑ j ∈ range n, C ((-1) ^ j * D.trace (x ^ (j + 1))) * X ^ j
  let v : B[ε] ⊗[A] R := inl z ⊗ₜ x
  let w : B[ε] ⊗[A] R := inr 1 ⊗ₜ x
  let T : B[ε] ⊗[A] R := ∑ j ∈ range n, inr ((-z) ^ j) ⊗ₜ (x ^ (j + 1))
  let F (y : B[ε] ⊗[A] R) := Algebra.TensorProduct.rid A A B[ε] (D.toLaw.toFun B[ε] y)
  have hF (t : B[ε]) : F (t ⊗ₜ[A] x + 1) = aeval t P := by
    dsimp only [F]
    rw [Algebra.TensorProduct.one_def, D.toFun_tmul_add_tmul_one, map_sum]
    simp only [P, map_sum, _root_.map_mul, aeval_C, _root_.map_pow, aeval_X, one_pow,
      _root_.mul_one, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
  have hneg : -v = inl (-z) ⊗ₜ[A] x := by
    dsimp only [v]
    rw [← neg_tmul, ← inl_neg]
  have hv : (-v) ^ n = 0 := by
    rw [hneg, Algebra.TensorProduct.tmul_pow, inl_pow]
    rw [neg_pow z, hz, mul_zero, inl_zero, zero_tmul]
  -- The geometric sum in `-v` inverts `1 + v` in this truncated coefficient ring.
  have hgeom : (1 + v) * (∑ j ∈ range n, (-v) ^ j) = 1 := by
    simpa only [sub_neg_eq_add, hv, sub_zero] using mul_neg_geom_sum (-v) n
  have hT : T = (∑ j ∈ range n, (-v) ^ j) * w := by
    rw [Finset.sum_mul (range n) (fun j ↦ (-v) ^ j) w]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    -- Multiplication by `w` places each power in the infinitesimal summand.
    rw [hneg, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [inl_pow, inl_mul_inr, smul_eq_mul, mul_one, pow_succ x]
  have hfac : (1 + v) * (1 + T) = (inl z + inr 1) ⊗ₜ[A] x + 1 := by
    calc
      _ = 1 + v + (1 + v) * T := by rw [mul_add, mul_one (1 + v)]
      _ = 1 + v + w := by
        rw [hT, ← mul_assoc (1 + v) (∑ j ∈ range n, (-v) ^ j) w, hgeom, one_mul w]
      _ = _ := by rw [add_tmul]; exact add_rotate 1 v w
  have hQ : F (1 + T) = 1 + inr (aeval z Q) := by
    dsimp only [F, T]
    rw [D.rid_toFun_one_add_sum_inr_tmul (range n) (fun j ↦ (-z) ^ j) (fun j ↦ x ^ (j + 1))]
    apply congrArg fun t : B ↦ (1 : B[ε]) + inr t
    simp only [Q, map_sum, _root_.map_mul, aeval_C, _root_.map_pow, aeval_X,
      _root_.map_neg, _root_.map_one]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [neg_pow z]
    ring
  have hmul : F (1 + v) * F (1 + T) = F ((inl z + inr 1) ⊗ₜ[A] x + 1) := by
    rw [← hfac]
    simp only [F, D.isMultiplicative.toFun_mul, _root_.map_mul]
  have hs := congrArg snd hmul
  have he : (inr (1 : B) : B[ε]) ^ 2 = 0 := by rw [pow_two, inr_mul_inr]
  rw [add_comm (1 : B[ε] ⊗[A] R) v, hF (inl z), hF, hQ, aeval_add_of_sq_eq_zero P _ _ he] at hs
  have hinl (p : A[X]) : aeval (inl z : B[ε]) p = inl (aeval z p) :=
    aeval_algHom_apply (inlAlgHom A B B) z p
  simp only [hinl, snd_add, DualNumber.snd_mul, fst_inl, fst_add, fst_one, fst_inr,
    add_zero, snd_inl, snd_one, snd_inr, zero_add, mul_zero, mul_one] at hs
  exact hs.symm

/-- **Integral Newton identities** for a Chenevier determinant. For every `k`,
`k Λₖ(x) = ∑_{j=0}^{k-1} (-1)^j Λ_{k-1-j}(x) Tr(x^(j+1))`.
No factorial or integer is assumed invertible. See Chenevier, Example 1.11(ii). -/
theorem mul_charCoeff_eq_sum_trace_pow (D : Determinant A R d) (x : R) (k : ℕ) :
    (k : A) * D.charCoeff k x =
      ∑ j ∈ range k, (-1) ^ j * D.charCoeff (k - (j + 1)) x * D.trace (x ^ (j + 1)) := by
  cases k with
  | zero => simp
  | succ k =>
    let P : A[X] := ∑ i ∈ range (d + 1), C (D.charCoeff i x) * X ^ i
    let Q : A[X] := ∑ j ∈ range (k + 1), C ((-1) ^ j * D.trace (x ^ (j + 1))) * X ^ j
    -- Reducing modulo `X^(k+1)` retains the coefficient of `X^k`.
    let f : A[X] := X ^ (k + 1)
    have hz : AdjoinRoot.root f ^ (k + 1) = 0 := by
      rw [← AdjoinRoot.mk_X, ← _root_.map_pow, AdjoinRoot.mk_eq_zero]
    have h : f ∣ derivative P - P * Q := by
      apply AdjoinRoot.mk_eq_mk.mp
      rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq, _root_.map_mul]
      exact D.aeval_derivative_sum_charCoeff x hz
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp h) k (Nat.lt_succ_self k)
    rw [mul_comm P Q] at hcoeff
    simp only [coeff_sub, sub_eq_zero, coeff_derivative, coeff_mul] at hcoeff
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j i ↦ Q.coeff j * P.coeff i)] at hcoeff
    have hP (i : ℕ) : P.coeff i = D.charCoeff i x := by
      simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
      split
      · rfl
      · rw [D.charCoeff_eq_zero (by lia)]
    rw [hP, mul_comm, ← Nat.cast_succ] at hcoeff
    refine hcoeff.trans (Finset.sum_congr rfl fun j hj ↦ ?_)
    have hQ : Q.coeff j = (-1) ^ j * D.trace (x ^ (j + 1)) := by
      simp only [Q, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, ite_eq_left hj]
    rw [hP, hQ, Nat.succ_sub_succ_eq_sub]
    ring

end TauCeti.Determinant
