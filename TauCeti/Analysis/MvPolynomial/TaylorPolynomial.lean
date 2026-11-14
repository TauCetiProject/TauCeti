/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.Taylor.Polynomial
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# Multivariate Taylor polynomials of bounded-degree polynomial functions

On a finite-dimensional real Euclidean space `EuclideanSpace ℝ ι`,
`TauCeti.taylorPolynomial ℝ m u y` belongs to the bounded-degree polynomial space
`TauCeti.polynomialsDegLE ι m` for every map `u : EuclideanSpace ℝ ι → ℝ` and every center `y`
(`TauCeti.taylorPolynomial_mem_polynomialsDegLE`), without any regularity assumption on `u`.

Conversely, every `q ∈ polynomialsDegLE ι m` is smooth of every order
(`TauCeti.contDiff_of_mem_polynomialsDegLE`), its directional derivatives lower the degree bound
(`TauCeti.fderiv_apply_mem_polynomialsDegLE`, `TauCeti.iteratedFDerivAlong_mem_polynomialsDegLE`),
every iterated Fréchet derivative of order strictly above `m` vanishes identically
(`TauCeti.iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE`), and therefore `q` is reproduced by its
`m`-th Taylor polynomial about any expansion center `y`
(`TauCeti.taylorPolynomial_eq_self_of_mem_polynomialsDegLE`).

## Main results

* `TauCeti.hasFDerivAt_polynomialEvalₗ`, `TauCeti.fderiv_polynomialEvalₗ_apply`: the Fréchet
  derivative of `polynomialEvalₗ ι p` in terms of formal partial derivatives `MvPolynomial.pderiv`.
* `TauCeti.contDiff_of_mem_polynomialsDegLE`: bounded-degree polynomial functions are `C^n` for all
  `n : ℕ∞ω`.
* `TauCeti.iteratedFDerivAlong_mem_polynomialsDegLE`: differentiating along `k` directions maps
  `polynomialsDegLE ι m` into `polynomialsDegLE ι (m - k)`.
* `TauCeti.iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE`: for `q ∈ polynomialsDegLE ι m` and
  `m < k`, `iteratedFDeriv ℝ k q = 0`.
* `TauCeti.taylorPolynomial_mem_polynomialsDegLE`: `taylorPolynomial ℝ m u y ∈ polynomialsDegLE ι m`
  for every `u` and `y`.
* `TauCeti.taylorPolynomial_eq_self_of_mem_polynomialsDegLE`: `taylorPolynomial ℝ m q y = q` for
  every `q ∈ polynomialsDegLE ι m` and every `y`.
-/

public section

noncomputable section

open Nat MvPolynomial
open scoped ContDiff

namespace TauCeti

section Fintype

variable {ι : Type*} [Fintype ι]

/-- Formal evaluation `polynomialEvalₗ ι p` is smooth of every order `n : ℕ∞ω`. -/
theorem contDiff_polynomialEvalₗ (p : MvPolynomial ι ℝ) {n : ℕ∞ω} :
    ContDiff ℝ n (polynomialEvalₗ ι p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [polynomialEvalₗ_C]
    exact contDiff_const
  | add p q hp hq =>
    rw [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hmul : polynomialEvalₗ ι (p * X i) = fun x ↦ polynomialEvalₗ ι p x * x i := by
      ext x
      simp
    rw [hmul]
    exact hp.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- Every bounded-degree polynomial function on `EuclideanSpace ℝ ι` is smooth of every order. -/
theorem contDiff_of_mem_polynomialsDegLE {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) {n : ℕ∞ω} :
    ContDiff ℝ n q := by
  obtain ⟨p, -, rfl⟩ := (mem_polynomialsDegLE_iff ι).1 hq
  exact contDiff_polynomialEvalₗ p

/-- The Fréchet derivative of `polynomialEvalₗ ι p` at `x` is the linear combination of coordinate
projections weighted by the formal partial derivatives `pderiv i p` evaluated at `x`. -/
theorem hasFDerivAt_polynomialEvalₗ (p : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (polynomialEvalₗ ι p)
      (∑ i : ι, polynomialEvalₗ ι (pderiv i p) x •
        (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ)) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h0 : (∑ i : ι, polynomialEvalₗ ι (pderiv i (C a : MvPolynomial ι ℝ)) x •
        (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ)) = 0 := by
      simp
    rw [polynomialEvalₗ_C, h0]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    rw [map_add]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hmul : polynomialEvalₗ ι (p * X j) = fun y ↦ polynomialEvalₗ ι p y * y j := by
      ext y
      simp
    rw [hmul]
    refine (hp.mul (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt).congr_fderiv ?_
    ext v
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, apply_ite (eval (fun i ↦ x i)),
      add_mul, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

/-- Evaluating the Fréchet derivative of `polynomialEvalₗ ι p` at `x` in direction `v` gives
`∑ i, v i * polynomialEvalₗ ι (pderiv i p) x`. -/
theorem fderiv_polynomialEvalₗ_apply (p : MvPolynomial ι ℝ) (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (polynomialEvalₗ ι p) x v = ∑ i : ι, v i * polynomialEvalₗ ι (pderiv i p) x := by
  rw [(hasFDerivAt_polynomialEvalₗ p x).fderiv]
  simp [mul_comm]

end Fintype

/-- Differentiating a polynomial function of degree at most `m` in a fixed direction `v` yields a
polynomial function of degree at most `m - 1`. -/
theorem fderiv_apply_mem_polynomialsDegLE {ι : Type*} [Finite ι] {m : ℕ}
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m) (v : EuclideanSpace ℝ ι) :
    (fun x ↦ fderiv ℝ q x v) ∈ polynomialsDegLE ι (m - 1) := by
  have := Fintype.ofFinite ι
  obtain ⟨p, hp, rfl⟩ := (mem_polynomialsDegLE_iff ι).1 hq
  have hfun : (fun x ↦ fderiv ℝ (polynomialEvalₗ ι p) x v) =
      ∑ i : ι, v i • polynomialEvalₗ ι (pderiv i p) := by
    ext x
    simp [fderiv_polynomialEvalₗ_apply]
  rw [hfun]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ (v i) ?_
  rw [polynomialEvalₗ_mem_polynomialsDegLE_iff]
  exact (MvPolynomial.totalDegree_pderiv_le i p).trans (Nat.sub_le_sub_right hp 1)

section Taylor

variable {ι : Type*} [Fintype ι]

/-- Differentiating a polynomial function of degree at most `m` along a list `vs` of directions
yields a polynomial function of degree at most `m - vs.length`. -/
theorem iteratedFDerivAlong_mem_polynomialsDegLE {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) (vs : List (EuclideanSpace ℝ ι)) :
    iteratedFDerivAlong ℝ vs q ∈ polynomialsDegLE ι (m - vs.length) := by
  induction vs with
  | nil => simpa using hq
  | cons v vs ih =>
    rw [List.length_cons, ← Nat.sub_sub, iteratedFDerivAlong_cons]
    exact fderiv_apply_mem_polynomialsDegLE ih v

/-- Every iterated directional derivative of length strictly greater than `m` vanishes on
`polynomialsDegLE ι m`. -/
theorem iteratedFDerivAlong_eq_zero_of_mem_polynomialsDegLE {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) {vs : List (EuclideanSpace ℝ ι)} (hvs : m < vs.length) :
    iteratedFDerivAlong ℝ vs q = 0 := by
  cases vs with
  | nil => simp at hvs
  | cons v ws =>
    have hmw : m - ws.length = 0 := Nat.sub_eq_zero_of_le (Nat.lt_succ_iff.mp hvs)
    have hmem0 : iteratedFDerivAlong ℝ ws q ∈ polynomialsDegLE ι 0 :=
      hmw ▸ iteratedFDerivAlong_mem_polynomialsDegLE hq ws
    obtain ⟨c, hc⟩ := (mem_polynomialsDegLE_zero_iff ι).1 hmem0
    rw [iteratedFDerivAlong_cons, hc]
    ext x
    simp

/-- Every iterated Fréchet derivative of order strictly greater than `m` vanishes identically on
`polynomialsDegLE ι m`. -/
theorem iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE {m k : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) (hmk : m < k) :
    iteratedFDeriv ℝ k q = 0 := by
  ext x v
  rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv (contDiff_of_mem_polynomialsDegLE hq) v x]
  exact congrFun
    (iteratedFDerivAlong_eq_zero_of_mem_polynomialsDegLE hq (vs := List.ofFn v)
      (by simpa using hmk)) x

/-- For any map `u : EuclideanSpace ℝ ι → ℝ` (with no regularity assumptions) and any expansion
point `y`, the `m`-th Taylor polynomial `taylorPolynomial ℝ m u y` belongs to
`polynomialsDegLE ι m`. -/
theorem taylorPolynomial_mem_polynomialsDegLE (m : ℕ) (u : EuclideanSpace ℝ ι → ℝ)
    (y : EuclideanSpace ℝ ι) :
    taylorPolynomial ℝ m u y ∈ polynomialsDegLE ι m := by
  have hfun : taylorPolynomial ℝ m u y =
      ∑ j ∈ Finset.range (m + 1), (j ! : ℝ)⁻¹ •
        fun x ↦ iteratedFDeriv ℝ j u y (fun _ ↦ x - y) := by
    ext x
    simp [taylorPolynomial_apply]
  rw [hfun]
  refine Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ ?_
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine polynomialsDegLE_mono ι hjle ?_
  have hhom : (fun x : EuclideanSpace ℝ ι ↦ iteratedFDeriv ℝ j u y (fun _ ↦ x)) ∈
      polynomialsDegLE ι j := by
    simpa using (iteratedFDeriv ℝ j u y).toMultilinearMap.apply_const_mem_polynomialsDegLE
  exact comp_sub_mem_polynomialsDegLE y hhom

/-- Every polynomial function of degree at most `m` is reproduced by its `m`-th Taylor polynomial
about any expansion center `y`. -/
@[simp]
theorem taylorPolynomial_eq_self_of_mem_polynomialsDegLE {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) (y : EuclideanSpace ℝ ι) :
    taylorPolynomial ℝ m q y = q :=
  taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero
    (contDiff_of_mem_polynomialsDegLE hq)
    (iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE hq (Nat.lt_succ_self m)) y

end Taylor

end TauCeti
