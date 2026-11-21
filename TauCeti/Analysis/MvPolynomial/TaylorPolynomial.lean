/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.Taylor.Polynomial
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace

/-!
# Multivariate Taylor polynomials of bounded-degree polynomial functions

On a finite-dimensional real Euclidean space `EuclideanSpace ℝ ι`,
`TauCeti.taylorPolynomial ℝ m u y` belongs to the bounded-degree polynomial space
`TauCeti.polynomialsDegLE ι m` for every map `u : EuclideanSpace ℝ ι → ℝ` and every center `y`
(`TauCeti.taylorPolynomial_mem_polynomialsDegLE`), without any regularity assumption on `u`.

Conversely, by `TauCeti.Analysis.MvPolynomial.PolynomialSpace`, every `q ∈ polynomialsDegLE ι m`
is smooth of every order (`TauCeti.contDiff_of_mem_polynomialsDegLE`), its directional derivatives
lower the degree bound (`TauCeti.fderiv_apply_mem_polynomialsDegLE`,
`TauCeti.iteratedFDerivAlong_mem_polynomialsDegLE`), every iterated Fréchet derivative of order
strictly above `m` vanishes identically (`TauCeti.iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE`),
and therefore `q` is reproduced by its `m`-th Taylor polynomial about any expansion center `y`
(`TauCeti.taylorPolynomial_eq_self_of_mem_polynomialsDegLE`).

## Main results

* `TauCeti.iteratedFDerivAlong_mem_polynomialsDegLE`: differentiating along `k` directions maps
  `polynomialsDegLE ι m` into `polynomialsDegLE ι (m - k)`.
* `TauCeti.iteratedFDerivAlong_eq_zero_of_mem_polynomialsDegLE`: for `q ∈ polynomialsDegLE ι m`
  and `m < vs.length`, `iteratedFDerivAlong ℝ vs q = 0`.
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
    obtain ⟨c, hc⟩ := (mem_polynomialsDegLE_zero_iff ι).1
      (hmw ▸ iteratedFDerivAlong_mem_polynomialsDegLE hq ws)
    rw [iteratedFDerivAlong_cons, hc]; ext; simp

/-- For any map `u : EuclideanSpace ℝ ι → ℝ` (with no regularity assumptions) and any expansion
point `y`, the `m`-th Taylor polynomial `taylorPolynomial ℝ m u y` belongs to
`polynomialsDegLE ι m`. -/
theorem taylorPolynomial_mem_polynomialsDegLE (m : ℕ) (u : EuclideanSpace ℝ ι → ℝ)
    (y : EuclideanSpace ℝ ι) :
    taylorPolynomial ℝ m u y ∈ polynomialsDegLE ι m := by
  convert Submodule.sum_mem (polynomialsDegLE ι m) (t := Finset.range (m + 1)) fun j hj ↦
    Submodule.smul_mem _ ((j ! : ℝ)⁻¹) <|
      polynomialsDegLE_mono ι (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) <|
        comp_sub_mem_polynomialsDegLE y (by
          simpa using (iteratedFDeriv ℝ j u y).toMultilinearMap.apply_const_mem_polynomialsDegLE)
    using 1
  ext x
  simp [taylorPolynomial_apply]

/-- Every polynomial function of degree at most `m` is reproduced by its `m`-th Taylor polynomial
about any expansion center `y`. -/
@[simp]
theorem taylorPolynomial_eq_self_of_mem_polynomialsDegLE {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) (y : EuclideanSpace ℝ ι) :
    taylorPolynomial ℝ m q y = q :=
  taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero
    (contDiff_of_mem_polynomialsDegLE hq)
    (iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE (Nat.lt_succ_self m) hq) y

end Taylor

end TauCeti
