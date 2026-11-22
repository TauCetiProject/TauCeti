/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace

/-!
# Multivariate Taylor polynomials

For a function `u : E → F` between real normed spaces, the **Taylor polynomial of degree `m` of
`u` centred at `y`** is

`T^m_y u (x) = ∑_{k ≤ m} (1/k!) D^k u(y) (x - y, …, x - y)`,

where `D^k u(y) = iteratedFDeriv ℝ k u y`. This file defines it as `TauCeti.taylorPolynomial m u y`
and records its basic properties:

* the **integral form of the remainder**: if `u` is `C^(m + 1)` along the segment from `y` to `x`,
  then
  `u x - T^m_y u x = (1/m!) ∫₀¹ (1 - t)^m D^(m+1) u(y + t (x - y)) (x - y, …, x - y) dt`;
* on `EuclideanSpace ℝ ι`, `T^m_y u` is a polynomial function of total degree at most `m`, for
  every `u` and `y`;
* a polynomial function of total degree at most `m` is its own Taylor polynomial of degree `m` at
  every centre. As a consequence, the space `TauCeti.polynomialsDegLE ι m` of such functions is
  invariant under translations.

Averaging `T^m_y u` over centres `y` in a ball against a bump function gives the averaged Taylor
polynomial used in polynomial approximation of Sobolev functions (Bramble–Hilbert estimates); the
integral remainder is the starting point of the Sobolev representation formula for the error.

## Main declarations

* `TauCeti.taylorPolynomial`: the Taylor polynomial of degree `m` of `u` centred at `y`.
* `TauCeti.sub_taylorPolynomial_eq_integral`: the integral form of the remainder.
* `TauCeti.taylorPolynomial_mem_polynomialsDegLE`: on Euclidean space the Taylor polynomial of
  degree `m` lies in `polynomialsDegLE ι m`.
* `TauCeti.taylorPolynomial_eq_of_mem_polynomialsDegLE`: polynomial functions of degree at most `m`
  are fixed by taking the Taylor polynomial of degree `m`.
* `TauCeti.comp_add_mem_polynomialsDegLE`: translation invariance of `polynomialsDegLE ι m`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer (2008), §4.1.
-/

public section

noncomputable section

open scoped Nat

namespace TauCeti

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **Taylor polynomial** of degree `m` of `u : E → F` centred at `y`, as a function of `x`:
`∑_{k ≤ m} (1/k!) D^k u(y) (x - y, …, x - y)`, with `D^k u(y) = iteratedFDeriv ℝ k u y`. -/
def taylorPolynomial (m : ℕ) (u : E → F) (y : E) : E → F := fun x ↦
  ∑ k ∈ Finset.range (m + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k u y (fun _ ↦ x - y)

theorem taylorPolynomial_apply (m : ℕ) (u : E → F) (y x : E) :
    taylorPolynomial m u y x =
      ∑ k ∈ Finset.range (m + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k u y (fun _ ↦ x - y) :=
  (rfl)

/-- The Taylor polynomial of degree `0` is the constant function with value `u y`. -/
@[simp]
theorem taylorPolynomial_zero (u : E → F) (y : E) : taylorPolynomial 0 u y = fun _ ↦ u y := by
  ext x
  simp [taylorPolynomial_apply]

/-- Raising the degree by one adds the next term of the Taylor expansion. -/
theorem taylorPolynomial_succ (m : ℕ) (u : E → F) (y x : E) :
    taylorPolynomial (m + 1) u y x = taylorPolynomial m u y x +
      ((m + 1)! : ℝ)⁻¹ • iteratedFDeriv ℝ (m + 1) u y (fun _ ↦ x - y) := by
  rw [taylorPolynomial_apply, Finset.sum_range_succ, ← taylorPolynomial_apply]

/-- A Taylor polynomial takes the value `u y` at its centre `y`. -/
@[simp]
theorem taylorPolynomial_self (m : ℕ) (u : E → F) (y : E) : taylorPolynomial m u y y = u y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [taylorPolynomial_succ, ih, sub_self,
      (iteratedFDeriv ℝ (m + 1) u y).map_coord_zero 0 rfl, smul_zero, add_zero]

/-- **Taylor's formula with integral remainder.** If `u` is `C^(m + 1)` at every point of the
segment from `y` to `x`, then
`u x - T^m_y u x = (1/m!) ∫₀¹ (1 - t)^m D^(m+1) u(y + t (x - y)) (x - y, …, x - y) dt`. -/
theorem sub_taylorPolynomial_eq_integral [CompleteSpace F] {m : ℕ} {u : E → F} {y x : E}
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) u (y + t • (x - y))) :
    u x - taylorPolynomial m u y x = (m ! : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
      (1 - t) ^ m • iteratedFDeriv ℝ (m + 1) u (y + t • (x - y)) (fun _ ↦ x - y) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv hu
  rw [add_sub_cancel] at h
  rw [taylorPolynomial_apply]
  exact sub_eq_of_eq_add' h

end Normed

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- A polynomial function of total degree at most `m` on `EuclideanSpace ℝ ι` is its own Taylor
polynomial of degree `m`, at every centre `y`. -/
theorem taylorPolynomial_eq_of_mem_polynomialsDegLE {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ}
    (hq : q ∈ polynomialsDegLE ι m) (y : EuclideanSpace ℝ ι) :
    taylorPolynomial m q y = q := by
  ext x
  have hcd : ContDiff ℝ (m + 1) q := contDiff_of_mem_polynomialsDegLE hq
  have h := sub_taylorPolynomial_eq_integral (m := m) (y := y) (x := x)
    fun _ _ ↦ hcd.contDiffAt
  rw [iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE (Nat.lt_succ_self m) hq] at h
  have h0 : q x - taylorPolynomial m q y x = 0 := by simpa using h
  exact (sub_eq_zero.1 h0).symm

omit [Fintype ι] in
/-- **Translation invariance.** Translating a polynomial function of total degree at most `m` on
`EuclideanSpace ℝ ι` gives a polynomial function of total degree at most `m`. -/
theorem comp_add_mem_polynomialsDegLE [Finite ι] {m : ℕ}
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m) (c : EuclideanSpace ℝ ι) :
    (fun x ↦ q (x + c)) ∈ polynomialsDegLE ι m := by
  let := Fintype.ofFinite ι
  -- Expand `q` around `c`: `q (x + c) = ∑_{k ≤ m} (1/k!) D^k q(c) (x, …, x)`.
  have hexp : (fun x ↦ q (x + c)) =
      ∑ k ∈ Finset.range (m + 1), (k ! : ℝ)⁻¹ • fun x ↦ iteratedFDeriv ℝ k q c fun _ ↦ x := by
    ext x
    conv_lhs => rw [← taylorPolynomial_eq_of_mem_polynomialsDegLE hq c]
    simp [taylorPolynomial_apply]
  rw [hexp]
  exact Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ <|
    polynomialsDegLE_mono ι (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) <| by
      simpa using (iteratedFDeriv ℝ k q c).toMultilinearMap.apply_const_mem_polynomialsDegLE

/-- On `EuclideanSpace ℝ ι`, the Taylor polynomial of degree `m` of any function, at any centre,
is a polynomial function of total degree at most `m`. -/
theorem taylorPolynomial_mem_polynomialsDegLE (m : ℕ) (u : EuclideanSpace ℝ ι → ℝ)
    (y : EuclideanSpace ℝ ι) :
    taylorPolynomial m u y ∈ polynomialsDegLE ι m := by
  have hexp : taylorPolynomial m u y = ∑ k ∈ Finset.range (m + 1),
      (k ! : ℝ)⁻¹ • fun x ↦ iteratedFDeriv ℝ k u y fun _ ↦ x + -y := by
    ext x
    simp [taylorPolynomial_apply, sub_eq_add_neg]
  rw [hexp]
  exact Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ <|
    polynomialsDegLE_mono ι (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) <|
      comp_add_mem_polynomialsDegLE (by
        simpa using (iteratedFDeriv ℝ k u y).toMultilinearMap.apply_const_mem_polynomialsDegLE) (-y)

end Euclidean

end TauCeti
