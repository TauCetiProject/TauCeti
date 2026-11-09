/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Rescaling power series

This file records general facts about Mathlib's coefficientwise rescaling
`PowerSeries.rescale` of power series.

A series `f = a X + a₂ X² + ⋯` without constant term, rescaled by a multiple `c` of its linear
coefficient `a`, is divisible by `a c`, with a quotient whose linear coefficient is `1`:

`f(c X) = a c · g(X)`, `g(X) = X + a₂ (c / a) X² + a₃ (c / a) c X³ + ⋯`.

Over a complete local ring, `g` then has a compositional inverse, so the values of `f` on `c I`
are exactly `a c I` for an adic ideal `I`. This is how multiplication by an integer `n` on a
formal group is analysed deep inside the maximal ideal of a discrete valuation ring.

## Main results

* `PowerSeries.rescale_C`: rescaling the variable fixes constant power series.
* `PowerSeries.exists_rescale_eq_C_mul`: `f(c X) = a c · g(X)` with `g(X) = X + ⋯` when `f` has no
  constant term and its linear coefficient `a` divides `c`.
* `PowerSeries.coeff_multiset_prod_rescale_C_mul_rescale`: replacing `Q(t)` by `a Q(b t)`
  multiplies the coefficient of `tᵏ` in `∏_{x ∈ s} Q(x t)` by `a ^ |s| bᵏ`.
-/

public section

namespace PowerSeries

/-- Rescaling the power-series variable fixes constant power series. -/
@[simp]
theorem rescale_C {R : Type*} [CommSemiring R] (a b : R) :
    rescale a (C b) = C b := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

/-- A series without constant term, rescaled by a multiple `c` of its linear coefficient `a`, is
`a c` times a series of the form `X + ⋯`: `f(c X) = a c · g(X)`. -/
theorem exists_rescale_eq_C_mul {R : Type*} [CommSemiring R] {f : R⟦X⟧}
    (hf : constantCoeff f = 0) {c : R} (hc : coeff 1 f ∣ c) :
    ∃ g : R⟦X⟧, constantCoeff g = 0 ∧ coeff 1 g = 1 ∧
      rescale c f = C (coeff 1 f * c) * g := by
  obtain ⟨d, hd⟩ := hc
  refine ⟨mk fun i ↦ if i = 0 then 0 else if i = 1 then 1 else coeff i f * d * c ^ (i - 2),
    by simp [← coeff_zero_eq_constantCoeff_apply], by simp, ?_⟩
  ext i
  rw [coeff_rescale, coeff_C_mul, coeff_mk]
  rcases i with _ | _ | i
  · simp [hf]
  · simp [mul_comm]
  · simp only [show i + 1 + 1 ≠ 0 by omega, show i + 1 + 1 ≠ 1 by omega, ↓reduceIte,
      show i + 1 + 1 - 2 = i by omega, hd]
    ring

/-- **Homogeneity of `∏ Q(x t)`**: replacing `Q(t)` by `a Q(b t)` multiplies the coefficient of
`tᵏ` in `∏_{x ∈ s} Q(x t)` by `a ^ |s| bᵏ`. -/
theorem coeff_multiset_prod_rescale_C_mul_rescale {R : Type*} [CommSemiring R] (a b : R)
    (Q : PowerSeries R) (s : Multiset R) (k : ℕ) :
    coeff k (s.map fun x => rescale x (C a * rescale b Q)).prod =
      a ^ s.card * b ^ k * coeff k (s.map fun x => rescale x Q).prod := by
  have h : (s.map fun x => rescale x (C a * rescale b Q)).prod =
      C (a ^ s.card) * rescale b (s.map fun x => rescale x Q).prod := by
    simp [Multiset.prod_map_mul, map_multiset_prod, Multiset.map_map, rescale_rescale, mul_comm]
  rw [h, coeff_C_mul, coeff_rescale, mul_assoc]

end PowerSeries
