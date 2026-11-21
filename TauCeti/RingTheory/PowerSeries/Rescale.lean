/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Analysis.Normed.Monoid.MulUnit

/-!
# Rescaling power series

This file records general facts about Mathlib's coefficientwise rescaling
`PowerSeries.rescale` of power series.

A series `f = a X + a₂ X² + ⋯` without constant term, rescaled by a multiple `c` of its linear
coefficient `a`, is divisible by `a c`, with a quotient whose linear coefficient is `1`:

`f(c X) = a c · g(X)`, `g(X) = X + a₂ (c / a) X² + a₃ (c / a) c X³ + ⋯`.

Over a complete local ring, `g` then has a compositional inverse, so the values of `f` on `c I`
are exactly `a c I` for an adic ideal `I`. This is how multiplication by an integer `n` on a
formal group is analysed deep inside the maximal ideal of a discrete valuation ring. When `u` is a
multiplicative unit (`TauCeti.IsNormMulUnit`) with `‖u‖ s = r`, rescaling by `u` transports
weighted coefficient norms at radius `r` to weighted coefficient norms at radius `s`.

## Main results

* `PowerSeries.rescale_C`: rescaling the variable fixes constant power series.
* `PowerSeries.rescale_neg_one_rescale_neg_one`: rescaling the variable by `-1` is an involution.
* `PowerSeries.constantCoeff_rescale`: rescaling the variable keeps the constant coefficient.
* `PowerSeries.constantCoeff_evalNegHom`: negating the variable keeps the constant coefficient.
* `PowerSeries.rescale_smul`, `PowerSeries.evalNegHom_smul`: rescaling and negating the variable
  commute with scalar multiplication.
* `PowerSeries.exists_rescale_eq_C_mul`: `f(c X) = a c · g(X)` with `g(X) = X + ⋯` when `f` has no
  constant term and its linear coefficient `a` divides `c`.
* `PowerSeries.coeff_multiset_prod_rescale_C_mul_rescale`: replacing `Q(t)` by `a Q(b t)`
  multiplies the coefficient of `tᵏ` in `∏_{x ∈ s} Q(x t)` by `a ^ |s| bᵏ`.
* `PowerSeries.norm_coeff_rescale_mul_pow`: rescaling by a multiplicative unit `u` with
  `‖u‖ s = r` identifies `‖coeff n (rescale u f)‖ sⁿ` with `‖coeff n f‖ rⁿ`.
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

/-- Rescaling the power-series variable by `-1` is an involution: `F(-(-X)) = F(X)`. -/
@[simp]
theorem rescale_neg_one_rescale_neg_one {R : Type*} [CommRing R] (F : R⟦X⟧) :
    rescale (-1) (rescale (-1) F) = F := by
  simp [rescale_rescale]

/-- Rescaling the variable does not change the constant coefficient. -/
@[simp]
theorem constantCoeff_rescale {R : Type*} [CommSemiring R] (a : R) (f : R⟦X⟧) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp

/-- Negating the power-series variable does not change the constant coefficient. -/
@[simp]
theorem constantCoeff_evalNegHom {R : Type*} [CommRing R] (f : R⟦X⟧) :
    constantCoeff (evalNegHom f) = constantCoeff f := by
  rw [evalNegHom, constantCoeff_rescale]

/-- Rescaling commutes with scalar multiplication. -/
@[simp]
theorem rescale_smul {R S : Type*} [Semiring R] [CommSemiring S] [Module R S]
    [SMulCommClass R S S] (a : S) (r : R) (f : S⟦X⟧) :
    rescale a (r • f) = r • rescale a f := by
  ext n
  simp [coeff_rescale, mul_smul_comm]

/-- Negating the power-series variable commutes with scalar multiplication. -/
@[simp]
theorem evalNegHom_smul {R S : Type*} [Semiring R] [CommRing S] [Module R S]
    [SMulCommClass R S S] (r : R) (f : S⟦X⟧) :
    evalNegHom (r • f) = r • evalNegHom f :=
  rescale_smul (-1) r f

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

/-- Rescaling by a multiplicative unit `u` preserves weighted coefficient norms when the weight is
changed by `‖u‖`: if `‖u‖ * s = r`, then `‖coeff n (rescale u f)‖ * s ^ n = ‖coeff n f‖ * r ^ n`. -/
theorem norm_coeff_rescale_mul_pow {R : Type*} [CommSemiring R] [Norm R] (f : R⟦X⟧) {u : R}
    (hu : TauCeti.IsNormMulUnit u) {r s : ℝ} (hrs : ‖u‖ * s = r) (n : ℕ) :
    ‖coeff n (rescale u f)‖ * s ^ n = ‖coeff n f‖ * r ^ n := by
  rw [coeff_rescale]
  have hpow (m : ℕ) : ‖u ^ m * coeff n f‖ * s ^ m = ‖coeff n f‖ * r ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc ‖u ^ (m + 1) * coeff n f‖ * s ^ (m + 1)
          = (‖u ^ m * coeff n f‖ * s ^ m) * (‖u‖ * s) := by
            rw [pow_succ', mul_assoc, hu.norm_mul, pow_succ']
            ring
        _ = ‖coeff n f‖ * r ^ (m + 1) := by
            rw [ih, hrs, pow_succ]
            ring
  exact hpow n

end PowerSeries
