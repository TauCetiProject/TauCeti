/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Twist
public import TauCeti.RingTheory.LaurentSeries.Ramified

/-!
# Rescaling formal Laurent series

For a unit `a` of a commutative semiring `R`, the substitution `f (X) ↦ f (a X)` is an
`R`-algebra automorphism of `R⸨X⸩`. It multiplies the coefficient of `Xⁿ` by the unit `a ^ n`,
for every integer `n`, and extends `PowerSeries.rescale` on power series.

The construction is the twist `HahnSeries.twistEquiv` by the character `n ↦ a ^ n`.
This makes rescaling available without a fraction field or a field of coefficients.

Rescaling an expanded series `f (X ^ d)` by `a` is expansion of the series rescaled by
`a ^ d`. Consequently, rescaling by a `d`-th root of unity fixes every expanded series.

## Main definitions

* `TauCeti.LaurentSeries.rescale`: rescaling by units, as a homomorphism to the algebra
  automorphisms of `R⸨X⸩`.

## Main results

* `TauCeti.LaurentSeries.coeff_rescale`: rescaling multiplies coefficients by powers of `a`.
* `TauCeti.LaurentSeries.rescale_single`: rescaling a monomial.
* `TauCeti.LaurentSeries.rescale_coe`: compatibility with rescaling power series.
* `TauCeti.LaurentSeries.rescale_expand`: compatibility with exponent expansion `X ↦ X ^ d`.
* `TauCeti.LaurentSeries.rescale_expand_of_pow_eq_one`: rescaling by a `d`-th root of unity
  fixes the image of expansion by `d`.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries LaurentSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommSemiring R]

/-- The rescaling `f (X) ↦ f (a X)` of Laurent series by a unit `a`, as an `R`-algebra
automorphism. It multiplies the coefficient of `Xⁿ` by `a ^ n`, and the automorphisms for `a`
and `b` compose to the one for `a * b`. -/
noncomputable def rescale : Rˣ →* (R⸨X⸩ ≃ₐ[R] R⸨X⸩) where
  toFun a := .ofRingEquiv
    (f := @AlgEquiv.toRingEquiv _ _ _ _ _ _
      (HahnSeries.instAlgebra (Γ := ℤ)) (HahnSeries.instAlgebra (Γ := ℤ))
      (twistEquiv (zpowersHom Rˣ a))) fun r ↦ by
    -- Laurent series inherit their algebra structure from power series; Hahn twists use
    -- the coefficientwise algebra structure. Both send scalars to the same constant series.
    ext n
    simp +contextual [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, coeff_single]
  map_one' := AlgEquiv.ext fun f ↦ by
    ext n
    simp
  map_mul' a b := AlgEquiv.ext fun f ↦ by
    ext n
    simp [mul_zpow, mul_assoc]

/-- Rescaling by `a` multiplies the coefficient of `Xⁿ` by `a ^ n`. -/
@[simp]
theorem coeff_rescale (a : Rˣ) (f : R⸨X⸩) (n : ℤ) :
    (rescale a f).coeff n = ↑(a ^ n) * f.coeff n := by
  simp [rescale]

/-- Rescaling sends the monomial `c Xⁿ` to `a ^ n c Xⁿ`. -/
@[simp]
theorem rescale_single (a : Rˣ) (n : ℤ) (c : R) :
    rescale a (single n c) = single n (↑(a ^ n) * c) := by
  ext m
  rcases eq_or_ne m n with rfl | h
  · simp
  · simp [coeff_single_of_ne h]

/-- On power series, rescaling Laurent series is `PowerSeries.rescale`. -/
@[simp]
theorem rescale_coe (a : Rˣ) (f : R⟦X⟧) :
    rescale a (f : R⸨X⸩) = ((PowerSeries.rescale (a : R) f : R⟦X⟧) : R⸨X⸩) := by
  ext n
  rw [coeff_rescale, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · simp
  · rw [PowerSeries.coeff_rescale, ← Units.val_pow_eq_pow_val,
      ← zpow_natCast, Int.natAbs_of_nonneg (not_lt.mp hn)]

/-- Rescaling an expanded series by `a` is expanding the series rescaled by `a ^ d`:
`f ((a X) ^ d) = (f (a ^ d X)) (X ^ d)`. -/
theorem rescale_expand (a : Rˣ) (d : ℕ+) (f : R⸨X⸩) :
    rescale a (expand R d f) = expand R d (rescale (a ^ (d : ℕ)) f) := by
  ext n
  rw [coeff_rescale]
  by_cases hn : (d : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_expand_mul, coeff_expand_mul, coeff_rescale, zpow_mul, zpow_natCast]
  · rw [coeff_expand_of_not_dvd d f hn, coeff_expand_of_not_dvd d _ hn, mul_zero]

/-- Rescaling by a `d`-th root of unity fixes every series expanded by `X ↦ X ^ d`. -/
theorem rescale_expand_of_pow_eq_one {a : Rˣ} {d : ℕ+} (ha : a ^ (d : ℕ) = 1) (f : R⸨X⸩) :
    rescale a (expand R d f) = expand R d f := by
  rw [rescale_expand, ha, map_one, AlgEquiv.one_apply]

end TauCeti.LaurentSeries
