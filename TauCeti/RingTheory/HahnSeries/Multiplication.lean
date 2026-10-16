/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Powers of Hahn series, and scalars commuting with multiplication

Over a domain, taking a power multiplies the order and raises the leading coefficient to that
power. These formulas detect whether a leading pole term can be cancelled by a power.

The order formula allows semiring coefficients; Mathlib's `HahnSeries.addVal` requires ring
coefficients, so its `AddValuation.map_pow` does not cover this generality.

The formulas are `TauCeti.hahnSeries_leadingCoeff_pow n` and
`TauCeti.hahnSeries_orderTop_pow n`; both are also simplification lemmas. The exponent is
explicit, and the series is inferred from the equality being rewritten.

With the typeclasses below in scope, use the qualified names as follows:

```lean
example (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n :=
  TauCeti.hahnSeries_leadingCoeff_pow n (f := f)

example [Nontrivial R] (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).orderTop = n • f.orderTop :=
  TauCeti.hahnSeries_orderTop_pow n (f := f)
```

This file also records that coefficientwise scalar multiplication commutes with multiplication of
Hahn series (`TauCeti.hahnSeries_smulCommClass`). Mathlib provides this for the action of Hahn
series on Hahn modules, and for Hahn series through their algebra structure; but the default
algebra structure on Laurent series `R⸨X⸩` comes from `R⟦X⟧` and is not definitionally the
coefficientwise one, so for instance the `R⸨X⸩`-module structure on `R`-derivations of `R⸨X⸩`
needs this instance.
-/

public section

namespace TauCeti

/-- Coefficientwise scalar multiplication commutes with multiplication of Hahn series. -/
instance hahnSeries_smulCommClass {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [CommSemiring R] :
    SMulCommClass R (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_comm r x y := by
    simp only [← HahnSeries.C_mul_eq_smul, smul_eq_mul, mul_left_comm]

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- The leading coefficient of a power is the power of the leading coefficient. -/
@[simp]
theorem hahnSeries_leadingCoeff_pow (n : ℕ) {f : HahnSeries Γ R} :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- The order of a power is the corresponding multiple of the order, including at zero. -/
@[simp]
theorem hahnSeries_orderTop_pow [Nontrivial R] (n : ℕ) {f : HahnSeries Γ R} :
    (f ^ n).orderTop = n • f.orderTop := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_nsmul]

end TauCeti
