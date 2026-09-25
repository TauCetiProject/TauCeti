/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Evaluation

/-!
# Evaluation of power series and division by `X - C c`

Mathlib evaluates a power series over `R` at a topologically nilpotent point `a` of a complete,
separated, linearly topologized `R`-algebra `S` through `PowerSeries.aeval`. This file records the
values of that evaluation on the generators, `X ↦ a` and `C r ↦ algebraMap R S r`, and performs
division by a linear factor over a ring `A` in which power series can be evaluated at `c`:

```text
f = (X - C c) * divXSubC hc f + C (f(c)),
```

where the quotient `PowerSeries.divXSubC hc f` is the explicit series whose `n`-th coefficient is
the value at `c` of the tail `∑ₖ f_{n+1+k} X^k` of `f`, that is `∑ₖ f_{n+1+k} c^k`. The identity
is checked coefficientwise from the recursion `tailₙ(c) = fₙ + c * tailₙ₊₁(c)`, which is
`PowerSeries.aeval` applied to `tailₙ = X * tailₙ₊₁ + C fₙ`. The divisibility criterion

```text
(X - C c) ∣ f  ↔  f(c) = 0
```

follows: one direction is that `X - C c` evaluates to zero, and the other reads off the
factorization once the remainder `f(c)` vanishes. This is the special case of Weierstrass division
by `X - C c` that a complete local ring such as `ℤ_[p]` uses at a point `c` of its maximal ideal;
the explicit quotient makes the general division theorem unnecessary here.

The evaluability hypothesis `HasEval c` is where the topology enters: it is what makes the tails
of `f` evaluable at `c`, and it already excludes the units. For a unit `c` the series `X - C c`
is a unit of `A⟦X⟧`, so it divides everything, while `f(c)` need not vanish; and a unit is
topologically nilpotent only in the zero ring.

## Main results

* `PowerSeries.aeval_X`, `PowerSeries.aeval_C`: the values of evaluation on the generators.
* `PowerSeries.divXSubC`: the quotient of a power series on division by `X - C c`, with its
  coefficients `PowerSeries.coeff_divXSubC` and their series expansion
  `PowerSeries.hasSum_coeff_divXSubC`.
* `PowerSeries.X_sub_C_mul_divXSubC_add_C_aeval`: the division `f = (X - C c) * q + C (f(c))`.
* `PowerSeries.X_sub_C_mul_divXSubC`: the factorization `f = (X - C c) * q` when `f(c) = 0`.
* `PowerSeries.X_sub_C_dvd_iff_aeval_eq_zero`: divisibility by `X - C c` is vanishing at `c`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Proposition 7.2 (Weierstrass division).
-/

public section

namespace PowerSeries

section Aeval

variable {R S : Type*} [CommRing R] [CommRing S] [UniformSpace R] [UniformSpace S]
  [IsUniformAddGroup R] [IsTopologicalSemiring R] [IsUniformAddGroup S] [T2Space S]
  [CompleteSpace S] [IsTopologicalRing S] [IsLinearTopology S S] [Algebra R S]
  [ContinuousSMul R S] {a : S}

/-- Evaluation at `a` sends `X` to `a`. -/
@[simp]
theorem aeval_X (ha : HasEval a) : aeval ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, aeval_coe, Polynomial.aeval_X]

/-- Evaluation at `a` sends a constant to its image in `S`. -/
@[simp]
theorem aeval_C (ha : HasEval a) (r : R) : aeval ha (C r) = algebraMap R S r := by
  rw [← Polynomial.coe_C, aeval_coe, Polynomial.aeval_C]

end Aeval

section LinearFactor

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [T2Space A] [CompleteSpace A] [IsLinearTopology A A] {c : A}

/-- The quotient of a power series `f` on division by `X - C c`, at a point `c` where power series
can be evaluated: its `n`-th coefficient is the value at `c` of the tail `∑ₖ f_{n+1+k} X^k` of `f`.
The remainder is the constant `f(c)`; see `PowerSeries.X_sub_C_mul_divXSubC_add_C_aeval`. -/
noncomputable def divXSubC (hc : HasEval c) (f : A⟦X⟧) : A⟦X⟧ :=
  mk fun n ↦ aeval hc (mk fun k ↦ coeff (n + 1 + k) f)

/-- The `n`-th coefficient of the quotient is the value at `c` of the shifted tail
`∑ₖ f_{n+1+k} X^k` of `f`. -/
@[simp]
theorem coeff_divXSubC (hc : HasEval c) (f : A⟦X⟧) (n : ℕ) :
    coeff n (divXSubC hc f) = aeval hc (mk fun k ↦ coeff (n + 1 + k) f) :=
  coeff_mk _ _

/-- The coefficients of the quotient by `X - C c` are the explicit series
`∑ₖ f_{n+1+k} c^k`. -/
theorem hasSum_coeff_divXSubC (hc : HasEval c) (f : A⟦X⟧) (n : ℕ) :
    HasSum (fun k ↦ coeff (n + 1 + k) f * c ^ k) (coeff n (divXSubC hc f)) := by
  simpa [smul_eq_mul] using hasSum_aeval hc (mk fun k ↦ coeff (n + 1 + k) f)

/-- The value at `c` of the tail `∑ₖ f_{n+k} X^k` of `f` is `fₙ + c * (∑ₖ f_{n+1+k} X^k)(c)`. -/
theorem aeval_mk_coeff_add (hc : HasEval c) (f : A⟦X⟧) (n : ℕ) :
    aeval hc (mk fun k ↦ coeff (n + k) f) =
      coeff n f + c * aeval hc (mk fun k ↦ coeff (n + 1 + k) f) := by
  have htail :
      (mk fun k ↦ coeff (n + k) f) = X * (mk fun k ↦ coeff (n + 1 + k) f) + C (coeff n f) := by
    refine (eq_X_mul_shift_add_const _).trans ?_
    simp [add_assoc, add_comm 1]
  simpa [add_comm] using congrArg (aeval hc) htail

/-- **Division by `X - C c`.** At a point `c` where power series can be evaluated,
`f = (X - C c) * q + C (f(c))` with `q = divXSubC hc f`. -/
@[simp]
theorem X_sub_C_mul_divXSubC_add_C_aeval (hc : HasEval c) (f : A⟦X⟧) :
    (X - C c) * divXSubC hc f + C (aeval hc f) = f := by
  have hf : (mk fun k ↦ coeff (0 + k) f) = f := by ext; simp
  ext (_ | n)
  · have h := aeval_mk_coeff_add hc f 0
    rw [hf] at h
    simp [sub_mul, divXSubC, h]
  · simp [sub_mul, aeval_mk_coeff_add hc f (n + 1)]

/-- A power series vanishing at `c` factors as `f = (X - C c) * divXSubC hc f`. -/
theorem X_sub_C_mul_divXSubC (hc : HasEval c) {f : A⟦X⟧} (hf : aeval hc f = 0) :
    (X - C c) * divXSubC hc f = f := by
  simpa [hf] using X_sub_C_mul_divXSubC_add_C_aeval hc f

/-- **Divisibility by a linear factor is vanishing at its root.** At a point `c` where power
series can be evaluated, a power series is divisible by `X - C c` exactly when its value at `c` is
zero; the quotient is `PowerSeries.divXSubC hc f`. -/
theorem X_sub_C_dvd_iff_aeval_eq_zero (hc : HasEval c) (f : A⟦X⟧) :
    (X - C c) ∣ f ↔ aeval hc f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · exact fun hf ↦ ⟨_, (X_sub_C_mul_divXSubC hc hf).symm⟩

end LinearFactor

end PowerSeries
