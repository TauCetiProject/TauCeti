/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.ArtinSchreier
public import Mathlib.FieldTheory.RatFunc.Valuation
public import TauCeti.RingTheory.Valuation.Discrete.Order
public import Mathlib.Algebra.Field.ZMod

/-!
# An Artin–Schreier class over an imperfect residue field

Let `k = 𝔽_p(a)`. In `k((T))`, the class of `a T⁻ᵖ` has no integral representative and no
representative with pole order prime to `p`. Indeed, `a` is not a `p`-th power in `k`, since
its order at infinity is `-1`. Cancellation of the leading Laurent coefficient would require
such a root.

This is a concrete counterexample to removing the perfect-residue-field hypothesis from
Artin–Schreier reduction (Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Proposition 3.7.8). The obstruction holds already in the completion, so allowing infinite
Laurent series as substitutions does not repair it.
-/

public section

open scoped LaurentSeries

namespace TauCeti

/-- In `𝔽_p(a)((T))`, the class of `a T⁻ᵖ` has no reduced Artin–Schreier representative:
every substitution leaves a pole whose order is divisible by `p`. -/
theorem artinSchreier_imperfect_residue_counterexample (p : ℕ) [Fact p.Prime] :
    ¬ ∃ w : (RatFunc (ZMod p))⸨X⸩,
      0 ≤ (HahnSeries.single (-(p : ℤ)) RatFunc.X - (w ^ p - w)).orderTop ∨
        ((HahnSeries.single (-(p : ℤ)) RatFunc.X - (w ^ p - w)).order < 0 ∧
          ¬ (p : ℤ) ∣ (HahnSeries.single (-(p : ℤ)) RatFunc.X - (w ^ p - w)).order) := by
  classical
  apply LaurentSeries.not_exists_regular_or_pole_not_dvd (Fact.out : p.Prime).one_lt
  intro b hb
  have h := congrArg (RatFunc.inftyValuation (ZMod p)).ord hb
  rw [Valuation.ord_pow] at h
  simp only [Valuation.ord_def, RatFunc.inftyValuation.X, WithZero.log_exp] at h
  have hp : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hd : (p : ℤ) ∣ (-1 : ℤ) := ⟨_, h.symm⟩
  have := Int.le_of_dvd (by omega : (0 : ℤ) < 1) (dvd_neg.mp hd)
  omega

end TauCeti
