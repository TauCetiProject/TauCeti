/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm

import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Integral coefficients of the formal exponential

The invariant derivation of a formal group is conjugate, by its formal exponential, to the
ordinary derivative. Iterating this identity expresses the exponential's factorial-scaled
coefficients as integral coefficients. This supplies the denominator estimate needed to
evaluate formal exponentials over p-adic fields.

The iterated-derivation argument follows `PowerSeries.constantCoeff_iterate_mahlerDerivation`,
with the invariant derivation in place of the multiplicative group's Mahler derivation. Both
use the weighted chain rule and coefficient-extraction lemmas in
`TauCeti.RingTheory.PowerSeries.Derivative`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4–6.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

section Rational

variable [Algebra ℚ R] (F : FormalGroup R)

/-- Substitution of the exponential conjugates the invariant derivation to the ordinary
derivative. -/
theorem derivative_subst_exp (g : PowerSeries R) :
    PowerSeries.derivative (PowerSeries.subst F.exp g) =
      PowerSeries.subst F.exp (F.invariantDerivation g) := by
  rw [F.invariantDerivation_apply]
  exact PowerSeries.derivative_subst_of_derivative_eq_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_exp) F.derivative_exp g

/-- The iterated chain rule for substitution of the formal exponential. -/
theorem iterate_derivative_subst_exp (g : PowerSeries R) (n : ℕ) :
    PowerSeries.derivative^[n] (PowerSeries.subst F.exp g) =
      PowerSeries.subst F.exp (F.invariantDerivation^[n] g) := by
  exact PowerSeries.iterate_derivative_subst F.derivative_subst_exp g n

/-- The constant coefficient of an iterated invariant derivative recovers a factorial-scaled
coefficient after exponential substitution. -/
theorem constantCoeff_iterate_invariantDerivation (g : PowerSeries R) (n : ℕ) :
    PowerSeries.constantCoeff (F.invariantDerivation^[n] g) =
      n.factorial * PowerSeries.coeff n (PowerSeries.subst F.exp g) := by
  exact PowerSeries.constantCoeff_iterate_of_derivative_subst F.constantCoeff_exp
    F.derivative_subst_exp g n

end Rational

/-- After extending scalars to a rational algebra, every exponential coefficient becomes
integral when multiplied by its degree factorial. -/
theorem factorial_mul_coeff_exp_mem_range (F : FormalGroup R) [Algebra ℚ S]
    (f : R →+* S) (n : ℕ) :
    n.factorial * PowerSeries.coeff n (F.map f).exp ∈ Set.range f := by
  have hmap (g : PowerSeries R) :
      PowerSeries.map f (F.invariantDerivation^[n] g) =
        (F.map f).invariantDerivation^[n] (PowerSeries.map f g) := by
    exact Function.Semiconj.iterate_right (F.map_invariantDerivation f) n g
  refine ⟨PowerSeries.constantCoeff (F.invariantDerivation^[n] PowerSeries.X), ?_⟩
  have h := (F.map f).constantCoeff_iterate_invariantDerivation PowerSeries.X n
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (F.map f).constantCoeff_exp
  rw [PowerSeries.subst_X hs] at h
  rw [← PowerSeries.map_X (f := f), ← hmap] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  exact h

end FormalGroup
