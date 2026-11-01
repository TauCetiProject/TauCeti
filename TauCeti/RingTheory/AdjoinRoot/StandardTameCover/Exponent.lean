/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.Localization.Away.Units
import TauCeti.RingTheory.Unramified.AdjoinRoot

/-!
# Recovering the invertibility of a root-cover exponent

For a positive exponent `e`, formal unramifiedness of `A[x]/(x^e - f)` forces `e` to be
invertible in `A`. Consequently, the root cover is étale away from `f` exactly when `e` is
invertible in `A_f`.

Over a domain, when `f` is prime and does not divide `e`, invertibility descends from `A_f`
to `A`.
This supplies the exponent condition when identifying a normalization, already known to be
étale off a prime divisor, with a standard tamely ramified cover. In particular, one need not
assume the exponent is a unit before identifying the root algebra.

The argument uses the monogenic unramifiedness criterion
`Polynomial.isUnit_mk_derivative_of_formallyUnramified_adjoinRoot`: the derivative
`e x^(e-1)` is a unit in the root algebra. Units descend along its finite free positive-rank
map from the base.

## References

* [Stacks Project, Lemma 58.31.5](https://stacks.math.columbia.edu/tag/0EYG), the exponent
  condition in the standard-cover description.
-/

public section

open Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {f : A} {e : ℕ}

/-- A positive-degree root algebra can be formally unramified only if its exponent is
invertible in the base ring. No condition on the constant term is required. -/
theorem isUnit_natCast_of_standardTameCover_formallyUnramified (he : e ≠ 0)
    [Algebra.FormallyUnramified A (standardTameCover A f e)] : IsUnit (e : A) := by
  nontriviality A
  have hmonic : (X ^ e - C f).Monic := monic_X_pow_sub_C f he
  have := hmonic.free_adjoinRoot
  have : Nontrivial (standardTameCover A f e) :=
    (AdjoinRoot.nontrivial_iff_of_monic hmonic).mpr (by
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero he)]
      exact_mod_cast Nat.pos_of_ne_zero he)
  have hderiv := (X ^ e - C f).isUnit_mk_derivative_of_formallyUnramified_adjoinRoot
  have hunit : IsUnit
      ((e : standardTameCover A f e) * AdjoinRoot.root (X ^ e - C f) ^ (e - 1)) := by
    simpa [derivative_X_pow, AdjoinRoot.mk_X] using hderiv
  exact (isUnit_map_iff (algebraMap A (standardTameCover A f e)) _).mp
    (by simpa using isUnit_of_mul_isUnit_left hunit)

section Away

variable (f) (Af Cf : Type*) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af]
  [CommRing Cf] [Algebra (standardTameCover A f e) Cf]
  [IsLocalization.Away (algebraMap A (standardTameCover A f e) f) Cf] [Algebra A Cf]
  [IsScalarTower A (standardTameCover A f e) Cf] [Algebra Af Cf] [IsScalarTower A Af Cf]

include f in
/-- A positive-degree root cover is étale off the divisor exactly when its exponent is
invertible off the divisor. This applies to arbitrary models of the two localizations. -/
theorem standardTameCover_etale_away_iff (he : e ≠ 0) :
    Algebra.Etale Af Cf ↔ IsUnit (e : Af) := by
  constructor
  · intro h
    have := Algebra.Etale.of_equiv (standardTameCoverAwayAlgEquiv f e Af Cf).symm
    exact isUnit_natCast_of_standardTameCover_formallyUnramified
      (f := algebraMap A Af f) he
  · exact standardTameCover_etale_away f Af Cf

end Away

end TauCeti

namespace Prime

open TauCeti

variable {A : Type*} [CommRing A] [IsDomain A] {f : A} {e : ℕ}

/-- For a prime divisor, étaleness of the root cover off the divisor forces its exponent to be
a unit on the base, provided the exponent does not vanish along the divisor. -/
theorem isUnit_natCast_of_standardTameCover_etale_away (hf : Prime f) (hfe : ¬ f ∣ (e : A))
    (Af Cf : Type*) [CommRing Af] [Algebra A Af]
    [IsLocalization.Away f Af] [CommRing Cf] [Algebra (standardTameCover A f e) Cf]
    [IsLocalization.Away (algebraMap A (standardTameCover A f e) f) Cf] [Algebra A Cf]
    [IsScalarTower A (standardTameCover A f e) Cf] [Algebra Af Cf] [IsScalarTower A Af Cf]
    [Algebra.Etale Af Cf] : IsUnit (e : A) := by
  have he : e ≠ 0 := by rintro rfl; simp at hfe
  apply hf.isUnit_of_isUnit_away_of_not_dvd (S := Af) _ hfe
  simpa using (standardTameCover_etale_away_iff f Af Cf he).mp inferInstance

end Prime
