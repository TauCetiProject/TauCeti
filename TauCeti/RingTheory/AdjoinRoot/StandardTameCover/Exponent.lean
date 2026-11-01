/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.Unramified.RootExtraction

/-!
# Étaleness of a root cover away from the divisor

For a positive exponent `e`, the root cover `A[x]/(x^e - f)` is étale away from `f` exactly
when `e` is invertible in `A_f`. The equivalence applies to arbitrary localization models.
Its necessary direction uses
`TauCeti.isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C` from
`TauCeti.RingTheory.Unramified.RootExtraction`, which also supplies prime-divisor descent via
`Prime.isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C_away`.

## References

* [Stacks Project, Lemma 58.31.5](https://stacks.math.columbia.edu/tag/0EYG), the exponent
  condition in the standard-cover description.
-/

public section

namespace TauCeti

variable {A : Type*} [CommRing A] {f : A} {e : ℕ}

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
    exact isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C (algebraMap A Af f) he
  · exact standardTameCover_etale_away f Af Cf

end Away

end TauCeti
