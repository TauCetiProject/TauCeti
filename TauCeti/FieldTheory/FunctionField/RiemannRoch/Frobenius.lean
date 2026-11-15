/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Frobenius.Range
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The genus of Frobenius power subfields

Over perfect constants of exponential characteristic `p`, the power subfield `F^{p^n}` has the
same genus as `F`. This concerns the normalized places of the power subfield, not the unnormalized
restriction of the valuations of `F`. The isomorphism given by iterated Frobenius transports the
places, divisor degrees and dimensions of Riemann–Roch spaces semilinearly.

If `hF : IsFunctionField k F`, the power subfield is again a function field by
`hF.of_isAlgebraic_top (E := frobeniusPowers k F p n)`: the instance
`isPurelyInseparable_frobeniusPowers` supplies the required algebraicity. In this setting,
`genus_frobeniusPowers` compares the genera of function fields.

No separability of `F / F^{p^n}` is assumed; in positive characteristic this extension is purely
inseparable. Nor is exactness of the constant field needed for equality of the two suprema.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Iterated Frobenius preserves the genus over perfect constants: `g(F^{p^n} / k) = g(F / k)`.
The statement identifies the defining suprema even without a function-field hypothesis. -/
theorem genus_frobeniusPowers (p : ℕ) [ExpChar k p] [PerfectRing k p] (n : ℕ) :
    genus k (frobeniusPowers k F p n) = genus k F :=
  genus_eq_of_ringEquiv (iterateFrobeniusEquiv k p n)
    (iterateFrobeniusEquivPowers k F p n) (iterateFrobeniusEquivPowers_algebraMap k F p n)

end TauCeti
