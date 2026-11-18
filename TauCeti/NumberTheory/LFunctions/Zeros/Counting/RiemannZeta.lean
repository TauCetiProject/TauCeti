/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Counting.Basic

/-!
# The symmetric zero count of the Riemann zeta function

For the card `riemannZetaData` of the Riemann zeta function, the symmetric count `N±(T)` of the
zeros of the completed function `Λ = completedRiemannZeta` with `0 ≤ Re s ≤ 1` and
`-T ≤ Im s ≤ T` is twice the one-sided count `N(T)` of those with `0 < Im s ≤ T`, at every height.
Two facts about `Λ` enter: its divisor is invariant under complex conjugation, since
`Λ (conj s) = conj (Λ s)`, and it has no zero on the real axis; on the segment `[0, 1]` it has
poles at the endpoints and `riemannZeta` is negative in between.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §9.2.
-/

public section

open Set

namespace TauCeti.LFunctions

/-- **`N±(T) = 2 N(T)` for the Riemann zeta function.** The zeros of the completed Riemann zeta
function in the critical strip with `|Im s| ≤ T` are twice as many as those with
`0 < Im s ≤ T`, counted with multiplicity, at every height `T`. -/
theorem riemannZetaData_symmetricZeroCountingFunction (T : ℝ) :
    riemannZetaData.symmetricZeroCountingFunction T =
      2 * riemannZetaData.zeroCountingFunction T :=
  riemannZetaData.symmetricZeroCountingFunction_eq_two_mul
    (by simpa only [riemannZetaData_completed] using divisor_completedRiemannZeta_conj)
    (by simpa only [riemannZetaData_completed] using
      fun x _ ↦ divisor_completedRiemannZeta_ofReal_nonpos x) T

end TauCeti.LFunctions
