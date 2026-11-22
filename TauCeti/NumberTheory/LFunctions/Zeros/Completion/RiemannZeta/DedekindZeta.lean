/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Rat
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# Zero counts of the completed Riemann zeta function and `dedekindZetaC ℚ`

Because `TauCeti.LFunctions.dedekindZetaC ℚ` has the same punctured germs as `riemannZeta`
everywhere (`TauCeti.LFunctions.zeroCount_dedekindZetaC_rat`), critical-strip zero counts of the
entire Riemann completion `TauCeti.LFunctions.zetaEntireCompletion` coincide with those of
`dedekindZetaC ℚ`.

## Main results

* `TauCeti.LFunctions.zeroCount_zetaEntireCompletion_eq_dedekindZetaC_rat_inter`: zero-count
  comparison between `zetaEntireCompletion` and `dedekindZetaC ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Set

namespace TauCeti.LFunctions

/-- On any region `R`, the zero count of `zetaEntireCompletion` is the zero count of
`dedekindZetaC ℚ` on the intersection of `R` with the open critical strip. -/
theorem zeroCount_zetaEntireCompletion_eq_dedekindZetaC_rat_inter (R : Set ℂ) :
    zeroCount zetaEntireCompletion univ R =
      zeroCount (dedekindZetaC ℚ) univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [zeroCount_dedekindZetaC_rat, zeroCount_zetaEntireCompletion_eq_riemannZeta_inter]

end TauCeti.LFunctions
