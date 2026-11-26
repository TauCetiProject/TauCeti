/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Nonvanishing of the continued Dedekind zeta function on `Re s ≥ 1`

The Euler product gives nonvanishing on the open half-plane. On its boundary we
apply `TauCeti.ne_zero_of_eqOn_dedekindZeta`, the `3-4-1` criterion for any
local continuation agreeing with the Dirichlet series, to the canonical continuation.
-/

public section

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The continued Dedekind zeta function does not vanish on `Re s ≥ 1` away from its pole. -/
theorem dedekindZetaC_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs₁ : s ≠ 1) :
    dedekindZetaC K s ≠ 0 := by
  rcases hs.lt_or_eq with h | h
  · rw [dedekindZetaC_eq_dedekindZeta K h]
    exact dedekindZeta_ne_zero_of_one_lt_re h
  · exact ne_zero_of_eqOn_dedekindZeta h.symm hs₁
      (analyticAt_dedekindZetaC K hs₁).differentiableAt fun _ hz ↦
        dedekindZetaC_eq_dedekindZeta K hz

end TauCeti.LFunctions
