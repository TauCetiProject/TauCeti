/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.Solenoidal
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Real

/-!
# Solenoidal `Lᵖ` fields on the real line

A solenoidal field on the real line is almost everywhere constant. Membership in `Lᵖ` for
`1 ≤ p < ∞` forces this constant to vanish.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

/-- For every finite exponent `p ≥ 1`, the solenoidal subspace on the real line is zero. -/
theorem solenoidalLp_real_eq_bot {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    solenoidalLp ℝ p volume = ⊥ := by
  refine le_antisymm (fun u hu ↦ ClosedSubmodule.mem_bot.mpr ?_) bot_le
  obtain ⟨c, hc⟩ := (mem_solenoidalLp_iff.mp hu).exists_ae_eq_const
  have hmem := (Lp.memLp u).ae_eq hc
  have hzero : c = 0 := by
    have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
    simpa only [Real.volume_univ, lt_self_iff_false, or_false] using
      (memLp_const_iff hp0 hp).mp hmem
  exact Lp.ext (hc.trans (hzero ▸ (Lp.coeFn_zero ℝ p volume).symm))

end TauCeti
