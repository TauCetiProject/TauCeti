/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Parity from global reflection equations with a power factor

If `f : 𝕜 → E` satisfies a global reflection equation `f (-z) = δ • f z` and factors as
`f z = z ^ m • g z` with `g` continuous and nonzero at the origin, then `δ = (-1) ^ m` and `g` is
even (`TauCeti.eq_neg_one_pow_and_even_of_eq_pow_smul`).

## Main results

* `TauCeti.eq_neg_one_pow_and_even_of_eq_pow_smul`: recovers `δ = (-1) ^ m` and evenness of the
  cofactor `g` from continuity and nonvanishing at `0`.
-/

public section

open Filter Topology

namespace TauCeti

/-- If `f z = z ^ m • g z` globally with `g` continuous and nonzero at `0`, and `f (-z) = δ • f z`
for all `z`, then `δ = (-1) ^ m` and `g` is even. -/
theorem eq_neg_one_pow_and_even_of_eq_pow_smul {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : 𝕜 → E} {δ : 𝕜} {m : ℕ}
    (hfg : ∀ z, f z = z ^ m • g z) (hparity : ∀ z, f (-z) = δ • f z)
    (hg_cts : ContinuousAt g 0) (hg0 : g 0 ≠ 0) :
    δ = (-1 : 𝕜) ^ m ∧ g.Even := by
  have hg_rel_ne {z : 𝕜} (hz : z ≠ 0) : (-1 : 𝕜) ^ m • g (-z) = δ • g z := by
    apply smul_right_injective E (pow_ne_zero m hz)
    calc z ^ m • ((-1 : 𝕜) ^ m • g (-z))
        = (-z) ^ m • g (-z) := by rw [smul_smul, ← mul_pow, mul_neg_one]
      _ = f (-z) := (hfg (-z)).symm
      _ = δ • f z := hparity z
      _ = z ^ m • (δ • g z) := by rw [hfg z, smul_comm]
  have hg_rel (z : 𝕜) : (-1 : 𝕜) ^ m • g (-z) = δ • g z := by
    by_cases hz : z = 0
    · subst hz
      have hleft : ContinuousAt (fun w : 𝕜 ↦ (-1 : 𝕜) ^ m • g (-w)) 0 :=
        (hg_cts.comp_of_eq continuous_neg.continuousAt neg_zero).const_smul _
      have hright : ContinuousAt (fun w : 𝕜 ↦ δ • g w) 0 := hg_cts.const_smul δ
      have heq : (fun w : 𝕜 ↦ (-1 : 𝕜) ^ m • g (-w)) =ᶠ[𝓝[≠] (0 : 𝕜)] fun w ↦ δ • g w :=
        eventually_nhdsWithin_of_forall fun _ hw ↦ hg_rel_ne hw
      simpa only [neg_zero] using
        ((hleft.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hright).mp heq).eq_of_nhds
    · exact hg_rel_ne hz
  have hδ_eq : δ = (-1 : 𝕜) ^ m := by
    have h0 := hg_rel 0
    rw [neg_zero] at h0
    exact (smul_left_injective 𝕜 hg0 h0).symm
  refine ⟨hδ_eq, fun z ↦ ?_⟩
  have hrel := hg_rel z
  rw [hδ_eq] at hrel
  exact smul_right_injective E (pow_ne_zero m (neg_ne_zero.mpr one_ne_zero)) hrel

end TauCeti
