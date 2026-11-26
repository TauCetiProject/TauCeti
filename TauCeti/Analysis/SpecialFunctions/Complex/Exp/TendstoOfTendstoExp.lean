/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CoveringMap

/-!
# A continuous logarithm of a convergent function converges

Let `g : ℝ → ℂ` be continuous on `(a, ∞)`. If `exp ∘ g` tends to a nonzero limit `c` as `s → a⁺`,
then `g` itself tends to a limit there. Near `a` the function `exp (g s) / c` lies in the slit
plane, so `g` differs from the principal logarithm `log (exp (g s) / c)` by a continuous function
with values in `log c + 2πiℤ`; on the connected interval `(a, s₁]` such a function is constant,
because `exp` is a covering map.

## Main results

* `Complex.exists_tendsto_of_tendsto_exp`: a function continuous on `(a, ∞)` whose exponential
  tends to a nonzero limit as `s → a⁺` tends to a limit there.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `src/Lib/ClassField/HeckeL/EulerProduct.lean`, where the covering-map argument is part
of the proof of `New.hasPrimeDensity_of_tendsto`. Here it is a standalone statement at any
point `a`.
-/

public section

open Filter Topology

namespace Complex

/-- **A continuous logarithm of a convergent function converges.** A function `g : ℝ → ℂ`
continuous on `(a, ∞)` whose exponential tends to a nonzero limit as `s → a⁺` tends to a limit
there: near `a` it differs from the principal logarithm of its exponential (divided by the limit)
by a continuous function with values in `log c + 2πiℤ`, which is constant. -/
theorem exists_tendsto_of_tendsto_exp {a : ℝ} {g : ℝ → ℂ} (hg : ContinuousOn g (Set.Ioi a))
    {c : ℂ} (hc : c ≠ 0) (h : Tendsto (fun s ↦ exp (g s)) (𝓝[>] a) (𝓝 c)) :
    ∃ C, Tendsto g (𝓝[>] a) (𝓝 C) := by
  have h' : Tendsto (fun s ↦ exp (g s) / c) (𝓝[>] a) (𝓝 1) := by
    simpa [div_self hc] using h.div_const c
  obtain ⟨s₁, hs₁, hslit⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (h' (isOpen_slitPlane.mem_nhds one_mem_slitPlane))
  have hmono : Set.Ioc a s₁ ⊆ Set.Ioi a := Set.Ioc_subset_Ioi_self
  -- `g - log (exp g / c)` is continuous on `(a, s₁]` and its exponential is `c`
  have hcont : ContinuousOn (fun s ↦ g s - log (exp (g s) / c)) (Set.Ioc a s₁) :=
    (hg.mono hmono).sub (((hg.mono hmono).cexp.div_const c).clog hslit)
  have hexp (t : ℝ) (ht : t ∈ Set.Ioc a s₁) : exp (g t - log (exp (g t) / c)) = c := by
    rw [exp_sub, exp_log (slitPlane_ne_zero (hslit ht)), div_div_cancel₀ (exp_ne_zero _)]
  have hconst (t : ℝ) (ht : t ∈ Set.Ioc a s₁) :
      g t - log (exp (g t) / c) = g s₁ - log (exp (g s₁) / c) :=
    isCoveringMap_exp.constOn_of_comp isPreconnected_Ioc hcont
      (fun u hu v hv ↦ Subtype.ext ((hexp u hu).trans (hexp v hv).symm)) ht ⟨hs₁, le_rfl⟩
  refine ⟨g s₁ - log (exp (g s₁) / c) + log 1, ((h'.clog one_mem_slitPlane).const_add _).congr' ?_⟩
  filter_upwards [Ioc_mem_nhdsGT hs₁] with t ht
  rw [← hconst t ht, sub_add_cancel]

end Complex
