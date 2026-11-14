/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Basic

/-!
# Test functions as `C^n` maps with the weak Whitney topology

A function in `𝓓^{n}_{K}(E, F)`, smooth of class `C^n` with support in a fixed compact set `K`, is
in particular a bundled `C^n` map `E → F`
(`ContDiffMapSupportedIn.toContMDiffMap`). The topology of `𝓓^{n}_{K}(E, F)` is uniform
convergence of every derivative of order at most `n` on all of `E`, which is stronger than
convergence of these derivatives uniformly on compact sets, the weak Whitney topology on `C^n`
maps. So this inclusion is continuous (`ContDiffMapSupportedIn.continuous_toContMDiffMap`).

The weak Whitney topology on maps between manifolds is built from charts, and is functorial
under composition with fixed smooth maps. Through this inclusion, test functions on a chart
target can therefore be transported to a manifold with a continuous dependence on the test
function, which is how chart extensions of test functions become continuous maps into bundle
test sections.
-/

public section

open scoped Manifold ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {K : TopologicalSpace.Compacts E}

/-- A test function supported in `K`, as a bundled `C^n` map. -/
def toContMDiffMap (f : 𝓓^{n}_{K}(E, F)) : C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ :=
  ⟨f, f.contDiff.contMDiff⟩

@[simp]
theorem coe_toContMDiffMap (f : 𝓓^{n}_{K}(E, F)) : ⇑(toContMDiffMap f) = f :=
  (rfl)

/-- The inclusion of the test functions supported in `K` into the `C^n` maps is continuous for
the weak Whitney topology: uniform convergence of every derivative on `E` implies its uniform
convergence on compact sets. -/
theorem continuous_toContMDiffMap :
    Continuous (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
  refine ContMDiffMap.continuous_weakWhitney_of_continuous_iteratedFDeriv fun m hm ↦ ?_
  have hm' : (m : ℕ∞) ≤ n := by exact_mod_cast hm
  refine (continuous_eval.comp
    ((structureMapCLM ℝ n m).continuous.prodMap continuous_id)).congr fun z ↦ ?_
  simp [structureMapCLM_apply, hm']

end ContDiffMapSupportedIn
