/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Conjugation symmetry of divided differences

Over a nontrivially normed field with a norm-preserving star ring structure (such as `ℂ`), local
conjugation symmetry of a function at a self-conjugate centre passes to its divided difference
at that centre, including the value there, which is the derivative. A normalization constant is
allowed: this is useful when a holomorphic regular factor carries a fixed complex phase.

## Main results

* `TauCeti.eventually_dslope_div_const_conj`: if `f (conj z) / c = conj (f z / c)` near a
  centre `a` with `conj a = a`, then the same holds for `dslope f a` near `a`.
-/

public section

open Filter Topology
open scoped ComplexConjugate

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]

/-- Dividing a function by a constant and taking its divided difference at a self-conjugate
centre preserves local conjugation symmetry. No differentiability assumption is needed: at the
centre, conjugation also respects the convention that the derivative is zero when absent. -/
theorem eventually_dslope_div_const_conj {f : 𝕜 → 𝕜} {a : 𝕜} (ha : conj a = a) (c : 𝕜)
    (hf : ∀ᶠ z in 𝓝 a, f (conj z) / c = conj (f z / c)) :
    ∀ᶠ z in 𝓝 a, dslope f a (conj z) / c = conj (dslope f a z / c) := by
  have hfa : f a / c = conj (f a / c) := by simpa only [ha] using hf.self_of_nhds
  have hderiv : deriv f a / c = conj (deriv f a / c) := by
    have h : (conj ∘ (f · / c) ∘ conj) =ᶠ[𝓝 a] (f · / c) :=
      hf.mono fun z hz => by simp only [Function.comp_apply, hz, starRingEnd_self_apply]
    simpa only [deriv_conj_conj, Function.comp_apply, ha, deriv_div_const] using h.deriv_eq.symm
  have hslope {w : 𝕜} (hw : w ≠ a) : dslope f a w / c = (f w / c - f a / c) / (w - a) := by
    rw [dslope_of_ne _ hw, slope_def_field, div_right_comm, sub_div]
  filter_upwards [hf] with z hz
  rcases eq_or_ne z a with rfl | hza
  · simpa only [ha, dslope_same] using hderiv
  have hcza : conj z ≠ a := fun h => hza (by simpa [ha] using congrArg conj h)
  rw [hslope hza, hslope hcza, map_div₀, map_sub, map_sub, ha, hz, ← hfa]

end TauCeti
