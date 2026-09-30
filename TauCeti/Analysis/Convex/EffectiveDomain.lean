/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The effective domain of an extended-real convex function

For a function `f : E → EReal` with convex real epigraph, the effective domain
`{x | f x ≠ ⊤}` is convex. If `f` never takes the value `⊥`, its real representative
`x ↦ (f x).toReal` is convex on that domain and agrees there with `f` by
`EReal.coe_toReal`.

## Main statements

* `TauCeti.convex_setOf_ne_top` — the effective domain is convex;
* `TauCeti.convexOn_toReal` — the real representative is convex on the effective domain.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §4.
-/

public section

namespace TauCeti

open Set

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

/-- The effective domain `{x | f x ≠ ⊤}` of a function with convex real epigraph is convex: it is
the image of the epigraph under the first projection. -/
theorem convex_setOf_ne_top (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    Convex ℝ {x | f x ≠ ⊤} := by
  have hdom : {x | f x ≠ ⊤} = Prod.fst '' {p : E × ℝ | f p.1 ≤ p.2} := by
    ext x
    simp only [mem_ofPred_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨_, EReal.le_coe_toReal h⟩,
      fun ⟨r, hr⟩ => ne_top_of_le_ne_top (EReal.coe_ne_top r) hr⟩
  rw [hdom]
  exact hf.is_linear_image (LinearMap.fst ℝ E ℝ).isLinear

/-- **The real representative of a convex function.** If `f : E → EReal` has convex real epigraph
and never takes the value `⊥`, then `x ↦ (f x).toReal` is convex on the effective domain
`{x | f x ≠ ⊤}`, where it agrees with `f` by `EReal.coe_toReal`. -/
theorem convexOn_toReal (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ConvexOn ℝ {x | f x ≠ ⊤} fun x => (f x).toReal := by
  refine ⟨convex_setOf_ne_top hf, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hf (x := (x, (f x).toReal)) (y := (y, (f y).toReal))
    (EReal.le_coe_toReal hx) (EReal.le_coe_toReal hy) ha hb hab
  simp only [mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h
  have h' : f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
    exact_mod_cast h
  have h'' := EReal.toReal_le_toReal h' (hbot _) (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at h''
  simpa only [smul_eq_mul] using h''

end TauCeti
