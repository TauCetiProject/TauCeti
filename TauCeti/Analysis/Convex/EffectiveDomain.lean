/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.EReal.Basic

/-!
# The effective domain of an extended-real convex function

For a function `f : E → EReal` with convex real epigraph, the effective domain
`{x | f x ≠ ⊤}` is convex. If `f` never takes the value `⊥`, its real representative
`x ↦ (f x).toReal` is convex on that domain and agrees there with `f` by
`EReal.coe_toReal`.

## Main statements

* `TauCeti.le_coe_of_convex_epigraph` — the epigraph gives a convex-combination bound;
* `TauCeti.convex_setOf_ne_top` — the effective domain is convex;
* `TauCeti.convexOn_toReal` — the real representative is convex on the effective domain;
* `TauCeti.setOf_ite_ne_top`, `TauCeti.ite_ne_bot` and `TauCeti.convex_epigraph_ite` — a real
  function convex on `Ω` and extended by `⊤` off `Ω` has effective domain `Ω`, never takes the
  value `⊥`, and has convex real epigraph.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §4.
-/

public section

namespace TauCeti

open Set

variable {E : Type*} [AddCommMonoid E] [SMul ℝ E] {f : E → EReal}

/-- A convex real epigraph bounds the value at a convex combination by the corresponding
combination of the real representatives of its endpoint values. -/
theorem le_coe_of_convex_epigraph (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    {x y : E} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
  simpa using hf (x := (x, (f x).toReal)) (y := (y, (f y).toReal))
    (EReal.le_coe_toReal hx) (EReal.le_coe_toReal hy) ha hb hab

/-- The effective domain `{x | f x ≠ ⊤}` of a function with convex real epigraph is convex: it is
closed under convex combinations. -/
theorem convex_setOf_ne_top (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    Convex ℝ {x | f x ≠ ⊤} := fun _ hx _ hy _ _ ha hb hab =>
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (le_coe_of_convex_epigraph hf hx hy ha hb hab)

/-- **The real representative of a convex function.** If `f : E → EReal` has convex real epigraph
and never takes the value `⊥`, then `x ↦ (f x).toReal` is convex on the effective domain
`{x | f x ≠ ⊤}`, where it agrees with `f` by `EReal.coe_toReal`. -/
theorem convexOn_toReal (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ConvexOn ℝ {x | f x ≠ ⊤} fun x => (f x).toReal := by
  refine ⟨convex_setOf_ne_top hf, fun x hx y hy a b ha hb hab => ?_⟩
  simpa only [EReal.toReal_coe, smul_eq_mul] using
    EReal.toReal_le_toReal (le_coe_of_convex_epigraph hf hx hy ha hb hab) (hbot _)
      (EReal.coe_ne_top _)

section Ite

variable {Ω : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ}

omit [AddCommMonoid E] [SMul ℝ E] in
/-- The effective domain of `u` extended by `⊤` off `Ω` is `Ω`. -/
theorem setOf_ite_ne_top :
    {x | (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊤} = Ω := by
  ext x
  by_cases hx : x ∈ Ω <;> simp [hx]

omit [AddCommMonoid E] [SMul ℝ E] in
/-- A real function extended by `⊤` never takes the value `⊥`. -/
@[simp]
theorem ite_ne_bot (x : E) : (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊥ := by
  by_cases hx : x ∈ Ω <;> simp [hx]

/-- A function convex on `Ω` and extended by `⊤` off `Ω` has convex real epigraph. -/
theorem convex_epigraph_ite (hu : ConvexOn ℝ Ω u) :
    Convex ℝ {p : E × ℝ | (if p.1 ∈ Ω then (u p.1 : EReal) else ⊤) ≤ p.2} := by
  have hepi : {p : E × ℝ | (if p.1 ∈ Ω then (u p.1 : EReal) else ⊤) ≤ p.2} =
      {p : E × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} := by
    ext p
    by_cases hp : p.1 ∈ Ω <;> simp [hp]
  exact hepi ▸ hu.convex_epigraph

end Ite

end TauCeti
