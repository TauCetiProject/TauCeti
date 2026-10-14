/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Transversality

/-!
# The Morse–Smale condition for a negative-gradient flow

Let `E` be a real Hilbert space and `f : E → ℝ` a function whose gradient
is globally Lipschitz, so that the negative-gradient flow `negativeGradientFlow f hf` exists for all
time. The results on transverse intersections and level slices of connecting trajectories
(`TauCeti.Analysis.Calculus.Morse.Transversality`, `…TrajectorySpace`) take transversality of the
unstable set of `p` and the stable set of `q` at a point `y` as a hypothesis. The predicate and its
elementary API need only completeness of `E`; the consequences drawn from it assume `E`
finite-dimensional.

`IsMorseSmale f hf` states that this transversality holds at every common point of the unstable
set of every nondegenerate critical point `p` and the stable set of every nondegenerate critical
point `q`; it has exactly the shape of the global transversality hypothesis `htr` taken by the
results of `TauCeti.Analysis.Calculus.Morse.Breaking`. For a Morse function (all of whose critical
points are nondegenerate), this is the classical Morse–Smale condition. It is a plain predicate:
the regularity of `f` is a separate hypothesis of the statements that use it.

## Main declarations

* `TauCeti.IsMorseSmale f hf`: the unstable set of each nondegenerate critical point `p` and the
  stable set of each nondegenerate critical point `q` are transverse at each of their common
  points.
* `TauCeti.isMorseSmale_iff`: the unfolded form of the predicate, its characteristic lemma and
  introduction rule outside this file.
* `TauCeti.IsMorseSmale.transverse_at`: its pointwise elimination rule.
* `TauCeti.isMorseSmale_congr`: the predicate does not depend on the Lipschitz witness.
* `TauCeti.IsMorseSmale.morseIndex_lt`: for a Morse–Smale function, a trajectory between two
  different nondegenerate critical points runs from higher to strictly lower Morse index.
* `TauCeti.IsMorseSmale.unstableSet_inter_stableSet_eq_empty`: consequently no trajectory runs
  from `p` to a different nondegenerate critical point `q` with `morseIndex f p ≤ morseIndex f q`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (the Morse–Smale condition).
-/

public section

open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The Morse–Smale condition.** For a function `f` with `K`-Lipschitz gradient, the unstable set
of each nondegenerate critical point `p` and the stable set of each nondegenerate critical point `q`
of the negative-gradient flow are transverse at each common point `y`: the spans of their tangent
cones at `y` together span the whole space. (When `E` is finite-dimensional and `f` is `C²`, these
sets are `C¹` manifolds near `y`, by the slice charts
`IsNondegenerateCriticalPoint.exists_unstableSet_chart` and `…exists_stableSet_chart`, and these
spans are their tangent spaces.) -/
def IsMorseSmale (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K (∇ f)) : Prop :=
  ∀ ⦃p q y : E⦄, IsNondegenerateCriticalPoint f p → IsNondegenerateCriticalPoint f q →
    y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
    y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤

/-- The introduction and elimination rule for `IsMorseSmale`: transversality of the unstable set of
each nondegenerate critical point `p` and the stable set of each nondegenerate critical point `q`
at each common point. -/
theorem isMorseSmale_iff (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K (∇ f)) :
    IsMorseSmale f hf ↔ ∀ ⦃p q y : E⦄, IsNondegenerateCriticalPoint f p →
      IsNondegenerateCriticalPoint f q →
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
      y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤ :=
  Iff.rfl

/-- **The pointwise elimination rule for `IsMorseSmale`.** For a Morse–Smale function, at a point
`y` of `W^u(p) ∩ W^s(q)`, for nondegenerate critical points `p` and `q`, the spans of the tangent
cones of the unstable set of `p` and the stable set of `q` together span the whole space. -/
theorem IsMorseSmale.transverse_at {f : E → ℝ} {K : ℝ≥0} {hf : LipschitzWith K (∇ f)}
    (h : IsMorseSmale f hf) {p q y : E} (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q)
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤ :=
  h hp hq hy.1 hy.2

/-- **Independence of the Lipschitz witness.** The Morse–Smale condition does not depend on the
Lipschitz bound used to define the negative-gradient flow. -/
theorem isMorseSmale_congr (f : E → ℝ) {K K' : ℝ≥0} (hf : LipschitzWith K (∇ f))
    (hf' : LipschitzWith K' (∇ f)) : IsMorseSmale f hf ↔ IsMorseSmale f hf' := by
  rw [isMorseSmale_iff, isMorseSmale_iff, negativeGradientFlow_congr f hf hf']

variable [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {hf : LipschitzWith K (∇ f)} {p q y : E}

/-- **The Morse index drops along trajectories.** For a `C²` Morse–Smale function, a trajectory of
the negative-gradient flow from a nondegenerate critical point `p` to a different nondegenerate
critical point `q` forces `morseIndex f q < morseIndex f p`. -/
theorem IsMorseSmale.morseIndex_lt (h : IsMorseSmale f hf) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hpq : p ≠ q)
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    morseIndex f q < morseIndex f p :=
  hp.morseIndex_lt_of_mem_unstableSet_inter_stableSet hq hfs hf hpq hyu hys
    (h.transverse_at hp hq ⟨hyu, hys⟩)

/-- **No trajectories up the index.** For a `C²` Morse–Smale function, the unstable set of a
nondegenerate critical point `p` does not meet the stable set of a different nondegenerate critical
point `q` whose Morse index is at least that of `p`. -/
theorem IsMorseSmale.unstableSet_inter_stableSet_eq_empty (h : IsMorseSmale f hf)
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hpq : p ≠ q) (hind : morseIndex f p ≤ morseIndex f q) :
    Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hy ↦
    (h.morseIndex_lt hp hq hfs hpq hy.1 hy.2).not_ge hind

end TauCeti
