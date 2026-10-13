/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TrajectorySpace

/-!
# The Morse–Smale condition for a negative-gradient flow

Let `E` be a finite-dimensional real inner product space and `f : E → ℝ` a `C²` function whose
gradient is globally Lipschitz, so that the negative-gradient flow `negativeGradientFlow f hf`
exists for all time. `f` is **Morse–Smale** when every critical point is nondegenerate, and for
every pair of critical points `p`, `q` the unstable set of `p` and the stable set of `q` meet
transversally at each of their common points: at every point `y` of
`W^u(p) ∩ W^s(q)`, the tangent spaces of `W^u(p)` and `W^s(q)` at `y` span `E`.

The results on transverse intersections and level slices of connecting trajectories
(`TauCeti.Analysis.Calculus.Morse.Transversality`, `…TrajectorySpace`) are stated at a point,
with transversality there as a hypothesis. Under `IsMorseSmale` that hypothesis is discharged, so
the statements below hold at every point of every intersection, for every pair of critical points.

## Main declarations

* `TauCeti.IsMorseSmale f hf`: the Morse–Smale condition.
* `TauCeti.IsMorseSmale.isNondegenerateCriticalPoint`: critical points are nondegenerate.
* `TauCeti.IsMorseSmale.exists_unstableSet_inter_stableSet_chart`: `W^u(p) ∩ W^s(q)` is flattened
  near each of its points by a `C¹` chart with `C¹` inverse.
* `TauCeti.IsMorseSmale.finrank_span_tangentConeAt_unstableSet_inter_stableSet_add_morseIndex`:
  its tangent spaces have dimension `morseIndex f p - morseIndex f q`.
* `TauCeti.IsMorseSmale.morseIndex_lt_of_mem_unstableSet_inter_stableSet`: the Morse index drops
  strictly along a connecting trajectory.
* `TauCeti.IsMorseSmale.exists_unstableSet_inter_stableSet_level_chart` and
  `TauCeti.IsMorseSmale.finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex`
  : the level slice `W^u(p) ∩ W^s(q) ∩ {f = c}` is a `C¹` submanifold of dimension
  `morseIndex f p - morseIndex f q - 1`.
* `TauCeti.IsMorseSmale.isDiscrete_unstableSet_inter_stableSet_level`: if the indices differ by
  one, the level slice is discrete.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3.
-/

public section

open Set
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0}

/-- **The Morse–Smale condition.** A `C²` function `f` on a finite-dimensional real inner product
space, with globally Lipschitz gradient `hf`, is Morse–Smale when all its critical points are
nondegenerate and, for all critical points `p` and `q`, the unstable set of `p` and the stable
set of `q` of the negative-gradient flow meet transversally at each common point. -/
structure IsMorseSmale (f : E → ℝ) (hf : LipschitzWith K (∇ f)) : Prop where
  /-- `f` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 f
  /-- Every critical point of `f` is nondegenerate. -/
  nondegenerate : HasNondegenerateCriticalPointsOn f univ
  /-- The unstable set of a critical point `p` and the stable set of a critical point `q` are
  transverse at each point of their intersection. -/
  transverse : ∀ ⦃p q y : E⦄, fderiv ℝ f p = 0 → fderiv ℝ f q = 0 →
    y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
    y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤

namespace IsMorseSmale

variable {hf : LipschitzWith K (∇ f)} {p q y : E} {c : ℝ}

/-- Every critical point of a Morse–Smale function is nondegenerate. -/
theorem isNondegenerateCriticalPoint (h : IsMorseSmale f hf) (hp : fderiv ℝ f p = 0) :
    IsNondegenerateCriticalPoint f p :=
  hasNondegenerateCriticalPointsOn_iff.1 h.nondegenerate (mem_univ p) hp

section Intersection

variable (h : IsMorseSmale f hf) (hp : fderiv ℝ f p = 0) (hq : fderiv ℝ f q = 0)
  (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
  (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
include h hp hq hyu hys

/-- **Chart for a connecting locus.** Near each point of `W^u(p) ∩ W^s(q)`, the set of points
lying on trajectories from `p` to `q` is flattened by a `C¹` chart with `C¹` inverse onto the
intersection of the tangent spaces of `W^u(p)` and `W^s(q)`. -/
theorem exists_unstableSet_inter_stableSet_chart :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ↔
        e z ∈
          Submodule.span ℝ
            (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
            Submodule.span ℝ
              (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) :=
  (h.isNondegenerateCriticalPoint hp).exists_unstableSet_inter_stableSet_chart
    (h.isNondegenerateCriticalPoint hq) h.contDiff hf hyu hys (h.transverse hp hq hyu hys)

/-- The tangent space of `W^u(p) ∩ W^s(q)` at each of its points is the intersection of the
tangent spaces of `W^u(p)` and `W^s(q)`. -/
theorem span_tangentConeAt_unstableSet_inter_stableSet :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) y) =
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) :=
  (h.isNondegenerateCriticalPoint hp).span_tangentConeAt_unstableSet_inter_stableSet
    (h.isNondegenerateCriticalPoint hq) h.contDiff hf hyu hys (h.transverse hp hq hyu hys)

/-- The tangent space of `W^u(p) ∩ W^s(q)` at each of its points has dimension
`morseIndex f p - morseIndex f q`. -/
theorem finrank_span_tangentConeAt_unstableSet_inter_stableSet_add_morseIndex :
    Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q) y)) +
      morseIndex f q = morseIndex f p := by
  have hp' := h.isNondegenerateCriticalPoint hp
  have hq' := h.isNondegenerateCriticalPoint hq
  have htr := h.transverse hp hq hyu hys
  exact hp'.finrank_span_tangentConeAt_unstableSet_inter_stableSet_add_morseIndex
    hq' h.contDiff hf hyu hys htr

/-- **The Morse index drops strictly along a connecting trajectory.** If `p ≠ q` and
`W^u(p) ∩ W^s(q)` is nonempty, then `morseIndex f q < morseIndex f p`. -/
theorem morseIndex_lt_of_mem_unstableSet_inter_stableSet (hpq : p ≠ q) :
    morseIndex f q < morseIndex f p :=
  (h.isNondegenerateCriticalPoint hp).morseIndex_lt_of_mem_unstableSet_inter_stableSet
    (h.isNondegenerateCriticalPoint hq) h.contDiff hf hpq hyu hys (h.transverse hp hq hyu hys)

variable (hpq : p ≠ q) (hyc : f y = c)
include hpq hyc

/-- **Chart for a level slice.** If `p ≠ q`, near each point `y` of `W^u(p) ∩ W^s(q)` with
`f y = c`, the level slice `W^u(p) ∩ W^s(q) ∩ {f = c}` is flattened by a `C¹` chart with `C¹`
inverse onto the intersection of the tangent spaces of `W^u(p)` and `W^s(q)` with `ker df_y`. -/
theorem exists_unstableSet_inter_stableSet_level_chart :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c} ↔
        e z ∈
          Submodule.span ℝ
            (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
            Submodule.span ℝ
              (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) ⊓
            (fderiv ℝ f y).ker := by
  have hp' := h.isNondegenerateCriticalPoint hp
  have hq' := h.isNondegenerateCriticalPoint hq
  have htr := h.transverse hp hq hyu hys
  exact hp'.exists_unstableSet_inter_stableSet_level_chart
    hq' h.contDiff hf hpq hyu hys htr hyc

/-- The tangent space of the level slice at `y` is the intersection of the tangent spaces of
`W^u(p)` and `W^s(q)` with `ker df_y`. -/
theorem span_tangentConeAt_unstableSet_inter_stableSet_level :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) y) =
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) ⊓
        (fderiv ℝ f y).ker := by
  have hp' := h.isNondegenerateCriticalPoint hp
  have hq' := h.isNondegenerateCriticalPoint hq
  have htr := h.transverse hp hq hyu hys
  exact hp'.span_tangentConeAt_unstableSet_inter_stableSet_level
    hq' h.contDiff hf hpq hyu hys htr hyc

/-- The level slice has dimension `morseIndex f p - morseIndex f q - 1` at each of its points. -/
theorem finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex :
    Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) y)) +
      morseIndex f q + 1 = morseIndex f p := by
  have hp' := h.isNondegenerateCriticalPoint hp
  have hq' := h.isNondegenerateCriticalPoint hq
  have htr := h.transverse hp hq hyu hys
  exact hp'.finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex
    hq' h.contDiff hf hpq hyu hys htr hyc

end Intersection

/-- **Index-difference-one level slices are discrete.** If `f` is Morse–Smale and the Morse
indices of the critical points `p` and `q` differ by one, then each level slice
`W^u(p) ∩ W^s(q) ∩ {f = c}` is discrete. -/
theorem isDiscrete_unstableSet_inter_stableSet_level (h : IsMorseSmale f hf)
    (hp : fderiv ℝ f p = 0) (hq : fderiv ℝ f q = 0)
    (hind : morseIndex f p = morseIndex f q + 1) :
    IsDiscrete (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) :=
  (h.isNondegenerateCriticalPoint hp).isDiscrete_unstableSet_inter_stableSet_level
    (h.isNondegenerateCriticalPoint hq) h.contDiff hf hind
    fun _ hy ↦ h.transverse hp hq hy.1.1 hy.1.2

end IsMorseSmale

end TauCeti
