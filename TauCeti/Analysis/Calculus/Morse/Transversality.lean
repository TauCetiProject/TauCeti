/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GlobalChart
public import TauCeti.Analysis.Calculus.TransverseIntersection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Dynamics.Flow.ConnectingOrbit

/-!
# Transverse intersections of unstable and stable manifolds

Let `p` and `q` be nondegenerate critical points of a globally `C²` function `f` with globally
Lipschitz gradient on a finite-dimensional real inner product space. The trajectories of the
negative-gradient flow running from `p` to `q` are the points of `W^u(p) ∩ W^s(q)`, the
intersection of the unstable set of `p` with the stable set of `q`. The **Morse–Smale condition**
asks that these two embedded submanifolds meet transversally: at every common point `y`, their
tangent spaces span the ambient space. Tangent spaces are taken intrinsically, as spans of the
tangent cones `tangentConeAt ℝ _ y`.

This file proves the two basic consequences of transversality at a point `y` of
`W^u(p) ∩ W^s(q)`.

* Near `y`, the intersection is an embedded `C¹` submanifold of dimension
  `morseIndex f p - morseIndex f q`: a `C¹` chart with `C¹` inverse flattens it onto the
  intersection of the two tangent spaces, whose dimension `d` satisfies
  `d + morseIndex f q = morseIndex f p`. This is the space of connecting trajectories whose
  points, counted modulo the flow, define the Morse differential.
* If `p ≠ q`, the Morse index drops strictly: `morseIndex f q < morseIndex f p`. The velocity
  `-∇f y` of the trajectory through `y` is tangent to both invariant sets and is nonzero, so the
  intersection has positive dimension.

The tangent spaces themselves have the expected dimensions: `morseIndex f p` for the unstable set
of `p`, and the complementary dimension for the stable set of `q`.

## Main results

* `TauCeti.IsNondegenerateCriticalPoint.finrank_span_tangentConeAt_unstableSet` and
  `TauCeti.IsNondegenerateCriticalPoint.finrank_span_tangentConeAt_stableSet_add_morseIndex`: the
  dimensions of the tangent spaces of the unstable and stable sets.
* `TauCeti.IsNondegenerateCriticalPoint.exists_unstableSet_inter_stableSet_chart`: a transverse
  intersection of an unstable and a stable set is an embedded `C¹` submanifold, flattened onto the
  intersection of the tangent spaces.
* `TauCeti.IsNondegenerateCriticalPoint.finrank_span_tangentConeAt_inf_add_morseIndex`: that
  intersection has dimension `morseIndex f p - morseIndex f q`.
* `TauCeti.IsNondegenerateCriticalPoint.morseIndex_lt_of_mem_unstableSet_inter_stableSet`: along a
  transverse trajectory joining distinct critical points, the Morse index drops strictly.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (Morse–Smale condition) and Chapter 3 (spaces of trajectories).
-/

public section

open Set
open scoped Gradient NNReal

namespace TauCeti

namespace IsNondegenerateCriticalPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {p q y : E} {K : ℝ≥0}

omit [FiniteDimensional ℝ E] in
/-- A global straightening chart of the unstable or stable set has an invertible derivative at
each point of its source. -/
private theorem exists_hasFDerivAt_of_chart {e : OpenPartialHomeomorph E E} {z : E}
    (hz : z ∈ e.source) (he : ∀ w ∈ e.source, ContDiffAt ℝ 1 e w)
    (hes : ∀ w ∈ e.target, ContDiffAt ℝ 1 e.symm w) :
    ∃ A : E ≃L[ℝ] E, HasFDerivAt e (A : E →L[ℝ] E) z := by
  have hd := (he z hz).differentiableAt one_ne_zero
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hz hd
    ((hes _ (e.map_source hz)).differentiableAt one_ne_zero)
  exact ⟨A, hA ▸ hd.hasFDerivAt⟩

/-- The tangent space of the unstable set of a Morse critical point `p`, at any of its points, has
dimension the Morse index of `p`. -/
theorem finrank_span_tangentConeAt_unstableSet (hp : IsNondegenerateCriticalPoint f p)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p) :
    Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y)) =
      morseIndex f p := by
  obtain ⟨e, hye, he, hes, hS⟩ := hp.exists_unstableSet_chart hfs hf hy
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_of_chart hye he hes
  rw [(isSliceChart_iff.2 hS).finrank_span_tangentConeAt
    (Submodule.closed_of_finiteDimensional _) hye hy hA,
    hp.contDiffAt.finrank_unstableLinearSubspace]

/-- The tangent space of the stable set of a Morse critical point `q`, at any of its points, has
dimension the ambient dimension minus the Morse index of `q`. -/
theorem finrank_span_tangentConeAt_stableSet_add_morseIndex (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y)) +
      morseIndex f q = Module.finrank ℝ E := by
  obtain ⟨e, hye, he, hes, hS⟩ := hq.exists_stableSet_chart hfs hf hy
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_of_chart hye he hes
  rw [(isSliceChart_iff.2 hS).finrank_span_tangentConeAt
    (Submodule.closed_of_finiteDimensional _) hye hy hA]
  exact hq.finrank_stableLinearSubspace_add_morseIndex

/-- **Transverse unstable and stable sets meet in an embedded submanifold.** If the unstable set of
a Morse critical point `p` and the stable set of a Morse critical point `q` meet transversally at
`y`, then near `y` their intersection, the set of points on trajectories from `p` to `q`, is
flattened by a `C¹` chart with `C¹` inverse onto the intersection of their tangent spaces. -/
theorem exists_unstableSet_inter_stableSet_chart (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ↔
        e z ∈
          Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
            Submodule.span ℝ
              (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) := by
  obtain ⟨e₁, hy₁, he₁, hes₁, hS₁⟩ := hp.exists_unstableSet_chart hfs hf hyu
  obtain ⟨e₂, hy₂, he₂, hes₂, hS₂⟩ := hq.exists_stableSet_chart hfs hf hys
  obtain ⟨e, hye, he, hes, hS⟩ := exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top
    one_ne_zero (isSliceChart_iff.2 hS₁) (isSliceChart_iff.2 hS₂) hy₁ hy₂ hyu hys he₁ he₂
    ((hes₁ _ (e₁.map_source hy₁)).differentiableAt one_ne_zero)
    ((hes₂ _ (e₂.map_source hy₂)).differentiableAt one_ne_zero) htr
  exact ⟨e, hye, he, hes, isSliceChart_iff.1 hS⟩

/-- **The space of connecting trajectories has dimension the index difference.** If the unstable set
of a Morse critical point `p` and the stable set of a Morse critical point `q` meet transversally
at `y`, then the intersection of their tangent spaces at `y`, which is the tangent space of
`W^u(p) ∩ W^s(q)` by `exists_unstableSet_inter_stableSet_chart`, has dimension
`morseIndex f p - morseIndex f q`. -/
theorem finrank_span_tangentConeAt_inf_add_morseIndex (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤) :
    Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
          Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) :
            Submodule ℝ E) +
      morseIndex f q = morseIndex f p := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y))
    (Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y))
  rw [htr, finrank_top, hp.finrank_span_tangentConeAt_unstableSet hfs hf hyu] at hdim
  have hs := hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf hys
  omega

/-- **The Morse index drops strictly along a transverse trajectory.** If a trajectory of the
negative-gradient flow runs from a Morse critical point `p` to a different Morse critical point
`q`, and the unstable set of `p` meets the stable set of `q` transversally at a point `y` of it,
then `morseIndex f q < morseIndex f p`. Under the Morse–Smale condition, trajectories therefore
only run from higher to lower index. -/
theorem morseIndex_lt_of_mem_unstableSet_inter_stableSet (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hpq : p ≠ q) (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤) :
    morseIndex f q < morseIndex f p := by
  have hdim := hp.finrank_span_tangentConeAt_inf_add_morseIndex hq hfs hf hyu hys htr
  set φ := negativeGradientFlow f hf
  -- The velocity `-∇f y` of the trajectory through `y` is tangent to both invariant sets.
  have hvel : HasDerivAt (fun t ↦ φ t y) (-∇ f y) 0 := by
    simpa only [φ, _root_.Flow.map_zero_apply] using
      (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y 0
  have htan {S : Set E} (hS : IsInvariant φ S) (hyS : y ∈ S) :
      -∇ f y ∈ Submodule.span ℝ (tangentConeAt ℝ S y) := by
    refine Submodule.subset_span ?_
    simpa only [φ, _root_.Flow.map_zero_apply] using
      hvel.mem_tangentConeAt (Filter.Eventually.of_forall fun t ↦ hS t hyS)
  -- It is nonzero, since `y` lies on a nonconstant trajectory.
  have hgrad : ∇ f y ≠ 0 := fun h ↦ by
    have hinj := Flow.orbit_injective_of_ne_of_mem_unstableSet_inter_stableSet hpq ⟨hyu, hys⟩
    have hfix := (forall_negativeGradientFlow_eq_self_iff f hf y).2 h
    exact zero_ne_one (hinj ((hfix 0).trans (hfix 1).symm))
  have hmem : -∇ f y ∈ Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet φ p) y) ⊓
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet φ q) y) :=
    Submodule.mem_inf.2 ⟨htan (Flow.isInvariant_unstableSet φ p) hyu,
      htan (Flow.isInvariant_stableSet φ q) hys⟩
  have hpos : 0 < Module.finrank ℝ
      (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet φ p) y) ⊓
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet φ q) y) : Submodule ℝ E) := by
    refine Nat.pos_of_ne_zero fun h ↦ hgrad ?_
    rw [Submodule.finrank_eq_zero.1 h, Submodule.mem_bot, neg_eq_zero] at hmem
    exact hmem
  omega

end IsNondegenerateCriticalPoint

end TauCeti
