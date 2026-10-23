/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic
public import TauCeti.Analysis.Calculus.Morse.TrajectorySpace
public import TauCeti.Geometry.Manifold.LinearSlice

/-!
# Trajectory spaces of a Morse–Smale negative-gradient flow are manifolds

Let `E` be a finite-dimensional real inner product space and `f : E → ℝ` a `C²` function with
globally Lipschitz gradient. If `f` satisfies the Morse–Smale condition `IsMorseSmale f hf`, the
pointwise results on transverse intersections of unstable and stable sets
(`TauCeti.Analysis.Calculus.Morse.Transversality`, `…TrajectorySpace`) apply at every point, and the
sets they describe are manifolds.

## Main declarations

* `TauCeti.IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet`: under the Morse–Smale
  condition, the set of points on trajectories from `p` to `q` is a `C¹` manifold of dimension
  `morseIndex f p - morseIndex f q`, embedded in `E`.
* `TauCeti.IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet_level`: each level slice
  `W^u(p) ∩ W^s(q) ∩ {f = c}` of it is a `C¹` manifold of dimension
  `morseIndex f p - morseIndex f q - 1`, embedded in `E`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (the Morse–Smale condition).
-/

public section

open scoped Gradient NNReal Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0} {hf : LipschitzWith K (∇ f)} {p q : E} {c : ℝ}

/-- **The connecting locus is a manifold.** Under the Morse–Smale condition, for nondegenerate
critical points `p` and `q` of a `C²` function, the set `W^u(p) ∩ W^s(q)` of points on trajectories
from `p` to `q` is a `C¹` manifold of dimension `morseIndex f p - morseIndex f q`: it is modelled on
any subspace `L` of that dimension, and its inclusion into `E` is `C¹`. -/
theorem IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet (h : IsMorseSmale f hf)
    (hfs : ContDiff ℝ 2 f) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L + morseIndex f q = morseIndex f p) :
    ∃ C : ChartedSpace L ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q), letI := C
      IsManifold 𝓘(ℝ, L) 1 ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) ∧
      ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) 1 (Subtype.val : ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) → E) := by
  refine exists_isManifold_of_finrankSubspaceCharts fun y ⟨hyu, hys⟩ ↦ ?_
  have htr := h.transverse_at hp hq ⟨hyu, hys⟩
  obtain ⟨e, hye, he, hes, hmem⟩ :=
    hp.exists_unstableSet_inter_stableSet_chart hq hfs hf hyu hys htr
  refine ⟨e, _, hye, fun z hz ↦ (he z hz).contMDiffAt, fun z hz ↦ (hes z hz).contMDiffAt, hmem,
    ?_⟩
  have hdim := hp.finrank_span_tangentConeAt_unstableSet_inter_stableSet_add_morseIndex hq hfs hf
    hyu hys htr
  rw [hp.span_tangentConeAt_unstableSet_inter_stableSet hq hfs hf hyu hys htr] at hdim
  omega

/-- **Level slices of the connecting locus are manifolds.** Under the Morse–Smale condition, for
nondegenerate critical points `p` and `q` of a `C²` function, each level slice
`W^u(p) ∩ W^s(q) ∩ {f = c}` is a `C¹` manifold of dimension `morseIndex f p - morseIndex f q - 1`:
it is modelled on any subspace `L` of that dimension, and its inclusion into `E` is `C¹`. -/
theorem IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet_level (h : IsMorseSmale f hf)
    (hfs : ContDiff ℝ 2 f) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L + morseIndex f q + 1 = morseIndex f p) :
    ∃ C : ChartedSpace L ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}), letI := C
      IsManifold 𝓘(ℝ, L) 1 ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) ∧
      ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) 1 (Subtype.val : ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) → E) := by
  have hpq : p ≠ q := by rintro rfl; omega
  refine exists_isManifold_of_finrankSubspaceCharts fun y ⟨⟨hyu, hys⟩, hyc⟩ ↦ ?_
  have htr := h.transverse_at hp hq ⟨hyu, hys⟩
  obtain ⟨e, hye, he, hes, hmem⟩ :=
    hp.exists_unstableSet_inter_stableSet_level_chart hq hfs hf hpq hyu hys htr hyc
  refine ⟨e, _, hye, fun z hz ↦ (he z hz).contMDiffAt, fun z hz ↦ (hes z hz).contMDiffAt, hmem,
    ?_⟩
  have hdim := hp.finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex hq
    hfs hf hpq hyu hys htr hyc
  rw [hp.span_tangentConeAt_unstableSet_inter_stableSet_level hq hfs hf hpq hyu hys htr hyc]
    at hdim
  omega

end TauCeti
