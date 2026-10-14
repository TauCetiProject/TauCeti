/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TrajectorySpace
public import TauCeti.Geometry.Manifold.LinearSlice

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
* `TauCeti.isMorseSmale_iff`: the unfolded form of the predicate, its introduction and
  elimination rule outside this file.
* `TauCeti.isMorseSmale_congr`: the predicate does not depend on the Lipschitz witness.
* `TauCeti.IsMorseSmale.morseIndex_lt`: for a Morse–Smale function, a trajectory between two
  different nondegenerate critical points runs from higher to strictly lower Morse index.
* `TauCeti.IsMorseSmale.unstableSet_inter_stableSet_eq_empty`: consequently no trajectory runs
  from `p` to a different nondegenerate critical point `q` with `morseIndex f p ≤ morseIndex f q`.
* `TauCeti.IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet`: under the Morse–Smale
  condition, the set of points on trajectories from `p` to `q` is a `C¹` manifold of dimension
  `morseIndex f p - morseIndex f q`, embedded in `E`.
* `TauCeti.IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet_level`: each level slice
  `W^u(p) ∩ W^s(q) ∩ {f = c}` of it is a `C¹` manifold of dimension
  `morseIndex f p - morseIndex f q - 1`, embedded in `E`. For `f q < c < f p` every trajectory
  from `p` to `q` crosses this slice exactly once, so it is then a model of the space of
  unparametrized trajectories; for other values of `c` it is empty when `p ≠ q`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (the Morse–Smale condition).
-/

public section

open scoped Gradient NNReal Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The Morse–Smale condition.** For a function `f` with `K`-Lipschitz gradient, the unstable set
of each nondegenerate critical point `p` and the stable set of each nondegenerate critical point `q`
of the negative-gradient flow are transverse at each common point `y`: the spans of their tangent
cones at `y` together span the whole space. (When `f` is `C²`, these sets are manifolds near `y`
and these spans are their tangent spaces.) -/
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
    (h hp hq hyu hys)

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

variable {c : ℝ}

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
  have htr := h hp hq hyu hys
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
it is modelled on any subspace `L` of that dimension, and its inclusion into `E` is `C¹`. (For an
intermediate level `f q < c < f p` this slice meets each trajectory from `p` to `q` exactly once;
for other levels it may be empty.) -/
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
  have htr := h hp hq hyu hys
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
