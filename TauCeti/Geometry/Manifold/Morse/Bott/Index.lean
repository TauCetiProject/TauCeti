/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic

/-!
# The critical value and the index of a Morse–Bott critical submanifold

Along a critical submanifold `i : S → M` of a function `f`, both the value of `f` and, in the
Morse–Bott case, the Morse index of `f` are locally constant. Hence on each connected component of
`S` the function `f` takes a single critical value, and every point has the same Morse index, the
**index of the component**. These are the invariants that enter the Morse–Bott inequalities and the
attachment of negative disc bundles: the negative normal bundle of a component has constant rank
equal to its index.

The value is locally constant because `d(f ∘ i) = df ∘ di` vanishes on `S`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isLocallyConstant_comp`). For the index, recall
from `TauCeti.Geometry.Manifold.Morse.Bott.Basic` that at each point the Morse indices of `f` and
`-f` add up to the codimension of `S`
(`IsNondegenerateCriticalSubmanifold.manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank`).
Both indices are lower semicontinuous on the critical set
(`TauCeti.eventually_manifoldMorseIndex_le`), since a negative-definite subspace of the Hessian
stays negative-definite at nearby points. Two lower semicontinuous functions with constant sum are
locally constant. The same argument fails without the Morse–Bott condition, where the index can
jump along a degenerate critical submanifold.

## Main declarations

* `IsNondegenerateCriticalSubmanifold.eventually_manifoldMorseIndex_eq` and
  `IsNondegenerateCriticalSubmanifold.isLocallyConstant_manifoldMorseIndex`, in the namespace
  `TauCeti.SmoothEmbedding`: the Morse index is locally constant along a Morse–Bott critical
  submanifold.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Filter Function Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ}

namespace SmoothEmbedding

variable {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
include hn

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] [FiniteDimensional ℝ E]
  (h : i.IsNondegenerateCriticalSubmanifold f)
include h

/-- **The Morse index is locally constant along a Morse–Bott critical submanifold.** At every
point near `s₀`, the Morse index of `f` at `i s` equals its Morse index at `i s₀`. -/
theorem eventually_manifoldMorseIndex_eq (s₀ : S) :
    ∀ᶠ s in 𝓝 s₀, manifoldMorseIndex I f (i s) = manifoldMorseIndex I f (i s₀) := by
  -- The indices of `f` and `-f` are both lower semicontinuous on the critical set, and their sum
  -- is the codimension of the submanifold, so neither can jump.
  have hi : ContinuousAt i s₀ := (i.contMDiff s₀).continuousAt
  filter_upwards [hi.eventually (eventually_manifoldMorseIndex_le (h.contMDiffAt s₀)),
    hi.eventually (eventually_manifoldMorseIndex_le (h.neg.contMDiffAt s₀))] with s hle hle'
  have hsum := h.manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank hn s
  have hsum₀ := h.manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank hn s₀
  have h₁ := hle (h.mem_criticalPoints s)
  have h₂ := hle' (h.neg.mem_criticalPoints s)
  omega

/-- **The index of a Morse–Bott critical submanifold.** The Morse index of `f` is a locally
constant function on a Morse–Bott critical submanifold, so it is constant on each connected
component (`IsLocallyConstant.apply_eq_of_preconnectedSpace`). By
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.neg`, the same holds for the Morse
index of `-f`. -/
theorem isLocallyConstant_manifoldMorseIndex :
    IsLocallyConstant fun s ↦ manifoldMorseIndex I f (i s) :=
  (IsLocallyConstant.iff_eventually_eq _).2 (h.eventually_manifoldMorseIndex_eq hn)

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

end TauCeti
