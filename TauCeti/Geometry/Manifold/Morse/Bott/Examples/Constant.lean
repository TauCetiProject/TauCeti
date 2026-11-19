/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.BettiNumber
import TauCeti.AlgebraicTopology.Singular.Sublevel

/-!
# The constant function as a Morse–Bott function

A constant function `f = c` on a locally connected boundaryless manifold `M` is the extreme case
of a Morse–Bott function. Every point is critical, the critical submanifolds are the connected
components `C` of `M`, each embedded as an open subset (`TauCeti.isMorseBottFamily_ofOpens_const`),
their normal spaces are zero (`TauCeti.SmoothEmbedding.subsingleton_normalSpace_ofOpens`), and
the Morse index vanishes everywhere (`TauCeti.manifoldMorseIndex_const`). Unless `M` is empty or
zero-dimensional, `f` is not a Morse function (`TauCeti.isMorse_const_iff`): its Hessian vanishes,
so its critical points are degenerate.

In the Morse–Bott inequalities a critical submanifold `C` of index `λ` contributes its Betti numbers
shifted by `λ`, that is `bⱼ₋λ(C)` in degree `j`, to the relative homology of the band around its
critical level. For the constant function there is a single critical level `c`, crossing it passes
from the empty sublevel to all of `M`, and every index is `0`. On a compact manifold the relative
homology `Hⱼ({f ≤ b}, {f ≤ a}; k)` of the band, for `a < c ≤ b`, therefore has dimension the sum of
the `bⱼ(C; k)` over the components (`TauCeti.finrank_singularHomology_sublevelPair_const`), which
is `bⱼ(M; k)` (`TauCeti.bettiNumber_eq_sum_connectedComponents_of_compactSpace`): the contribution
of the critical set is the Betti polynomial of `M` itself.

## Main results

* `TauCeti.finrank_singularHomology_sublevelPair_const`: the relative homology across the level of
  a constant function has dimension the sum of the Betti numbers of the components.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Module
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [LocallyConnectedSpace M]
  [Fintype (ConnectedComponents M)]

variable (I) in
include I in
/-- **The critical level of a constant function contributes the Betti numbers of the manifold.**
Let `M` be a compact boundaryless manifold and `k` a division ring. For the constant function
`f = c` and `a < c ≤ b`, the relative homology `Hⱼ({f ≤ b}, {f ≤ a}; k)` has dimension the sum,
over the connected components `C` of `M`, of `bⱼ(C; k)`. The components are the critical
submanifolds of `f` (`TauCeti.isMorseBottFamily_ofOpens_const`), all of index `0`, so this is the
Morse–Bott contribution of the level `c`, and it equals `bⱼ(M; k)`
(`TauCeti.bettiNumber_eq_sum_connectedComponents_of_compactSpace`). -/
theorem finrank_singularHomology_sublevelPair_const (k : Type u) [DivisionRing k] {a b c : ℝ}
    (ha : a < c) (hb : c ≤ b) (j : ℕ) :
    finrank k ((sublevelPair (fun _ : M ↦ c) (ha.le.trans hb)).singularHomology
        (ModuleCat.of k k) j : ModuleCat k) =
      ∑ C : ConnectedComponents M, bettiNumber k C.opens j := by
  rw [← bettiNumber_eq_sum_connectedComponents_of_compactSpace I k j, bettiNumber_def,
    (singularHomologyIsoSublevelPair (ha.le.trans hb) (fun _ ↦ ha) (fun _ ↦ hb)
      (ModuleCat.of k k) j).toLinearEquiv.finrank_eq]

end TauCeti
