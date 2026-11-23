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

In the Morse–Bott inequalities a critical submanifold `C` of index `λ` contributes, in degree `j`,
its homology in degree `j - λ` twisted by the orientation sheaf of its negative normal bundle to the
relative homology of the band around its critical level. When that bundle is orientable, or over
`𝔽₂`, this is the shifted Betti number `bⱼ₋λ(C)`. For the constant function there is a single
critical level `c`, crossing it passes from the empty sublevel to all of `M`, and every index is
`0`, so the negative normal bundle is zero and no twist arises. For the constant function `f = c` on
any topological space `X` and over any ring `k`, the relative homology `Hⱼ({f ≤ b}, {f ≤ a}; k)` of
the band, for `a < c ≤ b`, is the homology of `X`, so its dimension is `bⱼ(X; k)`
(`TauCeti.finrank_singularHomology_sublevelPair_const_eq_bettiNumber`): the contribution of the
critical set is the Betti polynomial of the space itself. On a compact boundaryless manifold `M`
and over a division ring `k` this is the sum of the `bⱼ(C; k)` over the components
(`TauCeti.finrank_singularHomology_sublevelPair_const`), as the Morse–Bott contribution of the
critical submanifolds `C` is computed.

## Main results

* `TauCeti.finrank_singularHomology_sublevelPair_const_eq_bettiNumber`: the relative homology
  across the level of a constant function has dimension the Betti number of the space.
* `TauCeti.finrank_singularHomology_sublevelPair_const`: on a compact manifold, the same dimension
  is the sum of the Betti numbers of the components.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Module
open scoped ContDiff Manifold

universe u

namespace TauCeti

/-- **The critical level of a constant function contributes the Betti numbers of the space.** For
the constant function `f = c` on a topological space `X` and `a < c ≤ b`, the relative homology
`Hⱼ({f ≤ b}, {f ≤ a}; k)` has dimension `bⱼ(X; k)`: crossing the level `c` passes from the empty
sublevel to all of `X`. -/
theorem finrank_singularHomology_sublevelPair_const_eq_bettiNumber {X : Type u}
    [TopologicalSpace X] (k : Type u) [Ring k] {a b c : ℝ} (ha : a < c) (hb : c ≤ b) (j : ℕ) :
    finrank k ((sublevelPair (fun _ : X ↦ c) (ha.le.trans hb)).singularHomology
        (ModuleCat.of k k) j : ModuleCat k) = bettiNumber k X j := by
  rw [bettiNumber_def, (singularHomologyIsoSublevelPair (ha.le.trans hb) (fun _ ↦ ha) (fun _ ↦ hb)
    (ModuleCat.of k k) j).toLinearEquiv.finrank_eq]

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
Morse–Bott contribution of the level `c`. It equals `bⱼ(M; k)`
(`TauCeti.finrank_singularHomology_sublevelPair_const_eq_bettiNumber`). -/
theorem finrank_singularHomology_sublevelPair_const (k : Type u) [DivisionRing k] {a b c : ℝ}
    (ha : a < c) (hb : c ≤ b) (j : ℕ) :
    finrank k ((sublevelPair (fun _ : M ↦ c) (ha.le.trans hb)).singularHomology
        (ModuleCat.of k k) j : ModuleCat k) =
      ∑ C : ConnectedComponents M, bettiNumber k C.opens j := by
  rw [finrank_singularHomology_sublevelPair_const_eq_bettiNumber k ha hb,
    bettiNumber_eq_sum_connectedComponents_of_compactSpace I k j]

end TauCeti
