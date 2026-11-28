/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.RankDegreeHomology
import TauCeti.AlgebraicTopology.Cohomology.Relative

/-!
# Vanishing of relative cohomology below the Morse–Bott index

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on the level
`f = c`, with Morse index `r` at every point of `i`, and let `a < c < b` be such that the band
`f⁻¹[a, b]` is compact and all its critical points lie on `i`.

Below the index `r`, the relative singular homology `Hₖ({f ≤ b}, {f ≤ a})` vanishes
(`IsNondegenerateCriticalSubmanifold.isZero_singularHomology_sublevelPair_of_lt` in
`TauCeti.Geometry.Manifold.Morse.Bott.RankDegreeHomology`), so the universal-coefficient vanishing
for singular cohomology (`TopPair.isZero_singularCohomology_of_isZero_singularHomology`) yields:

* `IsNondegenerateCriticalSubmanifold.isZero_singularCohomology_sublevelPair_of_lt`:
  `Hᵐ({f ≤ b}, {f ≤ a}; R, N) = 0` for all `m < r`, whenever the chain coefficients `R` are
  projective.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology
open scoped ContDiff Manifold

universe u

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' : Type*} {S : Type u} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
  (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
  (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a Morse–Bott level the relative cohomology vanishes below the index.** Let
`i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `f = c` along `i` and Morse
index `r` at every point of `i`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and
all its critical points lie on `i`. Then the relative singular cohomology
`Hᵐ({f ≤ b}, {f ≤ a}; R, N)` vanishes for every `m < r` whenever the chain coefficient object
`R` is projective. -/
theorem isZero_singularCohomology_sublevelPair_of_lt {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (N : C) {m : ℕ} (hmr : m < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularCohomology R k N m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R N m fun _ hj ↦
    h.isZero_singularHomology_sublevelPair_of_lt hfs hc hac hcb hcompact hcrit hr R
      (hj.trans_lt hmr)

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
