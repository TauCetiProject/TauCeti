/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
import TauCeti.AlgebraicTopology.Cohomology.Relative
import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Ulift
import TauCeti.Topology.VectorBundle.MayerVietoris.Basic

/-!
# Vanishing of relative homology and cohomology below the Morse–Bott index

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on the level
`f = c`, with Morse index `r` at every point of `i`, and let `a < c < b` be such that the band
`f⁻¹[a, b]` is compact and all its critical points lie on `i`.

Across the level `c`, the relative homology `Hₖ({f ≤ b}, {f ≤ a})` is isomorphic to the relative
homology of the Thom pair of a universe-lifted vector bundle of rank `r` over `S`
(`IsNondegenerateCriticalSubmanifold.exists_thomPair_ulift_singularHomology_iso`), which vanishes
below the rank (`TauCeti.isZero_singularHomology_thomPair_of_compactSpace`). Hence:

* `IsNondegenerateCriticalSubmanifold.isZero_singularHomology_sublevelPair_of_lt`:
  `Hₖ({f ≤ b}, {f ≤ a}; R) = 0` for all `k < r`, with coefficients in any abelian category with
  coproducts;
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
/-- **Across a Morse–Bott level the relative homology vanishes below the index.** Let
`i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `f = c` along `i` and Morse
index `r` at every point of `i`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and
all its critical points lie on `i`. Then `Hₖ({f ≤ b}, {f ≤ a}) = 0` for `k < r`, with coefficients
in any abelian category with coproducts. -/
theorem isZero_singularHomology_sublevelPair_of_lt {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C) {k : ℕ} (hk : k < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularHomology R k) := by
  cases isEmpty_or_nonempty S with
  | inl _ =>
    exact isZero_singularHomology_sublevelPair_of_isEmpty hfs (hac.trans hcb).le hcompact hcrit R k
  | inr _ =>
    have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
      hc hac.le hcb.le hcompact hcrit
    obtain ⟨V, _, _, _, _, _, _, ⟨e⟩⟩ := h.exists_thomPair_ulift_singularHomology_iso
      hfs hc hac hcb hcompact hcrit hr R k
    have hzero : IsZero ((thomPair (ULift.{u} (Fin r) → ℝ) V).singularHomology R k) :=
      isZero_singularHomology_thomPair_of_compactSpace R ((finrank_ulift_fin_fun ℝ r).symm ▸ hk)
    exact hzero.of_iso e

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a Morse–Bott level the relative cohomology vanishes below the index.** Under the
hypotheses of `isZero_singularHomology_sublevelPair_of_lt`, the relative singular cohomology
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
