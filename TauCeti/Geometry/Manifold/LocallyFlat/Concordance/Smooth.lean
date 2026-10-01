/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Concordance.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance

/-!
# Smooth concordances are topological concordances

A smooth concordance (`TauCeti.SmoothEmbedding.Concordance`) between smooth embeddings of
boundaryless manifolds has for track a smooth embedding of `M × ℝ` into `N × ℝ`, and smooth
embeddings of boundaryless manifolds are locally flat
(`TauCeti.IsLocallyFlat.of_isSmoothEmbedding`). So the track is a locally flat embedding, and with
the same collars it is a topological concordance (`TauCeti.TopologicalConcordance`). This file
records that comparison: smooth concordance implies topological concordance, the complementary model
of the topological concordance being the complement of the immersion underlying the track. The
converse fails in general, which is why the two relations are kept apart.

## Main definitions

* `TauCeti.SmoothEmbedding.Concordance.toTopologicalConcordance`: a smooth concordance, read as a
  topological concordance.

## Main results

* `TauCeti.SmoothEmbedding.Concordant.exists_topologicallyConcordant`: smoothly concordant
  embeddings of boundaryless manifolds are topologically concordant, for some complementary model.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology
open scoped Manifold ContDiff

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [I.Boundaryless] [J.Boundaryless]

namespace SmoothEmbedding

variable {f g : SmoothEmbedding I J n M N}

/-- A smooth concordance between smooth embeddings of boundaryless manifolds is a topological
concordance, with the same track: the complementary model is the complement of the immersion
underlying the track. -/
def Concordance.toTopologicalConcordance (Φ : Concordance f g) :
    TopologicalConcordance E Φ.toSmoothEmbedding.isImmersion.complement f g where
  toFun := Φ
  isLocallyFlat_toFun := by
    simpa only [Concordance.coe_toSmoothEmbedding] using Φ.toSmoothEmbedding.isLocallyFlat
  isCollaredTrack_toFun := Φ.isCollaredTrack

@[simp]
theorem Concordance.coe_toTopologicalConcordance (Φ : Concordance f g) :
    ⇑Φ.toTopologicalConcordance = ⇑Φ :=
  (rfl)

/-- A smooth concordance witnesses topological concordance. -/
theorem Concordance.topologicallyConcordant (Φ : Concordance f g) :
    TopologicallyConcordant E Φ.toSmoothEmbedding.isImmersion.complement f g :=
  topologicallyConcordant_iff_nonempty.2 ⟨Φ.toTopologicalConcordance⟩

/-- **Smoothly concordant embeddings of boundaryless manifolds are topologically concordant**, for
some complementary model of the topological concordance. -/
theorem Concordant.exists_topologicallyConcordant (hfg : Concordant f g) :
    ∃ (F' : Type u) (_ : TopologicalSpace F') (_ : Zero F'), TopologicallyConcordant E F' f g := by
  obtain ⟨Φ⟩ := concordant_iff_nonempty.1 hfg
  exact ⟨_, _, _, Φ.topologicallyConcordant⟩

end SmoothEmbedding

end TauCeti
