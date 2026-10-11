/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Topology.Homotopy.Isotopy.Track

/-!
# Smooth tracks and their split differentials

The time-preserving track `(t, x) ↦ (t, F(t, x))` of a smooth isotopy is jointly
smooth. Its differential admits a continuous linear left inverse whenever the
isotopy has positive differentiability order. For compact sources and Hausdorff
targets, the track is also a closed topological embedding.

These results supply the space-time image and its split tangent directions used
when extending the velocity of an isotopy to an ambient vector field. They apply
to manifolds with corners and infinite-dimensional models. A split differential
is not asserted to provide an immersion normal form at boundary points.

Reference: M. Hirsch, *Differential Topology*, Chapter 8, §1, the proof of the
isotopy extension theorem. The differential calculation uses Mathlib's product
chain rule and `Manifold.IsImmersion.isDiffImmersionAt`.
-/

public section

namespace TauCeti.SmoothIsotopy

open Set Topology
open scoped Manifold ContDiff

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} {f₀ f₁ : C^n⟮I, M; J, N⟯}

/-- The smooth time-preserving track of an isotopy through smooth embeddings. -/
def track (F : SmoothIsotopy f₀ f₁) :
    C^n⟮(𝓡∂ 1).prod I, unitInterval × M; (𝓡∂ 1).prod J, unitInterval × N⟯ :=
  ⟨fun p => (p.1, F p), contMDiff_fst.prodMk F.contMDiff⟩

/-- The smooth track records time and the moving point. -/
@[simp] theorem track_apply (F : SmoothIsotopy f₀ f₁) (p : unitInterval × M) :
    F.track p = (p.1, F p) := (rfl)

/-- Forgetting smoothness preserves the track. -/
@[simp] theorem toContinuousMap_track (F : SmoothIsotopy f₀ f₁) :
    _root_.toContinuousMap F.track = F.toIsotopy.track := by
  apply ContinuousMap.ext
  intro p
  exact (F.track_apply p).trans (by simp)

/-- The smooth track of a compact-source isotopy into a Hausdorff manifold is a
closed topological embedding. -/
theorem isClosedEmbedding_track [CompactSpace M] [T2Space N] (F : SmoothIsotopy f₀ f₁) :
    IsClosedEmbedding F.track := by
  have h := F.toIsotopy.isClosedEmbedding_track
  rwa [← F.toContinuousMap_track] at h

/-- At positive differentiability order, every differential of the track has a
continuous linear left inverse. No compactness or finite-dimensionality is required. -/
theorem hasLeftInverse_mfderiv_track (F : SmoothIsotopy f₀ f₁) (hn : n ≠ 0)
    (p : unitInterval × M) :
    (mfderiv ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) F.track p).HasLeftInverse := by
  have hs := (F.isSmoothEmbedding p.1).isImmersion.isDiffImmersionAt hn p.2
  have ht := (F.contMDiff.mdifferentiableAt hn (x := p)).hasLeftInverse_mfderiv_fst_prod_iff
  rw [isDiffImmersionAt_iff] at hs
  -- `track_apply` identifies the bundled track with the parameter-preserving function.
  have htrack : (F.track : unitInterval × M → unitInterval × N) =
      (fun q => (q.1, F q)) := funext F.track_apply
  rw [htrack]
  exact ht.mpr hs

end TauCeti.SmoothIsotopy
