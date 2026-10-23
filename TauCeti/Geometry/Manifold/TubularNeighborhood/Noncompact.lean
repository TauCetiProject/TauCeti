/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
public import TauCeti.Topology.MetricSpace.ContinuousRadius

/-!
# Tubular neighbourhoods with a variable radius

Every `C²` embedded boundaryless manifold in a finite-dimensional real inner product
space has a tubular neighbourhood with a positive continuous radius. Compactness and
closedness of the embedded image are not required. The addition map on the normal
bundle is an open embedding on this neighbourhood.

The local normal-map theorem is `exists_injOn_isOpen_image_normalTube`. The continuous
radius is chosen so that any two intersecting normal discs have their base points in
one local injectivity neighbourhood: use the larger of their two radii. This avoids
the uniform separation bound available only for a compact core.

The result concerns the topology of the normal bundle and does not assert smoothness
of the inverse tubular map.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Theorem 6.24.
-/

public section

open Set Function Topology
open scoped Manifold

namespace TauCeti

variable {V E H M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I 2 M]

/-- **Noncompact Euclidean tubular neighbourhood theorem.** A `C²` immersion inducing
the source topology admits a positive continuous radius on which its normal addition
map is an open embedding. -/
theorem exists_isOpenEmbedding_normalTubeOfRadius {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f) :
    ∃ r : C(M, ℝ), (∀ x, 0 < r x) ∧
      IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
        fun p : M × V => f p.1 + p.2) := by
  choose W hWo hxW δ hδ hinjOn hopen using exists_injOn_isOpen_image_normalTube hf himm
  obtain ⟨r, hr, hloc⟩ := hind.exists_continuous_radius_subordinate W hWo
    (fun x => ⟨x, hxW x⟩) δ hδ
  simp only [mem_normalTube] at hinjOn hopen
  let Φ : M × V → V := fun p => f p.1 + p.2
  -- Compare the larger radius so that both normal vectors lie in one injective patch.
  have hinjT : InjOn Φ (normalTubeOfRadius I f r) := by
    intro p hp q hq heq
    simp only [mem_normalTubeOfRadius] at hp hq
    have hdist : dist (f p.1) (f q.1) < r p.1 + r q.1 := by
      have hsub : f p.1 - f q.1 = q.2 - p.2 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm q.2]
        exact heq
      rw [dist_eq_norm, hsub]
      exact (norm_sub_le _ _).trans_lt (by linarith [hp.2, hq.2])
    rcases le_total (r q.1) (r p.1) with hle | hle
    · obtain ⟨x, hpx, hrδ, hball⟩ := hloc p.1
      have hqx : q.1 ∈ W x := hball q.1 (hdist.trans_le (by linarith))
      exact hinjOn x ⟨hpx, hp.1, hp.2.trans hrδ⟩
        ⟨hqx, hq.1, hq.2.trans_le (hle.trans hrδ.le)⟩ heq
    · obtain ⟨x, hqx, hrδ, hball⟩ := hloc q.1
      have hpx : p.1 ∈ W x := hball p.1 (by rw [dist_comm]; linarith)
      exact hinjOn x ⟨hpx, hp.1, hp.2.trans_le (hle.trans hrδ.le)⟩
        ⟨hqx, hq.1, hq.2.trans hrδ⟩ heq
  have hrad : IsOpen {p : M × V | ‖p.2‖ < r p.1} :=
    isOpen_lt (continuous_norm.comp continuous_snd) (r.continuous.comp continuous_fst)
  refine ⟨r, hr, .of_continuous_injective_isOpenMap ?_
    (fun p q h => Subtype.ext (hinjT p.2 q.2 h)) ?_⟩
  · exact ((hf.continuous.comp continuous_fst).add continuous_snd).comp continuous_subtype_val
  -- Openness follows by covering the variable tube by the local normal tubes.
  · intro U hU
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
    have himage : (normalTubeOfRadius I f r).domRestrict Φ '' (Subtype.val ⁻¹' O) =
        ⋃ x, Φ '' ((O ∩ {p : M × V | ‖p.2‖ < r p.1}) ∩
          {p | p.1 ∈ W x ∧ p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ < δ x}) := by
      ext z
      constructor
      · rintro ⟨⟨p, hp⟩, hpO, rfl⟩
        simp only [mem_normalTubeOfRadius] at hp
        obtain ⟨x, hpx, hrδ, -⟩ := hloc p.1
        exact mem_iUnion.mpr ⟨x, p, ⟨⟨hpO, hp.2⟩, hpx, hp.1, hp.2.trans hrδ⟩, rfl⟩
      · intro hz
        obtain ⟨x, p, ⟨⟨hpO, hpr⟩, -, hpN, -⟩, rfl⟩ := mem_iUnion.mp hz
        exact ⟨⟨p, mem_normalTubeOfRadius.mpr ⟨hpN, hpr⟩⟩, hpO, rfl⟩
    rw [himage]
    exact isOpen_iUnion fun x => hopen x _ (hO.inter hrad)

end TauCeti
