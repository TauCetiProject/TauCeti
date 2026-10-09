/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Radius
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Noncompact

/-!
# Smooth tubular radii

The Euclidean tubular neighbourhood of a `C²` embedding of a smooth boundaryless manifold can be
chosen with a positive smooth radius. Its entire closed normal disc bundle can be made to
map into any prescribed open neighbourhood of the embedded image. The open normal tube
retains the normal addition map as an open embedding.

This supplies smooth radii for fibrewise radial reparametrization. It asserts an open
embedding, rather than smoothness of the inverse addition map, which requires a separate
local normal-coordinate argument.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {V E H M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- A `C²` Euclidean embedding of a smooth manifold admits a positive smooth tubular radius.
Even the ambient closed balls of this radius stay inside the prescribed neighbourhood. -/
theorem exists_isOpenEmbedding_normalTubeOfRadius_contMDiff_subset {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧
      IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      ∀ x v, ‖v‖ ≤ r x → f x + v ∈ O := by
  have : T1Space M := I.t1Space M
  have : T2Space M := hind.isEmbedding.t2Space
  obtain ⟨R, hR, hemb⟩ := exists_isOpenEmbedding_normalTubeOfRadius hf
    himm hind
  let U : Set (M × V) := (fun p => f p.1 + p.2) ⁻¹' O
  have hU : IsOpen U :=
    hO.preimage ((hf.continuous.comp continuous_fst).add continuous_snd)
  have hzero : ∀ x, (x, (0 : V)) ∈ U := by
    intro x
    simpa [U] using hfO (mem_range_self x)
  obtain ⟨r, hr, hrR, hdisc⟩ := hU.exists_contMDiffMap_closedBall_subset (I := I)
    hzero R.continuous hR
  refine ⟨r, hr, isOpenEmbedding_normalTubeOfRadius_of_le r.contMDiff.continuous
    (fun x => (hrR x).le) hemb, ?_⟩
  intro x v hv
  exact hdisc x v (by simpa using hv)

end TauCeti
