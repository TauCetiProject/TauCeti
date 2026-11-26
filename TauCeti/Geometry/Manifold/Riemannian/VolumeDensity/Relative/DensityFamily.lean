/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Family

/-!
# Joint continuity of relative volume densities

For a fixed reference metric and a jointly continuous metric family, the relative volume
density is jointly continuous in the parameter and the point of the manifold.
-/

public noncomputable section

open Bundle Set Riemannian.Tensor TauCeti TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable {n n' : ℕ∞ω}

/-- The relative density with respect to a fixed metric is jointly continuous for a jointly
continuous family of metric tensors, with an arbitrary topological parameter space. -/
theorem continuous_relativeVolumeDensity_family
    {A : Type*} [TopologicalSpace A]
    (r : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (g : A → ContMDiffRiemannianMetric I n' E (TangentSpace I : M → Type _))
    (hg : Continuous (fun p : A × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2))) :
    Continuous (fun p : A × M ↦ r.relativeVolumeDensity (g p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let U := (trivializationAt E (TangentSpace I) p.2).baseSet
  have hp : p ∈ (univ : Set A) ×ˢ U := ⟨mem_univ _,
    mem_baseSet_trivializationAt E (TangentSpace I) p.2⟩
  let G (q : A × M) := chartGramMatrix (I := I)
    (WithMetric.toWithMetric (g q.1) p.2) (WithMetric.toWithMetric (g q.1) q.2)
  let R (q : A × M) := chartGramMatrix (I := I)
    (WithMetric.toWithMetric r p.2) (WithMetric.toWithMetric r q.2)
  have hG : ContinuousOn G (univ ×ˢ U) :=
    continuousOn_chartGramMatrix_toWithMetric_family g hg.continuousOn p.2 (fun _ hq ↦ hq.2)
  have hR : ContinuousOn R (univ ×ˢ U) :=
    continuousOn_chartGramMatrix_toWithMetric_family (fun _ : A ↦ r)
      (r.contMDiff.continuous.comp continuous_snd).continuousOn p.2 (fun _ hq ↦ hq.2)
  have hopen : IsOpen ((univ : Set A) ×ˢ U) :=
    isOpen_univ.prod (trivializationAt E (TangentSpace I) p.2).open_baseSet
  have hRne (q : A × M) (hq : q ∈ (univ : Set A) ×ˢ U) : (R q).det ≠ 0 :=
    (chartGramMatrix_det_pos _ (by
      rw [TangentBundle.trivializationAt_baseSet]
      exact (WithMetric.mem_chartAt_source_iff _ _).2 (by
        simpa only [U, TangentBundle.trivializationAt_baseSet] using hq.2))).ne'
  have hratio := ((continuous_id.matrix_det.comp_continuousOn hG).div
    (continuous_id.matrix_det.comp_continuousOn hR) hRne).sqrt
  refine (hratio.congr (fun q hq ↦ ?_)).continuousAt (hopen.mem_nhds hp)
  exact r.relativeVolumeDensity_eq_sqrt_div_chartGramMatrix (g q.1) (by
    simpa only [U, TangentBundle.trivializationAt_baseSet] using hq.2)

end Bundle.ContMDiffRiemannianMetric
