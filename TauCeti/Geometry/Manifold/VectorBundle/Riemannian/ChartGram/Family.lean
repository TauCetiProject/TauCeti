/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import TauCeti.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# Continuous chart Gram coefficients for metric families

A continuous family of native Riemannian metrics has jointly continuous chart Gram and inverse
Gram coefficients. The parameter space needs only a topology. The inverse coefficients serve
both the Riesz representation of differentials and the contraction of Hessians.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 3.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {P : Type*} [TopologicalSpace P]
  (g : P → ContinuousRiemannianMetric E (TangentSpace I : M → Type _))

open Riemannian.Tensor in
/-- Chart Gram entries are jointly continuous on any set where the metric family is continuous
and the spatial points lie in the chart base set. -/
theorem continuousOn_chartGramMatrix_family
    {S : Set (P × M)} (hg : ContinuousOn
      (fun p : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) S)
    (α : M) (hS : ∀ p ∈ S, p.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
      chartGramMatrix (I := I) α p.2 i j)
      S := by
  have : IsManifold I (0 + 1) M := by
    simpa only [zero_add] using (inferInstance : IsManifold I 1 M)
  have hframe (k : Fin (Module.finrank ℝ E)) :
      ContinuousOn
        (fun p : P × M ↦ TotalSpace.mk' E p.2 (chartLocalFrame (I := I) α k p.2))
        S :=
    (contMDiffOn_chartLocalFrame (I := I) (n := 0) α k).continuousOn.comp
      continuousOn_snd hS
  intro p hp
  have hpair := hg.clm_bundle_apply₂ (hframe i) (hframe j) p hp
  simp only [FiberBundle.continuousWithinAt_totalSpace] at hpair
  refine hpair.2.congr_of_eventuallyEq_of_mem (Filter.Eventually.of_forall fun q ↦ ?_) hp
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
  -- Evaluate the metric-dependent coefficient after installing this parameter metric.
  change chartGramMatrix (I := I) α q.2 i j = _
  rw [chartGramMatrix_apply]
  rfl

open Riemannian.Tensor in
/-- Inverse chart Gram entries are jointly continuous on any set where the metric family is
continuous and the spatial points lie in the chart base set. -/
theorem continuousOn_chartInvGramMatrix_family
    {S : Set (P × M)} (hg : ContinuousOn
      (fun p : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) S)
    (α : M) (hS : ∀ p ∈ S, p.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
      chartInvGramMatrix (I := I) α p.2 i j)
      S := by
  let A (p : P × M) :=
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
    chartGramMatrix (I := I) α p.2
  have hA : ContinuousOn A S :=
    continuousOn_pi.mpr fun k ↦ continuousOn_pi.mpr fun l ↦
      continuousOn_chartGramMatrix_family g hg α hS k l
  intro p hp
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
  have hdet : (A p).det ≠ 0 := (chartGramMatrix_det_pos (I := I) α (hS p hp)).ne'
  have hinv : ContinuousAt Inv.inv (A p) := continuousAt_matrix_inv (A p) (by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))
  have hi' : ContinuousWithinAt (fun q : P × M ↦ (A q)⁻¹ i j)
      S p :=
    continuousWithinAt_pi.mp
      (continuousWithinAt_pi.mp (hinv.comp_continuousWithinAt (hA p hp)) i) j
  have heq : (fun q : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
      chartInvGramMatrix (I := I) α q.2 i j) = fun q ↦ (A q)⁻¹ i j := by
    funext q
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
    -- Unfold only the local matrix family; the inverse-Gram identity handles inversion.
    dsimp only [A]
    change chartInvGramMatrix (I := I) α q.2 i j =
      (chartGramMatrix (I := I) α q.2)⁻¹ i j
    rw [chartInvGramMatrix_def]
  rw [heq]
  exact hi'

end TauCeti.Manifold
