/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram.Family
import TauCeti.Geometry.Manifold.VectorField.Regularity
import Mathlib.Tactic

/-!
# Continuous metric families and squared gradients

For a continuous family of native Riemannian metrics, the
squared gradient of a locally `C¹` scalar is jointly continuous. The parameter space is an
arbitrary topological space. The argument uses the native inverse-Gram formula for covector norms.

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
/-- The squared gradient of a locally `C¹` scalar is jointly continuous wherever the metric
family is jointly continuous. The parameter space needs only a topology. -/
theorem continuousOn_norm_sq_mgradient_family
    {U : Set M} (hg : ContinuousOn
      (fun p : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (univ ×ˢ U))
    (hU : IsOpen U) {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ) 1 f U) :
    ContinuousOn (fun p : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
      ‖mgradient I f p.2‖ ^ 2) (univ ×ˢ U) := by
  have : IsManifold I (0 + 1) M := by
    simpa only [zero_add] using (inferInstance : IsManifold I 1 M)
  intro p hp
  let V := U ∩ (trivializationAt E (TangentSpace I) p.2).baseSet
  have hV : IsOpen V := hU.inter (trivializationAt E (TangentSpace I) p.2).open_baseSet
  have hD (i : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun q : P × M ↦ mvfderiv I f q.2
        (chartLocalFrame (I := I) p.2 i q.2)) (univ ×ˢ V) :=
    (((hf.mono inter_subset_left).contMDiffOn_mvfderiv_apply hV
      ((contMDiffOn_chartLocalFrame (I := I) (n := 0) p.2 i).mono inter_subset_right)
      (by norm_num)).continuousOn).comp continuousOn_snd (fun _ hq ↦ hq.2)
  have hInv (i j : Fin (Module.finrank ℝ E)) :=
    continuousOn_chartInvGramMatrix_family g
      (hg.mono (prod_mono subset_rfl inter_subset_left)) p.2 (fun _ hq ↦ hq.2.2) i j
  have hsum := continuousOn_finsetSum Finset.univ fun i _ ↦
    continuousOn_finsetSum Finset.univ fun j _ ↦ ((hInv i j).mul (hD i)).mul (hD j)
  have heq : ContinuousOn (fun q : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
      ‖mgradient I f q.2‖ ^ 2) (univ ×ˢ V) := hsum.congr (fun q hq ↦ by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
    have hx : q.2 ∈ (chartAt H p.2).source := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hq.2.2
    -- The finite sum is the native chart-coefficient formula under this installed metric.
    change ‖mgradient I f q.2‖ ^ 2 = ∑ i, ∑ j,
      chartInvGramMatrix (I := I) p.2 q.2 i j *
        mvfderiv I f q.2 (chartLocalFrame (I := I) p.2 i q.2) *
        mvfderiv I f q.2 (chartLocalFrame (I := I) p.2 j q.2)
    rw [norm_mgradient_eq_norm_mvfderiv,
      norm_sq_eq_dotProduct_chartInvGramMatrix_mulVec p.2 hx]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring)
  exact (heq.continuousAt ((isOpen_univ.prod hV).mem_nhds
    ⟨mem_univ _, hp.2, mem_baseSet_trivializationAt E (TangentSpace I) p.2⟩)).continuousWithinAt

end TauCeti.Manifold
