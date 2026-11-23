/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Family
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian.ChainRule
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram.Family
public import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Joint continuity of scalar operators for metric families

For native smooth Riemannian metrics with jointly `C¹` pairings, the Laplace–Beltrami operator
of a locally `C²` scalar is jointly continuous. The proof uses the native
family Levi–Civita regularity theorem and contracts Hessian coefficients with the inverse chart
Gram matrix.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollaries 4.14–4.15.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  (g : P → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))

open Riemannian.Tensor in
/-- The Laplacian of a locally `C²` scalar is jointly continuous when the metric family is
jointly `C¹` on the same domain. -/
theorem continuousOn_laplaceBeltrami_family
    {U : Set M}
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (univ ×ˢ U))
    (hU : IsOpen U) {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ) 2 f U) :
    ContinuousOn (fun p : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
      laplaceBeltrami I f p.2) (univ ×ˢ U) := by
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := ∞) (by simp)
  intro p hp
  let V := U ∩ (trivializationAt E (TangentSpace I) p.2).baseSet
  have hV : IsOpen V := hU.inter (trivializationAt E (TangentSpace I) p.2).open_baseSet
  have hframe (k : Fin (Module.finrank ℝ E)) :
      ContMDiffOn I I.tangent 1 (T% (chartLocalFrame (I := I) p.2 k)) V :=
    (contMDiffOn_chartLocalFrame p.2 k).mono inter_subset_right
  have hH (i j : Fin (Module.finrank ℝ E)) :=
    (contMDiffOn_hessian_family g
      (hg.mono (prod_mono subset_rfl inter_subset_left)) hV (hf.mono inter_subset_left)
      (hframe i) (hframe j)).continuousOn
  have hInv (i j : Fin (Module.finrank ℝ E)) :=
    continuousOn_chartInvGramMatrix_family
      (fun r ↦ (g r).toContinuousRiemannianMetric)
      (hg.continuousOn.mono (prod_mono subset_rfl inter_subset_left)) p.2
      (fun _ hq ↦ hq.2.2) i j
  have hsum := continuousOn_finsetSum Finset.univ fun i _ ↦
    continuousOn_finsetSum Finset.univ fun j _ ↦ (hInv i j).mul (hH i j)
  have heq : ContinuousOn (fun q : P × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
      laplaceBeltrami I f q.2) (univ ×ˢ V) := hsum.congr (fun q hq ↦ by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
    -- The finite sum is the native chart-coefficient formula under this installed metric.
    change laplaceBeltrami I f q.2 = ∑ i, ∑ j,
      chartInvGramMatrix (I := I) p.2 q.2 i j *
        hessian I f q.2 (chartLocalFrame (I := I) p.2 i q.2)
          (chartLocalFrame (I := I) p.2 j q.2)
    exact laplaceBeltrami_eq_sum_chartInvGramMatrix_hessian p.2
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hq.2.2) f)
  exact (heq.continuousAt ((isOpen_univ.prod hV).mem_nhds
    ⟨mem_univ _, hp.2, mem_baseSet_trivializationAt E (TangentSpace I) p.2⟩)).continuousWithinAt

end TauCeti.Manifold
