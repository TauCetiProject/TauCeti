/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Existence of Riemannian metrics

Every `C^n` real vector bundle with finite-dimensional fibres over a σ-compact Hausdorff smooth
manifold modelled on a finite-dimensional space carries a `C^n` Riemannian metric
(`TauCeti.nonempty_contMDiffRiemannianMetric`). In particular, such a manifold carries a `C^n`
Riemannian metric on its tangent bundle. Here `n` ranges over `ℕ∞`: the metric is built with smooth
partitions of unity, so the analytic case is not covered.

The proof is the classical one. Over the base set of a trivialization `e`, pulling back a fixed
inner product on the model fibre along `e` gives a local metric. The fibrewise conditions on a
metric (symmetry, positive definiteness and a von Neumann bounded unit set) cut out a convex set of
continuous bilinear forms on each fibre (`TauCeti.convex_setOfPred_symm_pos_isVonNBounded`), so the
local metrics glue along a smooth partition of unity, by Mathlib's
`exists_contMDiffSection_forall_mem_convex_of_local`.

A Riemannian metric is the input of the metric constructions of differential geometry: it splits
the restriction of the tangent bundle of a manifold along a submanifold into tangent and normal
parts, and it gives the exponential maps, distances and volumes built from a metric.

## Main results

* `TauCeti.nonempty_contMDiffRiemannianMetric`: a `C^n` vector bundle with finite-dimensional
  fibres over a σ-compact Hausdorff smooth manifold modelled on a finite-dimensional space has a
  `C^n` Riemannian metric.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition 13.3
  (existence of Riemannian metrics, by partitions of unity); the same argument applies verbatim to
  an arbitrary vector bundle.
-/

public section

noncomputable section

open Bundle Bornology Set Module
open scoped Manifold ContDiff

namespace TauCeti

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Existence of Riemannian metrics.** A `C^n` real vector bundle with finite-dimensional fibres
over a σ-compact Hausdorff smooth manifold modelled on a finite-dimensional space carries a `C^n`
Riemannian metric. -/
theorem nonempty_contMDiffRiemannianMetric [∀ b, ContinuousConstSMul ℝ (E b)]
    [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] [IsManifold IB ∞ B]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F E IB] :
    Nonempty (ContMDiffRiemannianMetric IB n F E) := by
  -- A fixed inner product `φ` on the model fibre, transported from a Euclidean space.
  let T : F ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let φ : F →L[ℝ] F →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp T.toContinuousLinearMap T.toContinuousLinearMap
  have hφ (u w : F) : φ u w = inner ℝ (T u) (T w) := by simp [φ]
  -- The local metric pulled back along the preferred trivialization at `x`.
  let g (x b : B) : E b →L[ℝ] E b →L[ℝ] ℝ :=
    (ContinuousLinearMap.precomp ℝ ((trivializationAt F E x).continuousLinearMapAt ℝ b)).comp
      (φ.comp ((trivializationAt F E x).continuousLinearMapAt ℝ b))
  -- As in `Manifold.contMDiffOn_trivializationAt_pullbackForm`, these local instances keep the
  -- instance search for the bundle of bilinear forms within the default budget.
  have : ∀ b, ContinuousAdd (E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  let : ∀ b, AddCommGroup (E b →L[ℝ] E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local (n := n) IB
    (fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ)
    (fun b ↦ {g : E b →L[ℝ] E b →L[ℝ] ℝ | (∀ v w, g v w = g w v) ∧
      (∀ v, v ≠ 0 → 0 < g v v) ∧ IsVonNBounded ℝ {v | g v v < 1}})
    (fun _ ↦ convex_setOfPred_symm_pos_isVonNBounded) fun x ↦ by
      refine ⟨(trivializationAt F E x).baseSet,
        (trivializationAt F E x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x),
        g x, Manifold.contMDiffOn_trivializationAt_pullbackForm φ x, fun b hb ↦ ?_⟩
      -- Over the base set, `g x b` is `φ` read through the fibre isomorphism `L : E b ≃ F`.
      set L := (trivializationAt F E x).continuousLinearEquivAt ℝ b hb
      have hg (v w : E b) : g x b v w = inner ℝ (T (L v)) (T (L w)) := by
        simp [g, hφ, L, Trivialization.coe_continuousLinearEquivAt_eq _ hb]
      refine ⟨fun v w ↦ by rw [hg, hg, real_inner_comm], fun v hv ↦ ?_, ?_⟩
      · rw [hg, real_inner_self_eq_norm_sq]
        have : T (L v) ≠ 0 := by simpa using hv
        positivity
      · -- The unit set is the image of the Euclidean unit ball under `L⁻¹ ∘ T⁻¹`.
        refine ((NormedSpace.isVonNBounded_ball ℝ _ 1).image
          (L.symm.toContinuousLinearMap.comp T.symm.toContinuousLinearMap)).subset ?_
        intro v hv
        refine ⟨T (L v), ?_, by simp⟩
        rw [mem_ofPred_eq, hg, real_inner_self_eq_norm_sq] at hv
        simpa using (sq_lt_one_iff₀ (norm_nonneg _)).mp hv
  exact ⟨⟨s, fun b ↦ (hs b).1, fun b ↦ (hs b).2.1, fun b ↦ (hs b).2.2, s.contMDiff⟩⟩

/-- **Existence of a Riemannian metric on a manifold.** A finite-dimensional smooth manifold
admits a smooth Riemannian metric on its tangent bundle. -/
theorem nonempty_contMDiffRiemannianMetric_tangentBundle
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) := by
  let _ : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  let _ : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact nonempty_contMDiffRiemannianMetric

end TauCeti
