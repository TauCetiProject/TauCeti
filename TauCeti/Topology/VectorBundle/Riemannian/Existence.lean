/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.Riemannian

import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.VectorBundle.Bilinear
import TauCeti.Topology.VectorBundle.Section

/-!
# Existence of continuous Riemannian metrics

Every real vector bundle with finite-dimensional fibres over a normal paracompact space (for
instance a paracompact Hausdorff space) carries a continuous Riemannian metric, that is, a
continuously varying family of inner products on its fibres inducing their given topology
(`TauCeti.nonempty_continuousRiemannianMetric`). No compactness, finite cover or bound on the
number of trivializations is assumed.

Such a metric is the input for orthogonal complements of subbundles, for splitting short exact
sequences of vector bundles, and for reducing the structure group of a bundle to an orthogonal
group.

The proof is the classical one. Over the base set of a trivialization `e`, pulling back a fixed
inner product on the model fibre along `e` gives a continuous local metric
(`TauCeti.continuousOn_trivializationAt_pullbackForm`, in
`TauCeti.Topology.VectorBundle.Bilinear`). The fibrewise conditions on a metric
(symmetry, positive definiteness and a von Neumann bounded unit set) cut out a convex set of
continuous bilinear forms on each fibre (`TauCeti.convex_setOfPred_symm_pos_isVonNBounded`), so the
local metrics glue along a partition of unity, by
`TauCeti.exists_continuous_section_forall_mem_convex_of_local`. This is the continuous counterpart
of `TauCeti.nonempty_contMDiffRiemannianMetric`.

## Main results

* `TauCeti.nonempty_continuousRiemannianMetric`: a real vector bundle with finite-dimensional
  fibres over a normal paracompact space has a continuous Riemannian metric.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.2 (inner products on vector bundles over
  paracompact bases, by partitions of unity).
* J. Milnor and J. Stasheff, *Characteristic Classes*, Problem 2-C.
-/

public section

noncomputable section

open Bundle Bornology Set Module

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Existence of continuous Riemannian metrics.** A real vector bundle with finite-dimensional
fibres over a normal paracompact space carries a continuous Riemannian metric. -/
theorem nonempty_continuousRiemannianMetric [∀ b, ContinuousConstSMul ℝ (E b)]
    [NormalSpace B] [ParacompactSpace B] [FiniteDimensional ℝ F] :
    Nonempty (ContinuousRiemannianMetric F E) := by
  -- A fixed inner product `φ` on the model fibre, transported from a Euclidean space.
  let T : F ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let φ : F →L[ℝ] F →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp T.toContinuousLinearMap T.toContinuousLinearMap
  -- The local metric pulled back along the preferred trivialization at `x`.
  let g (x b : B) : E b →L[ℝ] E b →L[ℝ] ℝ :=
    (ContinuousLinearMap.precomp ℝ ((trivializationAt F E x).continuousLinearMapAt ℝ b)).comp
      (φ.comp ((trivializationAt F E x).continuousLinearMapAt ℝ b))
  -- These local instances keep the instance search for the vector bundle structure on the bundle
  -- of bilinear forms within the default budget.
  have : ∀ b, ContinuousAdd (E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  let : ∀ b, AddCommGroup (E b →L[ℝ] E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  obtain ⟨s, hsc, hs⟩ := exists_continuous_section_forall_mem_convex_of_local
    (F := F →L[ℝ] F →L[ℝ] ℝ) (E := fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ)
    (fun b ↦ {g : E b →L[ℝ] E b →L[ℝ] ℝ | (∀ v w, g v w = g w v) ∧
      (∀ v, v ≠ 0 → 0 < g v v) ∧ IsVonNBounded ℝ {v | g v v < 1}})
    (fun _ ↦ convex_setOfPred_symm_pos_isVonNBounded) fun x ↦ by
      refine ⟨(trivializationAt F E x).baseSet,
        (trivializationAt F E x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x),
        g x, continuousOn_trivializationAt_pullbackForm φ x, fun b hb ↦ ?_⟩
      -- Over the base set, `g x b` is the Euclidean inner product read through `T ∘ e b`.
      set L := ((trivializationAt F E x).continuousLinearEquivAt ℝ b hb).trans T
      refine L.mem_setOfPred_symm_pos_isVonNBounded_of_inner fun v w ↦ ?_
      simp [g, φ, L, Trivialization.coe_continuousLinearEquivAt_eq _ hb]
  exact ⟨⟨s, fun b ↦ (hs b).1, fun b ↦ (hs b).2.1, fun b ↦ (hs b).2.2, hsc⟩⟩

end TauCeti
