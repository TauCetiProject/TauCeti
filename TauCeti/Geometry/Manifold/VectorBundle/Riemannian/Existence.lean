/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
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

The same gluing extends metrics given near closed sets. If `A i` is a locally finite family of
pairwise disjoint closed sets, and `β i` is a smooth field of positive definite symmetric bilinear
forms on a neighbourhood of `A i`, then some metric equals `β i` over `A i` for every `i`
(`TauCeti.exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite`). For instance, a metric can
be prescribed to be Euclidean in given coordinates near finitely many points. More generally, the
metric can also be required to satisfy a convex fibrewise condition, given local metrics satisfying
it (`TauCeti.exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite`).

A Riemannian metric is the input of the metric constructions of differential geometry: it splits
the restriction of the tangent bundle of a manifold along a submanifold into tangent and normal
parts, and it gives the exponential maps, distances and volumes built from a metric.

## Main results

* `TauCeti.nonempty_contMDiffRiemannianMetric`: a `C^n` vector bundle with finite-dimensional
  fibres over a σ-compact Hausdorff smooth manifold modelled on a finite-dimensional space has a
  `C^n` Riemannian metric.
* `TauCeti.exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite`: there is a `C^n` Riemannian
  metric with prescribed values over each set of a locally finite family of pairwise disjoint
  closed sets.
* `TauCeti.exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite`: the same,
  for a metric which moreover satisfies a given convex fibrewise condition.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition 13.3
  (existence of Riemannian metrics, by partitions of unity); the same argument applies verbatim to
  an arbitrary vector bundle.
-/

public section

noncomputable section

open Bundle Bornology Function Set Module
open scoped Manifold ContDiff Topology

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
      -- Over the base set, `g x b` is the Euclidean inner product read through `T ∘ e b`.
      set L := ((trivializationAt F E x).continuousLinearEquivAt ℝ b hb).trans T
      refine L.mem_setOfPred_symm_pos_isVonNBounded_of_inner fun v w ↦ ?_
      simp [g, φ, L, Trivialization.coe_continuousLinearEquivAt_eq _ hb]
  exact ⟨⟨s, fun b ↦ (hs b).1, fun b ↦ (hs b).2.1, fun b ↦ (hs b).2.2, s.contMDiff⟩⟩

/-- **Riemannian metrics with prescribed values on closed sets and a convex fibrewise condition.**
Let `A i` be a locally finite family of pairwise disjoint closed subsets of a σ-compact Hausdorff
smooth manifold modelled on a finite-dimensional space. For each `i` let `β i` be a field of
bilinear forms on the fibres of a vector bundle with finite-dimensional fibres, which on an open
neighbourhood `U i` of `A i` is `C^n`, symmetric, positive definite and lies in a convex set
`c b` of forms over each point `b`. Suppose also that near each point outside `⋃ i, A i` there is a
local `C^n` field of symmetric positive definite forms lying in `c`. Then there is a `C^n`
Riemannian metric equal to `β i` over `A i`, for every `i`, and lying in `c b` over every `b`. -/
theorem exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite
    [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] [IsManifold IB ∞ B]
    [FiniteDimensional ℝ F]
    {ι : Type*} {A U : ι → Set B} {β : ι → (b : B) → E b →L[ℝ] E b →L[ℝ] ℝ}
    {c : (b : B) → Set (E b →L[ℝ] E b →L[ℝ] ℝ)}
    (hA : ∀ i, IsClosed (A i)) (hAf : LocallyFinite A) (hAd : Pairwise (Disjoint on A))
    (hU : ∀ i, IsOpen (U i)) (hAU : ∀ i, A i ⊆ U i)
    (hβ : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (β i b)) (U i))
    (hsymm : ∀ i, ∀ b ∈ U i, ∀ v w, β i b v w = β i b w v)
    (hpos : ∀ i, ∀ b ∈ U i, ∀ v, v ≠ 0 → 0 < β i b v v)
    (hc : ∀ b, Convex ℝ (c b)) (hβc : ∀ i, ∀ b ∈ U i, β i b ∈ c b)
    (hloc : ∀ x₀ ∉ ⋃ i, A i, ∃ V ∈ 𝓝 x₀, ∃ s : (b : B) → E b →L[ℝ] E b →L[ℝ] ℝ,
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
        (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (s b)) V ∧
      ∀ b ∈ V, ((∀ v w, s b v w = s b w v) ∧ ∀ v, v ≠ 0 → 0 < s b v v) ∧ s b ∈ c b) :
    ∃ g : ContMDiffRiemannianMetric IB n F E,
      (∀ i, ∀ b ∈ A i, g.inner b = β i b) ∧ ∀ b, g.inner b ∈ c b := by
  -- As in `nonempty_contMDiffRiemannianMetric`, these local instances keep the instance search
  -- for the bundle of bilinear forms within the default budget.
  have : ∀ b, ContinuousAdd (E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  let : ∀ b, AddCommGroup (E b →L[ℝ] E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  -- The fibrewise conditions: a positive definite symmetric form in `c b`, equal to `β i b` if
  -- `b ∈ A i`. Each is convex.
  let t (b : B) : Set (E b →L[ℝ] E b →L[ℝ] ℝ) :=
    ({s | (∀ v w, s v w = s w v) ∧ ∀ v, v ≠ 0 → 0 < s v v} ∩ c b) ∩
      {s | ∀ i, b ∈ A i → s = β i b}
  have ht (b : B) : Convex ℝ (t b) :=
    (convex_setOfPred_symm_pos.inter (hc b)).inter fun s hs s' hs' a d _ _ had i hb ↦ by
      rw [hs i hb, hs' i hb, ← add_smul, had, one_smul]
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local (n := n) IB
    (fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ) t ht fun x₀ ↦ by
      by_cases hx₀ : x₀ ∈ ⋃ i, A i
      · -- Near a point of `A i`, away from the other closed sets `A j`: the form `β i`.
        obtain ⟨i, hi⟩ := mem_iUnion.1 hx₀
        have hcl : IsClosed (⋃ j : {j // j ≠ i}, A j) :=
          (hAf.comp_injective Subtype.coe_injective).isClosed_iUnion fun j ↦ hA j
        have hx₀c : x₀ ∉ ⋃ j : {j // j ≠ i}, A j := fun h ↦ by
          obtain ⟨j, hj⟩ := mem_iUnion.1 h
          exact (hAd j.property.symm).le_bot ⟨hi, hj⟩
        refine ⟨U i ∩ (⋃ j : {j // j ≠ i}, A j)ᶜ,
          ((hU i).inter hcl.isOpen_compl).mem_nhds ⟨hAU i hi, hx₀c⟩, β i,
          (hβ i).mono inter_subset_left, fun y hy ↦
            ⟨⟨⟨hsymm i y hy.1, hpos i y hy.1⟩, hβc i y hy.1⟩, fun j hj ↦ ?_⟩⟩
        obtain rfl : i = j := by
          by_contra hne
          exact hy.2 (mem_iUnion.2 ⟨⟨j, Ne.symm hne⟩, hj⟩)
        rfl
      · -- Away from all the sets `A i`: the given local field.
        obtain ⟨V, hV, s, hs, hsV⟩ := hloc x₀ hx₀
        refine ⟨V ∩ (⋃ i, A i)ᶜ,
          Filter.inter_mem hV ((hAf.isClosed_iUnion hA).isOpen_compl.mem_nhds hx₀), s,
          hs.mono inter_subset_left, fun y hy ↦
            ⟨hsV y hy.1, fun i hi ↦ (hy.2 (mem_iUnion.2 ⟨i, hi⟩)).elim⟩⟩
  let G : ContMDiffRiemannianMetric IB n F E :=
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection σ
      ((Manifold.mem_positiveDefiniteBilinearSections _).2
        ⟨(Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ (hσ x).1.1.1 v w,
          fun x v hv ↦ (hσ x).1.1.2 v hv⟩)
  have hG (b : B) : G.inner b = σ b := by
    ext v w
    exact ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ b v w
  exact ⟨G, fun i b hb ↦ by rw [hG, ← (hσ b).2 i hb], fun b ↦ hG b ▸ (hσ b).1.2⟩

/-- **Riemannian metrics with prescribed values on closed sets.** Let `A i` be a locally finite
family of pairwise disjoint closed subsets of a σ-compact Hausdorff smooth manifold modelled on a
finite-dimensional space. For each `i` let `β i` be a field of bilinear forms on the fibres of a
`C^n` vector bundle with finite-dimensional fibres, which on an open neighbourhood `U i` of `A i`
is `C^n`, symmetric and positive definite. Then there is a `C^n` Riemannian metric equal to `β i`
over `A i`, for every `i`. -/
theorem exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite
    [∀ b, ContinuousConstSMul ℝ (E b)] [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]
    [IsManifold IB ∞ B] [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F E IB]
    {ι : Type*} {A U : ι → Set B} {β : ι → (b : B) → E b →L[ℝ] E b →L[ℝ] ℝ}
    (hA : ∀ i, IsClosed (A i)) (hAf : LocallyFinite A) (hAd : Pairwise (Disjoint on A))
    (hU : ∀ i, IsOpen (U i)) (hAU : ∀ i, A i ⊆ U i)
    (hβ : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (β i b)) (U i))
    (hsymm : ∀ i, ∀ b ∈ U i, ∀ v w, β i b v w = β i b w v)
    (hpos : ∀ i, ∀ b ∈ U i, ∀ v, v ≠ 0 → 0 < β i b v v) :
    ∃ g : ContMDiffRiemannianMetric IB n F E, ∀ i, ∀ b ∈ A i, g.inner b = β i b := by
  -- Away from the sets `A i`, any metric `g₀` is a local field of forms.
  obtain ⟨g₀⟩ := nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := E)
  obtain ⟨g, hg, -⟩ := exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite
    (c := fun _ ↦ univ) hA hAf hAd hU hAU hβ hsymm hpos (fun _ ↦ convex_univ)
    (fun _ _ _ ↦ mem_univ _) fun _ _ ↦ ⟨univ, Filter.univ_mem, g₀.inner,
      g₀.contMDiff.contMDiffOn, fun y _ ↦ ⟨⟨g₀.symm y, g₀.pos y⟩, mem_univ _⟩⟩
  exact ⟨g, hg⟩

end TauCeti
