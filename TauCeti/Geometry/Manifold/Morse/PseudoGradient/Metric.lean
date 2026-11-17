/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.EuclideanMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.WithGradient
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.WithGradient

/-!
# Adapted pseudo-gradients are negative gradients

Let `f` be a smooth function on a boundaryless σ-compact Hausdorff manifold `M`, modelled on a
finite-dimensional real space, and let `X` be a pseudo-gradient adapted to `f`
(`TauCeti.IsAdaptedPseudoGradient`). Then `X` is the negative gradient of `f` for some smooth
Riemannian metric `g` on `M`
(`TauCeti.IsAdaptedPseudoGradient.exists_contMDiffRiemannianMetric_neg_mgradient_eq`):
`g (X, ·) = -df`, that is `X = -grad_g f`. This is a converse of
`TauCeti.isAdaptedPseudoGradient_neg_mgradient`: results about negative gradient flows of smooth
metrics apply to the flow of every adapted pseudo-gradient. Moreover `g` can be prescribed
to be the Euclidean metric of the coordinates of given Morse charts, in which `X` is linear, on
given pairwise disjoint closed sets inside them, forming a locally finite family, for instance on
closed balls around the critical points (`exists_contMDiffRiemannianMetric_inner_eq_euclideanForm`).

The metric is glued from local metrics by a partition of unity, as in
`TauCeti.nonempty_contMDiffRiemannianMetric`. The fibrewise condition `g (X, ·) = -df` is affine in
`g`, so it survives convex combinations together with symmetry and positivity. Two kinds of local
metrics satisfy it.

* On the source of a Morse chart in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, the Euclidean
  metric of the coordinates (`TauCeti.MorseChart.euclideanForm`): there
  `f = f x + (1/2) Σᵢ wᵢ zᵢ²`, so `X` is the Euclidean negative gradient of `f`
  (`TauCeti.MorseChart.euclideanForm_apply_left_eq_neg_mvfderiv`). This covers the critical points.
* Where `df (X) < 0`, any metric `g₀` modified so that `X` becomes the gradient of `α = -df`, by
  `g (w, z) = g₀ (P w, P z) + α w * α z / α X` with `P w = w - (α w / α X) • X`
  (`ContinuousLinearMap.withGradient`). This covers the regular points.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm`: a
  smooth metric with `g (X, ·) = -df` which is the Euclidean metric of given Morse charts on given
  closed sets.
* `TauCeti.IsAdaptedPseudoGradient.exists_contMDiffRiemannianMetric_neg_mgradient_eq`: **every
  adapted pseudo-gradient is a negative gradient**, `X = -grad_g f` for a smooth metric `g`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2 (pseudo-gradient fields and gradient fields).
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, §3
  (gradient-like vector fields are gradients for suitable metrics).
-/

public section

open Bundle Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] {ι : Type*} {p : ι → M}

/-- The conditions on a metric at `y`: a symmetric positive definite bilinear form `s` on `T_y M`
with `s (X y, ·) = -df_y`, equal to the Euclidean metric of `φ i` if `y ∈ A i`. -/
private def metricCondition (X : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (φ : ∀ i, MorseChart E f (p i)) (A : ι → Set M) (y : M) :
    Set (TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) :=
  {s | (∀ v w, s v w = s w v) ∧ ∀ v, v ≠ 0 → 0 < s v v} ∩
    ({s | ∀ w, s (X y) w = -mvfderiv 𝓘(ℝ, E) f y w} ∩
      {s | ∀ i, y ∈ A i → s = (φ i).euclideanForm y})

/-- A smooth local metric satisfying the conditions near `y₀`: a field of bilinear forms which is
`C^∞` on a neighbourhood `U` of `y₀` and satisfies `metricCondition` at every point of `U`. -/
private def HasLocalMetric (X : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (φ : ∀ i, MorseChart E f (p i)) (A : ι → Set M) (y₀ : M) : Prop :=
  ∃ U ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ,
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) y
        (s y)) U ∧
    ∀ y ∈ U, s y ∈ metricCondition X φ A y

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The Euclidean metric of a Morse chart in which `X` is linear satisfies the conditions at a point
of the source of the chart, provided it is the prescribed metric on the sets `A i` there. -/
private theorem euclideanForm_mem_metricCondition {φ : ∀ i, MorseChart E f (p i)} {A : ι → Set M}
    {z : M} (ψ : MorseChart E f z)
    (hψ : ∀ y ∈ ψ.toChart.source, ψ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.toChart y (X y)) =
      fun j ↦ -(ψ.weight j * ψ.coord (ψ.toChart y) j))
    {y : M} (hy : y ∈ ψ.toChart.source)
    (hA : ∀ i, y ∈ A i → ψ.euclideanForm y = (φ i).euclideanForm y) :
    ψ.euclideanForm y ∈ metricCondition X φ A y :=
  ⟨⟨ψ.euclideanForm_comm y, fun _ hv ↦ ψ.euclideanForm_self_pos hy hv⟩,
    ψ.euclideanForm_apply_left_eq_neg_mvfderiv hψ hy, hA⟩

/-- Near a point of `A i`, the Euclidean metric of `φ i` is a local metric satisfying the
conditions: the other sets `A j` are disjoint from `A i`, and their union is closed. -/
private theorem exists_nhds_of_mem {φ : ∀ i, MorseChart E f (p i)}
    (hφ : ∀ i, ∀ y ∈ (φ i).toChart.source,
      (φ i).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ i).toChart y (X y)) =
        fun j ↦ -((φ i).weight j * (φ i).coord ((φ i).toChart y) j))
    {A : ι → Set M} (hA : ∀ i, IsClosed (A i)) (hAf : LocallyFinite A)
    (hAd : Pairwise (Disjoint on A)) (hAφ : ∀ i, A i ⊆ (φ i).toChart.source)
    {i : ι} {y₀ : M} (hi : y₀ ∈ A i) :
    HasLocalMetric X φ A y₀ := by
  have hc : IsClosed (⋃ j : {j // j ≠ i}, A j) :=
    (hAf.comp_injective Subtype.coe_injective).isClosed_iUnion fun j ↦ hA j
  have hy₀c : y₀ ∉ ⋃ j : {j // j ≠ i}, A j := fun h ↦ by
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact (hAd j.2.symm).le_bot ⟨hi, hj⟩
  refine ⟨(φ i).toChart.source ∩ (⋃ j : {j // j ≠ i}, A j)ᶜ,
    ((φ i).toChart.open_source.inter hc.isOpen_compl).mem_nhds ⟨hAφ i hi, hy₀c⟩,
    (φ i).euclideanForm, (φ i).contMDiffOn_euclideanForm.mono inter_subset_left,
    fun y hy ↦ euclideanForm_mem_metricCondition (φ i) (hφ i) hy.1 fun j hj ↦ ?_⟩
  obtain rfl : i = j := by
    by_contra hne
    exact hy.2 (mem_iUnion.2 ⟨⟨j, Ne.symm hne⟩, hj⟩)
  rfl

/-- Near a critical point outside the closed set `⋃ i, A i`, the Euclidean metric of a Morse chart
in which `X` is linear is a local metric satisfying the conditions. -/
private theorem exists_nhds_of_mfderiv_eq_zero (hX : IsAdaptedPseudoGradient f X)
    {φ : ∀ i, MorseChart E f (p i)} {A : ι → Set M} (hAc : IsClosed (⋃ i, A i))
    {y₀ : M} (hy₀ : y₀ ∉ ⋃ i, A i) (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ = 0) :
    HasLocalMetric X φ A y₀ := by
  obtain ⟨ψ, hψ⟩ := hX.exists_morseChart y₀ hcrit
  exact ⟨ψ.toChart.source ∩ (⋃ i, A i)ᶜ,
    (ψ.toChart.open_source.inter hAc.isOpen_compl).mem_nhds ⟨ψ.mem_source, hy₀⟩,
    ψ.euclideanForm, ψ.contMDiffOn_euclideanForm.mono inter_subset_left,
    fun y hy ↦ euclideanForm_mem_metricCondition ψ hψ hy.1 fun i hi ↦
      (hy.2 (mem_iUnion.2 ⟨i, hi⟩)).elim⟩

/-- Near a regular point outside the closed set `⋃ i, A i`, a smooth metric `g₀` modified so that
`X` becomes the gradient of `-df` is a local metric satisfying the conditions. -/
private theorem exists_nhds_of_mfderiv_ne_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hX : IsAdaptedPseudoGradient f X)
    (g₀ : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {φ : ∀ i, MorseChart E f (p i)} {A : ι → Set M} (hAc : IsClosed (⋃ i, A i))
    {y₀ : M} (hy₀ : y₀ ∉ ⋃ i, A i) (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0) :
    HasLocalMetric X φ A y₀ := by
  have hXX : Continuous fun z ↦ mvfderiv 𝓘(ℝ, E) f z (X z) :=
    ((hf.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hX.contMDiff).continuous
  refine ⟨(⋃ i, A i)ᶜ ∩ {z | mvfderiv 𝓘(ℝ, E) f z (X z) < 0},
    (hAc.isOpen_compl.inter (isOpen_lt hXX continuous_const)).mem_nhds
      ⟨hy₀, hX.mvfderiv_apply_lt_zero y₀ hcrit⟩,
    fun z ↦ (g₀.inner z).withGradient (-mvfderiv 𝓘(ℝ, E) f z) (X z),
    fun z hz ↦ ((g₀.contMDiff z).clm_bundle_withGradient
      ((hf.of_le (by simp)).contMDiff_totalSpaceMk_mvfderiv z).neg_section (hX.contMDiff z)
      (neg_ne_zero.2 hz.2.ne)).contMDiffWithinAt, fun z hz ↦ ?_⟩
  -- `-df` is positive on `X` there.
  have hpos : 0 < -mvfderiv 𝓘(ℝ, E) f z (X z) := neg_pos.2 hz.2
  refine ⟨⟨ContinuousLinearMap.withGradient_comm (g₀.symm z), fun v hv ↦
    ContinuousLinearMap.withGradient_apply_self_pos (g₀.symm z) (g₀.pos z) hpos hv⟩,
    fun w ↦ ?_, fun i hi ↦ (hz.1 (mem_iUnion.2 ⟨i, hi⟩)).elim⟩
  rw [ContinuousLinearMap.withGradient_apply_left_self hpos.ne', neg_apply]

/-- **Every adapted pseudo-gradient is a negative gradient, for a metric prescribed near the
critical points.** Let `f` be smooth and `X` a pseudo-gradient adapted to `f`. Let `A i` be a
locally finite family of pairwise disjoint closed sets, each contained in the source of a Morse
chart `φ i` in which `X` is the linear field. Then there is a smooth Riemannian metric `g` with
`g (X, ·) = -df`, which on each `A i` is the Euclidean metric of the coordinates of `φ i`. -/
theorem exists_contMDiffRiemannianMetric_inner_eq_euclideanForm [T2Space M] [SigmaCompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hX : IsAdaptedPseudoGradient f X)
    (φ : ∀ i, MorseChart E f (p i))
    (hφ : ∀ i, ∀ y ∈ (φ i).toChart.source,
      (φ i).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ i).toChart y (X y)) =
        fun j ↦ -((φ i).weight j * (φ i).coord ((φ i).toChart y) j))
    {A : ι → Set M} (hA : ∀ i, IsClosed (A i)) (hAf : LocallyFinite A)
    (hAd : Pairwise (Disjoint on A)) (hAφ : ∀ i, A i ⊆ (φ i).toChart.source) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      (∀ y w, g.inner y (X y) w = -mvfderiv 𝓘(ℝ, E) f y w) ∧
        ∀ i, ∀ y ∈ A i, g.inner y = (φ i).euclideanForm y := by
  obtain ⟨g₀⟩ := nonempty_contMDiffRiemannianMetric (IB := 𝓘(ℝ, E)) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
  -- As in `nonempty_contMDiffRiemannianMetric`, these local instances keep the instance search
  -- for the bundle of bilinear forms within the default budget.
  have : ∀ y : M, ContinuousAdd (TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) := fun y ↦ inferInstance
  let : ∀ y : M, AddCommGroup (TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) :=
    fun y ↦ inferInstance
  -- The conditions on the metric at a point are convex: symmetry and positivity are, and the
  -- other two are affine.
  have ht (y : M) : Convex ℝ (metricCondition X φ A y) := by
    refine convex_setOfPred_symm_pos.inter (Convex.inter ?_ ?_)
    · intro s hs s' hs' a b _ _ hab w
      simp [hs w, hs' w, ← add_mul, hab]
    · intro s hs s' hs' a b _ _ hab i hy
      rw [hs i hy, hs' i hy, ← add_smul, hab, one_smul]
  have hAc : IsClosed (⋃ i, A i) := hAf.isClosed_iUnion hA
  -- Glue local metrics satisfying these conditions by a partition of unity.
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local (n := (⊤ : ℕ∞)) 𝓘(ℝ, E)
    (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ)
    (metricCondition X φ A) ht fun y₀ ↦ by
      by_cases hy₀ : y₀ ∈ ⋃ i, A i
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hy₀
        exact exists_nhds_of_mem hφ hA hAf hAd hAφ hi
      by_cases hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ = 0
      · exact hX.exists_nhds_of_mfderiv_eq_zero hAc hy₀ hcrit
      · exact exists_nhds_of_mfderiv_ne_zero hf hX g₀ hAc hy₀ hcrit
  let g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection σ
      ((Manifold.mem_positiveDefiniteBilinearSections _).2
        ⟨(Manifold.mem_symmetricBilinearSections _).2 fun y v w ↦ (hσ y).1.1 v w,
          fun y v hv ↦ (hσ y).1.2 v hv⟩)
  have hg (y : M) : g.inner y = σ y := by
    ext v w
    exact ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ y v w
  refine ⟨g, fun y w ↦ ?_, fun i y hy ↦ ?_⟩
  · rw [hg]
    exact (hσ y).2.1 w
  · rw [hg]
    exact (hσ y).2.2 i hy

/-- **Every adapted pseudo-gradient is a negative gradient**: for a smooth function `f` on a
σ-compact Hausdorff manifold and a pseudo-gradient `X` adapted to `f`, there is a smooth
Riemannian metric for which `X = -grad f`. -/
theorem exists_contMDiffRiemannianMetric_neg_mgradient_eq [T2Space M] [SigmaCompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hX : IsAdaptedPseudoGradient f X) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      ∀ y, -Manifold.mgradient 𝓘(ℝ, E) f y = X y := by
  obtain ⟨g, hg, -⟩ := hX.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm hf
    (p := (Empty.elim : Empty → M)) (fun i ↦ i.elim) (fun i ↦ i.elim) (A := Empty.elim)
    (fun i ↦ i.elim) (locallyFinite_of_finite _) (fun i ↦ i.elim) fun i ↦ i.elim
  refine ⟨g, fun y ↦ ?_⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  rw [neg_eq_iff_eq_neg]
  refine ((Manifold.eq_mgradient_iff (I := 𝓘(ℝ, E)) (f := f) (x := y)).2 fun v ↦ ?_).symm
  rw [inner_neg_left, g.inner_eq y (X y) v, hg, neg_neg]

end IsAdaptedPseudoGradient

end TauCeti
