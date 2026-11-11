/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Gradient
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Metrics that are Euclidean in Morse charts

A Morse chart `ψ` at a critical point of `f`, with linear coordinates `L`, carries the Euclidean
metric `(v, w) ↦ L (dψ v) ⬝ L (dψ w)` of its coordinates (`TauCeti.MorseChart.euclideanForm`). It
is a smooth field of positive definite symmetric bilinear forms on the source of the chart.

A smooth function whose critical points in a compact set `K` are nondegenerate has a smooth
Riemannian metric which, at each critical point in `K`, is the Euclidean metric of some Morse chart
on the whole source of that chart
(`IsCompact.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm`). The Morse charts are
chosen on pairwise disjoint closed neighbourhoods of the finitely many critical points in `K`, and
the metric is obtained by extending their Euclidean metrics with a partition of unity
(`TauCeti.exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite`); it is then Euclidean in the
restrictions of the Morse charts to the interiors of these neighbourhoods.

For such a metric the negative gradient of `f` reads `z ↦ (-wᵢ zᵢ)ᵢ` in each of these charts
(`TauCeti.MorseChart.IsEuclidean.neg_mgradient_eq_field`). So every Morse function on a compact
manifold has a smooth metric whose negative gradient is a pseudo-gradient adapted to the function
(`TauCeti.IsMorse.exists_contMDiffRiemannianMetric_isAdaptedPseudoGradient_neg_mgradient`): the
results on the flows of adapted pseudo-gradients apply to its negative gradient flow, which is
linear near the critical points. These are the background metrics, standard near the critical
points, on which the trajectory spaces of Morse homology are built.

## Main declarations

* `TauCeti.MorseChart.euclideanForm`: the Euclidean metric of a Morse chart, with
  `TauCeti.MorseChart.contMDiffOn_euclideanForm`, `TauCeti.MorseChart.euclideanForm_comm` and
  `TauCeti.MorseChart.euclideanForm_self_pos`.
* `TauCeti.MorseChart.isEuclidean_iff_inner_eq_euclideanForm`: a metric is Euclidean in a Morse
  chart exactly when it is the Euclidean metric of the chart on its source.
* `IsCompact.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm`: a metric which is Euclidean
  in a Morse chart at each critical point in a compact set.
* `TauCeti.IsMorse.exists_contMDiffRiemannianMetric_isAdaptedPseudoGradient_neg_mgradient`: on a
  compact manifold, a metric whose negative gradient is an adapted pseudo-gradient.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Sections 2.1 and 2.2.
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and associative
  gluing*, Geom. Topol. Monogr. **18** (2012), [arXiv:1205.0713](https://arxiv.org/abs/1205.0713),
  Section 1 (Morse–Smale pairs whose metric is Euclidean in Morse coordinates near the critical
  points).
-/

public section

open Bundle Function Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

namespace MorseChart

section EuclideanForm

variable [FiniteDimensional ℝ E] (φ : MorseChart E f x)

/-- The dot product of the coordinates of a Morse chart, as a bilinear form on the model space. -/
private noncomputable def coordDot : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
    (φ.coordL : E →L[ℝ] _)).smulRight
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
        (φ.coordL : E →L[ℝ] _))

private theorem coordDot_apply (a b : E) : φ.coordDot a b = φ.coord a ⬝ᵥ φ.coord b := by
  simp [coordDot, dotProduct]

/-- The **Euclidean metric of a Morse chart** `ψ` with linear coordinates `L`: at a point `y`, the
bilinear form `(v, w) ↦ L (dψ v) ⬝ L (dψ w)` on the tangent space. -/
noncomputable def euclideanForm (y : M) :
    TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y)).comp
    (φ.coordDot.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y))

/-- The Euclidean metric of a Morse chart is the dot product of the coordinates `L (dψ v)`. -/
@[simp]
theorem euclideanForm_apply (y : M) (v w : TangentSpace 𝓘(ℝ, E) y) :
    φ.euclideanForm y v w = φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v) ⬝ᵥ
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w) :=
  -- The tangent spaces of `E` are `E` itself, where `coordDot` is the dot product.
  φ.coordDot_apply _ _

/-- The Euclidean metric of a Morse chart is symmetric. -/
theorem euclideanForm_comm (y : M) (v w : TangentSpace 𝓘(ℝ, E) y) :
    φ.euclideanForm y v w = φ.euclideanForm y w v := by
  simp only [euclideanForm_apply, dotProduct_comm]

/-- Restricting a Morse chart does not change its Euclidean metric. -/
@[simp]
theorem restr_euclideanForm {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    (φ.restr hs hx).euclideanForm = φ.euclideanForm := by
  have h : ((φ.restr hs hx).toChart : M → E) = φ.toChart := by
    rw [restr_toChart, OpenPartialHomeomorph.restr_apply]
  ext y v w
  simp only [euclideanForm_apply, restr_coord]
  rw [h]

/-- The Euclidean metric of a Morse chart is positive definite on the source of the chart, where
the differential of the chart is injective. -/
theorem euclideanForm_self_pos {y : M} (hy : y ∈ φ.toChart.source)
    {v : TangentSpace 𝓘(ℝ, E) y} (hv : v ≠ 0) : 0 < φ.euclideanForm y v v := by
  have hinv := isInvertible_mfderiv_extend φ.mem_maximalAtlas_one hy
  rw [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, Function.id_comp] at hinv
  obtain ⟨e, he⟩ := hinv
  have hne : φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v) ≠ 0 := by
    intro h
    refine hv (e.injective ?_)
    rw [map_zero]
    exact φ.coord.injective ((congrArg φ.coord (congrFun (congrArg DFunLike.coe he) v)).trans
      (h.trans (map_zero _).symm))
  rw [euclideanForm_apply]
  exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
    (Ne.symm (dotProduct_self_eq_zero.not.2 hne))

/-- **The Euclidean metric of a Morse chart is smooth** on the source of the chart, as a section
of the bundle of bilinear forms on the tangent spaces. -/
theorem contMDiffOn_euclideanForm [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) y
        (φ.euclideanForm y)) φ.toChart.source := by
  intro y hy
  -- The Euclidean metric is the pullback by the chart of the constant bilinear form `coordDot`
  -- on the tangent spaces of `E`, which reads as a constant in the trivial tangent bundle of `E`.
  have hψ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ + 1) φ.toChart y :=
    (contMDiffAt_of_mem_maximalAtlas φ.mem_maximalAtlas hy).of_le (by simp)
  let Q (z : E) : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ := φ.coordDot
  have hQ : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : E ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : E ↦ TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ) z
        (Q z)) (φ.toChart y) := by
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := φ.coordDot)
    ext v w
    simp [Q, hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
    -- The remaining coordinate changes are the identity `1` of the tangent spaces of `E`, typed so
    -- that `ContinuousLinearMap.comp_one` does not match; they compose away definitionally.
    rfl
  exact (contMDiffAt_bilinearForm_pullback hQ hψ).contMDiffWithinAt

end EuclideanForm

/-- A metric is Euclidean in a Morse chart exactly when it is the Euclidean metric of the chart on
the source of the chart. -/
theorem isEuclidean_iff_inner_eq_euclideanForm [FiniteDimensional ℝ E]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] (φ : MorseChart E f x) :
    φ.IsEuclidean ↔ ∀ y ∈ φ.toChart.source, ∀ v w : TangentSpace 𝓘(ℝ, E) y,
      inner ℝ v w = φ.euclideanForm y v w := by
  simp only [isEuclidean_iff, euclideanForm_apply]

end MorseChart

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

open Filter in
/-- **A metric which is Euclidean in Morse charts.** Let `K` be a compact subset of a Hausdorff
σ-compact manifold and let `f` be smooth. If every critical point of `f` in `K` is nondegenerate,
then there is a smooth Riemannian metric which, at each critical point `x` in `K`, is the Euclidean
metric of a Morse chart at `x` on the whole source of that chart.

No condition is imposed on the metric away from these charts, nor on the critical points of `f`
outside `K`. -/
theorem _root_.IsCompact.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm [T2Space M]
    [SigmaCompactSpace M] {K : Set M} (hK : IsCompact K) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hnd : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y),
      ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
        ∃ φ : MorseChart E f x, ∀ y ∈ φ.toChart.source, g.inner y = φ.euclideanForm y := by
  classical
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  -- The critical points in `K` are finitely many. Choose a Morse chart at each, and pairwise
  -- disjoint closed neighbourhoods `A c` inside these charts.
  let C := criticalPoints 𝓘(ℝ, E) f ∩ K
  have hCcrit (c : C) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero.1 c.2.1
  have hC : C.Finite :=
    finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint
      (hf.of_le (by simp)) hK fun x hx ↦ hnd x hx.2 (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.1)
  let φ : ∀ c : C, MorseChart E f c := fun c ↦
    ((hnd c c.2.2 (hCcrit c)).nonempty_morseChart
      (Eventually.of_forall fun _ ↦ hf.contMDiffAt)).some
  obtain ⟨W, hW, hWdisj⟩ := hC.t2_separation
  choose A hAn hAc hAsub using fun c : C ↦ exists_mem_nhds_isClosed_subset
    (Filter.inter_mem ((φ c).toChart.open_source.mem_nhds (φ c).mem_source)
      ((hW c).2.mem_nhds (hW c).1))
  have : Finite C := hC.to_subtype
  -- Extend the Euclidean metrics of the charts from the sets `A c` to a metric on `M`.
  obtain ⟨g, hg⟩ := exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite
    (U := fun c ↦ (φ c).toChart.source) (β := fun c ↦ (φ c).euclideanForm) hAc
    (locallyFinite_of_finite A)
    (fun c c' h ↦ (hWdisj c.2 c'.2 (Subtype.coe_injective.ne h)).mono
      (fun _ hy ↦ (hAsub c hy).2) fun _ hy ↦ (hAsub c' hy).2)
    (fun c ↦ (φ c).toChart.open_source) (fun c _ hy ↦ (hAsub c hy).1)
    (fun c ↦ (φ c).contMDiffOn_euclideanForm) (fun c _ _ ↦ (φ c).euclideanForm_comm _)
    fun c _ hy _ hv ↦ (φ c).euclideanForm_self_pos hy hv
  -- The metric is Euclidean in the restriction of each chart to the interior of `A c`.
  refine ⟨g, fun x hxK hx ↦ ?_⟩
  let c : C := ⟨x, mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hxK⟩
  refine ⟨(φ c).restr isOpen_interior (mem_interior_iff_mem_nhds.2 (hAn c)), fun y hy ↦ ?_⟩
  rw [MorseChart.restr_source] at hy
  rw [MorseChart.restr_euclideanForm]
  exact hg c y (interior_subset hy.2)

/-- **The negative gradient of a Morse function is an adapted pseudo-gradient for some metric.**
Every Morse function on a compact manifold has a smooth Riemannian metric, Euclidean in a Morse
chart at each critical point, whose negative gradient is a pseudo-gradient field adapted to the
function. -/
theorem IsMorse.exists_contMDiffRiemannianMetric_isAdaptedPseudoGradient_neg_mgradient
    [CompactSpace M] [T2Space M] (hf : IsMorse 𝓘(ℝ, E) f) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y),
      letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) := ⟨g.toRiemannianMetric⟩
      IsAdaptedPseudoGradient f fun y ↦ -mgradient 𝓘(ℝ, E) f y := by
  obtain ⟨g, hg⟩ := isCompact_univ.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm
    hf.contMDiff fun _ _ hx ↦ hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
    ⟨⟨g.inner, g.contMDiff, g.inner_eq⟩⟩
  refine ⟨g, isAdaptedPseudoGradient_neg_mgradient hf.contMDiff fun x hx ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hg x (mem_univ x) hx
  exact ⟨φ, φ.isEuclidean_iff_inner_eq_euclideanForm.2 fun y hy v w ↦ by
    rw [g.inner_eq, hφ y hy]⟩

end TauCeti
