/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.SmoothPath
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Interpolation

/-!
# Isotopic metrics of positive scalar curvature are concordant

Two metrics of positive scalar curvature on a closed manifold `M` are *isotopic* if they are
joined by a continuous path of metrics of positive scalar curvature. Here the space of metrics
carries the chart C² topology `Bundle.ContMDiffRiemannianMetric.chartC2Topology`. Isotopic metrics
are concordant: there is a metric of positive scalar curvature on `M × ℝ` which is the cylinder
`g₀ + dt²` for `t ≤ 0` and `g₁ + dt²` for `t ≥ 1`.

The proof first treats straight segments. Write `g_s = (1 - s) g₀ + s g₁` and suppose that every
`g_s` with `s ∈ [0, 1]` has positive scalar curvature. With `φ` the smooth transition from `0` to
`1` on `[0, 1]`, the path `t ↦ g_{φ(t)}` is smooth, constant for `t ≤ 0` and for `t ≥ 1`, and is
recorded by the metric `g_{φ(t)} + dt²` on `M × ℝ`, an interpolation of the cylinder metrics of
`g₀` and `g₁` with a weight depending only on `t`. The smooth-path theorem
`Bundle.ContMDiffRiemannianMetric.concordant_of_forall_inner_eq_cylinder`, which traverses the
path slowly, then shows that `g₀` and `g₁` are concordant.

For a general path `γ`, convex combinations of `γ s` and `γ s'` have positive scalar curvature
when `s'` is near `s`, since interpolation is continuous in the chart C² topology and positive
scalar curvature is a C²-open condition. Each short straight segment gives a concordance, and
connectedness of `[0, 1]` again finishes the argument.

## Main results

* `concordant_of_forall_hasPositiveScalarCurvature_convexCombination`, in the namespace
  `Bundle.ContMDiffRiemannianMetric`: if every convex combination of `g₀` and `g₁` has positive
  scalar curvature, then `g₀` and `g₁` are concordant.
* `JoinedIn.concordant`: on a closed manifold, two metrics joined by a C²-continuous path of
  metrics of positive scalar curvature are concordant.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* S. Stolz, *Positive scalar curvature: constructions and obstructions*, arXiv:2202.05904, for
  isotopy and concordance of metrics of positive scalar curvature.
-/

public section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

section Segment

variable {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- **A straight segment of metrics of positive scalar curvature gives a concordance.** On a
closed manifold, if every convex combination `(1 - s) g₀ + s g₁`, `s ∈ [0, 1]`, has positive
scalar curvature, then `g₀` and `g₁` are concordant. -/
theorem concordant_of_forall_hasPositiveScalarCurvature_convexCombination [CompactSpace M]
    (h : ∀ s, (g₀.convexCombination g₁ s).HasPositiveScalarCurvature) : Concordant g₀ g₁ := by
  -- Run along the segment by the smooth transition `φ`, constant outside `[0, 1]`.
  let φ : ℝ → unitInterval := fun t ↦
    ⟨Real.smoothTransition t, Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hφ₀ {t : ℝ} (ht : t ≤ 0) : φ t = 0 :=
    Subtype.ext (Real.smoothTransition.zero_of_nonpos ht)
  have hφ₁ {t : ℝ} (ht : 1 ≤ t) : φ t = 1 :=
    Subtype.ext (Real.smoothTransition.one_of_one_le ht)
  -- The path is recorded by the interpolation of the cylinder metrics with weight `φ(t)`.
  let G := g₀.cylinder.convexCombinationFun g₁.cylinder
    (fun p : M × ℝ ↦ Real.smoothTransition p.2)
    ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp contMDiff_snd)
    (fun p ↦ Real.smoothTransition.nonneg p.2) (fun p ↦ Real.smoothTransition.le_one p.2)
  have key := concordant_of_forall_inner_eq_cylinder (G := G)
    (g := fun t ↦ g₀.convexCombination g₁ (φ t))
    (fun p ↦ by
      ext v w
      simp only [G, φ, convexCombinationFun_inner, cylinder_inner, convexCombination_inner]
      ring)
    (fun t _ ↦ h (φ t)) (fun t ht ↦ by simp only [hφ₀ ht, hφ₀ le_rfl])
    (fun t ht ↦ by simp only [hφ₁ ht, hφ₁ le_rfl])
  rwa [hφ₀ le_rfl, hφ₁ le_rfl, convexCombination_zero, convexCombination_one] at key

end Segment

end Bundle.ContMDiffRiemannianMetric

open Bundle ContMDiffRiemannianMetric
open scoped TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- **Isotopic metrics are concordant.** On a closed manifold, two metrics joined by a path of
metrics of positive scalar curvature, continuous in the chart C² topology, are concordant. -/
theorem JoinedIn.concordant
    (h : JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} g₀ g₁) : Concordant g₀ g₁ := by
  obtain ⟨γ, hγ⟩ := h
  have hopen := isOpen_setOf_hasPositiveScalarCurvature_chartC2 (I := I) (M := M)
  -- Convex combinations of `γ s` and of `γ s'` for `s'` near `s` have positive scalar
  -- curvature, so the straight segment between them gives a concordance.
  have hloc (s : unitInterval) : ∀ᶠ s' in 𝓝 s, Concordant (γ s) (γ s') := by
    have hcont : Continuous fun q : unitInterval × unitInterval ↦
        (γ s).convexCombination (γ q.1) q.2 :=
      continuous_convexCombination continuous_const (γ.continuous.comp continuous_fst)
        continuous_snd
    filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun s' τ ↦ ((γ s).convexCombination (γ s') τ).HasPositiveScalarCurvature)
      fun τ _ ↦ (hcont.continuousAt (x := (s, τ))).preimage_mem_nhds
        (hopen.mem_nhds (by simpa using hγ s))] with s' hs'
    exact concordant_of_forall_hasPositiveScalarCurvature_convexCombination fun τ ↦
      hs' τ (mem_univ τ)
  have key := PreconnectedSpace.induction₂' (fun s s' : unitInterval ↦ Concordant (γ s) (γ s'))
    (fun s ↦ (hloc s).mono fun _ hs' ↦ ⟨hs', hs'.symm⟩) ⟨fun _ _ _ ↦ Concordant.trans⟩ 0 1
  simpa using key
