/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Stability
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
`g_s` with `s ∈ [0, 1]` has positive scalar curvature. For `a, b ∈ [0, 1]` consider the metric
`g_{(1 - φ(t)) a + φ(t) b} + dt²` on `M × ℝ`, where `φ` is the smooth transition from `0` to `1`
on `[0, 1]`. Its chart metrics depend smoothly on `(a, b)` and on the chart point, and for `a = b`
it is the cylinder `g_a + dt²`. Since the window `M × [0, 1]` is compact, positivity of scalar
curvature persists for `b` near `a`, by
`TauCeti.Manifold.exists_pos_eventually_forall_le_scalarCurvature`, and outside the window the
metric is a cylinder. Thus `g_a` and `g_b` are concordant for `b`
near `a`. As concordance is an equivalence relation and `[0, 1]` is connected, `g₀` and `g₁`
are concordant. This is the usual argument that traverses a path of metrics slowly, cut into
short pieces, each traversed in unit time.

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

-- Cache the canonical operator-space instances on the model `E × ℝ` of the cylinder, as in the
-- chart C² topology module: otherwise instance search for the scalar action on the bilinear
-- forms receiving chart metrics fails.
private local instance : NormedAddCommGroup (E × ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E × ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E × ℝ →L[ℝ] E × ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E × ℝ →L[ℝ] E × ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable (g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The weight `(1 - φ(t)) a + φ(t) b` interpolating from `a` at `t ≤ 0` to `b` at `t ≥ 1`, with
`φ` the smooth transition. -/
private def segmentWeight (a b : ℝ) (t : ℝ) : ℝ :=
  (1 - Real.smoothTransition t) * a + Real.smoothTransition t * b

private theorem contDiff_segmentWeight :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ ↦ segmentWeight q.1.1 q.1.2 q.2) := by
  have hφ : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ ↦ Real.smoothTransition q.2) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp contDiff_snd
  unfold segmentWeight
  fun_prop

private theorem segmentWeight_mem_Icc (a b : unitInterval) (t : ℝ) :
    segmentWeight a b t ∈ Icc (0 : ℝ) 1 := by
  have h₀ := Real.smoothTransition.nonneg t
  have h₁ := Real.smoothTransition.le_one t
  have ha := a.2
  have hb := b.2
  constructor <;> simp only [segmentWeight] <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

private theorem segmentWeight_of_nonpos (a b : ℝ) {t : ℝ} (ht : t ≤ 0) :
    segmentWeight a b t = a := by
  simp [segmentWeight, Real.smoothTransition.zero_of_nonpos ht]

private theorem segmentWeight_of_one_le (a b : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    segmentWeight a b t = b := by
  simp [segmentWeight, Real.smoothTransition.one_of_one_le ht]

/-- The metric `g_{(1 - φ(t)) a + φ(t) b} + dt²` on `M × ℝ`, where `g_s = (1 - s) g₀ + s g₁`. It
interpolates the cylinder metrics of `g₀` and `g₁` with a weight depending only on `t`. -/
private def segmentMetric (a b : unitInterval) :
    ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p) :=
  g₀.cylinder.convexCombinationFun g₁.cylinder (fun p ↦ segmentWeight a b p.2)
    ((contDiff_segmentWeight.comp ((contDiff_const (c := ((a : ℝ), (b : ℝ)))).prodMk
      contDiff_id)).contMDiff.comp contMDiff_snd)
    (fun p ↦ (segmentWeight_mem_Icc a b p.2).1) (fun p ↦ (segmentWeight_mem_Icc a b p.2).2)

variable {g₀ g₁}

omit [I.Boundaryless] [T2Space M] in
/-- Where the weight takes the value `c`, the segment metric is the cylinder metric of `g_c`. -/
private theorem segmentMetric_inner_eq {a b c : unitInterval} {p : M × ℝ}
    (h : segmentWeight a b p.2 = c) :
    (segmentMetric g₀ g₁ a b).inner p = (g₀.convexCombination g₁ c).cylinder.inner p := by
  ext v w
  simp only [segmentMetric, convexCombinationFun_inner, cylinder_inner, convexCombination_inner,
    h]
  ring

omit [I.Boundaryless] [T2Space M] in
/-- The chart metric of a segment metric on the chart target is the interpolation of the chart
metrics of the two cylinder metrics, with the weight read off the `ℝ`-coordinate. -/
private theorem chartMetric_segmentMetric (a b : unitInterval) (x : M × ℝ) {z : E × ℝ}
    (hz : z ∈ (extChartAt (I.prod 𝓘(ℝ)) x).target) :
    (segmentMetric g₀ g₁ a b).toNondegenerateMetric.chartMetric x z =
      (1 - segmentWeight a b z.2) • g₀.cylinder.toNondegenerateMetric.chartMetric x z +
        segmentWeight a b z.2 • g₁.cylinder.toNondegenerateMetric.chartMetric x z := by
  have hsnd : ((extChartAt (I.prod 𝓘(ℝ)) x).symm z).2 = z.2 := by
    rw [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      extChartAt_model_space_eq_id]
    simp
  rw [segmentMetric, chartMetric_convexCombinationFun _ _ _ _ _ _ x hz, hsnd]

omit [T2Space M] in
/-- The chart metrics of the segment metrics are jointly smooth in `(a, b)` and the chart point,
so their Gram matrices and first two derivatives vary continuously. -/
private theorem continuousAt_segmentMetric_jets {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (E × ℝ)) (x : M × ℝ) (q : unitInterval × unitInterval) :
    let G := fun q : unitInterval × unitInterval ↦ segmentMetric g₀ g₁ q.1 q.2
    ContinuousAt (fun r : (unitInterval × unitInterval) × (E × ℝ) ↦ LinearMap.toMatrix₂ b b
      ((G r.1).toNondegenerateMetric.chartMetric x r.2).toBilinForm)
      (q, extChartAt (I.prod 𝓘(ℝ)) x x) ∧
    ContinuousAt (fun r : (unitInterval × unitInterval) × (E × ℝ) ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (G r.1).toNondegenerateMetric.chartMetric x z (b i) (b j)) r.2 (b k))
      (q, extChartAt (I.prod 𝓘(ℝ)) x x) ∧
    ContinuousAt (fun r : (unitInterval × unitInterval) × (E × ℝ) ↦ fun m k i j ↦ fderiv ℝ
      (fun z ↦ fderiv ℝ (fun z' ↦ (G r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j))
        z (b k)) r.2 (b m)) (q, extChartAt (I.prod 𝓘(ℝ)) x x) := by
  have hw : ContDiff ℝ ∞ (fun r : (ℝ × ℝ) × (E × ℝ) ↦ segmentWeight r.1.1 r.1.2 r.2.2) :=
    contDiff_segmentWeight.comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hA (g : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)) :
      ContDiffOn ℝ ∞ (fun r : (ℝ × ℝ) × (E × ℝ) ↦ g.toNondegenerateMetric.chartMetric x r.2)
        (univ ×ˢ (extChartAt (I.prod 𝓘(ℝ)) x).target) :=
    (g.toNondegenerateMetric.contDiffOn_chartMetric x).comp contDiffOn_snd fun r hr ↦ hr.2
  exact continuousAt_chartMetric_jets b _ x
    (by fun_prop : Continuous fun q : unitInterval × unitInterval ↦ ((q.1 : ℝ), (q.2 : ℝ)))
    (((contDiffOn_const.sub hw.contDiffOn).smul (hA _)).add (hw.contDiffOn.smul (hA _)))
    (fun q z hz ↦ chartMetric_segmentMetric q.1 q.2 x hz) q

/-- If every `g_s` has positive scalar curvature, then `g_a` and `g_b` are concordant for all `b`
near `a`. -/
private theorem eventually_concordant_convexCombination [CompactSpace M]
    (h : ∀ s, (g₀.convexCombination g₁ s).HasPositiveScalarCurvature) (a : unitInterval) :
    ∀ᶠ b in 𝓝 a, Concordant (g₀.convexCombination g₁ a) (g₀.convexCombination g₁ b) := by
  let bE := Module.finBasis ℝ (E × ℝ)
  let G : unitInterval × unitInterval → ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p) := fun q ↦ segmentMetric g₀ g₁ q.1 q.2
  have hjets (x : M × ℝ) (q : unitInterval × unitInterval) :=
    continuousAt_segmentMetric_jets (g₀ := g₀) (g₁ := g₁) bE x q
  -- For `a = b` the segment metric is the cylinder metric of `g_a`.
  have hdiag (c : unitInterval) (p : M × ℝ) :
      (segmentMetric g₀ g₁ c c).inner p = (g₀.convexCombination g₁ c).cylinder.inner p :=
    segmentMetric_inner_eq (by simp [segmentWeight]; ring)
  obtain ⟨ε, hε, hev⟩ := TauCeti.Manifold.exists_pos_eventually_forall_le_scalarCurvature G bE
    (K := {(a, a)}) isCompact_singleton (L := univ ×ˢ Icc 0 1)
    (isCompact_univ.prod isCompact_Icc) (fun q _ x _ ↦ (hjets x q).1)
    (fun q _ x _ ↦ (hjets x q).2.1) (fun q _ x _ ↦ (hjets x q).2.2) (fun q hq x _ ↦ by
      rw [mem_singleton_iff.1 hq]
      simp only [G]
      rw [eqOn_scalarCurvature isOpen_univ (fun p _ ↦ hdiag a p) (mem_univ x),
        scalarCurvature_cylinder]
      exact (hasPositiveScalarCurvature_iff _).1 (h a) x.1)
  rw [nhdsSet_singleton] at hev
  filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hev]
    with b hb
  refine IsConcordance.concordant (G := segmentMetric g₀ g₁ a b)
    ⟨(hasPositiveScalarCurvature_iff _).2 fun p ↦ ?_,
      fun p hp ↦ segmentMetric_inner_eq (segmentWeight_of_nonpos _ _ hp),
      fun p hp ↦ segmentMetric_inner_eq (segmentWeight_of_one_le _ _ hp)⟩
  -- Outside the window `M × [0, 1]` the segment metric is a cylinder metric.
  rcases lt_or_ge p.2 0 with hp | hp₀
  · rw [eqOn_scalarCurvature (isOpen_lt continuous_snd continuous_const)
      (fun q hq ↦ segmentMetric_inner_eq (segmentWeight_of_nonpos _ _ (le_of_lt hq))) hp,
      scalarCurvature_cylinder]
    exact (hasPositiveScalarCurvature_iff _).1 (h a) p.1
  rcases lt_or_ge 1 p.2 with hp | hp₁
  · rw [eqOn_scalarCurvature (isOpen_lt continuous_const continuous_snd)
      (fun q hq ↦ segmentMetric_inner_eq (segmentWeight_of_one_le _ _ (le_of_lt hq))) hp,
      scalarCurvature_cylinder]
    exact (hasPositiveScalarCurvature_iff _).1 (h b) p.1
  · exact hε.trans_le (hb p ⟨mem_univ _, hp₀, hp₁⟩)

/-- **A straight segment of metrics of positive scalar curvature gives a concordance.** On a
closed manifold, if every convex combination `(1 - s) g₀ + s g₁`, `s ∈ [0, 1]`, has positive
scalar curvature, then `g₀` and `g₁` are concordant. -/
theorem concordant_of_forall_hasPositiveScalarCurvature_convexCombination [CompactSpace M]
    (h : ∀ s, (g₀.convexCombination g₁ s).HasPositiveScalarCurvature) : Concordant g₀ g₁ := by
  have key := PreconnectedSpace.induction₂'
    (fun a b : unitInterval ↦
      Concordant (g₀.convexCombination g₁ a) (g₀.convexCombination g₁ b))
    (fun a ↦ (eventually_concordant_convexCombination h a).mono fun _ hb ↦ ⟨hb, hb.symm⟩)
    ⟨fun _ _ _ ↦ Concordant.trans⟩ 0 1
  simpa using key

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
