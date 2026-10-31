/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.CompTime

/-!
# Smooth paths of metrics of positive scalar curvature give concordances

A smooth path `t ↦ g t` of metrics on `M` is recorded by a smooth metric `G` on `M × ℝ` which is
the cylinder metric `g t + dt²` at every point `(x, t)`; this encodes joint smoothness of the path
in `(x, t)`. Even when every `g t` has positive scalar curvature, `G` need not: its scalar
curvature at `(x, t)` differs from that of `g t` at `x` by terms in the first and second
`t`-derivatives of the path. Running the path slowly makes these terms small. If every `g t` with
`t ∈ [0, 1]` has positive scalar curvature, `M` is compact and the path is constant for `t ≤ 0`
and for `t ≥ 1`, then for every small `c` the metric `g (c t) + dt²` has positive scalar curvature.
For `c > 0` it is `g 0 + dt²` where `t ≤ 0` and `g 1 + dt²` where `t ≥ 1 / c`, so `g 0` and `g 1`
are concordant.

The slowed metric is `Bundle.ContMDiffRiemannianMetric.compTime`, from
`TauCeti.Geometry.Manifold.VectorBundle.Riemannian.CompTime`: for a smooth `φ : ℝ → ℝ`, the
metric on `M × ℝ` whose value at `(x, t)` is the value of `G` at `(x, φ t)`, on the same tangent
vectors. Unlike the pullback `Bundle.ContMDiffRiemannianMetric.reparamTime`, it does not multiply
the `ℝ`-components of tangent vectors by `φ'`.

For the scalar curvature, read the metrics `τ ↦ G (x, s + c τ)` in the chart at `(x, 0)`: their
chart metric is that of `G` along the affine map `(z, τ) ↦ (z, s + c τ)`, so their coordinate
`2`-jets depend continuously on `(c, s)` and the chart point. At `c = 0` the metric is the cylinder
over `g s`, whose scalar curvature at `(x, 0)` is that of `g s` at `x`. Since scalar curvature is a
continuous function of the coordinate `2`-jet
(`TauCeti.Manifold.continuousAt_scalarCurvature_of_continuousAt_chartMetric`), compactness of
`[0, 1] × M` gives a uniform range of `c`. Translating `(x, t)` to `(x, 0)` identifies the scalar
curvature of `g (c t) + dt²` at `(x, t)` with the value at `(c, c t, x)`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.eventually_hasPositiveScalarCurvature_compTime_mul`: a smooth
  path of metrics of positive scalar curvature on a compact manifold, run slowly enough, gives a
  metric of positive scalar curvature on `M × ℝ`.
* `Bundle.ContMDiffRiemannianMetric.concordant_of_forall_inner_eq_cylinder`: the ends of a smooth
  path of metrics of positive scalar curvature on a compact manifold are concordant.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* S. Stolz, *Positive scalar curvature—constructions and obstructions*, arXiv:2202.05904, for
  the statement that isotopic metrics of positive scalar curvature are concordant.
-/

public section

open Bundle Set Topology Filter
open TauCeti.Manifold (tangentSpaceProdEquiv tangentSpaceProdEquiv_apply)
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)} {φ : ℝ → ℝ}

section Slowing

variable [FiniteDimensional ℝ E] [T2Space M]

/-- **Translation invariance.** If `ψ τ = φ (τ + c)`, then the scalar curvature of the metric
`compTime` along `ψ` at `(x, t)` is that of the metric `compTime` along `φ` at `(x, t + c)`. -/
theorem scalarCurvature_compTime_of_eq_add {ψ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) {c : ℝ} (h : ∀ τ, ψ τ = φ (τ + c)) (p : M × ℝ) :
    (G.compTime hψ).scalarCurvature p = (G.compTime hφ).scalarCurvature (p.1, p.2 + c) := by
  have hc : ContDiff ℝ ∞ (· + c : ℝ → ℝ) := contDiff_id.add contDiff_const
  have hc' (t : ℝ) : deriv (· + c : ℝ → ℝ) t ≠ 0 := by simp
  have heq : G.compTime hψ = (G.compTime hφ).reparamTime hc hc' := by
    ext q v w
    have hd (u : TangentSpace (I.prod 𝓘(ℝ)) q) :
        mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id (· + c)) q u = u := by
      have := TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMap_id (I := I)
        (φ := (· + c)) (p := q) (by fun_prop) u
      apply (tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ)) (q.1, q.2 + c)).injective
      rw [this, tangentSpaceProdEquiv_apply]
      simp only [deriv_add_const, deriv_id'', one_mul]
      exact (tangentSpaceProdEquiv_apply (I := I) (J := 𝓘(ℝ))
        (q.1, q.2 + c) u).symm
    rw [reparamTime_inner, hd, hd]
    simp only [compTime_inner]
    exact congrArg (fun y ↦ G.inner (q.1, y) v w) (h q.2)
  rw [heq, scalarCurvature_reparamTime]

/-- The affine maps `τ ↦ s + c τ` used to slow down and translate a path of metrics. -/
private theorem contDiff_affine (q : ℝ × ℝ) : ContDiff ℝ ∞ (fun τ : ℝ ↦ q.2 + q.1 * τ) := by
  fun_prop

/-- The scalar curvature at `(x, 0)` of `τ ↦ G (x, s + c τ)` is jointly continuous in `(c, s)`
and `x`. -/
private theorem continuousAt_scalarCurvature_compTime_affine [I.Boundaryless] (q₀ : ℝ × ℝ)
    (x₀ : M) :
    ContinuousAt (fun r : (ℝ × ℝ) × M ↦
      (G.compTime (contDiff_affine r.1)).scalarCurvature (r.2, 0)) (q₀, x₀) := by
  let b := Module.finBasis ℝ (E × ℝ)
  let C := G.toNondegenerateMetric.chartMetric (x₀, (0 : ℝ))
  set T := (extChartAt I x₀).target
  have hT : IsOpen T := isOpen_extChartAt_target x₀
  have htarget : (extChartAt (I.prod 𝓘(ℝ)) (x₀, (0 : ℝ))).target = T ×ˢ univ := by
    rw [extChartAt_prod, PartialEquiv.prod_target, extChartAt_model_space_eq_id,
      PartialEquiv.refl_target]
  have hC : ContDiffOn ℝ ∞ C (T ×ˢ univ) :=
    htarget ▸ G.toNondegenerateMetric.contDiffOn_chartMetric (x₀, (0 : ℝ))
  -- In the chart at `(x₀, 0)`, the slowed metrics read `C` along the affine maps `A`.
  let A : (ℝ × ℝ) × (E × ℝ) → E × ℝ := fun r ↦ (r.2.1, r.1.2 + r.1.1 * r.2.2)
  have hA : ContDiff ℝ ∞ A := by fun_prop
  let V : Set ((ℝ × ℝ) × (E × ℝ)) := univ ×ˢ (T ×ˢ univ)
  have hV : IsOpen V := isOpen_univ.prod (hT.prod isOpen_univ)
  have hK (q : ℝ × ℝ) {w : E × ℝ} (hw : w ∈ T ×ˢ univ) :
      (G.compTime (contDiff_affine q)).toNondegenerateMetric.chartMetric (x₀, 0) w =
        C (A (q, w)) :=
    chartMetric_compTime _ x₀ 0 0 hw.1 w.2
  let F (i j : Fin (Module.finrank ℝ (E × ℝ))) : (ℝ × ℝ) × (E × ℝ) → ℝ :=
    fun r ↦ C (A r) (b i) (b j)
  have hF (i j) : ContDiffOn ℝ ∞ (F i j) V :=
    ((hC.comp hA.contDiffOn fun r (hr : r ∈ V) ↦
      (⟨hr.2.1, trivial⟩ : A r ∈ T ×ˢ univ)).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const
  -- The first derivatives of the coefficients in the chart variable, and their equality with
  -- those of the slowed metrics.
  let D (i j k) : (ℝ × ℝ) × (E × ℝ) → ℝ := fun r ↦ fderiv ℝ (fun z ↦ F i j (r.1, z)) r.2 (b k)
  have hD (i j k) {r} (hr : r ∈ V) : ContDiffAt ℝ 1 (D i j k) r := by
    refine (ContDiffAt.fderiv (f := fun (r : (ℝ × ℝ) × (E × ℝ)) z ↦ F i j (r.1, z))
      (g := Prod.snd) ?_ contDiffAt_snd (m := 1) (n := ∞) (by norm_cast)).clm_apply
      contDiffAt_const
    exact ((hF i j).contDiffAt (hV.mem_nhds hr)).comp _ (by fun_prop)
  have hd₁ (i j) {r : (ℝ × ℝ) × (E × ℝ)} (hr : r ∈ V) :
      fderiv ℝ (fun z ↦ (G.compTime (contDiff_affine r.1)).toNondegenerateMetric.chartMetric
        (x₀, 0) z (b i) (b j)) r.2 = fderiv ℝ (fun z ↦ F i j (r.1, z)) r.2 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(hT.prod isOpen_univ).mem_nhds hr.2] with z hz
    rw [hK r.1 hz]
  have hd₂ (i j k) {r : (ℝ × ℝ) × (E × ℝ)} (hr : r ∈ V) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun z' ↦
        (G.compTime (contDiff_affine r.1)).toNondegenerateMetric.chartMetric (x₀, 0) z' (b i) (b j))
        z (b k)) r.2 = fderiv ℝ (fun z ↦ D i j k (r.1, z)) r.2 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(hT.prod isOpen_univ).mem_nhds hr.2] with z hz
    rw [hd₁ i j (r := (r.1, z)) ⟨trivial, hz⟩]
  have hw₀ : (q₀, extChartAt (I.prod 𝓘(ℝ)) (x₀, (0 : ℝ)) (x₀, 0)) ∈ V :=
    ⟨trivial, htarget ▸ mem_extChartAt_target (x₀, (0 : ℝ))⟩
  have hint :
      extChartAt (I.prod 𝓘(ℝ)) (x₀, (0 : ℝ)) (x₀, 0) ∈ interior (range (I.prod 𝓘(ℝ))) := by
    rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
      ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ, interior_univ]
    trivial
  -- It remains to check the continuity of the Gram matrix and of its first and second
  -- derivatives, which near `(q₀, (x₀, 0))` are those of the coefficients `F i j`.
  have hcont := TauCeti.Manifold.continuousAt_scalarCurvature_of_continuousAt_chartMetric b
    (fun q ↦ G.compTime (contDiff_affine q)) (p₀ := q₀) hint ?_ ?_ ?_
  · exact ContinuousAt.comp (f := fun r : (ℝ × ℝ) × M ↦ (r.1, (r.2, (0 : ℝ)))) (x := (q₀, x₀))
      hcont (by fun_prop)
  · refine ContinuousAt.congr (f := fun r ↦ Matrix.of fun i j ↦ F i j r) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
      exact (hF i j).continuousOn.continuousAt (hV.mem_nhds hw₀)
    · ext i j
      simp [LinearMap.toMatrix₂_apply, hK r.1 hr.2, F]
  · refine ContinuousAt.congr (f := fun r k i j ↦ D i j k r) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
      exact (hD i j k hw₀).continuousAt
    · funext k i j
      simp only [D, hd₁ i j hr]
  · refine ContinuousAt.congr
      (f := fun r m k i j ↦ fderiv ℝ (fun z ↦ D i j k (r.1, z)) r.2 (b m)) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun m ↦ continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦
        continuousAt_pi.2 fun j ↦ ?_
      refine (ContDiffAt.fderiv (f := fun (r : (ℝ × ℝ) × (E × ℝ)) z ↦ D i j k (r.1, z))
        (g := Prod.snd) ?_ contDiffAt_snd (m := 0) (n := 1) (by norm_num)).continuousAt.clm_apply
        continuousAt_const
      exact (hD i j k hw₀).comp
        (f := fun rz : ((ℝ × ℝ) × (E × ℝ)) × (E × ℝ) ↦ (rz.1.1, rz.2)) _ (by fun_prop)
    · funext m k i j
      simp only [hd₂ i j k hr]

variable {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Where `c t` lies in a region on which the path is constant, the slowed metric is a cylinder. -/
private theorem compTime_mul_inner_of_eq (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p)
    {c s : ℝ} {p : M × ℝ} (hp : g (c * p.2) = g s) :
    (G.compTime (φ := (c * ·)) (contDiff_const.mul contDiff_id)).inner p =
      (g s).cylinder.inner p := by
  rw [compTime_inner, hG]
  dsimp only
  rw [hp, cylinder_inner_mk]

/-- **Slowing down a path of metrics of positive scalar curvature.** Let `G` be a metric on
`M × ℝ`, for a compact manifold `M`, which is the cylinder metric `g t + dt²` at every `(x, t)`.
If `g t` has positive scalar curvature for `t ∈ [0, 1]` and the path is constant for `t ≤ 0` and
for `t ≥ 1`, then for all `c` close to `0` the metric `g (c t) + dt²` has positive scalar
curvature. -/
theorem eventually_hasPositiveScalarCurvature_compTime_mul [I.Boundaryless] [CompactSpace M]
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, (g t).HasPositiveScalarCurvature)
    (h₀ : ∀ t ≤ 0, g t = g 0) (h₁ : ∀ t, 1 ≤ t → g t = g 1) :
    ∀ᶠ c in 𝓝 (0 : ℝ),
      (G.compTime (φ := (c * ·)) (contDiff_const.mul contDiff_id)).HasPositiveScalarCurvature := by
  -- Without slowing, the metric is the cylinder over the frozen metric `g s`.
  have hK₀ (s : ℝ) (x : M) :
      (G.compTime (contDiff_affine (0, s))).scalarCurvature (x, 0) = (g s).scalarCurvature x := by
    rw [eqOn_scalarCurvature (g₂ := (g s).cylinder) isOpen_univ (fun p _ ↦ ?_) (mem_univ (x, 0)),
      scalarCurvature_cylinder]
    rw [compTime_inner, hG]
    dsimp only
    rw [zero_mul, add_zero, cylinder_inner_mk]
  -- By compactness, slowing by a small enough factor keeps the scalar curvature positive.
  have hev : ∀ᶠ c in 𝓝 (0 : ℝ), ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set M),
      0 < (G.compTime (contDiff_affine (c, y.1))).scalarCurvature (y.2, 0) := by
    refine (isCompact_Icc.prod isCompact_univ).eventually_forall_of_forall_eventually
      fun y hy ↦ ?_
    have hcont := (continuousAt_scalarCurvature_compTime_affine (G := G) (0, y.1) y.2).comp
      (f := fun z : ℝ × (ℝ × M) ↦ ((z.1, z.2.1), z.2.2)) (x := (0, y)) (by fun_prop)
    refine hcont.eventually (lt_mem_nhds ?_)
    exact ((hasPositiveScalarCurvature_iff _).1 (hpos y.1 hy.1) y.2).trans_eq (hK₀ y.1 y.2).symm
  filter_upwards [hev] with c hc
  refine (hasPositiveScalarCurvature_iff _).2 fun p ↦ ?_
  rcases lt_or_ge (c * p.2) 0 with hp | hp
  · -- Before the path starts, the slowed metric is the cylinder over `g 0`.
    rw [eqOn_scalarCurvature (g₂ := (g 0).cylinder)
      (isOpen_lt (continuous_const.mul continuous_snd) continuous_const)
      (fun q hq ↦ compTime_mul_inner_of_eq hG (h₀ _ (le_of_lt hq))) hp, scalarCurvature_cylinder]
    exact (hasPositiveScalarCurvature_iff _).1 (hpos 0 ⟨le_rfl, zero_le_one⟩) p.1
  rcases lt_or_ge 1 (c * p.2) with hp' | hp'
  · -- After the path ends, the slowed metric is the cylinder over `g 1`.
    rw [eqOn_scalarCurvature (g₂ := (g 1).cylinder)
      (isOpen_lt continuous_const (continuous_const.mul continuous_snd))
      (fun q hq ↦ compTime_mul_inner_of_eq hG (h₁ _ (le_of_lt hq))) hp', scalarCurvature_cylinder]
    exact (hasPositiveScalarCurvature_iff _).1 (hpos 1 ⟨zero_le_one, le_rfl⟩) p.1
  · -- Along the path, translate `(x, t)` to `(x, 0)`.
    have h := scalarCurvature_compTime_of_eq_add (G := G) (φ := (c * ·))
      (contDiff_const.mul contDiff_id)
      (contDiff_affine (c, c * p.2)) (c := p.2) (fun τ ↦ by simp only; ring) (p.1, 0)
    simp only [zero_add] at h
    rw [← h]
    exact hc (c * p.2, p.1) ⟨⟨hp, hp'⟩, mem_univ _⟩

/-- **Smooth paths of metrics of positive scalar curvature give concordances.** Let `G` be a metric
on `M × ℝ`, for a compact manifold `M`, which is the cylinder metric `g t + dt²` at every
`(x, t)`. If `g t` has positive scalar curvature for `t ∈ [0, 1]` and the path is constant for
`t ≤ 0` and for `t ≥ 1`, then `g 0` and `g 1` are concordant. -/
theorem concordant_of_forall_inner_eq_cylinder [I.Boundaryless] [CompactSpace M]
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, (g t).HasPositiveScalarCurvature)
    (h₀ : ∀ t ≤ 0, g t = g 0) (h₁ : ∀ t, 1 ≤ t → g t = g 1) : Concordant (g 0) (g 1) := by
  obtain ⟨c, hpsc, hc⟩ :=
    ((eventually_hasPositiveScalarCurvature_compTime_mul hG hpos h₀ h₁).filter_mono
      nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))
  refine concordant_of_inner_eq_cylinder hpsc (a := 0) (b := c⁻¹) (fun p hp ↦ ?_) fun p hp ↦ ?_
  · exact compTime_mul_inner_of_eq hG (h₀ _ (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hp))
  · refine compTime_mul_inner_of_eq hG (h₁ _ ?_)
    calc 1 = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ c * p.2 := by gcongr

end Slowing

end Bundle.ContMDiffRiemannianMetric
