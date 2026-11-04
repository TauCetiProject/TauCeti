/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.CompTime

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
curvature of `g (c t) + dt²` at `(x, t)` with the value at `(c, c t, x)`. The continuity in
`(c, s)` and the translation invariance are
`Bundle.ContMDiffRiemannianMetric.continuousAt_scalarCurvature_compTime_affine` and
`Bundle.ContMDiffRiemannianMetric.scalarCurvature_compTime_of_eq_add`, from
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.CompTime`.

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
  have hA (q : ℝ × ℝ) : ContDiff ℝ ∞ (fun τ : ℝ ↦ q.2 + q.1 * τ) := by fun_prop
  -- Without slowing, the metric is the cylinder over the frozen metric `g s`.
  have hK₀ (s : ℝ) (x : M) :
      (G.compTime (hA (0, s))).scalarCurvature (x, 0) = (g s).scalarCurvature x := by
    rw [eqOn_scalarCurvature (g₂ := (g s).cylinder) isOpen_univ (fun p _ ↦ ?_) (mem_univ (x, 0)),
      scalarCurvature_cylinder]
    rw [compTime_inner, hG]
    dsimp only
    rw [zero_mul, add_zero, cylinder_inner_mk]
  -- By compactness, slowing by a small enough factor keeps the scalar curvature positive.
  have hev : ∀ᶠ c in 𝓝 (0 : ℝ), ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set M),
      0 < (G.compTime (hA (c, y.1))).scalarCurvature (y.2, 0) := by
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
      (hA (c, c * p.2)) (c := p.2) (fun τ ↦ by simp only; ring) (p.1, 0)
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
