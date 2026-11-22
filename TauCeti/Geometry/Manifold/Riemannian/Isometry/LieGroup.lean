/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CompactUnitary
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.CompactOpen
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# The isometry group of a compact Riemannian manifold is a Lie group

Let `M` be a compact smooth boundaryless Riemannian manifold whose distance is the Riemannian
distance. Its group `M ≃ᵢ M` of metric isometries, with the compact-open topology, has no small
subgroups (`IsometryEquiv.hasNoSmallSubgroups`). Since it is a compact Hausdorff group, it
therefore carries the structure of a finite-dimensional real Lie group
(`IsometryEquiv.exists_lieGroup`), by `TauCeti.Lie.HasNoSmallSubgroups.exists_lieGroup`. This is
the Lie group part of the Myers–Steenrod theorem; isometry groups of compact fibres are the
compact structure groups of Riemannian fibre bundles. The atlas obtained this way is abstract:
the smoothness of the evaluation map `(e, x) ↦ e x` for it is not established here.

The underlying local statement holds on every smooth boundaryless Riemannian manifold, compact or
not: an isometry all of whose powers stay close enough to the identity fixes a neighbourhood of a
given point (`IsometryEquiv.exists_nhds_one_forall_pow_mem_eqOn`).

## Main results

* `IsometryEquiv.exists_nhds_one_forall_pow_mem_eqOn`: an isometry all of whose powers lie in a
  suitable neighbourhood of the identity fixes a neighbourhood of a given point.
* `IsometryEquiv.hasNoSmallSubgroups`: the isometry group of a compact Riemannian manifold has no
  small subgroups.
* `IsometryEquiv.exists_lieGroup`: the isometry group of a compact Riemannian manifold is a
  finite-dimensional real Lie group.

## Implementation notes

The local statement is proved in one chart. Fix `x : M` and the extended chart `φ` at `x`.
Isometries are smooth, and the identification of the compact-open topology with the weak Whitney
topology (`IsometryEquiv.continuous_toContMDiffMap`) shows that an isometry `e` close to the
identity keeps a closed coordinate ball `B` around `φ x` inside the chart, with coordinate
representative `φ ∘ e ∘ φ.symm` whose derivative is within `1 / 2` of the identity on `B`.
Suppose every power `g ^ k` of `g` is that close, write `g_k` for the coordinate representative
of `g ^ k`, and let `z` be a point near `φ x` with `w = g_1 z`. Then `g_k w = g_(k + 1) z`, so the
differences `g_k w - g_k z` telescope to `g_N z - z`, which stays bounded. On the other hand, the
mean value inequality makes each difference `g_k w - g_k z` lie within `‖w - z‖ / 2` of `w - z`,
so `N ‖w - z‖ / 2 ≤ ‖g_N z - z‖` for every `N`. Hence `w = z`. Finitely many of the resulting
neighbourhoods cover the compact manifold `M`.

This is the averaging argument of Bochner and Montgomery for groups of differentiable
transformations, with the finite averages `(1 / N) ∑_(k < N) g_k` along the powers of a single
isometry in place of an average over a compact subgroup.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. (2) 40 (1939), 400–416.
* S. Bochner and D. Montgomery, *Groups of differentiable and real or complex analytic
  transformations*, Ann. of Math. (2) 46 (1945), 685–694.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

open Bundle Filter Function Manifold Metric Set Topology
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney
  TauCeti.RiemannianIsometryWeakWhitney

/-- If maps `f k` are uniformly `C¹`-close to the identity on a convex set `s` containing `z` and
`w`, satisfy `f k w = f (k + 1) z` and `f 0 z = z`, and the orbit `f k z` stays within a bounded
distance of `z`, then `w = z`. Here `f k` stands for the `k`-th power of a map sending `z` to `w`,
written in a chart. -/
private theorem eq_of_forall_hasFDerivWithinAt_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (hs : Convex ℝ s)
    {f : ℕ → E → E} {f' : ℕ → E → E →L[ℝ] E}
    (hf : ∀ k, ∀ y ∈ s, HasFDerivWithinAt (f k) (f' k y) s y)
    (hf' : ∀ k, ∀ y ∈ s, ‖f' k y - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    {z w : E} (hz : z ∈ s) (hw : w ∈ s) (h0 : f 0 z = z) (hstep : ∀ k, f k w = f (k + 1) z)
    {C : ℝ} (hC : ∀ k, ‖f k z - z‖ ≤ C) : w = z := by
  -- Each step `f (k + 1) z - f k z = f k w - f k z` is within `‖w - z‖ / 2` of `w - z`.
  have hstep_le (k : ℕ) : ‖(f (k + 1) z - f k z) - (w - z)‖ ≤ 1 / 2 * ‖w - z‖ := by
    simpa [← hstep k] using
      hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (hf k) (hf' k) hz hw
  -- Summing the steps, `‖w - z‖ / 2` is at most `C / N` for every `N`.
  have hN (N : ℕ) : (N : ℝ) * (1 / 2 * ‖w - z‖) ≤ C := by
    have hsum : ‖(f N z - z) - (N : ℝ) • (w - z)‖ ≤ N * (1 / 2 * ‖w - z‖) := by
      have htel : f N z - z - (N : ℝ) • (w - z) =
          ∑ k ∈ Finset.range N, ((f (k + 1) z - f k z) - (w - z)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k ↦ f k z), h0,
          Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
      rw [htel]
      refine (norm_sum_le _ _).trans ?_
      simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) ↦ hstep_le k
    have htri := norm_sub_norm_le ((N : ℝ) • (w - z)) (f N z - z)
    rw [norm_smul, Real.norm_natCast] at htri
    linarith [hC N, norm_sub_rev (f N z - z) ((N : ℝ) • (w - z))]
  by_contra hne
  have hpos : 0 < 1 / 2 * ‖w - z‖ := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hne)
    positivity
  obtain ⟨N, hN'⟩ := exists_nat_gt (C / (1 / 2 * ‖w - z‖))
  have := (div_lt_iff₀ hpos).1 hN'
  linarith [hN N]

namespace IsometryEquiv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- A weak Whitney chart test on the smooth map underlying an isometry `e`, in terms of `e`. -/
private theorem mem_chartJetSet_iff (e : M ≃ᵢ M) (x : M) (m : ℕ)
    (K : Set (extChartAt I x).target) (V : Set (E [×m]→L[ℝ] E)) :
    (e.toRiemannianIsometry I I).toDiffeomorph.toContMDiffMap ∈
        ContMDiffMap.chartJetSet x x m K V ↔
      ∀ z ∈ K, e ((extChartAt I x).symm z) ∈ (extChartAt I x).source ∧
        iteratedFDerivWithin ℝ m (extChartAt I x ∘ e ∘ (extChartAt I x).symm)
          (extChartAt I x).target z ∈ V := by
  simp only [ContMDiffMap.mem_chartJetSet, Diffeomorph.coe_coe,
    TauCeti.RiemannianIsometry.coe_toDiffeomorph, IsometryEquiv.coe_toRiemannianIsometry]

/-- Isometries near the identity map a closed coordinate ball around `x` into the chart at `x`,
with coordinate `m`-jets on that ball in any open set `V` that contains the identity's `m`-jets
there. -/
private theorem eventually_iteratedFDerivWithin_chart_mem (x : M) (m : ℕ) {ρ : ℝ}
    (hBT : closedBall (extChartAt I x x) ρ ⊆ (extChartAt I x).target)
    {V : Set (E [×m]→L[ℝ] E)} (hV : IsOpen V)
    (hid : ∀ z ∈ closedBall (extChartAt I x x) ρ,
      iteratedFDerivWithin ℝ m id (extChartAt I x).target z ∈ V) :
    ∀ᶠ e : M ≃ᵢ M in 𝓝 1, ∀ z ∈ closedBall (extChartAt I x x) ρ,
      e ((extChartAt I x).symm z) ∈ (extChartAt I x).source ∧
        iteratedFDerivWithin ℝ m (extChartAt I x ∘ e ∘ (extChartAt I x).symm)
          (extChartAt I x).target z ∈ V := by
  let K : Set (extChartAt I x).target := (↑) ⁻¹' closedBall (extChartAt I x x) ρ
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hBT]
    exact isCompact_closedBall _ _
  -- The identity passes the weak Whitney test given by `K` and `V`.
  have h1 : ((1 : M ≃ᵢ M).toRiemannianIsometry I I).toDiffeomorph.toContMDiffMap ∈
      ContMDiffMap.chartJetSet x x m K V := by
    rw [mem_chartJetSet_iff]
    rintro ⟨z, hz⟩ hzB
    refine ⟨(extChartAt I x).map_target hz, ?_⟩
    rw [iteratedFDerivWithin_congr (f := id)
      (f₁ := extChartAt I x ∘ ⇑(1 : M ≃ᵢ M) ∘ (extChartAt I x).symm)
      (fun y hy ↦ (extChartAt I x).right_inv hy) hz]
    exact hid z hzB
  filter_upwards [IsometryEquiv.continuous_toContMDiffMap.continuousAt.preimage_mem_nhds
    ((ContMDiffMap.isOpen_chartJetSet x x m (by simp) hK hV).mem_nhds h1)] with e he z hzB
  rw [mem_preimage, mem_chartJetSet_iff] at he
  exact he ⟨z, hBT hzB⟩ hzB

/-- Isometries near the identity map a closed coordinate ball around `x` into the chart at `x`,
with coordinate derivative within `1 / 2` of the identity on that ball. -/
private theorem eventually_norm_fderiv_chart_sub_id_lt (x : M) {ρ : ℝ}
    (hBT : closedBall (extChartAt I x x) ρ ⊆ (extChartAt I x).target) :
    ∀ᶠ e : M ≃ᵢ M in 𝓝 1, ∀ z ∈ closedBall (extChartAt I x x) ρ,
      e ((extChartAt I x).symm z) ∈ (extChartAt I x).source ∧
        ‖fderiv ℝ (extChartAt I x ∘ e ∘ (extChartAt I x).symm) z -
          ContinuousLinearMap.id ℝ E‖ < 1 / 2 := by
  have hT : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  filter_upwards [eventually_iteratedFDerivWithin_chart_mem x 1 hBT
    (V := continuousMultilinearCurryFin1 ℝ E E ⁻¹' ball (ContinuousLinearMap.id ℝ E) (1 / 2))
    (isOpen_ball.preimage (continuousMultilinearCurryFin1 ℝ E E).continuous)
    fun z hzB ↦ by
      rw [mem_preimage, iteratedFDerivWithin_of_isOpen 1 hT (hBT hzB),
        TauCeti.continuousMultilinearCurryFin1_iteratedFDeriv_one, fderiv_id, mem_ball,
        dist_self]
      norm_num] with e he z hzB
  obtain ⟨h₁, h₂⟩ := he z hzB
  rw [mem_preimage, iteratedFDerivWithin_of_isOpen 1 hT (hBT hzB),
    TauCeti.continuousMultilinearCurryFin1_iteratedFDeriv_one,
    mem_ball_iff_norm] at h₂
  exact ⟨h₁, h₂⟩

/-- Isometries near the identity map a closed coordinate ball of radius `r` around `x` into the
chart at `x`, with coordinate values in the ball of radius `ρ > r`. -/
private theorem eventually_mem_ball_chart (x : M) {r ρ : ℝ}
    (hBT : closedBall (extChartAt I x x) r ⊆ (extChartAt I x).target) (hr : r < ρ) :
    ∀ᶠ e : M ≃ᵢ M in 𝓝 1, ∀ z ∈ closedBall (extChartAt I x x) r,
      e ((extChartAt I x).symm z) ∈ (extChartAt I x).source ∧
        extChartAt I x (e ((extChartAt I x).symm z)) ∈ ball (extChartAt I x x) ρ := by
  filter_upwards [eventually_iteratedFDerivWithin_chart_mem x 0 hBT
    (V := continuousMultilinearCurryFin0 ℝ E E ⁻¹' ball (extChartAt I x x) ρ)
    (isOpen_ball.preimage (continuousMultilinearCurryFin0 ℝ E E).continuous)
    fun z hzB ↦ by
      simpa only [mem_preimage, continuousMultilinearCurryFin0_apply,
        iteratedFDerivWithin_zero_apply, id_eq] using closedBall_subset_ball hr hzB]
    with e he z hzB
  obtain ⟨h₁, h₂⟩ := he z hzB
  rw [mem_preimage, continuousMultilinearCurryFin0_apply, iteratedFDerivWithin_zero_apply] at h₂
  exact ⟨h₁, h₂⟩

variable (I) in
include I in
/-- **Isometries with all powers near the identity fix a neighbourhood.** For every point `x` of a
smooth boundaryless Riemannian manifold, there are a neighbourhood `U` of the identity in the
isometry group `M ≃ᵢ M` and a neighbourhood `W` of `x` such that every isometry all of whose powers
lie in `U` fixes `W` pointwise. -/
theorem exists_nhds_one_forall_pow_mem_eqOn (x : M) :
    ∃ U ∈ 𝓝 (1 : M ≃ᵢ M), ∃ W ∈ 𝓝 x, ∀ g : M ≃ᵢ M, (∀ n : ℕ, g ^ n ∈ U) → EqOn g id W := by
  set φ := extChartAt I x
  set z₀ : E := φ x
  obtain ⟨ε, hε, hεT⟩ :=
    Metric.isOpen_iff.1 (isOpen_extChartAt_target x) z₀ (mem_extChartAt_target x)
  set ρ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  have hBT : closedBall z₀ ρ ⊆ φ.target := (closedBall_subset_ball (half_lt_self hε)).trans hεT
  have hBT' : closedBall z₀ (ρ / 2) ⊆ φ.target :=
    (closedBall_subset_closedBall (half_le_self hρ.le)).trans hBT
  refine ⟨_, (eventually_norm_fderiv_chart_sub_id_lt x hBT).and
      (eventually_mem_ball_chart x hBT' (half_lt_self hρ)),
    φ.source ∩ φ ⁻¹' ball z₀ (ρ / 2), inter_mem (extChartAt_source_mem_nhds x)
      ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds z₀ (half_pos hρ))),
    fun g hg p ⟨hpS, hpB⟩ ↦ ?_⟩
  -- Apply the telescoping estimate to the coordinate representatives of the powers of `g`.
  set f : ℕ → E → E := fun k ↦ φ ∘ ⇑(g ^ k) ∘ φ.symm
  set z : E := φ p
  have hzB : z ∈ closedBall z₀ (ρ / 2) := ball_subset_closedBall hpB
  have hpz : φ.symm z = p := φ.left_inv hpS
  have hdiff (k : ℕ) (y : E) (hy : y ∈ closedBall z₀ ρ) :
      HasFDerivAt (f k) (fderiv ℝ (f k) y) y := by
    have hx : φ.symm y ∈ (chartAt H x).source := by
      rw [← extChartAt_source I]
      exact φ.map_target (hBT hy)
    have hy' : (g ^ k) (φ.symm y) ∈ (chartAt H x).source := by
      rw [← extChartAt_source I]
      exact ((hg k).1 y hy).1
    have hcd := ((contMDiffAt_iff_of_mem_source hx hy').1
      ((IsometryEquiv.contMDiff I I (g ^ k)).contMDiffAt)).2
    rw [I.range_eq_univ, contDiffWithinAt_univ, φ.right_inv (hBT hy)] at hcd
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hw : f 1 z ∈ closedBall z₀ ρ := ball_subset_closedBall ((hg 1).2 z hzB).2
  have hgp : g p ∈ φ.source := by
    have := ((hg 1).2 z hzB).1
    rwa [pow_one, hpz] at this
  have hfix := eq_of_forall_hasFDerivWithinAt_sub_le (convex_closedBall z₀ ρ)
    (fun k y hy ↦ (hdiff k y hy).hasFDerivWithinAt) (fun k y hy ↦ ((hg k).1 y hy).2.le)
    (closedBall_subset_closedBall (half_le_self hρ.le) hzB) hw
    (by simp [f, φ.right_inv (hBT' hzB)])
    (fun k ↦ by simp [f, hpz, φ.left_inv hgp, pow_succ])
    (C := ρ + ρ / 2) fun k ↦ by
      refine (norm_sub_le_norm_sub_add_norm_sub _ z₀ _).trans (add_le_add ?_ ?_)
      · exact (mem_ball_iff_norm.1 ((hg k).2 z hzB).2).le
      · rw [← mem_closedBall_iff_norm']
        exact hzB
  simp only [f, comp_apply, pow_one, hpz, z] at hfix
  exact φ.injOn hgp hpS hfix

variable [CompactSpace M]

variable (I) in
include I in
/-- **The isometry group of a compact Riemannian manifold has no small subgroups.** On a compact
smooth boundaryless Riemannian manifold `M`, some neighbourhood of the identity in `M ≃ᵢ M`, with
the compact-open topology, contains no nontrivial subgroup. -/
theorem hasNoSmallSubgroups : TauCeti.HasNoSmallSubgroups (M ≃ᵢ M) := by
  choose U hU W hW hfix using exists_nhds_one_forall_pow_mem_eqOn I (M := M)
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover W hW
  refine TauCeti.HasNoSmallSubgroups.of_forall_pow_mem
    ⟨⋂ x ∈ t, U x, (biInter_finset_mem t).2 fun x _ ↦ hU x, fun g hg ↦ ?_⟩
  ext p
  obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (ht.symm ▸ mem_univ p : p ∈ ⋃ x ∈ t, W x)
  exact hfix x g (fun n ↦ mem_iInter₂.1 (hg n) x hx) hpx

variable (I) in
include I in
/-- **The isometry group of a compact Riemannian manifold is a Lie group.** On a compact smooth
boundaryless Riemannian manifold `M`, the compact group `M ≃ᵢ M` of metric isometries, with the
compact-open topology, carries a smooth atlas modelled on a Euclidean space for which it is a Lie
group. -/
theorem exists_lieGroup :
    ∃ (d : ℕ) (atlas : ChartedSpace (EuclideanSpace ℝ (Fin d)) (M ≃ᵢ M)),
      letI := atlas
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (M ≃ᵢ M) :=
  TauCeti.Lie.HasNoSmallSubgroups.exists_lieGroup (hasNoSmallSubgroups I)

end IsometryEquiv
