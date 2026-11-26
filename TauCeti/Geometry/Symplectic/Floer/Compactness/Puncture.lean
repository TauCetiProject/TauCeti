/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
import TauCeti.Analysis.Hofer
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Floer solutions in a closed manifold near a finite-energy puncture

Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed
symplectic manifold, and let `u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` for
domain-dependent almost complex structures `J(z, x)` tamed by `ω` on a punctured neighbourhood of
a point `z₀`, with integrable Floer energy density `ρ = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`. Two such
punctures occur in Gromov–Floer compactness: the bubbling points of a limit of Floer solutions, once
the limit is known to be a Floer solution of finite energy off them, and the point at infinity of a
bubble, a `J₀`-holomorphic plane of finite area, read in the chart `w ↦ w⁻¹` at infinity
(`TauCeti.Geometry.Symplectic.Floer.Compactness.Infinity`). This file proves that the derivative of
`u` blows up strictly slower than `1 / |z - z₀|`:

`|z - z₀|² ρ(z) → 0` as `z → z₀`, `z ≠ z₀`
(`TauCeti.SmoothTwoForm.IsNondegenerate.tendsto_sq_dist_mul_floerEnergyDensity_nhdsNE`),

and, measuring sizes in `M` through an injective differentiable map `e : M → F` into a normed space
such as the Whitney embedding, `|z - z₀| ‖d(e ∘ u)(z)‖ → 0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.tendsto_dist_mul_norm_fderiv_comp_nhdsNE`). This is the
first step of the removal of the puncture, the manifold counterpart of
`TauCeti.tendsto_norm_sub_mul_norm_fderiv_nhdsNE` for a vector-space target. Balls of `ℝ × ℝ` are
squares for its sup norm, and `|z - z₀|` is the sup distance.

The proof has two steps, each local in the target through the closed-manifold estimates of
`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`.

* **Boundedness.** `|z - z₀| √ρ(z)` stays bounded near `z₀`. Otherwise Hofer's lemma
  (`TauCeti.hofer_of_continuousOn_closedBall`), applied to `√ρ` on the disc of radius
  `|z - z₀| / 4` about `z`, finds a disc on which `√ρ` is at most twice its value `N` at the centre
  and whose radius is large compared with `1 / N`. Such a disc carries a fixed amount `δ` of energy
  (`IsNondegenerate.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le`),
  while the energy of the punctured disc of radius `2 |z - z₀|` about `z₀` tends to `0`.
* **Decay.** By boundedness, `ρ ≤ (2 A / |z - z₀|)²` on the disc of radius `|z - z₀| / 2` about
  `z`, so `e ∘ u` is Lipschitz there with a constant of order `1 / |z - z₀|`, and the disc of radius
  `θ |z - z₀|` about `z`, for a fixed small `θ`, has image under `e` small enough for the
  mean-value inequality on a closed manifold
  (`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt`).
  It gives `θ² |z - z₀|² ρ(z) ≤ C (θ² |z - z₀|² + ∫ ρ)`, the integral over the punctured disc of
  radius `2 |z - z₀|` about `z₀`, which tends to `0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.2
  (Hofer's lemma), Section 4.3 (the mean-value inequality) and Section 4.5 (removal of
  singularities).
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {e : M → F} {U D Ω : Set (ℝ × ℝ)} {u : ℝ × ℝ → M} {z₀ : ℝ × ℝ}

omit [FiniteDimensional ℝ E] [TopologicalSpace H] [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] in
/-- The distance to `z₀` tends to `0` in the punctured neighbourhoods of `z₀`. -/
private theorem tendsto_dist_nhdsNE : Tendsto (fun z ↦ dist z z₀) (𝓝[≠] z₀) (𝓝 0) := by
  have h : Tendsto (fun z ↦ dist z z₀) (𝓝 z₀) (𝓝 (dist z₀ z₀)) :=
    (continuous_id.dist continuous_const).tendsto z₀
  rw [dist_self] at h
  exact h.mono_left nhdsWithin_le_nhds

omit [FiniteDimensional ℝ E] [TopologicalSpace H] [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] in
/-- The integral of an integrable function on `Ω` over the part of `Ω` in the ball of radius
`2 |z - z₀|` about `z₀` tends to `0` as `z → z₀`. -/
private theorem tendsto_setIntegral_ball_two_mul_dist_inter {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f Ω) :
    Tendsto (fun z ↦ ∫ y in ball z₀ (2 * dist z z₀) ∩ Ω, f y) (𝓝[≠] z₀) (𝓝 0) := by
  have : NullSingletonClass (volume : Measure (ℝ × ℝ)) := Measure.prod.instNullSingletonClass_fst
  have hr := hf.tendsto_setIntegral_ball_nhds_zero z₀
  simp only [Measure.restrict_restrict measurableSet_ball] at hr
  have hd : Tendsto (fun z ↦ 2 * dist z z₀) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using tendsto_dist_nhdsNE.const_mul 2
  exact hr.comp hd

omit [FiniteDimensional ℝ E] [TopologicalSpace H] [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] in
/-- Points of the closed ball of radius `a ≤ 3 d / 4` about a point `z` at distance `d > 0` from
`z₀` lie in the punctured ball of radius `2 d` about `z₀`, at distance at least `d - a` from
`z₀`. -/
private theorem mem_ball_two_mul_dist_of_mem_closedBall {z y : ℝ × ℝ} {a : ℝ} (hz : z ≠ z₀)
    (ha : a ≤ dist z z₀ * (3 / 4)) (hy : y ∈ closedBall z a) :
    y ∈ ball z₀ (2 * dist z z₀) ∧ y ≠ z₀ ∧ dist z z₀ - a ≤ dist y z₀ := by
  have hd : 0 < dist z z₀ := dist_pos.2 hz
  have h₁ := dist_triangle y z z₀
  have h₂ := dist_triangle_left z z₀ y
  have hyz := mem_closedBall.1 hy
  refine ⟨mem_ball.2 (by linarith), fun h ↦ ?_, by linarith⟩
  rw [h, dist_comm] at hyz
  linarith

/-- Energy on the discs of Hofer's lemma for a single datum: the case of a one-point parameter
window of `IsNondegenerate.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le`. -/
private theorem IsNondegenerate.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le'
    (hω : ω.IsNondegenerate) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (U ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B) :
    ∃ σ > 0, ∃ δ > 0, ∃ κ > 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃Ω T : Set (ℝ × ℝ)⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃N : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
      (∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
        (ω.perturbedMFDeriv Ks Kt u y).toLinearMap) →
      MeasurableSet T → T ⊆ Ω → IntegrableOn (ω.floerEnergyDensity Ks Kt u) T →
      √(ω.floerEnergyDensity Ks Kt u z₀) = N → 0 < N → 2 * B ≤ N →
      closedBall z₀ (σ / N) ⊆ T →
      (∀ y ∈ closedBall z₀ (σ / N), √(ω.floerEnergyDensity Ks Kt u y) ≤ 2 * N) →
      (σ / N) ^ 2 < κ → δ ≤ ∫ y in T, ω.floerEnergyDensity Ks Kt u y := by
  have hπ (α : M) : MapsTo (fun q : (Unit × (ℝ × ℝ)) × E ↦ (q.1.2, q.2))
      ((univ ×ˢ U) ×ˢ (extChartAt I α).target) (U ×ˢ (extChartAt I α).target) :=
    fun q hq ↦ ⟨hq.1.2, hq.2⟩
  obtain ⟨σ, hσ, δ, hδ, κ, hκ, hdisc⟩ :=
    hω.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le
      (J := fun _ ↦ J) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (C := univ) he he_inj
      (isOpen_univ.prod hU) isCompact_univ hD (prod_mono subset_rfl hDU)
      (fun α ↦ Floer.contDiffOn_almostComplexInChartAt_uncurry_const (hJ α) (hπ α))
      (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (hXs α) (hπ α))
      (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (hXt α) (hπ α))
      (fun _ _ ↦ hJt) hc (fun _ _ ↦ hJc) (fun _ _ ↦ hBs) fun _ _ ↦ hBt
  exact ⟨σ, hσ, δ, hδ, κ, hκ, fun u Ω T z₀ N ↦ hdisc (p := ()) (mem_univ _)⟩

/-- Near a finite-energy puncture, `|z - z₀| √ρ(z)` is bounded. -/
private theorem IsNondegenerate.exists_eventually_dist_mul_sqrt_floerEnergyDensity_le
    (hω : ω.IsNondegenerate) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (U ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω)
    (hfl : ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω) (hz₀ : Ω ∈ 𝓝[≠] z₀) :
    ∃ A, ∀ᶠ z in 𝓝[≠] z₀, dist z z₀ * √(ω.floerEnergyDensity Ks Kt u z) ≤ A := by
  obtain ⟨σ, hσ, δ, hδ, κ, hκ, hdisc⟩ :=
    hω.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le' he he_inj hU hD hDU hJ
      hXs hXt hJt hc hJc hBs hBt
  set ρ := ω.floerEnergyDensity Ks Kt u
  have hρc : ContinuousOn ρ Ω :=
    ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt hΩ (hu.of_le (by norm_num))
      (fun α ↦ (hXs α).continuousOn.mono (prod_mono (hΩD.trans hDU) subset_rfl))
      fun α ↦ (hXt α).continuousOn.mono (prod_mono (hΩD.trans hDU) subset_rfl)
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhdsWithin_iff.1 hz₀
  have hd := tendsto_dist_nhdsNE (z₀ := z₀)
  have hzR : ∀ᶠ z in 𝓝[≠] z₀, 2 * dist z z₀ < R :=
    (hd.const_mul 2).eventually (gt_mem_nhds (by simpa using hR))
  have hzE : ∀ᶠ z in 𝓝[≠] z₀, ∫ y in ball z₀ (2 * dist z z₀) ∩ Ω, ρ y < δ :=
    (tendsto_setIntegral_ball_two_mul_dist_inter hint).eventually (gt_mem_nhds hδ)
  have hzκ : ∀ᶠ z in 𝓝[≠] z₀, (dist z z₀ / 4) ^ 2 < κ :=
    ((hd.div_const 4).pow 2).eventually (gt_mem_nhds (by simpa using hκ))
  have hzB : ∀ᶠ z in 𝓝[≠] z₀, 2 * B * dist z z₀ < 4 * σ :=
    (hd.const_mul (2 * B)).eventually (gt_mem_nhds (by simpa using hσ))
  refine ⟨4 * σ, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hzR, hzE, hzκ, hzB] with z hz hzR hzE hzκ hzB
  rw [mem_compl_singleton_iff] at hz
  set d := dist z z₀
  have hd0 : 0 < d := dist_pos.2 hz
  by_contra! hzA
  -- The set `T`: the part of `Ω` in the ball of radius `2 d` about `z₀`, which contains the
  -- closed ball of radius `3 d / 4` about `z`.
  set T := ball z₀ (2 * d) ∩ Ω
  have hTsub {y : ℝ × ℝ} (hy : y ∈ closedBall z (3 * (d / 4))) : y ∈ T := by
    obtain ⟨hy₁, hy₂, -⟩ := mem_ball_two_mul_dist_of_mem_closedBall hz (by linarith) hy
    exact ⟨hy₁, hRΩ ⟨ball_subset_ball hzR.le hy₁, hy₂⟩⟩
  -- Hofer's lemma for `√ρ` on the disc of radius `d / 4` about `z`.
  obtain ⟨ε', hε', x', hε'd, hx'z, hϕ, hball⟩ := TauCeti.hofer_of_continuousOn_closedBall z
    (ε := d / 4) (by positivity) (ϕ := fun y ↦ √(ρ y))
    (hρc.sqrt.mono fun y hy ↦ (hTsub hy).2) fun y _ ↦ Real.sqrt_nonneg _
  set N := √(ρ x') with hN
  have hσN : σ < ε' * N := by linarith
  have hN0 : 0 < N := by
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h hε'.le]
  have hσε : σ / N < ε' := (div_lt_iff₀ hN0).2 hσN
  have hsub : closedBall x' (σ / N) ⊆ closedBall z (3 * (d / 4)) := fun y hy ↦ by
    have := dist_triangle y x' z
    rw [mem_closedBall] at hy ⊢
    linarith
  have h : δ ≤ ∫ y in T, ρ y := hdisc hΩ hΩD hu hfl
    (measurableSet_ball.inter hΩ.measurableSet) inter_subset_right
    (hint.mono_set inter_subset_right) hN.symm hN0
    (by nlinarith [mul_le_mul_of_nonneg_right hε'd hN0.le]) (fun y hy ↦ hTsub (hsub hy))
    (fun y hy ↦ hball y (by rw [dist_comm]; exact (mem_closedBall.1 hy).trans hσε.le))
    (lt_of_le_of_lt (pow_le_pow_left₀ (div_pos hσ hN0).le (hσε.le.trans hε'd) 2) hzκ)
  linarith

omit [FiniteDimensional ℝ E] [TopologicalSpace H] [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] in
/-- From `t √ρ ≤ A` with `d / 2 ≤ t` and `d > 0`, `ρ ≤ (2 max A 0 / d)²`. -/
private theorem le_sq_div_of_mul_sqrt_le {t d ρ A : ℝ} (hd : 0 < d) (ht : d / 2 ≤ t)
    (hρ : 0 ≤ ρ) (h : t * √ρ ≤ A) : ρ ≤ (2 * max A 0 / d) ^ 2 := by
  have h₂ : √ρ ≤ 2 * max A 0 / d := by
    rw [le_div_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg ρ), le_max_left A 0]
  rw [← Real.sq_sqrt hρ]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h₂ 2

omit [FiniteDimensional ℝ E] [TopologicalSpace H] [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] in
/-- From `(θ d)² ρ ≤ C ((θ d)² + G)` with `θ > 0`, `d² ρ ≤ C (d² + G / θ²)`. -/
private theorem sq_mul_le_mul_add_div_sq {θ d ρ C G : ℝ} (hθ : 0 < θ)
    (h : (θ * d) ^ 2 * ρ ≤ C * ((θ * d) ^ 2 + G)) : d ^ 2 * ρ ≤ C * (d ^ 2 + G / θ ^ 2) := by
  have hθ2 : 0 < θ ^ 2 := by positivity
  rw [show C * (d ^ 2 + G / θ ^ 2) = C * ((θ * d) ^ 2 + G) / θ ^ 2 by field_simp,
    le_div_iff₀ hθ2]
  linarith [h]

/-- **The mean-value inequality at the scale of a density bound.** Under the hypotheses of the
mean-value inequality on a closed manifold, for every `A ≥ 0` there are a ratio `θ > 0`, a
threshold `η > 0` and a constant `C'` with the following property. Let `0 < d ≤ 1`, let the closed
disc of radius `θ d` about `z` lie in `Ω`, and let `ρ ≤ (A / d)²` on it. If
`(θ d)² + ∫_{B_{θ d}(z)} ρ < η`, then `(θ d)² ρ(z) ≤ C' ((θ d)² + ∫_{B_{θ d}(z)} ρ)`. The density
bound makes `e ∘ u` Lipschitz on the disc with a constant of order `1 / d`, so its image under `e`
is small enough for the mean-value inequality. -/
private theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_le_sq_div
    (hω : ω.IsNondegenerate) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (U ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω)
    (hfl : ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω) {A : ℝ} (hA : 0 ≤ A) :
    ∃ θ > 0, θ ≤ 1 / 2 ∧ ∃ η > 0, ∃ C' ≥ 0, ∀ ⦃z : ℝ × ℝ⦄ ⦃d : ℝ⦄, 0 < d → d ≤ 1 →
      closedBall z (θ * d) ⊆ Ω →
      (∀ y ∈ closedBall z (θ * d), ω.floerEnergyDensity Ks Kt u y ≤ (A / d) ^ 2) →
      (θ * d) ^ 2 + ∫ y in ball z (θ * d), ω.floerEnergyDensity Ks Kt u y < η →
      (θ * d) ^ 2 * ω.floerEnergyDensity Ks Kt u z ≤
        C' * ((θ * d) ^ 2 + ∫ y in ball z (θ * d), ω.floerEnergyDensity Ks Kt u y) := by
  -- The mean-value inequality for the constant family over the one-point parameter space `Unit`.
  have hπ (α : M) : MapsTo (fun q : (Unit × (ℝ × ℝ)) × E ↦ (q.1.2, q.2))
      ((univ ×ˢ U) ×ˢ (extChartAt I α).target) (U ×ˢ (extChartAt I α).target) :=
    fun q hq ↦ ⟨hq.1.2, hq.2⟩
  obtain ⟨l, hl, η, hη, C', hC', hmv⟩ :=
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt
      (J := fun _ ↦ J) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (C := univ)
      (continuous_iff_continuousAt.2 fun x ↦ (he x).continuousAt) he_inj
      (isOpen_univ.prod hU) isCompact_univ hD (prod_mono subset_rfl hDU)
      (fun α ↦ Floer.contDiffOn_almostComplexInChartAt_uncurry_const (hJ α) (hπ α))
      (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (hXs α) (hπ α))
      (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (hXt α) (hπ α))
      fun _ _ ↦ hJt
  -- The ratio `θ` makes the Lipschitz constant `2 (A / (d √c) + B₀)` times `θ d` less than `l`.
  set B₀ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  set Q := A / √c + B₀ with hQ_def
  have hQ : 0 ≤ Q := by positivity
  set θ := min (1 / 2) (l / (4 * Q + 1))
  have hθ : 0 < θ := lt_min one_half_pos (div_pos hl (by linarith [hQ]))
  have hθQ : 2 * θ * Q < l := by
    have h := min_le_right (1 / 2) (l / (4 * Q + 1))
    rw [le_div_iff₀ (by linarith [hQ])] at h
    nlinarith
  refine ⟨θ, hθ, min_le_left _ _, η, hη, C', hC', fun z d hd0 hd1 hrΩ hρA hsm ↦ ?_⟩
  have hr0 : 0 < θ * d := mul_pos hθ hd0
  have hLip := hω.lipschitzOnWith_comp_of_floerEnergyDensity_le (A := (A / d) ^ 2) (B := B₀)
    (convex_closedBall z (θ * d)) (fun y ↦ J y (u y)) hc (fun y _ ↦ he _)
    (fun y hy ↦ ((hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds (hrΩ hy))))
    (fun y hy ↦ hJc y (hΩD (hrΩ hy)) _)
    (fun y hy ↦ (hBs y (hΩD (hrΩ hy)) _).trans (le_max_left _ _))
    (fun y hy ↦ (hBt y (hΩD (hrΩ hy)) _).trans (le_max_left _ _))
    (fun y hy ↦ hfl y (hrΩ hy)) hρA
  have hLr : 2 * (√((A / d) ^ 2 / c) + B₀) * (θ * d) < l := by
    have hc' : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
    rw [Real.sqrt_div' _ hc.le, Real.sqrt_sq (div_nonneg hA hd0.le),
      show 2 * (A / d / √c + B₀) * (θ * d) = 2 * θ * (A / √c + B₀ * d) by field_simp]
    refine lt_of_le_of_lt ?_ hθQ
    rw [hQ_def]
    exact mul_le_mul_of_nonneg_left (by linarith [mul_le_of_le_one_right hB₀ hd1]) (by positivity)
  have hdist (y : ℝ × ℝ) (hy : y ∈ closedBall z (θ * d)) : dist (e (u y)) (e (u z)) < l := by
    refine (hLip.dist_le_mul y hy z (mem_closedBall_self hr0.le)).trans_lt ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall.1 hy) (by positivity)).trans_lt hLr
  exact hmv (p := ()) (mem_univ _) hΩ hr0.le hrΩ (hrΩ.trans hΩD) hu
    (fun y hy ↦ hfl y (hrΩ (ball_subset_closedBall hy))) hdist
    (hint.mono_set (ball_subset_closedBall.trans hrΩ)) hsm

/-- **The energy density of a Floer solution in a closed manifold near a finite-energy
puncture.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, and let
the structures `J(z, x)` and the Hamiltonian vector fields of `K_s` and `K_t`, read in the chart at
every point, be `C²` on `U × (extChartAt I α).target` for an open set `U` of the domain containing
a compact window `D`, with `J(z, x)` tamed by `ω` for `z ∈ D`. Let `e : M → F` be an injective
differentiable map into a normed space, such as the Whitney embedding, with the structures
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and the pushforwards
`d e (X_{K_s})`, `d e (X_{K_t})` at most `B`. Let `u` be a `C³` solution of the Floer equation
`(du - X_K)^{0,1} = 0` on an open set `Ω ⊆ D` which is a punctured neighbourhood of `z₀`, with
integrable Floer energy density `ρ`. Then `|z - z₀|² ρ(z) → 0` as `z → z₀`, `z ≠ z₀`. -/
theorem IsNondegenerate.tendsto_sq_dist_mul_floerEnergyDensity_nhdsNE
    (hω : ω.IsNondegenerate) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (U ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω)
    (hfl : ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω) (hz₀ : Ω ∈ 𝓝[≠] z₀) :
    Tendsto (fun z ↦ dist z z₀ ^ 2 * ω.floerEnergyDensity Ks Kt u z) (𝓝[≠] z₀) (𝓝 0) := by
  set ρ := ω.floerEnergyDensity Ks Kt u
  -- By boundedness, `|z - z₀| √ρ(z) ≤ A` on a punctured ball of radius `r₁` about `z₀`.
  obtain ⟨A₀, hA₀⟩ := hω.exists_eventually_dist_mul_sqrt_floerEnergyDensity_le he he_inj hU hD hDU
    hJ hXs hXt hJt hc hJc hBs hBt hΩ hΩD hu hfl hint hz₀
  obtain ⟨r₁, hr₁, hr₁A⟩ := Metric.mem_nhdsWithin_iff.1 hA₀
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhdsWithin_iff.1 hz₀
  obtain ⟨θ, hθ, hθ2, η, hη, C', hC', hmv⟩ :=
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_le_sq_div he he_inj hU hD hDU hJ hXs hXt
      hJt hc hJc hBs hBt hΩ hΩD hu hfl hint (A := 2 * max A₀ 0) (by positivity)
  have hd := tendsto_dist_nhdsNE (z₀ := z₀)
  have hG := tendsto_setIntegral_ball_two_mul_dist_inter hint (z₀ := z₀)
  have hρ0 {y : ℝ × ℝ} (hy : y ∈ Ω) : 0 ≤ ρ y :=
    floerEnergyDensity_nonneg hω (hJt y (hΩD hy) _) (hfl y hy)
  -- The upper bound `C' (|z - z₀|² + G(z) / θ²)`, where `G(z)` is the energy of the punctured ball
  -- of radius `2 |z - z₀|` about `z₀`, tends to `0`.
  have hup : Tendsto (fun z ↦ C' * (dist z z₀ ^ 2 +
      (∫ y in ball z₀ (2 * dist z z₀) ∩ Ω, ρ y) / θ ^ 2)) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using ((hd.pow 2).add (hG.div_const (θ ^ 2))).const_mul C'
  have hsmall : Tendsto (fun z ↦ (θ * dist z z₀) ^ 2 + ∫ y in ball z₀ (2 * dist z z₀) ∩ Ω, ρ y)
      (𝓝[≠] z₀) (𝓝 0) := by
    simpa using ((hd.const_mul θ).pow 2).add hG
  have hzR : ∀ᶠ z in 𝓝[≠] z₀, 2 * dist z z₀ < R :=
    (hd.const_mul 2).eventually (gt_mem_nhds (by simpa using hR))
  have hzr₁ : ∀ᶠ z in 𝓝[≠] z₀, 2 * dist z z₀ < r₁ :=
    (hd.const_mul 2).eventually (gt_mem_nhds (by simpa using hr₁))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (by filter_upwards [hz₀] with z hz using mul_nonneg (sq_nonneg _) (hρ0 hz)) ?_
  filter_upwards [self_mem_nhdsWithin, hzR, hzr₁, hd.eventually (ge_mem_nhds one_pos),
    hsmall.eventually (gt_mem_nhds hη)] with z hz hzR hzr₁ hz1 hzη
  rw [mem_compl_singleton_iff] at hz
  have hd0 : 0 < dist z z₀ := dist_pos.2 hz
  -- The closed disc of radius `θ d` about `z`, for `d = |z - z₀|`, lies in the punctured ball of
  -- radius `2 d` about `z₀`, hence in `Ω`, at distance at least `d / 2` from `z₀`.
  have hmem {y : ℝ × ℝ} (hy : y ∈ closedBall z (θ * dist z z₀)) :
      y ∈ ball z₀ (2 * dist z z₀) ∩ Ω ∧ y ∈ ball z₀ r₁ ∩ {z₀}ᶜ ∧ dist z z₀ / 2 ≤ dist y z₀ := by
    obtain ⟨hy₁, hy₂, hy₃⟩ := mem_ball_two_mul_dist_of_mem_closedBall hz (by nlinarith) hy
    exact ⟨⟨hy₁, hRΩ ⟨ball_subset_ball hzR.le hy₁, hy₂⟩⟩, ⟨ball_subset_ball hzr₁.le hy₁, hy₂⟩,
      by nlinarith⟩
  -- There `ρ ≤ (2 A / d)²`, by boundedness at distance at least `d / 2` from `z₀`.
  have hρA (y : ℝ × ℝ) (hy : y ∈ closedBall z (θ * dist z z₀)) :
      ρ y ≤ (2 * max A₀ 0 / dist z z₀) ^ 2 :=
    le_sq_div_of_mul_sqrt_le hd0 (hmem hy).2.2 (hρ0 (hmem hy).1.2) (hr₁A (hmem hy).2.1)
  -- The energy of the disc is at most that of the punctured ball of radius `2 d` about `z₀`.
  have hI : ∫ y in ball z (θ * dist z z₀), ρ y ≤ ∫ y in ball z₀ (2 * dist z z₀) ∩ Ω, ρ y :=
    setIntegral_mono_set (hint.mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ.measurableSet)
        fun y hy ↦ hρ0 hy.2)
      (Eventually.of_forall fun y hy ↦ (hmem (ball_subset_closedBall hy)).1)
  have h := hmv hd0 hz1 (fun y hy ↦ (hmem hy).1.2) hρA (by linarith)
  exact sq_mul_le_mul_add_div_sq hθ (h.trans (mul_le_mul_of_nonneg_left (by linarith) hC'))

/-- **The derivative of a Floer solution in a closed manifold near a finite-energy puncture.**
Under the hypotheses of `IsNondegenerate.tendsto_sq_dist_mul_floerEnergyDensity_nhdsNE`, the
derivative of `e ∘ u` blows up strictly slower than `1 / |z - z₀|`:
`|z - z₀| ‖d(e ∘ u)(z)‖ → 0` as `z → z₀`, `z ≠ z₀`. -/
theorem IsNondegenerate.tendsto_dist_mul_norm_fderiv_comp_nhdsNE
    (hω : ω.IsNondegenerate) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (U ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω)
    (hfl : ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω) (hz₀ : Ω ∈ 𝓝[≠] z₀) :
    Tendsto (fun z ↦ dist z z₀ * ‖fderiv ℝ (e ∘ u) z‖) (𝓝[≠] z₀) (𝓝 0) := by
  have hρ := hω.tendsto_sq_dist_mul_floerEnergyDensity_nhdsNE he he_inj hU hD hDU hJ hXs hXt hJt
    hc hJc hBs hBt hΩ hΩD hu hfl hint hz₀
  set B₀ := max B 0
  have hd := tendsto_dist_nhdsNE (z₀ := z₀)
  have hup : Tendsto (fun z ↦ 2 * (√(dist z z₀ ^ 2 * ω.floerEnergyDensity Ks Kt u z / c) +
      B₀ * dist z z₀)) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using (((hρ.div_const c).sqrt).add (hd.const_mul B₀)).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun z ↦ by positivity) ?_
  filter_upwards [hz₀] with z hz
  have hDz := hω.norm_fderiv_comp_le (J := J z (u z)) hc (he _)
    ((hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hz))
    (hJc z (hΩD hz) _) ((hBs z (hΩD hz) _).trans (le_max_left B 0))
    ((hBt z (hΩD hz) _).trans (le_max_left B 0)) (hfl z hz)
  have hsqrt : √(dist z z₀ ^ 2 * ω.floerEnergyDensity Ks Kt u z / c) =
      dist z z₀ * √(ω.floerEnergyDensity Ks Kt u z / c) := by
    rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq dist_nonneg]
  rw [hsqrt]
  calc dist z z₀ * ‖fderiv ℝ (e ∘ u) z‖
      ≤ dist z z₀ * (2 * (√(ω.floerEnergyDensity Ks Kt u z / c) + B₀)) :=
        mul_le_mul_of_nonneg_left hDz dist_nonneg
    _ = 2 * (dist z z₀ * √(ω.floerEnergyDensity Ks Kt u z / c) + B₀ * dist z z₀) := by ring

end TauCeti.SmoothTwoForm
