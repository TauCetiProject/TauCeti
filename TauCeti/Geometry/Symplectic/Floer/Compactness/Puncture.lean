/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Manifold
import TauCeti.Analysis.Hofer
import TauCeti.Analysis.Normed.Module.Ball.Rescale
import TauCeti.Geometry.Manifold.ContMDiff.AddSmul
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Floer solutions and pseudoholomorphic maps in a closed manifold near a finite-energy puncture

## Floer solutions

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

## Pseudoholomorphic maps

Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed
symplectic manifold, taming a smooth almost complex structure `J₀`, and let `u` be a
`J₀`-holomorphic map, a solution of `∂ₜu = J₀(u) ∂ₛu`, written as the Floer equation with zero
perturbation. Its energy density `ρ = ω(∂ₛu, ∂ₜu)` is the Floer energy density for the zero
perturbation. This file proves the first step of the removal of singularities for such maps
(McDuff and Salamon, Section 4.5) in a closed manifold, with no condition on where the map takes
its values: near a puncture of finite energy the energy density blows up strictly slower than
`1 / |z - z₀|²`.

* **The mean-value inequality without a constant term**
  (`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_mul_setIntegral`). The
  mean-value inequality for Floer solutions in a closed manifold
  (`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt`) reads
  `r² ρ(z₀) ≤ C (r² + ∫_{B_r(z₀)} ρ)`, the term `r²` accounting for the Hamiltonian perturbation.
  For `J₀`-holomorphic maps the equation is invariant under the rescalings `w ↦ z₀ + ε w` of the
  domain, which multiply the energy density by `ε²` and preserve the energy
  (`TauCeti.SmoothTwoForm.floerEnergyDensity_rescale`,
  `TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_rescale`). Applying the inequality to the
  rescaled map on the disc of radius `r / ε` and letting `ε → ∞` removes the term `r²`:
  `r² ρ(z₀) ≤ C ∫_{B_r(z₀)} ρ`, as long as the energy is below a threshold and the image of the
  disc is small, measured through an injective map `e : M → X`.
* **Small energy, small density**
  (`IsNondegenerate.exists_pos_forall_floerEnergyDensity_lt_of_setIntegral_lt`).
  For every `η > 0` there is `δ > 0` such that a `J₀`-holomorphic map on the unit disc of energy
  less than `δ` has energy density less than `η` at the centre. Otherwise there are maps `uₖ` with
  energies tending to zero and densities at the centre bounded below. Along a subsequence the maps
  converge off finitely many bubbling points by the compactness theorem in a closed manifold
  (`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset`). Every
  bubbling point carries a fixed amount of energy, so there is none, and the energy densities are
  bounded on the disc of radius `1 / 2`. The maps are then uniformly Lipschitz through `e`
  (`IsNondegenerate.lipschitzOnWith_comp_of_floerEnergyDensity_le`), so a disc of a fixed small
  radius has small image, and the mean-value inequality without constant term bounds the density
  at the centre by a multiple of the energy, which tends to zero. Its rescaled form
  (`IsNondegenerate.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral`), for the rescaled
  maps of `TauCeti.SmoothTwoForm.IsNondegenerate.integrableOn_and_setIntegral_rescale_le`, says
  that if the energies over discs `B_{s a}(p a)` tend to zero along any filter, then so do the
  scaled densities `(s a)² ρ(p a)`.
* **Decay at a puncture** (`IsNondegenerate.tendsto_norm_sub_sq_mul_floerEnergyDensity_nhdsNE`,
  `IsNondegenerate.tendsto_norm_sub_mul_norm_fderiv_comp_nhdsNE`). For a `J₀`-holomorphic map of
  finite energy on a punctured disc `B_R(z₀) \ {z₀}`, `|z - z₀|² ρ(z) → 0` and
  `|z - z₀| ‖d (e ∘ u)(z)‖ → 0` as `z → z₀`. The disc of radius `|z - z₀| / 2` about `z` lies in
  the punctured disc of radius `2 |z - z₀|`, whose energy tends to zero.
  This is the zero-perturbation case of the decay of Floer solutions above, stated with
  hypotheses only on the punctured disc and proved instead through the small-energy estimate.
* **Decay at infinity** (`IsNondegenerate.tendsto_norm_sq_mul_floerEnergyDensity_cocompact`,
  `IsNondegenerate.tendsto_norm_mul_norm_fderiv_comp_cocompact`). For a `J₀`-holomorphic map of
  finite energy outside a disc, `|z|² ρ(z) → 0` and `|z| ‖d (e ∘ u)(z)‖ → 0` as `z → ∞`: the disc
  of radius `|z| / 2` about `z` lies outside the disc of radius `|z| / 2` about `0`, whose
  complement carries energy tending to zero. This is the end of a bubble, a finite-energy
  `J₀`-holomorphic plane, at the point at infinity of the sphere.

So the images of the circles about the puncture, and of the large circles about `0`, have
derivative `o(1)` in the angle through `e`. In a vector space the corresponding statement is
`TauCeti.tendsto_norm_sub_mul_norm_fderiv_nhdsNE`; there the isoperimetric inequality then gives
the decay of the energy and the continuous extension across the puncture. In a closed manifold the
continuous extension, and hence the removal of the singularity at infinity of a bubble, is not
proved here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.2
  (Hofer's lemma), Section 4.3 (the mean-value inequality), Section 4.5 (removal of
  singularities) and Section 4.6 (bubbling off finitely many points).
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

section FloerSolution

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

end FloerSolution

section Holomorphic

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}

section Data

/-- If `a ≤ C (t² + E)` for every small `t > 0` with `t² + E < δ`, and `E < δ`, then `a ≤ C E`. -/
private theorem le_mul_of_forall_le_mul_sq_add {a C E δ : ℝ} (hE : E < δ)
    (h : ∀ t ∈ Ioc (0 : ℝ) 1, t ^ 2 + E < δ → a ≤ C * (t ^ 2 + E)) : a ≤ C * E := by
  have hcont : Continuous fun t : ℝ ↦ t ^ 2 + E := by fun_prop
  have hlim : Tendsto (fun t : ℝ ↦ C * (t ^ 2 + E)) (𝓝[>] 0) (𝓝 (C * E)) := by
    simpa using ((hcont.tendsto 0).const_mul C).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ^ 2 + E < δ :=
    ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by simpa using hE))
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos, hsmall] with t h1 h2 using h t h1 h2

end Data

section Closed

variable [I.Boundaryless] [CompactSpace M]

/-- **The mean-value inequality for pseudoholomorphic maps in a closed manifold.** Let `ω` be a
nondegenerate two-form on a compact boundaryless manifold `M` taming a smooth almost complex
structure `J₀`, and let `e : M → X` be a continuous injective map into a metric space, such as an
embedding into a Euclidean space. There are `l > 0`, a threshold `δ > 0` and a constant `C` with
the following property. Let `u` be `C³` on an open set `Ω` containing the closed ball
`closedBall z₀ r` of `ℝ × ℝ`, `J₀`-holomorphic on the open ball, with `e(u(y))` within `l` of
`e(u(z₀))` for `y` in the closed ball. If the energy density `ρ = ω(∂ₛu, ∂ₜu)` is integrable on the
open ball `B_r(z₀)` and `∫_{B_r(z₀)} ρ < δ`, then

`r² ρ(z₀) ≤ C ∫_{B_r(z₀)} ρ`.

Unlike the mean-value inequality for Floer solutions
(`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt`), there is no
constant term `C r²`: the equation and the energy are invariant under rescaling the domain. -/
theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_mul_setIntegral
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x))
    {X : Type*} [MetricSpace X] {e : M → X} (he : Continuous e) (he_inj : Injective e) :
    ∃ l > 0, ∃ δ > 0, ∃ C ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄,
      IsOpen Ω → 0 ≤ r → closedBall z₀ r ⊆ Ω → ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
      (∀ y ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J₀.almostComplexStructureAt (u y))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y).toLinearMap) →
      (∀ y ∈ closedBall z₀ r, dist (e (u y)) (e (u z₀)) < l) →
      IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) (ball z₀ r) →
      ∫ y in ball z₀ r, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y < δ →
      r ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z₀ ≤
        C * ∫ y in ball z₀ r, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y := by
  -- The mean-value inequality for the constant family over the one-point parameter space `Unit`,
  -- on the domain window `closedBall 0 1`.
  have hπ (α : M) : MapsTo (fun q : (Unit × (ℝ × ℝ)) × E ↦ (q.1.2, q.2))
      (univ ×ˢ (extChartAt I α).target) (univ ×ˢ (extChartAt I α).target) :=
    fun _ hq ↦ ⟨mem_univ _, hq.2⟩
  obtain ⟨l, hl, δ, hδ, C, hC, hmv⟩ := hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt
    (P := Unit) (J := fun _ _ ↦ J₀.almostComplexStructureAt) (Ks := fun _ _ _ ↦ 0)
    (Kt := fun _ _ _ ↦ 0) he he_inj (W := univ) (C := univ) (D := closedBall 0 1) isOpen_univ
    isCompact_univ (isCompact_closedBall _ _) (subset_univ _)
    (fun α ↦ Floer.contDiffOn_almostComplexInChartAt_uncurry_const
      (Floer.contDiffOn_almostComplexInChartAt_const J₀ α) (hπ α))
    (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const
      (contDiffOn_hamiltonianVectorFieldInChartAt_zero ω α) (hπ α))
    (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const
      (contDiffOn_hamiltonianVectorFieldInChartAt_zero ω α) (hπ α))
    (fun _ _ _ _ x ↦ hJ₀ x)
  refine ⟨l, hl, δ, hδ, C, hC, fun u Ω z₀ r hΩ hr hrΩ hu hhol hdist hint hE ↦ ?_⟩
  set ρ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u
  rcases hr.eq_or_lt with rfl | hr
  · simp
  -- For every radius `ρ' ∈ (0, 1]` with `ρ'² + ∫_{B_r(z₀)} ρ < δ`, the mean-value inequality for
  -- the rescaled map `w ↦ u(z₀ + (r / ρ') w)` on the ball of radius `ρ'` gives
  -- `r² ρ(z₀) ≤ C (ρ'² + ∫_{B_r(z₀)} ρ)`.
  have key : ∀ ρ' ∈ Ioc (0 : ℝ) 1, ρ' ^ 2 + ∫ y in ball z₀ r, ρ y < δ →
      r ^ 2 * ρ z₀ ≤ C * (ρ' ^ 2 + ∫ y in ball z₀ r, ρ y) := by
    intro ρ' hρ' hsmall
    -- Write `r = ε ρ'`, with `ε = r / ρ'`.
    obtain ⟨ε, hε, rfl⟩ : ∃ ε, 0 < ε ∧ ε * ρ' = r :=
      ⟨r / ρ', div_pos hr hρ'.1, div_mul_cancel₀ r hρ'.1.ne'⟩
    obtain ⟨hintv, hEv⟩ := hω.integrableOn_and_setIntegral_rescale_le hJ₀ hΩ
      (hu.of_le (by norm_num)) hε (ball_subset_closedBall.trans hrΩ) hhol hint
    have hmv' := hmv (p := ()) (u := fun w ↦ u (z₀ + ε • w))
      (Ω := (fun w ↦ z₀ + ε • w) ⁻¹' Ω) (z₀ := 0) (r := ρ') (mem_univ _)
      (hΩ.preimage (continuous_const.add (continuous_const_smul _))) hρ'.1.le
      (fun w hw ↦ hrΩ (add_smul_mem_closedBall hε.le hw))
      (closedBall_subset_closedBall hρ'.2) (hu.comp_add_smul z₀ ε)
      (fun w hw ↦ (ω.isComplexLinearMap_perturbedMFDeriv_zero_rescale_iff hε.ne').2
        (hhol _ (add_smul_mem_ball hε hw)))
      (fun w hw ↦ by simpa using hdist _ (add_smul_mem_closedBall hε.le hw))
      hintv (by linarith)
    rw [floerEnergyDensity_zero_rescale, smul_zero, add_zero] at hmv'
    calc (ε * ρ') ^ 2 * ρ z₀ = ρ' ^ 2 * (ε ^ 2 * ρ z₀) := by ring
      _ ≤ _ := hmv'
      _ ≤ C * (ρ' ^ 2 + ∫ y in ball z₀ (ε * ρ'), ρ y) := by gcongr
  -- Letting `ρ' → 0` removes the term `C ρ'²`.
  exact le_mul_of_forall_le_mul_sq_add hE key

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- The energy over a subset of the unit ball is at most the energy over the ball. -/
private theorem IsNondegenerate.setIntegral_le_setIntegral_ball (hω : ω.IsNondegenerate)
    (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x))
    {u : ℝ × ℝ → M} (hhol : ∀ y ∈ ball (0 : ℝ × ℝ) 1, IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (u y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) (ball 0 1))
    {s : Set (ℝ × ℝ)} (hs : s ⊆ ball 0 1) :
    ∫ y in s, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y ≤
      ∫ y in ball 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y :=
  setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_ball).2
    (Eventually.of_forall fun y hy ↦ floerEnergyDensity_nonneg hω (hJ₀ _) (hhol y hy)))
    (Eventually.of_forall hs)

/-- The case of `IsNondegenerate.tendsto_floerEnergyDensity_of_tendsto_setIntegral` where the
energy densities are uniformly bounded on `closedBall 0 (1 / 2)`. The maps are then uniformly
Lipschitz there through `e`, so on the closed ball of a small fixed radius `r` their images are
within the constant `l` of the mean-value inequality, and that inequality bounds `r² ρₖ(0)` by a
constant times the energy. -/
private theorem IsNondegenerate.tendsto_floerEnergyDensity_of_tendsto_setIntegral_of_le
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) (ball 0 1))
    (hhol : ∀ k, ∀ y ∈ ball (0 : ℝ × ℝ) 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u k y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) y).toLinearMap)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k)) (ball 0 1))
    (hE : Tendsto (fun k ↦ ∫ y in ball (0 : ℝ × ℝ) 1,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) y) atTop (𝓝 0))
    {A : ℝ} (hA : ∀ k, ∀ y ∈ closedBall (0 : ℝ × ℝ) (1 / 2),
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) y ≤ A) :
    Tendsto (fun k ↦ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) 0) atTop (𝓝 0) := by
  set ρ : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k)
  have hmono (k : ℕ) {s : Set (ℝ × ℝ)} (hs : s ⊆ ball 0 1) :=
    hω.setIntegral_le_setIntegral_ball J₀ hJ₀ (hhol k) (hint k) hs
  obtain ⟨l, hl, δ, hδ, C, hC, hmv⟩ :=
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_mul_setIntegral J₀ hJ₀
      (continuous_iff_continuousAt.2 fun x ↦ (he x).continuousAt) he_inj
  -- The Lipschitz constant `2 (√(A / c) + B)` of `lipschitzOnWith_comp_of_floerEnergyDensity_le`,
  -- with `B = 0` since the pushforwards of the Hamiltonian vector fields vanish.
  set L := 2 * (√(A / c) + 0)
  have hL : 0 ≤ L := by positivity
  have hlip (k : ℕ) : LipschitzOnWith L.toNNReal (e ∘ u k) (closedBall 0 (1 / 2)) := by
    have hsub : closedBall (0 : ℝ × ℝ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    exact hω.lipschitzOnWith_comp_of_floerEnergyDensity_le (convex_closedBall _ _)
      (fun z ↦ J₀.almostComplexStructureAt (u k z)) hc (fun _ _ ↦ he _)
      (fun z hz ↦ ((hu k).mdifferentiableOn (by norm_num)).mdifferentiableAt
        (isOpen_ball.mem_nhds (hsub hz))) (fun _ _ ↦ hJc _)
      (fun _ _ ↦ norm_mvfderiv_hamiltonianVectorField_zero_le_zero ω e _)
      (fun _ _ ↦ norm_mvfderiv_hamiltonianVectorField_zero_le_zero ω e _)
      (fun z hz ↦ hhol k z (hsub hz)) (fun z hz ↦ hA k z hz)
  set r := min (1 / 2) (l / (2 * (L + 1)))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr1 : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hdist (k : ℕ) : ∀ y ∈ closedBall (0 : ℝ × ℝ) r, dist (e (u k y)) (e (u k 0)) < l := by
    intro y hy
    calc dist (e (u k y)) (e (u k 0))
        ≤ L.toNNReal * dist y 0 :=
          (hlip k).dist_le_mul y (closedBall_subset_closedBall (min_le_left _ _) hy) 0 (by simp)
      _ ≤ L * (l / (2 * (L + 1))) := by
          rw [Real.coe_toNNReal _ hL]
          exact mul_le_mul_of_nonneg_left ((mem_closedBall.1 hy).trans (min_le_right _ _)) hL
      _ < l := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hbound : ∀ᶠ k in atTop, ρ k 0 ≤ C / r ^ 2 * ∫ y in ball 0 1, ρ k y := by
    filter_upwards [hE.eventually (gt_mem_nhds hδ)] with k hk
    have hsub : ball (0 : ℝ × ℝ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
    have h := hmv isOpen_ball hr.le (closedBall_subset_ball hr1) (hu k)
      (fun y hy ↦ hhol k y (hsub hy)) (hdist k) ((hint k).mono_set hsub)
      ((hmono k hsub).trans_lt hk)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
    exact h.trans (mul_le_mul_of_nonneg_left (hmono k hsub) hC)
  refine squeeze_zero' (Eventually.of_forall fun k ↦ floerEnergyDensity_nonneg hω (hJ₀ _)
    (hhol k 0 (mem_ball_self one_pos))) hbound ?_
  simpa only [mul_zero] using hE.const_mul (C / r ^ 2)

/-- The sequential form of
`IsNondegenerate.exists_pos_forall_floerEnergyDensity_lt_of_setIntegral_lt`: if `J₀`-holomorphic
maps `uₖ` on the unit ball have energies tending to `0`, their energy densities at the centre tend
to `0`. -/
private theorem IsNondegenerate.tendsto_floerEnergyDensity_of_tendsto_setIntegral
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) (ball 0 1))
    (hhol : ∀ k, ∀ y ∈ ball (0 : ℝ × ℝ) 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u k y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) y).toLinearMap)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k)) (ball 0 1))
    (hE : Tendsto (fun k ↦ ∫ y in ball (0 : ℝ × ℝ) 1,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) y) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) 0) atTop (𝓝 0) := by
  -- The compactness theorem on the closed unit ball.
  obtain ⟨δ₀, hδ₀, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) (J := fun _ ↦ J₀.almostComplexStructureAt) he he_inj
    isOpen_univ (isCompact_closedBall (0 : ℝ × ℝ) 1) (subset_univ _)
    (fun α ↦ Floer.contDiffOn_almostComplexInChartAt_const J₀ α)
    (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_zero ω α)
    (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_zero ω α) (fun _ _ x ↦ hJ₀ x) hc
    (fun _ _ ↦ hJc)
    (fun _ _ ↦ norm_mvfderiv_hamiltonianVectorField_zero_le_zero ω e)
    (fun _ _ ↦ norm_mvfderiv_hamiltonianVectorField_zero_le_zero ω e)
  obtain ⟨E₀, hE₀⟩ := hE.bddAbove_range
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨φ, hφ, Z, -, -, hZ, hbd, -⟩ := hconv isOpen_ball ball_subset_closedBall
    (fun k ↦ hu (ns k)) (fun k ↦ hhol (ns k)) (fun k ↦ hint (ns k))
    (fun k ↦ hE₀ ⟨ns k, rfl⟩)
  have hEφ : Tendsto (fun n ↦ ∫ y in ball (0 : ℝ × ℝ) 1,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u (ns (φ n))) y) atTop (𝓝 0) :=
    hE.comp (hns.comp hφ.tendsto_atTop)
  -- Energy at least `δ₀` concentrates at every bubbling point, while the energies tend to `0`.
  have hZe : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨n, hn₁, hn₂⟩ := ((hZ z hz 1 one_pos).and (hEφ.eventually (gt_mem_nhds hδ₀))).exists
    linarith [hω.setIntegral_le_setIntegral_ball J₀ hJ₀ (hhol (ns (φ n))) (hint (ns (φ n)))
      (inter_subset_right (s := ball z 1))]
  -- So the energy densities are bounded on `closedBall 0 (1 / 2)`.
  obtain ⟨A, hA⟩ := hbd (closedBall 0 (1 / 2)) (isCompact_closedBall _ _) (by
    rw [hZe, Finset.coe_empty, sdiff_empty]
    exact closedBall_subset_ball (by norm_num))
  exact ⟨φ, hω.tendsto_floerEnergyDensity_of_tendsto_setIntegral_of_le J₀ hJ₀ he he_inj hc hJc
    (fun k ↦ hu (ns (φ k))) (fun k ↦ hhol (ns (φ k))) (fun k ↦ hint (ns (φ k))) hEφ hA⟩

/-- **Small energy, small energy density.** Let `ω` be a nondegenerate two-form on a compact
boundaryless manifold `M` taming a smooth almost complex structure `J₀`, and let `e : M → F` be an
injective differentiable map into a normed space, such as the Whitney embedding, with `J₀`
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J₀ v)` with `c > 0`. For every `η > 0`
there is `δ > 0` with the following property. Let `u` be `C³` on the unit ball `B_1(0)` of
`ℝ × ℝ`, `J₀`-holomorphic there, with integrable energy density `ρ`. If the energy `∫_{B_1(0)} ρ`
is less than `δ`, then `ρ(0) < η`. No condition is put on where the map takes its values. -/
theorem IsNondegenerate.exists_pos_forall_floerEnergyDensity_lt_of_setIntegral_lt
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ⦃u : ℝ × ℝ → M⦄, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball 0 1) →
      (∀ y ∈ ball (0 : ℝ × ℝ) 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J₀.almostComplexStructureAt (u y))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y).toLinearMap) →
      IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) (ball 0 1) →
      ∫ y in ball (0 : ℝ × ℝ) 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y < δ →
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u 0 < η := by
  -- Otherwise there are maps `uₖ` of energy less than `1 / (k + 1)` with `ρₖ(0) ≥ η`.
  by_contra! h
  choose u hu hhol hint hE hρ using fun k : ℕ ↦ h (1 / (k + 1)) Nat.one_div_pos_of_nat
  have hlim := hω.tendsto_floerEnergyDensity_of_tendsto_setIntegral J₀ hJ₀ he he_inj hc hJc hu
    hhol hint (squeeze_zero (fun k ↦ setIntegral_nonneg measurableSet_ball fun y hy ↦
      floerEnergyDensity_nonneg hω (hJ₀ _) (hhol k y hy)) (fun k ↦ (hE k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact (hρ k).not_gt hk

/-- **Small energy, small energy density, at every scale.** Under the hypotheses of
`IsNondegenerate.exists_pos_forall_floerEnergyDensity_lt_of_setIntegral_lt`, let `u` be `C³` on an
open set `U ⊆ ℝ × ℝ` and `J₀`-holomorphic there, with energy density `ρ`. Let `B_{s a}(p a)` be
discs, indexed by `a` along a filter `l`, that eventually have positive radius, lie in `U` and
carry integrable `ρ`. If the energies `∫_{B_{s a}(p a)} ρ` tend to `0` along `l`, then so do the
scaled energy densities `(s a)² ρ(p a)` at the centres. This is the previous statement for the
rescaled maps `w ↦ u(p a + s a • w)`. -/
theorem IsNondegenerate.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U)
    (hhol : ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y).toLinearMap)
    {α : Type*} {l : Filter α} {p : α → ℝ × ℝ} {s : α → ℝ} (hs : ∀ᶠ a in l, 0 < s a)
    (hpsU : ∀ᶠ a in l, ball (p a) (s a) ⊆ U)
    (hint : ∀ᶠ a in l, IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u)
      (ball (p a) (s a)))
    (hE : Tendsto (fun a ↦ ∫ y in ball (p a) (s a),
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y) l (𝓝 0)) :
    Tendsto (fun a ↦ s a ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u (p a)) l
      (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hsmall⟩ :=
    hω.exists_pos_forall_floerEnergyDensity_lt_of_setIntegral_lt J₀ hJ₀ he he_inj hc hJc hη
  filter_upwards [hs, hpsU, hint, hE.eventually (gt_mem_nhds hδ)] with a hsa hsub hinta hEa
  have hball : ball (p a) (s a * 1) = ball (p a) (s a) := by rw [mul_one]
  -- The rescaled map `w ↦ u(p a + s a • w)` on the unit ball.
  have hmem {w : ℝ × ℝ} (hw : w ∈ ball (0 : ℝ × ℝ) 1) : p a + s a • w ∈ U :=
    hsub (hball ▸ add_smul_mem_ball hsa hw)
  obtain ⟨hintv, hEv⟩ := hω.integrableOn_and_setIntegral_rescale_le hJ₀ hU
    (hu.of_le (by norm_num)) hsa (hball.symm ▸ hsub) (fun y hy ↦ hhol y (hsub (hball ▸ hy)))
    (hball.symm ▸ hinta)
  have h := hsmall ((hu.comp_add_smul (p a) (s a)).mono fun w hw ↦ hmem hw)
    (fun w hw ↦ (ω.isComplexLinearMap_perturbedMFDeriv_zero_rescale_iff hsa.ne').2
      (hhol _ (hmem hw))) hintv (hEv.trans_lt (hball ▸ hEa))
  rw [floerEnergyDensity_zero_rescale, smul_zero, add_zero] at h
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (floerEnergyDensity_nonneg hω (hJ₀ _) (hhol _ (hsub (mem_ball_self hsa)))))]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- From the decay of `t² ρ` to the decay of `t ‖d (e ∘ u)‖`, for a nonnegative weight `t`. -/
private theorem IsNondegenerate.tendsto_mul_norm_fderiv_comp_of_tendsto
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {l : Filter (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ∀ z, 0 ≤ t z)
    (hu : ∀ᶠ z in l, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hhol : ∀ᶠ z in l, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (h : Tendsto (fun z ↦ t z ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z) l
      (𝓝 0)) :
    Tendsto (fun z ↦ t z * ‖fderiv ℝ (e ∘ u) z‖) l (𝓝 0) := by
  have hlim : Tendsto (fun z ↦
      2 * √(t z ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c)) l (𝓝 0) := by
    simpa only [zero_div, Real.sqrt_zero, mul_zero] using (h.div_const c).sqrt.const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun z ↦ mul_nonneg (ht z) (norm_nonneg _)) ?_ hlim
  filter_upwards [hu, hhol] with z hz hzhol
  have hd : ‖fderiv ℝ (e ∘ u) z‖ ≤
      2 * √(ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c) := by
    simpa only [add_zero] using hω.norm_fderiv_comp_le hc (he _) hz (hJc _)
      (norm_mvfderiv_hamiltonianVectorField_zero_le_zero ω e _)
      (norm_mvfderiv_hamiltonianVectorField_zero_le_zero ω e _) hzhol
  calc t z * ‖fderiv ℝ (e ∘ u) z‖
      ≤ t z * (2 * √(ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c)) :=
        mul_le_mul_of_nonneg_left hd (ht z)
    _ = 2 * √(t z ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c) := by
        rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ht z)]
        ring

/-- The common step of the two decay theorems: if `ρ` is integrable on `U` and the disc of radius
`t z / 2` about `z` eventually lies in `U` and in a set `S z` whose energy `∫_{S z} |ρ|` over `U`
tends to `0`, then `(t z)² ρ(z) → 0`. -/
private theorem IsNondegenerate.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral_norm
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U)
    (hhol : ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) U)
    {l : Filter (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} {S : ℝ × ℝ → Set (ℝ × ℝ)} (ht : ∀ᶠ z in l, 0 < t z)
    (hsubU : ∀ᶠ z in l, ball z (t z / 2) ⊆ U) (hsubS : ∀ᶠ z in l, ball z (t z / 2) ⊆ S z)
    (hE : Tendsto (fun z ↦ ∫ y in S z,
      ‖ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y‖ ∂volume.restrict U) l (𝓝 0)) :
    Tendsto (fun z ↦ t z ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z) l
      (𝓝 0) := by
  set ρ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u
  have h := hω.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral J₀ hJ₀ he he_inj hc hJc
    hU hu hhol (p := fun z ↦ z) (s := fun z ↦ t z / 2) (ht.mono fun _ ↦ half_pos) hsubU
    (hsubU.mono fun _ hz ↦ hint.mono_set hz) ?_
  · -- `(t z)² ρ(z) = 4 (t z / 2)² ρ(z)`.
    have h4 := h.const_mul 4
    rw [mul_zero] at h4
    exact h4.congr fun z ↦ by ring
  refine squeeze_zero' (hsubU.mono fun z hz ↦ setIntegral_nonneg measurableSet_ball fun y hy ↦
    floerEnergyDensity_nonneg hω (hJ₀ _) (hhol y (hz hy))) ?_ hE
  filter_upwards [hsubU, hsubS] with z hzU hzS
  calc ∫ y in ball z (t z / 2), ρ y
      ≤ ∫ y in ball z (t z / 2), ‖ρ y‖ :=
        (le_abs_self _).trans (abs_integral_le_integral_abs (f := ρ))
    _ = ∫ y in ball z (t z / 2), ‖ρ y‖ ∂volume.restrict U := by
        rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 hzU]
    _ ≤ ∫ y in S z, ‖ρ y‖ ∂volume.restrict U :=
        setIntegral_mono_set hint.norm.integrableOn
          (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall hzS)

/-- **Decay of the energy density at a finite-energy puncture.** Let `ω` be a nondegenerate
two-form on a compact boundaryless manifold `M` taming a smooth almost complex structure `J₀`,
uniformly tame with respect to an injective differentiable map `e : M → F` with constant `c > 0`.
Let `u` be `C³` and `J₀`-holomorphic on a punctured disc `B_R(z₀) \ {z₀}`, with integrable energy
density `ρ = ω(∂ₛu, ∂ₜu)` on `B_R(z₀)`. Then `|z - z₀|² ρ(z) → 0` as `z → z₀`. -/
theorem IsNondegenerate.tendsto_norm_sub_sq_mul_floerEnergyDensity_nhdsNE
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {z₀ : ℝ × ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ R \ {z₀}))
    (hhol : ∀ z ∈ ball z₀ R \ {z₀}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) (ball z₀ R)) :
    Tendsto (fun z ↦ ‖z - z₀‖ ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z)
      (𝓝[≠] z₀) (𝓝 0) := by
  set U := ball z₀ R \ {z₀}
  have hev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ (R / 2) \ {z₀} :=
    sdiff_mem_nhdsWithin_compl (ball_mem_nhds z₀ (half_pos hR)) _
  -- The energy of the disc of radius `t` about `z₀` tends to `0` with `t`. Lebesgue measure on
  -- `ℝ × ℝ` is an additive Haar measure, so it vanishes on points, and removing the puncture
  -- does not change the restricted measure.
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hUR : volume.restrict U = volume.restrict (ball z₀ R) :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton z₀))
  have hε := MeasureTheory.IntegrableOn.tendsto_setIntegral_ball_nhds_zero hint.norm z₀
  have htend : Tendsto (fun z ↦ 2 * ‖z - z₀‖) (𝓝[≠] z₀) (𝓝 0) := by
    have h0 : Continuous fun z : ℝ × ℝ ↦ 2 * ‖z - z₀‖ := by fun_prop
    simpa using (h0.tendsto z₀).mono_left nhdsWithin_le_nhds
  -- The disc of radius `|z - z₀| / 2` about `z` lies in `U` and in the disc of radius
  -- `2 |z - z₀|` about `z₀`.
  refine hω.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral_norm J₀ hJ₀ he he_inj hc hJc
    (isOpen_ball.sdiff isClosed_singleton) hu hhol (hint.mono_set sdiff_subset)
    (hev.mono fun z hz ↦ norm_pos_iff.2 (sub_ne_zero.2 hz.2))
    (hev.mono fun z hz ↦ (ball_half_norm_sub_subset hz).trans inter_subset_left)
    (hev.mono fun z hz ↦ (ball_half_norm_sub_subset hz).trans inter_subset_right) ?_
  rw [hUR]
  exact hε.comp htend

/-- **Decay of the derivative at a finite-energy puncture.** Under the hypotheses of
`IsNondegenerate.tendsto_norm_sub_sq_mul_floerEnergyDensity_nhdsNE`,
`|z - z₀| ‖d (e ∘ u)(z)‖ → 0` as `z → z₀`: the images under `e` of the circles about the puncture
have derivative `o(1)` in the angle. -/
theorem IsNondegenerate.tendsto_norm_sub_mul_norm_fderiv_comp_nhdsNE
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {z₀ : ℝ × ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ R \ {z₀}))
    (hhol : ∀ z ∈ ball z₀ R \ {z₀}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) (ball z₀ R)) :
    Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderiv ℝ (e ∘ u) z‖) (𝓝[≠] z₀) (𝓝 0) := by
  have hU : ball z₀ R \ {z₀} ∈ 𝓝[≠] z₀ :=
    sdiff_mem_nhdsWithin_compl (ball_mem_nhds z₀ hR) _
  have hU' : ∀ᶠ z in 𝓝[≠] z₀, ball z₀ R \ {z₀} ∈ 𝓝 z := by
    filter_upwards [hU] with z hz using (isOpen_ball.sdiff isClosed_singleton).mem_nhds hz
  exact hω.tendsto_mul_norm_fderiv_comp_of_tendsto J₀ he hc hJc (fun _ ↦ norm_nonneg _)
    (by filter_upwards [hU'] with z hz' using
      (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt hz')
    (by filter_upwards [hU] with z hz using hhol z hz)
    (hω.tendsto_norm_sub_sq_mul_floerEnergyDensity_nhdsNE J₀ hJ₀ he he_inj hc hJc hR hu hhol hint)

/-- **Decay of the energy density at infinity.** Let `ω` be a nondegenerate two-form on a compact
boundaryless manifold `M` taming a smooth almost complex structure `J₀`, uniformly tame with
respect to an injective differentiable map `e : M → F` with constant `c > 0`. Let `u` be `C³` and
`J₀`-holomorphic outside the closed disc of radius `T` about `0`, with integrable energy density
`ρ = ω(∂ₛu, ∂ₜu)` there. Then `|z|² ρ(z) → 0` as `z → ∞`. This applies to the end at infinity of a
finite-energy `J₀`-holomorphic plane, such as a bubble. -/
theorem IsNondegenerate.tendsto_norm_sq_mul_floerEnergyDensity_cocompact
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {T : ℝ} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (closedBall 0 T)ᶜ)
    (hhol : ∀ z ∈ (closedBall (0 : ℝ × ℝ) T)ᶜ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u)
      (closedBall 0 T)ᶜ) :
    Tendsto (fun z ↦ ‖z‖ ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z)
      (cocompact (ℝ × ℝ)) (𝓝 0) := by
  have hev : ∀ᶠ z in cocompact (ℝ × ℝ), 2 * max T 0 < ‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually_gt_atTop _
  -- The energy outside the ball of radius `t` about `0` tends to `0` as `t → ∞`.
  have hε := tendsto_setIntegral_compl_ball (μ := volume.restrict (closedBall 0 T)ᶜ) hint.norm
    (0 : ℝ × ℝ)
  have htend : Tendsto (fun z : ℝ × ℝ ↦ ‖z‖ / 2) (cocompact (ℝ × ℝ)) atTop :=
    tendsto_norm_cocompact_atTop.atTop_div_const two_pos
  -- The disc of radius `|z| / 2` about `z` lies outside the closed disc of radius `T` and outside
  -- the disc of radius `|z| / 2` about `0`.
  exact hω.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral_norm J₀ hJ₀ he he_inj hc hJc
    isClosed_closedBall.isOpen_compl hu hhol hint
    (hev.mono fun z hz ↦ (mul_nonneg zero_le_two (le_max_right T 0)).trans_lt hz)
    (hev.mono fun z hz ↦ (ball_half_norm_subset hz).trans inter_subset_right)
    (hev.mono fun z hz ↦ (ball_half_norm_subset hz).trans
      (inter_subset_left.trans (compl_subset_compl.2 ball_subset_closedBall)))
    (hε.comp htend)

/-- **Decay of the derivative at infinity.** Under the hypotheses of
`IsNondegenerate.tendsto_norm_sq_mul_floerEnergyDensity_cocompact`, `|z| ‖d (e ∘ u)(z)‖ → 0` as
`z → ∞`: the images under `e` of the large circles about `0` have derivative `o(1)` in the angle. -/
theorem IsNondegenerate.tendsto_norm_mul_norm_fderiv_comp_cocompact
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {u : ℝ × ℝ → M} {T : ℝ} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (closedBall 0 T)ᶜ)
    (hhol : ∀ z ∈ (closedBall (0 : ℝ × ℝ) T)ᶜ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u)
      (closedBall 0 T)ᶜ) :
    Tendsto (fun z ↦ ‖z‖ * ‖fderiv ℝ (e ∘ u) z‖) (cocompact (ℝ × ℝ)) (𝓝 0) := by
  have hU : (closedBall (0 : ℝ × ℝ) T)ᶜ ∈ cocompact (ℝ × ℝ) :=
    (isCompact_closedBall _ _).compl_mem_cocompact
  have hU' : ∀ᶠ z in cocompact (ℝ × ℝ), (closedBall (0 : ℝ × ℝ) T)ᶜ ∈ 𝓝 z := by
    filter_upwards [hU] with z hz using isClosed_closedBall.isOpen_compl.mem_nhds hz
  exact hω.tendsto_mul_norm_fderiv_comp_of_tendsto J₀ he hc hJc (fun _ ↦ norm_nonneg _)
    (by filter_upwards [hU'] with z hz' using
      (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt hz')
    (by filter_upwards [hU] with z hz using hhol z hz)
    (hω.tendsto_norm_sq_mul_floerEnergyDensity_cocompact J₀ hJ₀ he he_inj hc hJc hu hhol hint)

end Closed

end Holomorphic

end TauCeti.SmoothTwoForm
