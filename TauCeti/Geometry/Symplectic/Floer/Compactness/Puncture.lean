/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Manifold
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Pseudoholomorphic maps into a closed manifold near a finite-energy puncture

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
  (`IsNondegenerate.tendsto_floerEnergyDensity_of_tendsto_setIntegral`).
  If `J₀`-holomorphic maps `uₖ` on the unit disc have energies tending to zero, their energy
  densities at the centre tend to zero. Along a subsequence the maps converge off finitely many
  bubbling points by the compactness theorem in a closed manifold
  (`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset`). Every
  bubbling point carries a fixed amount of energy, so there is none, and the energy densities are
  bounded on the disc of radius `1 / 2`. The maps are then uniformly Lipschitz through `e`
  (`IsNondegenerate.lipschitzOnWith_comp_of_floerEnergyDensity_le`), so a disc of a fixed small
  radius has small image, and the mean-value inequality without constant term bounds the density
  at the centre by a multiple of the energy. Its rescaled form
  (`IsNondegenerate.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral`) says that if the
  energies over discs `B_{sₖ}(cₖ)` tend to zero, then so do the scaled densities `sₖ² ρ(cₖ)`.
* **Decay at a puncture** (`IsNondegenerate.tendsto_norm_sub_sq_mul_floerEnergyDensity_nhdsNE`,
  `IsNondegenerate.tendsto_norm_sub_mul_norm_fderiv_comp_nhdsNE`). For a `J₀`-holomorphic map of
  finite energy on a punctured disc `B_R(z₀) \ {z₀}`, `|z - z₀|² ρ(z) → 0` and
  `|z - z₀| ‖d (e ∘ u)(z)‖ → 0` as `z → z₀`. The disc of radius `|z - z₀| / 2` about `z` lies in
  the punctured disc of radius `2 |z - z₀|`, whose energy tends to zero.
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

Balls of `ℝ × ℝ` are squares for its sup norm, and `|z - z₀|` is the sup norm of `z - z₀`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.3 (the mean-value inequality), Section 4.5 (removal of singularities) and
  Section 4.6 (bubbling off finitely many points).
-/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}

section Rescale

variable {u : ℝ × ℝ → M} {c : ℝ × ℝ} {ε : ℝ}

omit [FiniteDimensional ℝ E] in
/-- The energy density of the rescaled map `w ↦ u(c + ε w)` for the zero perturbation is `ε²`
times that of `u` at `c + ε w`. -/
private theorem floerEnergyDensity_zero_rescale (ω : SmoothTwoForm I M) (w : ℝ × ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun w ↦ u (c + ε • w)) w =
      ε ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u (c + ε • w) := by
  have h := ω.floerEnergyDensity_rescale (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) (u := u)
    (c := c) (ε := ε) (w := w)
  simp only [mul_zero] at h
  exact h

omit [FiniteDimensional ℝ E] in
/-- The rescaled map `w ↦ u(c + ε w)` is `J₀`-holomorphic at `w` when `u` is at `c + ε w`. -/
private theorem isComplexLinearMap_rescale (ω : SmoothTwoForm I M)
    (J₀ : SmoothAlmostComplexStructure I M) (hε : ε ≠ 0) {w : ℝ × ℝ}
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u (c + ε • w)))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u (c + ε • w)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u (c + ε • w)))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun w ↦ u (c + ε • w)) w).toLinearMap := by
  have h' := (ω.isComplexLinearMap_perturbedMFDeriv_rescale_iff (Ks := fun _ _ ↦ 0)
    (Kt := fun _ _ ↦ 0) (u := u) (c := c) (w := w) hε).2 h
  simp only [mul_zero] at h'
  exact h'

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- The rescaled map `w ↦ u(c + ε w)` is `C³` where `u` is. -/
private theorem contMDiffOn_rescale {U : Set (ℝ × ℝ)} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (fun w ↦ u (c + ε • w)) ((fun w ↦ c + ε • w) ⁻¹' U) :=
  hu.comp (contDiff_const.add (contDiff_id.const_smul ε)).contMDiff.contMDiffOn
    (mapsTo_preimage _ _)

/-- The rescaling `w ↦ c + ε w` maps the ball of radius `r` about `0` into the ball of radius
`ε r` about `c`. -/
private theorem add_smul_mem_ball (hε : 0 < ε) {r : ℝ} {w : ℝ × ℝ} (hw : w ∈ ball 0 r) :
    c + ε • w ∈ ball c (ε * r) := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
  exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hε

/-- The rescaling `w ↦ c + ε w` maps the closed ball of radius `r` about `0` into the closed ball
of radius `ε r` about `c`. -/
private theorem add_smul_mem_closedBall (hε : 0 ≤ ε) {r : ℝ} {w : ℝ × ℝ}
    (hw : w ∈ closedBall 0 r) : c + ε • w ∈ closedBall c (ε * r) := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hw) hε

variable [I.Boundaryless]

omit [FiniteDimensional ℝ E] in
/-- **The energy of a rescaled map.** Let `u` be `C³` on an open set `U` containing the ball
`B_{ε r}(c)`, `J₀`-holomorphic on that ball, with integrable energy density there. Then the rescaled
map `w ↦ u(c + ε w)` has integrable energy density on the ball `B_r(0)`, and its energy there is at
most the energy of `u` over `B_{ε r}(c)`. -/
private theorem IsNondegenerate.integrableOn_and_setIntegral_rescale_le (hω : ω.IsNondegenerate)
    (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U) (hε : 0 < ε)
    {r : ℝ} (hcU : ball c (ε * r) ⊆ U)
    (hhol : ∀ y ∈ ball c (ε * r), IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (u y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y).toLinearMap)
    (hint : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u) (ball c (ε * r))) :
    IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun w ↦ u (c + ε • w)))
        (ball 0 r) ∧
      ∫ w in ball 0 r, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0)
          (fun w ↦ u (c + ε • w)) w ≤
        ∫ y in ball c (ε * r), ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y := by
  set ρ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u
  have hρ0 : ∀ y ∈ ball c (ε * r), 0 ≤ ρ y := fun y hy ↦
    floerEnergyDensity_nonneg hω (hJ₀ _) (hhol y hy)
  have hmaps : MapsTo (fun w : ℝ × ℝ ↦ c + ε • w) (ball 0 r) (ball c (ε * r)) :=
    fun _ hw ↦ add_smul_mem_ball hε hw
  -- The energy density of the rescaled map is continuous on the open preimage of `U`.
  have hX (α : M) : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α
      (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))) (((fun w ↦ c + ε • w) ⁻¹' U) ×ˢ
        (extChartAt I α).target) := by
    rw [hamiltonianVectorFieldInChartAt_zero]
    exact continuousOn_const
  have hcont := ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt
    (hU.preimage (continuous_const.add (continuous_const_smul ε)))
    ((contMDiffOn_rescale hu).of_le (by norm_num)) hX hX
  have hmeas := (hcont.mono fun w hw ↦ hcU (hmaps hw)).aestronglyMeasurable (μ := volume)
    (measurableSet_ball (x := (0 : ℝ × ℝ)) (ε := r))
  have hnn : 0 ≤ᵐ[volume.restrict (ball (0 : ℝ × ℝ) r)]
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun w ↦ u (c + ε • w)) :=
    (ae_restrict_iff' measurableSet_ball).2 <| Eventually.of_forall fun w hw ↦ by
      rw [floerEnergyDensity_zero_rescale]
      exact mul_nonneg (sq_nonneg ε) (hρ0 _ (hmaps hw))
  -- The energy of the rescaled map over `B_r(0)` is that of `u` over the image of the ball.
  have hl := ω.lintegral_floerEnergyDensity_rescale (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    (u := u) (c := c) hε.ne' (measurableSet_ball (x := (0 : ℝ × ℝ)) (ε := r))
  simp only [mul_zero] at hl
  have hE : ∫⁻ w in ball 0 r, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun _ _ ↦ 0) (fun w ↦ u (c + ε • w)) w) ≤
        ENNReal.ofReal (∫ y in ball c (ε * r), ρ y) := by
    rw [hl, ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall hρ0))]
    exact lintegral_mono_set (image_subset_iff.2 hmaps)
  exact MeasureTheory.integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le hmeas hnn
    subset_rfl (setIntegral_nonneg measurableSet_ball hρ0) hE

end Rescale

section Data

/-- A smooth almost complex structure, as a family constant over the domain `ℝ × ℝ`, is `C²` in
every chart. -/
private theorem contDiffOn_almostComplexInChartAt_const (J₀ : SmoothAlmostComplexStructure I M)
    (α : M) : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α
      (fun (_ : ℝ × ℝ) ↦ J₀.almostComplexStructureAt)) (univ ×ˢ (extChartAt I α).target) := by
  refine (((J₀.contDiffOn_inChart α).of_le (by simp)).comp
    (contDiff_snd.contDiffOn (s := univ ×ˢ (extChartAt I α).target))
    fun p hp ↦ hp.2).congr fun p _ ↦ ?_
  simp

omit [FiniteDimensional ℝ E] in
/-- The Hamiltonian vector field of the zero perturbation is `C²` in every chart. -/
private theorem contDiffOn_hamiltonianVectorFieldInChartAt_zero (ω : SmoothTwoForm I M) (α : M) :
    ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)))
      (univ ×ˢ (extChartAt I α).target) := by
  rw [hamiltonianVectorFieldInChartAt_zero]
  exact contDiffOn_const

omit [FiniteDimensional ℝ E] in
/-- The pushforward of the Hamiltonian vector field of the zero Hamiltonian vanishes. -/
private theorem norm_mvfderiv_hamiltonianVectorField_zero_le_zero [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ω : SmoothTwoForm I M) (e : M → F) (x : M) :
    ‖mvfderiv I e x (ω.hamiltonianVectorField (fun _ ↦ (0 : ℝ)) x)‖ ≤ 0 := by
  rw [hamiltonianVectorField_const, Pi.zero_apply, map_zero, norm_zero]

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
  have hX (α : M) := contDiffOn_hamiltonianVectorFieldInChartAt_zero ω α
  obtain ⟨l, hl, δ, hδ, C, hC, hmv⟩ := hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt
    (P := Unit) (J := fun _ _ ↦ J₀.almostComplexStructureAt) (Ks := fun _ _ _ ↦ 0)
    (Kt := fun _ _ _ ↦ 0) he he_inj (W := univ) (C := univ) (D := closedBall 0 1) isOpen_univ
    isCompact_univ (isCompact_closedBall _ _) (subset_univ _)
    (fun α ↦ Floer.contDiffOn_almostComplexInChartAt_uncurry_const
      (contDiffOn_almostComplexInChartAt_const J₀ α) (hπ α))
    (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (hX α) (hπ α))
    (fun α ↦ contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (hX α) (hπ α))
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
    obtain ⟨hintv, hEv⟩ := hω.integrableOn_and_setIntegral_rescale_le J₀ hJ₀ hΩ hu hε
      (ball_subset_closedBall.trans hrΩ) hhol hint
    have hmv' := hmv (p := ()) (u := fun w ↦ u (z₀ + ε • w))
      (Ω := (fun w ↦ z₀ + ε • w) ⁻¹' Ω) (z₀ := 0) (r := ρ') (mem_univ _)
      (hΩ.preimage (continuous_const.add (continuous_const_smul _))) hρ'.1.le
      (fun w hw ↦ hrΩ (add_smul_mem_closedBall hε.le hw))
      (closedBall_subset_closedBall hρ'.2) (contMDiffOn_rescale hu)
      (fun w hw ↦ isComplexLinearMap_rescale ω J₀ hε.ne' (hhol _ (add_smul_mem_ball hε hw)))
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

/-- **Small energy, small energy density.** Let `ω` be a nondegenerate two-form on a compact
boundaryless manifold `M` taming a smooth almost complex structure `J₀`, and let `e : M → F` be an
injective differentiable map into a normed space, such as the Whitney embedding, with `J₀`
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J₀ v)` with `c > 0`. Let `uₖ` be `C³` maps
on the unit ball `B_1(0)` of `ℝ × ℝ`, `J₀`-holomorphic there, with integrable energy densities
`ρₖ`. If the energies `∫_{B_1(0)} ρₖ` tend to `0`, then so do the energy densities `ρₖ(0)` at the
centre. No condition is put on where the maps take their values. -/
theorem IsNondegenerate.tendsto_floerEnergyDensity_of_tendsto_setIntegral
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
    (contDiffOn_almostComplexInChartAt_const J₀) (contDiffOn_hamiltonianVectorFieldInChartAt_zero ω)
    (contDiffOn_hamiltonianVectorFieldInChartAt_zero ω) (fun _ _ x ↦ hJ₀ x) hc (fun _ _ ↦ hJc)
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

/-- **Small energy, small energy density, at every scale.** Under the hypotheses of
`IsNondegenerate.tendsto_floerEnergyDensity_of_tendsto_setIntegral`, let `u` be `C³` on an open set
`U ⊆ ℝ × ℝ` and `J₀`-holomorphic there, and let `B_{sₖ}(pₖ) ⊆ U` be discs over which the energy
density `ρ` of `u` is integrable. If the energies `∫_{B_{sₖ}(pₖ)} ρ` tend to `0`, then so do the
scaled energy densities `sₖ² ρ(pₖ)` at the centres. This is the previous statement for the
rescaled maps `w ↦ u(pₖ + sₖ w)`. -/
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
    {p : ℕ → ℝ × ℝ} {s : ℕ → ℝ} (hs : ∀ k, 0 < s k) (hpsU : ∀ k, ball (p k) (s k) ⊆ U)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u)
      (ball (p k) (s k)))
    (hE : Tendsto (fun k ↦ ∫ y in ball (p k) (s k),
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u y) atTop (𝓝 0)) :
    Tendsto (fun k ↦ s k ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u (p k)) atTop
      (𝓝 0) := by
  have hball (k : ℕ) : ball (p k) (s k * 1) = ball (p k) (s k) := by rw [mul_one]
  have hres (k : ℕ) := hω.integrableOn_and_setIntegral_rescale_le J₀ hJ₀ hU hu (hs k)
    ((hball k).symm ▸ hpsU k) (fun y hy ↦ hhol y (hpsU k ((hball k) ▸ hy)))
    ((hball k).symm ▸ hint k)
  -- The rescaled maps `w ↦ u(pₖ + sₖ w)` on the unit ball.
  have hmem (k : ℕ) {w : ℝ × ℝ} (hw : w ∈ ball (0 : ℝ × ℝ) 1) : p k + s k • w ∈ U :=
    hpsU k ((hball k) ▸ add_smul_mem_ball (hs k) hw)
  have h := hω.tendsto_floerEnergyDensity_of_tendsto_setIntegral J₀ hJ₀ he he_inj hc hJc
    (u := fun k w ↦ u (p k + s k • w)) (fun k ↦ (contMDiffOn_rescale hu).mono fun w hw ↦ hmem k hw)
    (fun k w hw ↦ isComplexLinearMap_rescale ω J₀ (hs k).ne' (hhol _ (hmem k hw)))
    (fun k ↦ (hres k).1) ?_
  · simpa only [floerEnergyDensity_zero_rescale, smul_zero, add_zero] using h
  -- The energies of the rescaled maps are at most those of `u` over the discs.
  refine squeeze_zero (fun k ↦ setIntegral_nonneg measurableSet_ball fun w hw ↦ ?_)
    (fun k ↦ (hres k).2.trans_eq (by rw [hball])) hE
  rw [floerEnergyDensity_zero_rescale]
  exact mul_nonneg (sq_nonneg _) (floerEnergyDensity_nonneg hω (hJ₀ _) (hhol _ (hmem k hw)))

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
  have hB (x : M) : ‖mvfderiv I e x (ω.hamiltonianVectorField (fun _ ↦ (0 : ℝ)) x)‖ ≤ 0 := by
    rw [hamiltonianVectorField_const, Pi.zero_apply, map_zero]
    exact (norm_zero (E := F)).le
  filter_upwards [hu, hhol] with z hz hzhol
  have hd : ‖fderiv ℝ (e ∘ u) z‖ ≤
      2 * √(ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c) := by
    simpa only [add_zero] using hω.norm_fderiv_comp_le hc (he _) hz (hJc _) (hB _) (hB _) hzhol
  calc t z * ‖fderiv ℝ (e ∘ u) z‖
      ≤ t z * (2 * √(ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c)) :=
        mul_le_mul_of_nonneg_left hd (ht z)
    _ = 2 * √(t z ^ 2 * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z / c) := by
        rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ht z)]
        ring

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [CompactSpace M] in
/-- The disc of radius `|z - z₀| / 2` about a point `z` of `B_{R / 2}(z₀) \ {z₀}` lies in the
punctured disc `B_R(z₀) \ {z₀}` and in the disc of radius `2 |z - z₀|` about `z₀`. -/
private theorem ball_half_norm_sub_subset {z z₀ : ℝ × ℝ} {R : ℝ}
    (hz : z ∈ ball z₀ (R / 2) \ {z₀}) :
    ball z (‖z - z₀‖ / 2) ⊆ (ball z₀ R \ {z₀}) ∩ ball z₀ (2 * ‖z - z₀‖) := by
  intro y hy
  rw [mem_ball, dist_eq_norm] at hy
  have hz' : ‖z - z₀‖ < R / 2 := by simpa [dist_eq_norm] using hz.1
  have h₁ : ‖y - z₀‖ ≤ ‖y - z‖ + ‖z - z₀‖ := by simpa using norm_add_le (y - z) (z - z₀)
  have h₂ : ‖z - z₀‖ ≤ ‖z - y‖ + ‖y - z₀‖ := by simpa using norm_add_le (z - y) (y - z₀)
  rw [norm_sub_rev z y] at h₂
  have hpos : 0 < ‖z - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.2)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    linarith
  · rintro rfl
    simp at h₂
    linarith
  · rw [mem_ball, dist_eq_norm]
    linarith

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [CompactSpace M] in
/-- The disc of radius `|z| / 2` about a point `z` with `|z| > 2 max T 0` lies outside the closed
discs of radii `|z| / 2` and `T` about `0`. -/
private theorem ball_half_norm_subset {z : ℝ × ℝ} {T : ℝ} (hz : 2 * max T 0 < ‖z‖) :
    ball z (‖z‖ / 2) ⊆ (closedBall 0 (‖z‖ / 2))ᶜ ∩ (closedBall 0 T)ᶜ := by
  intro y hy
  rw [mem_ball, dist_eq_norm] at hy
  have h₁ : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by simpa using norm_add_le (z - y) y
  rw [norm_sub_rev] at h₁
  have hT := le_max_left T 0
  refine ⟨?_, ?_⟩ <;> simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] <;>
    linarith

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [CompactSpace M] in
/-- For a function integrable outside the closed disc of radius `T` about `0`, its integrals
outside the closed discs of radius `t` tend to `0` as `t → ∞`. -/
private theorem tendsto_setIntegral_compl_closedBall {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hf : IntegrableOn f (closedBall 0 T)ᶜ) :
    Tendsto (fun t ↦ ∫ y in (closedBall (0 : ℝ × ℝ) t)ᶜ, f y) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := f)
    (s := fun t : ℝ ↦ (closedBall (0 : ℝ × ℝ) t)ᶜ) (fun _ ↦ measurableSet_closedBall.compl)
    (fun _ _ hts ↦ compl_subset_compl.2 (closedBall_subset_closedBall hts)) ⟨T, hf⟩
  have hempty : ⋂ t : ℝ, (closedBall (0 : ℝ × ℝ) t)ᶜ = ∅ :=
    eq_empty_of_forall_notMem fun y hy ↦ mem_iInter.1 hy ‖y‖ (by simp)
  rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h

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
  set ρ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u
  set U := ball z₀ R \ {z₀}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hsub {z : ℝ × ℝ} (hz : z ∈ ball z₀ (R / 2) \ {z₀}) := ball_half_norm_sub_subset hz
  -- The energy of the disc of radius `t` about `z₀` tends to `0` with `t`. Lebesgue measure on
  -- `ℝ × ℝ` is an additive Haar measure, so it vanishes on points.
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hε := MeasureTheory.IntegrableOn.tendsto_setIntegral_ball_nhds_zero hint.norm z₀
  have hρ0 {y : ℝ × ℝ} (hy : y ∈ U) : 0 ≤ ρ y := floerEnergyDensity_nonneg hω (hJ₀ _) (hhol y hy)
  rw [tendsto_iff_seq_tendsto]
  intro z hz
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hz.eventually (sdiff_mem_nhdsWithin_compl (ball_mem_nhds z₀ (half_pos hR)) _))
  refine (tendsto_add_atTop_iff_nat N).1 ?_
  have hpos (k : ℕ) : 0 < ‖z (k + N) - z₀‖ / 2 :=
    half_pos (norm_pos_iff.2 (sub_ne_zero.2 (hN _ (Nat.le_add_left _ _)).2))
  have hsubk (k : ℕ) := hsub (hN (k + N) (Nat.le_add_left _ _))
  have h := hω.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral J₀ hJ₀ he he_inj hc hJc
    hU hu hhol (p := fun k ↦ z (k + N)) (s := fun k ↦ ‖z (k + N) - z₀‖ / 2) hpos
    (fun k ↦ (hsubk k).trans inter_subset_left)
    (fun k ↦ hint.mono_set ((hsubk k).trans (inter_subset_left.trans sdiff_subset))) ?_
  · have h4 := h.const_mul 4
    rw [mul_zero] at h4
    exact h4.congr fun k ↦ by simp only [Function.comp_apply, ρ]; ring
  -- The energies of the discs tend to `0`.
  have htend : Tendsto (fun k ↦ 2 * ‖z (k + N) - z₀‖) atTop (𝓝 0) := by
    have := ((tendsto_add_atTop_iff_nat N).2 (tendsto_nhds_of_tendsto_nhdsWithin hz)).sub_const z₀
    simpa using (this.norm.const_mul 2)
  refine squeeze_zero (fun k ↦ setIntegral_nonneg measurableSet_ball fun y hy ↦
    hρ0 ((hsubk k hy).1)) (fun k ↦ ?_) (by simpa using hε.comp htend)
  calc ∫ y in ball (z (k + N)) (‖z (k + N) - z₀‖ / 2), ρ y
      ≤ ∫ y in ball (z (k + N)) (‖z (k + N) - z₀‖ / 2), ‖ρ y‖ :=
        (le_abs_self _).trans (abs_integral_le_integral_abs (f := ρ))
    _ = ∫ y in ball (z (k + N)) (‖z (k + N) - z₀‖ / 2), ‖ρ y‖ ∂volume.restrict (ball z₀ R) := by
        rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.2
          ((hsubk k).trans (inter_subset_left.trans sdiff_subset))]
    _ ≤ ∫ y in ball z₀ (2 * ‖z (k + N) - z₀‖), ‖ρ y‖ ∂volume.restrict (ball z₀ R) :=
        setIntegral_mono_set hint.norm.integrableOn
          (Eventually.of_forall fun _ ↦ norm_nonneg _)
          (Eventually.of_forall fun y hy ↦ ((hsubk k) hy).2)

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
  set ρ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u
  set U := (closedBall (0 : ℝ × ℝ) T)ᶜ
  have hsub {z : ℝ × ℝ} (hz : 2 * max T 0 < ‖z‖) := ball_half_norm_subset (T := T) hz
  have hint' : IntegrableOn (fun y ↦ ‖ρ y‖) U := hint.norm
  have hε := tendsto_setIntegral_compl_closedBall hint'
  have hρ0 {y : ℝ × ℝ} (hy : y ∈ U) : 0 ≤ ρ y := floerEnergyDensity_nonneg hω (hJ₀ _) (hhol y hy)
  -- The filter `cocompact (ℝ × ℝ)` is countably generated: it is the comap of `atTop` by the norm.
  have : (cocompact (ℝ × ℝ)).IsCountablyGenerated := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  rw [tendsto_iff_seq_tendsto]
  intro z hz
  have hzn : Tendsto (fun k ↦ ‖z k‖) atTop atTop := tendsto_norm_cocompact_atTop.comp hz
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hzn.eventually_gt_atTop (2 * max T 0))
  refine (tendsto_add_atTop_iff_nat N).1 ?_
  have hpos (k : ℕ) : 0 < ‖z (k + N)‖ / 2 :=
    half_pos ((mul_nonneg zero_le_two (le_max_right T 0)).trans_lt (hN _ (Nat.le_add_left _ _)))
  have hsubk (k : ℕ) := hsub (hN (k + N) (Nat.le_add_left _ _))
  have h := hω.tendsto_sq_mul_floerEnergyDensity_of_tendsto_setIntegral J₀ hJ₀ he he_inj hc hJc
    isClosed_closedBall.isOpen_compl hu hhol (p := fun k ↦ z (k + N))
    (s := fun k ↦ ‖z (k + N)‖ / 2) hpos (fun k ↦ (hsubk k).trans inter_subset_right)
    (fun k ↦ hint.mono_set ((hsubk k).trans inter_subset_right)) ?_
  · have h4 := h.const_mul 4
    rw [mul_zero] at h4
    exact h4.congr fun k ↦ by simp only [Function.comp_apply, ρ]; ring
  -- The energies of the discs tend to `0`.
  have htend : Tendsto (fun k ↦ ‖z (k + N)‖ / 2) atTop atTop :=
    ((tendsto_add_atTop_iff_nat N).2 hzn).atTop_div_const two_pos
  refine squeeze_zero (fun k ↦ setIntegral_nonneg measurableSet_ball fun y hy ↦
    hρ0 ((hsubk k hy).2)) (fun k ↦ ?_) (hε.comp htend)
  calc ∫ y in ball (z (k + N)) (‖z (k + N)‖ / 2), ρ y
      ≤ ∫ y in ball (z (k + N)) (‖z (k + N)‖ / 2), ‖ρ y‖ :=
        (le_abs_self _).trans (abs_integral_le_integral_abs (f := ρ))
    _ ≤ ∫ y in (closedBall (0 : ℝ × ℝ) (‖z (k + N)‖ / 2))ᶜ, ‖ρ y‖ := by
        refine setIntegral_mono_set (hint'.mono_set ?_)
          (Eventually.of_forall fun _ ↦ norm_nonneg _)
          (Eventually.of_forall fun y hy ↦ ((hsubk k) hy).1)
        exact compl_subset_compl.2 (closedBall_subset_closedBall
          ((le_max_left T 0).trans (by linarith [hN (k + N) (Nat.le_add_left _ _)])))

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

end TauCeti.SmoothTwoForm
