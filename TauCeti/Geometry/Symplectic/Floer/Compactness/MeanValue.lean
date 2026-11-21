/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The mean-value inequality for Floer solutions in a chart

Gromov–Floer compactness for Floer solutions in a closed manifold `M` uses an a priori bound on
small discs of small energy, the mean-value inequality. For solutions of the coordinate Floer
equation `∂ₜu - X(z, u)(0, 1) = J(z, u)(∂ₛu - X(z, u)(1, 0))` in a finite-dimensional normed space
`F`, on balls of `ℝ × ℝ`, which are squares for its sup norm, there are `δ > 0` and `C` such that a
solution on `B_r(z₀)` with `r² + ∫_{B_r(z₀)} ‖∂ₛu‖² < δ` satisfies
`r² ‖∂ₛu(z₀)‖² ≤ C (r² + ∫_{B_r(z₀)} ‖∂ₛu‖²)`
(`TauCeti.Floer.exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional`).
This file states it for solutions in a chart of a manifold.

For a solution `u : ℝ × ℝ → M` of `(du - X_K)^{0,1} = 0` with values in a chart, the same
inequality holds for the intrinsic Floer energy density `e(u) = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`:
if `r² + ∫_{B_r(z₀)} e(u) < δ`, then `r² e(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} e(u))` (in the namespace
`TauCeti.SmoothTwoForm`,
`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy`). On a compact
window of the chart, `e(u)` and `‖∂ₛv‖²` for the coordinate expression `v` of `u` bound each other
up to constants (`IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_sq_le` and
`exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq`), and the square `B_r(z₀)`
has area `4 r²` (`Real.volume_real_ball_prod`), so a pointwise bound between the densities
integrates over it (`TauCeti.setIntegral_le_mul_measureReal_add_setIntegral_of_le`).

So a disc of radius `r` and small energy has energy density at most `C (1 + ∫ e(u) / r²)` at its
centre. Contrapositively, a disc on which `r² e(u)` is large at the centre carries at least a fixed
amount of energy: this is the lower bound for the energy concentrating at a point where the energy
densities of a sequence of solutions blow up, once the discs about the centres chosen by
`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv` are known to lie in a
chart. That localization of small discs into charts is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.3
  (the mean-value inequality) and Section 8.1 (inhomogeneous equations).
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Real Set Topology

open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- The arithmetic closing the mean-value inequality in a chart: the energy density `f₀` at the
centre is at most `A' g₀ + B'` for the coordinate density `g₀`, which the coordinate mean-value
inequality bounds by the coordinate energy `G`, in turn at most `κ` times the Floer energy `I`. -/
private theorem sq_mul_le_of_le_mul_add {f₀ g₀ r A' B' C κ G I : ℝ} (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (hC : 0 ≤ C) (hI : 0 ≤ I) (hf₀ : f₀ ≤ A' * g₀ + B') (hmv : r ^ 2 * g₀ ≤ C * (r ^ 2 + G))
    (hG : r ^ 2 + G ≤ κ * (r ^ 2 + I)) :
    r ^ 2 * f₀ ≤ (A' * C * κ + B') * (r ^ 2 + I) := by
  calc r ^ 2 * f₀ ≤ A' * (r ^ 2 * g₀) + B' * r ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hf₀ (sq_nonneg r)]
    _ ≤ A' * (C * (κ * (r ^ 2 + I))) + B' * (r ^ 2 + I) :=
        add_le_add (mul_le_mul_of_nonneg_left (hmv.trans (by gcongr)) hA')
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hI) hB')
    _ = (A' * C * κ + B') * (r ^ 2 + I) := by ring

/-- **The mean-value inequality for Floer solutions in a chart of a manifold.** Let `ω` be a
nondegenerate two-form on `M` and `α` a point of `M`. Let the structures `J(z, x)` and the
Hamiltonian vector fields of `K_s` and `K_t`, read in the chart at `α`, be `C²` on an open set
`W ⊆ (ℝ × ℝ) × E` containing `D × K`, for compact `D ⊆ ℝ × ℝ` and a compact set `K` of chart
coordinates, and let `J(z, x)` be tamed by `ω` on `D × K`. There are a threshold `δ > 0` and a
constant `C` with the following property. Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0`
for `J(z, u)` on a ball `B_r(z₀) ⊆ D` of `ℝ × ℝ`, with values in the chart source and chart
coordinates in `K`, let `u` be `C³` on the ball, and let `∂ₛ` of its coordinate expression
`extChartAt I α ∘ u` be continuous on the closed ball. If the Floer energy density
`e(u) = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` is integrable on the ball and
`r² + ∫_{B_r(z₀)} e(u) < δ`, then

`r² e(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} e(u))`.

So a small disc of small energy has energy density at its centre at most `C / r²` times the
energy plus `C`. Balls of `ℝ × ℝ` are squares for its sup norm. -/
theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy
    (hω : ω.IsNondegenerate) (α : M) {W : Set ((ℝ × ℝ) × E)} {D : Set (ℝ × ℝ)} {K : Set E}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J) W)
    (hXs : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks) W)
    (hXt : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt) W)
    (hD : IsCompact D) (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y))) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 ≤ r → ball z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ (extChartAt I α ∘ u) y stdComplexLineReal)
        (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
        (ω.perturbedMFDeriv Ks Kt u y).toLinearMap) →
      MapsTo u (ball z₀ r) ((extChartAt I α).source ∩ extChartAt I α ⁻¹' K) →
      IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        C * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y) := by
  set e := extChartAt I α
  -- The energy density and `‖∂ₛv‖²` control each other on `D × K`, for `v = e ∘ u`.
  obtain ⟨A, hA0, B, hB0, hpt⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le (Kt := Kt) α
    hD hK hKα (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW) hJt
  obtain ⟨A', hA'0, B', hB'0, hrev⟩ :=
    ω.exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq (Kt := Kt) α hD hK hKα
      (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW)
  -- The mean-value inequality for the coordinate expressions.
  obtain ⟨δ, hδ, C, hC0, hmean⟩ :=
    Floer.exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional hW hJ
      (contDiffOn_hamiltonianOneFormInChartAt hXs hXt) hD hK hDKW
      (fun z _ _ hy ↦ Floer.almostComplexInChartAt_apply_apply (hKα hy) z)
  set κ := 1 + 4 * (A + B + 1) with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨δ / κ, div_pos hδ hκ0, A' * C * κ + B', by positivity,
    fun u z₀ r hr hrD hu hu' hfl huK hint hE ↦ ?_⟩
  set f := ω.floerEnergyDensity Ks Kt u
  set g : ℝ × ℝ → ℝ := fun y ↦ ‖fderiv ℝ (e ∘ u) y stdComplexLineReal‖ ^ 2
  have hus {y : ℝ × ℝ} (hy : y ∈ ball z₀ r) : u y ∈ e.source := (huK hy).1
  have hdiff {y : ℝ × ℝ} (hy : y ∈ ball z₀ r) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u y :=
    (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (isOpen_ball.mem_nhds hy)
  obtain ⟨hcd, hcfl⟩ := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub isOpen_ball
    hu (fun _ hy ↦ hus hy) hfl
  have hf0 : ∀ y ∈ ball z₀ r, 0 ≤ f y := fun y hy ↦
    hω.floerEnergyDensity_nonneg_of_tames_inChartAt hJt (hrD hy) (hus hy) (huK hy).2 (hfl y hy)
  have hgf : ∀ y ∈ ball z₀ r, g y ≤ A * f y + B := fun y hy ↦
    hpt (hrD hy) (hus hy) (huK hy).2 (hdiff hy) (hfl y hy)
  have hIf0 : 0 ≤ ∫ y in ball z₀ r, f y := setIntegral_nonneg measurableSet_ball hf0
  -- The coordinate energy is controlled by the Floer energy and the area `4 r²` of the square.
  have hIg := setIntegral_le_mul_measureReal_add_setIntegral_of_le measurableSet_ball
    measure_ball_lt_top.ne hA0 hB0 ((hu'.norm.pow 2).integrableOn_compact
      (isCompact_closedBall z₀ r) |>.mono_set ball_subset_closedBall) hint hf0 hgf
  rw [Real.volume_real_ball_prod z₀ hr] at hIg
  have hIgκ : r ^ 2 + ∫ y in ball z₀ r, g y ≤ κ * (r ^ 2 + ∫ y in ball z₀ r, f y) := by
    rw [hκ]
    linear_combination hIg + 4 * hIf0 + 3 * mul_nonneg hA0 hIf0 + 3 * mul_nonneg hB0 hIf0
  have hmv := hmean hr hrD hcd hu' hcfl (fun y hy ↦ (huK hy).2) (hIgκ.trans_lt <| by
      calc κ * (r ^ 2 + ∫ y in ball z₀ r, f y) < κ * (δ / κ) := by gcongr
        _ = δ := mul_div_cancel₀ _ hκ0.ne')
  -- At the centre, the energy density is controlled by `‖∂ₛv‖²`.
  rcases hr.eq_or_lt with rfl | hr0
  · simp
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr0
  exact sq_mul_le_of_le_mul_add hA'0 hB'0 hC0 hIf0 (hrev (hrD hz₀) (hus hz₀) (huK hz₀).2
    (hdiff hz₀) (hfl z₀ hz₀)) hmv hIgκ

end TauCeti.SmoothTwoForm
