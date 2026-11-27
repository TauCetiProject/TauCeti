/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold.Family
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
This file states it for solutions in a chart of a manifold, as well as the parametric Euclidean-ball
version (`TauCeti.SmoothTwoForm.IsNondegenerate.`
`exists_pos_forall_pi_mul_sq_mul_floerEnergyDensity_le_inChart`).

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

The threshold and the constant are uniform over a compact window of parameters `p` in a
finite-dimensional normed space, for families `J_p`, `K_p` read in the chart that are jointly `C²`
in the parameter
(`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric`):
both comparisons of densities hold with constants uniform over the window, and so does the
coordinate inequality (in the namespace `TauCeti.Floer`,
`exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional_parametric`).
The inequality for a single datum is the case of a one-point window.

So a disc of radius `r` and small energy has energy density at most `C (1 + ∫ e(u) / r²)` at its
centre. Contrapositively, a disc on which `r² e(u)` is large at the centre carries at least a fixed
amount of energy: this is the lower bound for the energy concentrating at a point where the energy
densities of a sequence of solutions blow up, once the discs about the centres chosen by
`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv` are known to lie in a
chart. That localization of small discs into charts, and the resulting energy concentration and
compactness off finitely many bubbling points, are in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Bubbling`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.3
  (the mean-value inequality) and Section 8.1 (inhomogeneous equations).
-/

public section

noncomputable section

open Bundle Complex ContinuousLinearMap Filter MeasureTheory Metric Real Set Topology

open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

section

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
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

/-- **The mean-value inequality for Floer solutions in a chart of a manifold, over a compact
parameter window.** Let `ω` be a nondegenerate two-form on `M` and `α` a point of `M`. Let the
structures `J_p(z, x)` and the Hamiltonian vector fields of `K_{s,p}` and `K_{t,p}`, read in the
chart at `α`, depend on a parameter `p` of a finite-dimensional normed space `P` and be jointly
`C²` on an open set `W ⊆ (P × (ℝ × ℝ)) × E` containing `(C × D) × K`, for compact `C ⊆ P`,
`D ⊆ ℝ × ℝ` and a compact set `K` of chart coordinates, and let `J_p(z, x)` be tamed by `ω` there.
There are a threshold `δ > 0` and a constant `C'`, the same for every parameter `p ∈ C`, with the
following property. Let `u` solve the Floer equation `(du - X_{K_p})^{0,1} = 0` for `J_p(z, u)` on a
ball `B_r(z₀) ⊆ D` of `ℝ × ℝ`, with values in the chart source and chart coordinates in `K`, let `u`
be `C³` on the ball, and let `∂ₛ` of its coordinate expression `extChartAt I α ∘ u` be continuous on
the closed ball. If the Floer energy density `e(u) = ω(∂ₛu - X_{K_{s,p}}, ∂ₜu - X_{K_{t,p}})` is
integrable on the ball and `r² + ∫_{B_r(z₀)} e(u) < δ`, then

`r² e(u)(z₀) ≤ C' (r² + ∫_{B_r(z₀)} e(u))`.

Balls of `ℝ × ℝ` are squares for its sup norm. -/
theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} (hω : ω.IsNondegenerate) (α : M)
    {W : Set ((P × (ℝ × ℝ)) × E)} {C : Set P} {D : Set (ℝ × ℝ)} {K : Set E} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α (Function.uncurry J)) W)
    (hXs : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α (Function.uncurry Ks)) W)
    (hXt : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α (Function.uncurry Kt)) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hCDKW : (C ×ˢ D) ×ˢ K ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J p z ((extChartAt I α).symm y))) :
    ∃ δ > 0, ∃ C' ≥ 0, ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, p ∈ C → 0 ≤ r →
      ball z₀ r ⊆ D → ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ (extChartAt I α ∘ u) y stdComplexLineReal)
        (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p y (u y))
        (ω.perturbedMFDeriv (Ks p) (Kt p) u y).toLinearMap) →
      MapsTo u (ball z₀ r) ((extChartAt I α).source ∩ extChartAt I α ⁻¹' K) →
      IntegrableOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (ball z₀ r) →
      r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y < δ →
      r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u z₀ ≤
        C' * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y) := by
  set e := extChartAt I α
  -- The energy density and `‖∂ₛv‖²` control each other on `(C × D) × K`, for `v = e ∘ u`.
  obtain ⟨A, hA0, B, hB0, hpt⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le (Kt := Kt) α
    hC hD hK hKα (hJ.continuousOn.mono hCDKW) (hXs.continuousOn.mono hCDKW) hJt
  obtain ⟨A', hA'0, B', hB'0, hrev⟩ :=
    ω.exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq (Kt := Kt) α hC hD hK
      hKα (hJ.continuousOn.mono hCDKW) (hXs.continuousOn.mono hCDKW)
  -- The mean-value inequality for the coordinate expressions.
  obtain ⟨δ, hδ, C, hC0, hmean⟩ :=
    Floer.exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional_parametric
      hW hJ (contDiffOn_hamiltonianOneFormInChartAt hXs hXt) hC hD hK hCDKW
      fun p _ z _ y hy v ↦ by
        rw [Floer.almostComplexInChartAt_uncurry, Floer.almostComplexInChartAt_apply_apply (hKα hy)]
  set κ := 1 + 4 * (A + B + 1) with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨δ / κ, div_pos hδ hκ0, A' * C * κ + B', by positivity,
    fun p u z₀ r hp hr hrD hu hu' hfl huK hint hE ↦ ?_⟩
  set f := ω.floerEnergyDensity (Ks p) (Kt p) u
  set g : ℝ × ℝ → ℝ := fun y ↦ ‖fderiv ℝ (e ∘ u) y stdComplexLineReal‖ ^ 2
  have hus {y : ℝ × ℝ} (hy : y ∈ ball z₀ r) : u y ∈ e.source := (huK hy).1
  have hdiff {y : ℝ × ℝ} (hy : y ∈ ball z₀ r) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u y :=
    (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (isOpen_ball.mem_nhds hy)
  obtain ⟨hcd, hcfl⟩ := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub isOpen_ball
    hu (by norm_num) (fun _ hy ↦ hus hy) hfl
  have hf0 : ∀ y ∈ ball z₀ r, 0 ≤ f y := fun y hy ↦
    hω.floerEnergyDensity_nonneg_of_tames_inChartAt (hJt p hp) (hrD hy) (hus hy) (huK hy).2
      (hfl y hy)
  have hgf : ∀ y ∈ ball z₀ r, g y ≤ A * f y + B := fun y hy ↦
    hpt hp (hrD hy) (hus hy) (huK hy).2 (hdiff hy) (hfl y hy)
  have hIf0 : 0 ≤ ∫ y in ball z₀ r, f y := setIntegral_nonneg measurableSet_ball hf0
  -- The coordinate energy is controlled by the Floer energy and the area `4 r²` of the square.
  have hIg := setIntegral_le_mul_measureReal_add_setIntegral_of_le measurableSet_ball
    measure_ball_lt_top.ne hA0 hB0 ((hu'.norm.pow 2).integrableOn_compact
      (isCompact_closedBall z₀ r) |>.mono_set ball_subset_closedBall) hint hf0 hgf
  rw [Real.volume_real_ball_prod z₀ hr] at hIg
  have hIgκ : r ^ 2 + ∫ y in ball z₀ r, g y ≤ κ * (r ^ 2 + ∫ y in ball z₀ r, f y) := by
    rw [hκ]
    linear_combination hIg + 4 * hIf0 + 3 * mul_nonneg hA0 hIf0 + 3 * mul_nonneg hB0 hIf0
  have hmv := hmean hp hr hrD hcd hu'
    (fun y hy ↦ by simpa using hcfl y hy)
    (fun y hy ↦ (huK hy).2) (hIgκ.trans_lt <| by
      calc κ * (r ^ 2 + ∫ y in ball z₀ r, f y) < κ * (δ / κ) := by gcongr
        _ = δ := mul_div_cancel₀ _ hκ0.ne')
  -- At the centre, the energy density is controlled by `‖∂ₛv‖²`.
  rcases hr.eq_or_lt with rfl | hr0
  · simp
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr0
  exact sq_mul_le_of_le_mul_add hA'0 hB'0 hC0 hIf0 (hrev hp (hrD hz₀) (hus hz₀) (huK hz₀).2
    (hdiff hz₀) (hfl z₀ hz₀)) hmv hIgκ

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
energy plus `C`. Balls of `ℝ × ℝ` are squares for its sup norm. This is the case of a one-point
parameter window of
`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric` in the
namespace `TauCeti.SmoothTwoForm`. -/
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
  -- The constant family over the one-point parameter space `Unit`.
  set pr := fun q : (Unit × (ℝ × ℝ)) × E ↦ (q.1.2, q.2)
  have hπ : MapsTo pr (pr ⁻¹' W) W := mapsTo_preimage _ _
  obtain ⟨δ, hδ, C, hC, h⟩ :=
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric
      (J := fun _ ↦ J) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (C := univ) α
      (hW.preimage (by fun_prop)) (Floer.contDiffOn_almostComplexInChartAt_uncurry_const hJ hπ)
      (contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const hXs hπ)
      (contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const hXt hπ) isCompact_univ hD hK hKα
      (fun q hq ↦ hDKW ⟨hq.1.2, hq.2⟩) fun _ _ ↦ hJt
  exact ⟨δ, hδ, C, hC, fun u z₀ r hr hrD hu hu' hfl huK hint hE ↦
    h (mem_univ ()) hr hrD hu hu' hfl huK hint hE⟩

end

section ChartMVI

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Conjugates the chart Floer data `(J, X_{K_s}, X_{K_t})` to Euclidean space via `toEuclidean`
and `Complex.equivRealProdCLM`, obtaining the parametric Euclidean mean-value inequality on
`C × (eℂ⁻¹ D) × (L '' K_α)`. -/
private theorem IsNondegenerate.exists_euclidean_chart_mvi [I.Boundaryless]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (α : M)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {Kα : Set E} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hKα : IsCompact Kα)
    (hKαt : Kα ⊆ (extChartAt I α).target)
    (hCDKW : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' Kα)) ⊆ W) :
    let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
    let LP := ContinuousLinearEquiv.refl ℝ P
    let eℂ := Complex.equivRealProdCLM
    ∃ δ > 0, ∀ ⦃p : P⦄ ⦃w : ℂ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))⦄ ⦃y₀ : ℂ⦄ ⦃r : ℝ⦄,
      p ∈ C → 0 ≤ r → ball y₀ r ⊆ eℂ ⁻¹' D → ContDiffOn ℝ 3 w (ball y₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ w y 1) (closedBall y₀ r) →
      (∀ y ∈ ball y₀ r,
        fderiv ℝ w y Complex.I -
            ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt p (y, w y) Complex.I =
          Floer.transportedAlmostComplexInChartAt I α LP L J p (y, w y)
            (fderiv ℝ w y 1 -
              ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt p (y, w y) 1)) →
      MapsTo w (ball y₀ r) (L '' Kα) →
      π * r ^ 2 + ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ w y₀ 1‖ ^ 2 ≤
        7 * π * r ^ 2 + 8 * ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 := by
  set e := extChartAt I α
  set eℂ := Complex.equivRealProdCLM
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let LP := ContinuousLinearEquiv.refl ℝ P
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  have hW' : IsOpen {q : P × (ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) |
      L.symm q.2.2 ∈ e.target ∧
        (LP.symm q.1, (eℂ q.2.1, e.symm (L.symm q.2.2))) ∈ W} := by
    simpa only [preimage_ofPred_eq, Floer.chartTransportEquiv_apply] using
      (isOpen_preimage_prod_extChartAt_symm (I := I) α hW).preimage
        (Floer.chartTransportEquiv LP L).continuous
  have hJ' := Floer.contDiffOn_transportedAlmostComplexInChartAt (n := 2) (by simp) α LP L hJ
  have hX' :=
    ω.contDiffOn_transportedHamiltonianOneFormInChartAt (n := 2) (by simp) α LP L hXsM hXtM
  have hCDKW' : C ×ˢ ((eℂ ⁻¹' D) ×ˢ (L '' Kα)) ⊆
      {q : P × (ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) |
        L.symm q.2.2 ∈ e.target ∧
          (LP.symm q.1, (eℂ q.2.1, e.symm (L.symm q.2.2))) ∈ W} := by
    rintro ⟨p, z, _⟩ ⟨hp, hz, y, hy, rfl⟩
    exact ⟨by simpa using hKαt hy, hCDKW ⟨hp, hz, ⟨y, hy, by simp⟩⟩⟩
  exact Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric
    hW' hJ' hX' hC (eℂ.toHomeomorph.isCompact_preimage.2 hD) (hKα.image L.continuous) hCDKW'
    fun p _ z _ x hx v ↦ by
      rcases hx with ⟨y, hy, rfl⟩
      exact Floer.transportedAlmostComplexInChartAt_apply_apply α LP L J p
        ((L.symm_apply_apply y).symm ▸ hKαt hy) v

omit [FiniteDimensional ℝ E] in
/-- Transporting `v : ℝ × ℝ → E` via `L : E ≃L[ℝ] F` and `Complex.equivRealProdCLM` bounds
`‖∂ₛ(L ∘ v ∘ eℂ)‖²` by `‖L‖² * ‖dv‖²`. -/
private theorem norm_fderiv_euclidean_one_sq_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (v : ℝ × ℝ → E) (y : ℂ) :
    ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y'))) y 1‖ ^ 2 ≤
      ‖(L : E →L[ℝ] F)‖ ^ 2 * ‖fderiv ℝ v (Complex.equivRealProdCLM y)‖ ^ 2 := by
  have hfw : fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y'))) y 1 =
      L (fderiv ℝ v (Complex.equivRealProdCLM y) stdComplexLineReal) :=
    (congrArg (fun f : ℂ →L[ℝ] F ↦ f 1)
      (L.comp_fderiv (f := v ∘ Complex.equivRealProdCLM) (x := y))).trans
      (congrArg L (fderiv_comp_equivRealProdCLM_one v y))
  have h1 : ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y'))) y 1‖ ≤
      ‖(L : E →L[ℝ] F)‖ * ‖fderiv ℝ v (Complex.equivRealProdCLM y)‖ := by
    have h2 : ‖fderiv ℝ v (Complex.equivRealProdCLM y) stdComplexLineReal‖ ≤
        ‖fderiv ℝ v (Complex.equivRealProdCLM y)‖ := by
      simpa [stdComplexLineReal] using
        (fderiv ℝ v (Complex.equivRealProdCLM y)).le_opNorm stdComplexLineReal
    rw [hfw]
    exact (L.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  calc ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y'))) y 1‖ ^ 2
      ≤ (‖(L : E →L[ℝ] F)‖ * ‖fderiv ℝ v (Complex.equivRealProdCLM y)‖) ^ 2 := by gcongr
    _ = ‖(L : E →L[ℝ] F)‖ ^ 2 * ‖fderiv ℝ v (Complex.equivRealProdCLM y)‖ ^ 2 := by rw [mul_pow]

omit [FiniteDimensional ℝ E] in
/-- Inverse coordinate comparison: `‖∂ₛv(c)‖²` is bounded by `‖L.symm‖²` times
`‖∂ₛ(L ∘ v ∘ eℂ)(eℂ.symm c)‖²`. -/
private theorem norm_fderiv_stdComplexLineReal_sq_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (v : ℝ × ℝ → E) (c : ℝ × ℝ) :
    ‖fderiv ℝ v c stdComplexLineReal‖ ^ 2 ≤
      ‖(L.symm : F →L[ℝ] E)‖ ^ 2 *
        ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y')))
          (Complex.equivRealProdCLM.symm c) 1‖ ^ 2 := by
  have hfw : fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y')))
        (Complex.equivRealProdCLM.symm c) 1 =
      L (fderiv ℝ v c stdComplexLineReal) := by
    have h1 := congrArg (fun f : ℂ →L[ℝ] F ↦ f 1)
      (L.comp_fderiv (f := v ∘ Complex.equivRealProdCLM) (x := Complex.equivRealProdCLM.symm c))
    simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
      h1.trans (congrArg L (fderiv_comp_equivRealProdCLM_one v (Complex.equivRealProdCLM.symm c)))
  have h2 : ‖fderiv ℝ v c stdComplexLineReal‖ ≤
      ‖(L.symm : F →L[ℝ] E)‖ *
        ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y')))
          (Complex.equivRealProdCLM.symm c) 1‖ := by
    have h1 : fderiv ℝ v c stdComplexLineReal =
        L.symm (fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y')))
          (Complex.equivRealProdCLM.symm c) 1) := by
      rw [hfw, ContinuousLinearEquiv.symm_apply_apply]
    rw [h1]
    exact L.symm.toContinuousLinearMap.le_opNorm _
  calc ‖fderiv ℝ v c stdComplexLineReal‖ ^ 2
      ≤ (‖(L.symm : F →L[ℝ] E)‖ *
          ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y')))
            (Complex.equivRealProdCLM.symm c) 1‖) ^ 2 := by gcongr
    _ = ‖(L.symm : F →L[ℝ] E)‖ ^ 2 *
          ‖fderiv ℝ (fun y' ↦ L (v (Complex.equivRealProdCLM y')))
            (Complex.equivRealProdCLM.symm c) 1‖ ^ 2 := by rw [mul_pow]

/-- Integral comparison between `‖∂ₛw‖²` on `ball y₀ r ⊆ eℂ⁻¹(ball c r)` and `f` on `ball c r`. -/
private theorem setIntegral_norm_fderiv_one_sq_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {w : ℂ → F} {f : ℝ × ℝ → ℝ} {y₀ : ℂ} {c : ℝ × ℝ} {r A₁ B₁ : ℝ}
    (hr : 0 ≤ r) (hA₁ : 0 ≤ A₁)
    (hball : ball y₀ r ⊆ Complex.equivRealProdCLM ⁻¹' ball c r)
    (hw_int : IntegrableOn (fun y ↦ ‖fderiv ℝ w y 1‖ ^ 2) (ball y₀ r))
    (hf_int : IntegrableOn f (ball c r)) (hf_nn : ∀ z ∈ ball c r, 0 ≤ f z)
    (hpt : ∀ y ∈ ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 ≤ A₁ * f (Complex.equivRealProdCLM y) + B₁) :
    ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 ≤ B₁ * (π * r ^ 2) + A₁ * ∫ z in ball c r, f z := by
  have heℂ_int : IntegrableOn (fun y ↦ f (Complex.equivRealProdCLM y))
      (Complex.equivRealProdCLM ⁻¹' ball c r) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      equivRealProdCLM.toHomeomorph.measurableEmbedding).2 hf_int
  have hvol : volume.real (ball y₀ r) = π * r ^ 2 := Complex.volume_real_ball y₀ hr
  calc ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2
      ≤ ∫ y in ball y₀ r, (A₁ * f (Complex.equivRealProdCLM y) + B₁) :=
        setIntegral_mono_on hw_int
          (((heℂ_int.mono_set hball).const_mul A₁).fun_add
            (integrableOn_const measure_ball_lt_top.ne))
          measurableSet_ball hpt
    _ = A₁ * (∫ y in ball y₀ r, f (Complex.equivRealProdCLM y)) + B₁ * (π * r ^ 2) := by
        rw [integral_add ((heℂ_int.mono_set hball).const_mul A₁)
          (integrableOn_const measure_ball_lt_top.ne), integral_const_mul, setIntegral_const,
          smul_eq_mul, hvol, mul_comm (π * r ^ 2)]
    _ ≤ B₁ * (π * r ^ 2) + A₁ * ∫ y in Complex.equivRealProdCLM ⁻¹' ball c r,
          f (Complex.equivRealProdCLM y) := by
        have hmono := setIntegral_mono_set heℂ_int
          (ae_restrict_of_forall_mem
            (isOpen_ball.preimage Complex.equivRealProdCLM.continuous).measurableSet
            fun y hy ↦ hf_nn _ hy)
          hball.eventuallySubset
        nlinarith
    _ = B₁ * (π * r ^ 2) + A₁ * ∫ z in ball c r, f z :=
        congrArg (fun x ↦ B₁ * (π * r ^ 2) + A₁ * x)
          (Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
            equivRealProdCLM.toHomeomorph.measurableEmbedding _ _)

/-- **Intrinsic chart mean-value inequality over a compact parameter window.** For a chart at `α`
and a compact set `K_α` of chart coordinates whose image lies in `W` over `C × D`, there exist
`δ > 0`, `M₁ > 0`, `M₂ > 0`, `M₃ ≥ 0` such that any `C³` solution `u` on an open `Ω ⊆ D` for
`p ∈ C` mapping `closedBall c r ⊆ Ω` into the chart with coordinates in `K_α` and satisfying the
small-energy condition `M₁ (π r²) + M₂ ∫_{B_r(c)} e(u) < δ` obeys
`π r² e(u)(c) ≤ M₃ (π r² + ∫_{B_r(c)} e(u))`. -/
theorem IsNondegenerate.exists_pos_forall_pi_mul_sq_mul_floerEnergyDensity_le_inChart
    [I.Boundaryless] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (α : M)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {Kα : Set E} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hKα : IsCompact Kα)
    (hKαt : Kα ⊆ (extChartAt I α).target)
    (hCDKW : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' Kα)) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ Kα,
      (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames (J p z ((extChartAt I α).symm y))) :
    ∃ δ > 0, ∃ M₁ > 0, ∃ M₂ > 0, ∃ M₃ ≥ 0,
      ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃r : ℝ⦄,
        IsOpen Ω → Ω ⊆ D → p ∈ C → 0 ≤ r → closedBall c r ⊆ Ω →
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
        (∀ z ∈ closedBall c r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap) →
        MapsTo u (closedBall c r) ((extChartAt I α).source ∩ extChartAt I α ⁻¹' Kα) →
        M₁ * (π * r ^ 2) + M₂ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z < δ →
        π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
          M₃ * (π * r ^ 2 + ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z) := by
  set e := extChartAt I α
  set eℂ := Complex.equivRealProdCLM
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  have hCDKWα : C ×ˢ (D ×ˢ Kα) ⊆
      {q : P × ((ℝ × ℝ) × E) | q.2.2 ∈ e.target ∧ (q.1, (q.2.1, e.symm q.2.2)) ∈ W} :=
    fun q hq ↦ ⟨hKαt hq.2.2, hCDKW ⟨hq.1, hq.2.1, ⟨q.2.2, hq.2.2, rfl⟩⟩⟩
  obtain ⟨A, hA, B, hB, C₀, hC₀, D₀, hD₀, hbd⟩ :=
    hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le α hC hD hKα hKαt
      ((Floer.contDiffOn_almostComplexInChartAt_of_contMDiffOn (n := 2) (by simp)
        α hJ).continuousOn.mono hCDKWα)
      ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXsM).continuousOn.mono
        hCDKWα)
      ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXtM).continuousOn.mono
        hCDKWα)
      hJt
  obtain ⟨δ, hδ, hmvi⟩ :=
    hω.exists_euclidean_chart_mvi α hW hKs hKt hJ hC hD hKα hKαt hCDKW
  -- Translate between Euclidean `‖∂ₛ(L ∘ e ∘ u ∘ eℂ)‖²` and the intrinsic energy density `e(u)`.
  set cL := ‖(L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ 2
  set cLs := ‖(L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ ^ 2
  set A₁ := cL * A + 1
  set B₁ := cL * B
  set C₁ := C₀ * cLs
  refine ⟨δ, hδ, 1 + B₁, by positivity, A₁, by positivity,
    max (C₁ * (7 + 8 * B₁) + D₀) (C₁ * 8 * A₁), by positivity,
    fun Ω p u c r hΩ hΩD hp hr hcr hu hfl huK hsmall ↦ ?_⟩
  rcases hr.eq_or_lt with rfl | _
  · simp [ball_zero]
  -- Continuity and nonnegativity of `e(u)` on `closedBall c r`.
  have he_cont : ContinuousOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (closedBall c r) :=
    ω.continuousOn_floerEnergyDensity_of_isOpen_prod hW hXsM.continuousOn hXtM.continuousOn hΩ hcr
      (hu.of_le (by norm_num)) fun z hz ↦
        hCDKW ⟨hp, hΩD (hcr hz), ⟨e (u z), (huK hz).2, e.left_inv (huK hz).1⟩⟩
  have he_int : IntegrableOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (ball c r) :=
    (he_cont.integrableOn_compact (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  have he_nn : ∀ z ∈ closedBall c r, 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z := fun z hz ↦ by
    have ht := hJt p hp z (hΩD (hcr hz)) (e (u z)) (huK hz).2
    rw [e.left_inv (huK hz).1] at ht
    exact floerEnergyDensity_nonneg hω ht (hfl z hz)
  -- Transport `u` to `w : ℂ → ℝ^d` via `L ∘ e ∘ u ∘ eℂ` and compare derivatives and integrals.
  set y₀ := eℂ.symm c
  set w : ℂ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun y ↦ L (e (u (eℂ y)))
  have hball_sub : ball y₀ r ⊆ eℂ ⁻¹' ball c r := fun y hy ↦ by
    simpa [y₀, eℂ] using (lipschitz_equivRealProd.dist_le_mul y y₀).trans_lt (by simpa using hy)
  have hcl_sub : closedBall y₀ r ⊆ eℂ ⁻¹' closedBall c r := fun y hy ↦ by
    simpa [y₀, eℂ] using (lipschitz_equivRealProd.dist_le_mul y y₀).trans (by simpa using hy)
  have hU₀ : IsOpen (eℂ ⁻¹' (Ω ∩ u ⁻¹' e.source)) :=
    (hu.continuousOn.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)).preimage eℂ.continuous
  have hsubU : closedBall y₀ r ⊆ eℂ ⁻¹' (Ω ∩ u ⁻¹' e.source) :=
    fun y hy ↦ ⟨hcr (hcl_sub hy), (huK (hcl_sub hy)).1⟩
  have hcdU : ContDiffOn ℝ 3 w (eℂ ⁻¹' (Ω ∩ u ⁻¹' e.source)) :=
    L.contDiff.comp_contDiffOn ((contMDiffOn_iff_contDiffOn.1 <|
      (contMDiffOn_extChartAt (n := 3)).comp (hu.mono inter_subset_left)
        fun z hz ↦ by rw [mem_preimage, ← extChartAt_source I]; exact hz.2).comp
      eℂ.contDiff.contDiffOn (mapsTo_preimage _ _))
  have hw_cont : ContinuousOn (fun y ↦ fderiv ℝ w y 1) (closedBall y₀ r) :=
    ((hcdU.continuousOn_fderiv_of_isOpen hU₀ (by norm_num)).clm_apply
      continuousOn_const).mono hsubU
  have hdiff (z : ℝ × ℝ) (hz : z ∈ closedBall c r) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
    (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds (hcr hz))
  have hpt_le (y : ℂ) (hy : y ∈ closedBall y₀ r) :
      ‖fderiv ℝ w y 1‖ ^ 2 ≤ A₁ * ω.floerEnergyDensity (Ks p) (Kt p) u (eℂ y) + B₁ := by
    have hzc : eℂ y ∈ closedBall c r := hcl_sub hy
    have h1 := (hbd hp (hΩD (hcr hzc)) (huK hzc).1 (huK hzc).2 (hdiff _ hzc) (hfl _ hzc)).1
    have h4 : ‖fderiv ℝ w y 1‖ ^ 2 ≤ cL * ‖fderiv ℝ (e ∘ u) (eℂ y)‖ ^ 2 :=
      norm_fderiv_euclidean_one_sq_le L (e ∘ u) y
    have h5 := he_nn _ hzc
    have hcL_nn : 0 ≤ cL := by positivity
    dsimp only [A₁, B₁]
    nlinarith
  have hw_int : IntegrableOn (fun y ↦ ‖fderiv ℝ w y 1‖ ^ 2) (ball y₀ r) :=
    ((hw_cont.norm.pow 2).integrableOn_compact (isCompact_closedBall y₀ r)).mono_set
      ball_subset_closedBall
  have hint_le : ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 ≤
      B₁ * (π * r ^ 2) + A₁ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    setIntegral_norm_fderiv_one_sq_le hr (by positivity) hball_sub hw_int he_int
      (fun z hz ↦ he_nn z (ball_subset_closedBall hz))
      fun y hy ↦ hpt_le y (ball_subset_closedBall hy)
  -- Apply the Euclidean chart MVI and convert `‖∂ₛw(y₀)‖²` back to `e(u)(c)`.
  have hmvi_w := hmvi (p := p) (w := w) (y₀ := y₀) (r := r) hp hr
    (hball_sub.trans (preimage_mono (ball_subset_closedBall.trans (hcr.trans hΩD))))
    (hcdU.mono (ball_subset_closedBall.trans hsubU)) hw_cont
    (fun y hy ↦ by
      have hzc : eℂ y ∈ closedBall c r := hcl_sub (ball_subset_closedBall hy)
      exact (ω.transported_floerEquation_iff α (ContinuousLinearEquiv.refl ℝ P) L (J := J)
        (Ks := Ks) (Kt := Kt) p (e ∘ u) y).2 <|
        (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
          (hdiff _ hzc) (huK hzc).1).1 (hfl _ hzc))
    (fun y hy ↦ ⟨e (u (eℂ y)), (huK (hcl_sub (ball_subset_closedBall hy))).2, rfl⟩)
    (by linarith)
  have hc_mem : c ∈ closedBall c r := mem_closedBall_self hr
  have hup := (hbd hp (hΩD (hcr hc_mem)) (huK hc_mem).1 (huK hc_mem).2 (hdiff c hc_mem)
    (hfl c hc_mem)).2
  have hre_w : ‖fderiv ℝ (e ∘ u) c stdComplexLineReal‖ ^ 2 ≤ cLs * ‖fderiv ℝ w y₀ 1‖ ^ 2 :=
    norm_fderiv_stdComplexLineReal_sq_le L (e ∘ u) c
  have hint_nn : 0 ≤ ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    setIntegral_nonneg measurableSet_ball fun z hz ↦ he_nn z (ball_subset_closedBall hz)
  have hπr_nn : 0 ≤ π * r ^ 2 := by positivity
  have hstep1 : π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
      C₁ * (π * r ^ 2 * ‖fderiv ℝ w y₀ 1‖ ^ 2) + D₀ * (π * r ^ 2) := by
    have : ω.floerEnergyDensity (Ks p) (Kt p) u c ≤ C₁ * ‖fderiv ℝ w y₀ 1‖ ^ 2 + D₀ := by
      nlinarith
    nlinarith
  have hC₁_nn : 0 ≤ C₁ := by positivity
  have hstep3 : π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
      (C₁ * (7 + 8 * B₁) + D₀) * (π * r ^ 2) +
        (C₁ * 8 * A₁) * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z := by nlinarith
  have hle1 : C₁ * (7 + 8 * B₁) + D₀ ≤ max (C₁ * (7 + 8 * B₁) + D₀) (C₁ * 8 * A₁) := le_max_left _ _
  have hle2 : C₁ * 8 * A₁ ≤ max (C₁ * (7 + 8 * B₁) + D₀) (C₁ * 8 * A₁) := le_max_right _ _
  nlinarith

end ChartMVI

end TauCeti.SmoothTwoForm
