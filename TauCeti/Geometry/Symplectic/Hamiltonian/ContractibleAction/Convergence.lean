/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Actions of loops converging to a constant loop

Let `ω` be a continuous weakly exact two-form on a boundaryless manifold `M`, and `φ` the
preferred extended chart at a point `x`. A `C²` loop `γ` that stays in a ball of the chart around
`φ x` is capped by the segments joining `φ (γ t)` to `φ x` in the chart. The area of this cap is
at most `π / 2 · B · δ · K`, where `B` bounds the coordinate expression of `ω` on the ball, `δ`
bounds the distance from `φ (γ t)` to `φ x` and `K` the speed of `φ ∘ γ`
(`TauCeti.IsWeaklyExact.norm_capArea_le`). So the cap area of loops converging uniformly to the
constant loop at `x`, with bounded speed in the chart at `x`, tends to `0`
(`TauCeti.IsWeaklyExact.tendsto_capArea_nhds_zero`), and their actions converge to the action
`-∫₀¹ H(t, x) dt` of the constant loop (`TauCeti.IsWeaklyExact.tendsto_contractibleLoopAction`).
The Hamiltonian term converges when the Hamiltonians converge uniformly on `[0, 1] × M` to a
Hamiltonian continuous along `[0, 1] × {x}`
(`TauCeti.tendsto_intervalIntegral_of_tendstoUniformlyOn`).

Consequently, a limit of actions of such loops lies in the contractible action spectrum of the
limit Hamiltonian as soon as the constant loop at `x` is one of its `1`-periodic orbits
(`TauCeti.SmoothTwoForm.mem_contractibleActionSpectrum_of_tendsto`). This is the closedness of
the spectrum used to prove spectrality of Floer-theoretic spectral invariants for degenerate
Hamiltonians: approximate a degenerate Hamiltonian by nondegenerate ones, whose spectral
invariants are actions of periodic orbits, and pass to the limit. For an autonomous Hamiltonian
`s F` without fast contractible periodic orbits, the limit orbits are constant loops at critical
points of `F` (`contractiblePeriodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints`
in `TauCeti.SmoothTwoForm.IsNondegenerate`), which is the situation of Irie's argument bounding
the `π₁`-sensitive Hofer–Zehnder capacity by a spectral invariant.

## Main results

* `TauCeti.IsWeaklyExact.norm_capArea_le`: the cap area of a loop inside a chart ball is bounded
  by the size of the form, the distance to the centre and the speed.
* `TauCeti.IsWeaklyExact.tendsto_capArea_nhds_zero`: loops converging uniformly to a constant loop
  with bounded speed have cap areas tending to `0`.
* `TauCeti.tendsto_intervalIntegral_of_tendstoUniformlyOn`: convergence of the Hamiltonian term.
* `TauCeti.IsWeaklyExact.tendsto_contractibleLoopAction`: the actions of such loops converge to
  the action of the constant loop.
* `TauCeti.SmoothTwoForm.mem_contractibleActionSpectrum_of_tendsto`: the limit of their actions
  lies in the spectrum of the limit Hamiltonian when the constant loop is a periodic orbit.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1.1 (Proposition 5.8, spectrality)
  and §5.1.2 (Step 2 of the proof of Lemma 5.7).
* K. Irie, *Hofer–Zehnder capacity of unit disk cotangent bundles and the loop product*, J. Eur.
  Math. Soc. 16 (2014), 2477–2497.
-/

public section

noncomputable section

open Filter Function Metric Set
open scoped Manifold Interval Topology Real

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The cap of a loop near a point -/

section CapArea

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [I.Boundaryless] [IsManifold I 2 M]
  {ω : RoughForm I M F 2}

/-- The profile `s ↦ (1 + cos (π s)) / 2` of the chart cap: it is `1` at `s = 0`, `0` at
`s = 1`, takes values in `[0, 1]` and has speed at most `π / 2`. -/
private def capProfile (s : ℝ) : ℝ := (1 + Real.cos (π * s)) / 2

private theorem capProfile_mem_Icc (s : ℝ) : capProfile s ∈ Icc (0 : ℝ) 1 := by
  have := Real.neg_one_le_cos (π * s)
  have := Real.cos_le_one (π * s)
  constructor <;> unfold capProfile <;> linarith

private theorem hasDerivAt_capProfile (s : ℝ) :
    HasDerivAt capProfile (-(Real.sin (π * s) * π) / 2) s := by
  have h := (((hasDerivAt_id s).const_mul π).cos).const_add 1
  simp only [mul_one, id] at h
  exact (h.div_const 2).congr_deriv (by ring)

private theorem abs_deriv_capProfile_le (s : ℝ) : |(-(Real.sin (π * s) * π) / 2)| ≤ π / 2 := by
  rw [abs_div, abs_neg, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  gcongr
  exact (mul_le_iff_le_one_left Real.pi_pos).2 (Real.abs_sin_le_one _)

variable (I) in
/-- The chart cap of a loop `γ` at `x`, in the coordinates of the preferred extended chart `φ` at
`x`: at time `s` it is the point `φ x + capProfile s • (φ (γ t) - φ x)` of the segment from
`φ (γ t)` to `φ x`. -/
private def chartCapCoord (x : M) (γ : ℝ → M) (z : ℝ × ℝ) : E :=
  extChartAt I x x + capProfile z.1 • (extChartAt I x (γ z.2) - extChartAt I x x)

variable (I) in
omit [I.Boundaryless] [IsManifold I 2 M] in
private theorem chartCapCoord_mem_ball {x : M} {γ : ℝ → M} {r δ : ℝ}
    (hδ : ∀ t, ‖extChartAt I x (γ t) - extChartAt I x x‖ ≤ δ) (hδr : δ < r) (z : ℝ × ℝ) :
    chartCapCoord I x γ z ∈ ball (extChartAt I x x) r := by
  rw [mem_ball, dist_eq_norm, chartCapCoord, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (capProfile_mem_Icc _).1]
  calc _ ≤ 1 * δ := mul_le_mul (capProfile_mem_Icc _).2 (hδ _) (norm_nonneg _) zero_le_one
    _ < r := by rwa [one_mul]

variable (I) in
omit [I.Boundaryless] in
private theorem contDiff_chartCapCoord {x : M} {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hsrc : ∀ t, γ t ∈ (extChartAt I x).source) :
    ContDiff ℝ 2 (extChartAt I x ∘ γ) ∧ ContDiff ℝ 2 (chartCapCoord I x γ) := by
  have hφγ : ContDiff ℝ 2 (extChartAt I x ∘ γ) := contMDiff_iff_contDiff.1
    ((contMDiffOn_extChartAt (x := x)).comp_contMDiff hγ fun t ↦ by
      simpa [extChartAt_source] using hsrc t)
  have hprof : ContDiff ℝ 2 capProfile :=
    (contDiff_const.add ((contDiff_const.mul contDiff_id).cos)).div_const 2
  exact ⟨hφγ, contDiff_const.add ((hprof.comp contDiff_fst).smul
    ((hφγ.sub contDiff_const).comp contDiff_snd))⟩

variable (I) in
omit [I.Boundaryless] in
/-- The chart cap is a cap of `γ`, centred at `x`. -/
private theorem isLoopCylinder_chartCap {x : M} {γ : ℝ → M} {r δ : ℝ}
    (hr : ball (extChartAt I x x) r ⊆ (extChartAt I x).target) (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hper : Periodic γ 1) (hsrc : ∀ t, γ t ∈ (extChartAt I x).source)
    (hδ : ∀ t, ‖extChartAt I x (γ t) - extChartAt I x x‖ ≤ δ) (hδr : δ < r) :
    IsLoopCylinder I ((extChartAt I x).symm ∘ chartCapCoord I x γ) γ fun _ ↦ x where
  contMDiff := (contMDiffOn_extChartAt_symm x).comp_contMDiff
    (contMDiff_iff_contDiff.2 (contDiff_chartCapCoord I hγ hsrc).2)
    fun z ↦ hr (chartCapCoord_mem_ball I hδ hδr z)
  apply_add_one z := by simp [chartCapCoord, hper z.2]
  apply_zero t := by simpa [chartCapCoord, capProfile] using (extChartAt I x).left_inv (hsrc t)
  apply_one t := by simp [chartCapCoord, capProfile]

variable (I) in
/-- The integrand of the area of the chart cap is at most `B · (π / 2 · δ · K)`: the form is
bounded by `B` on the ball, and the two partial derivatives of the cap by `π / 2 · δ` and `K`. -/
private theorem norm_chartCap_integrand_le {x : M} {γ : ℝ → M} {r B δ K : ℝ}
    (hr : ball (extChartAt I x x) r ⊆ (extChartAt I x).target)
    (hB : ∀ z ∈ ball (extChartAt I x x) r, ‖ω.inChartAt x z‖ ≤ B)
    (hγ : ContMDiff 𝓘(ℝ) I 2 γ) (hsrc : ∀ t, γ t ∈ (extChartAt I x).source)
    (hδ : ∀ t, ‖extChartAt I x (γ t) - extChartAt I x x‖ ≤ δ) (hδr : δ < r) (s t : ℝ)
    (hK : ‖deriv (extChartAt I x ∘ γ) t‖ ≤ K) :
    ‖ω (((extChartAt I x).symm ∘ chartCapCoord I x γ) (s, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I ((extChartAt I x).symm ∘ chartCapCoord I x γ) (s, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I ((extChartAt I x).symm ∘ chartCapCoord I x γ) (s, t) (0, 1)]‖ ≤
      B * (π / 2 * δ * K) := by
  set φ := extChartAt I x
  set c := chartCapCoord I x γ
  obtain ⟨hφγ, hcd⟩ := contDiff_chartCapCoord I hγ hsrc
  have hcball := chartCapCoord_mem_ball I hδ hδr (s, t)
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (c (s, t)) :=
    ((contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (hr hcball))).mdifferentiableAt two_ne_zero
  have heq : ω ((φ.symm ∘ c) (s, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I (φ.symm ∘ c) (s, t) (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (φ.symm ∘ c) (s, t) (0, 1)] =
      ω.inChartAt x (c (s, t)) ![fderiv ℝ c (s, t) (1, 0), fderiv ℝ c (s, t) (0, 1)] := by
    rw [RoughForm.inChartAt_apply, I.range_eq_univ, mfderivWithin_univ,
      mfderiv_comp (s, t) hsymm ((contMDiff_iff_contDiff.2 hcd).mdifferentiable two_ne_zero _),
      mfderiv_eq_fderiv]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [heq]
  have hdg : HasDerivAt (fun t ↦ φ (γ t) - φ x) (deriv (φ ∘ γ) t) t :=
    (hφγ.differentiable two_ne_zero t).hasDerivAt.sub_const (φ x)
  have hdc : HasFDerivAt c _ (s, t) := (((hasDerivAt_capProfile s).hasFDerivAt.comp (s, t)
    (f := Prod.fst) hasFDerivAt_fst).smul (hdg.hasFDerivAt.comp (s, t) (f := Prod.snd)
      hasFDerivAt_snd)).const_add (φ x)
  rw [hdc.fderiv]
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  refine (ContinuousAlternatingMap.le_opNorm_mul_prod_of_le _
    (b := ![π / 2 * δ, K]) fun i ↦ ?_).trans ?_
  · fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, comp_apply, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.toSpanSingleton_apply, zero_smul, smul_zero,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, one_mul,
        zero_add, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (abs_deriv_capProfile_le s) (hδ t) (norm_nonneg _) (by positivity)
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, comp_apply, add_apply,
        smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.toSpanSingleton_apply, one_smul, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst', smul_eq_mul, zero_mul, zero_smul, add_zero, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (capProfile_mem_Icc s).1]
      exact (mul_le_mul (capProfile_mem_Icc s).2 hK (norm_nonneg _) zero_le_one).trans_eq
        (one_mul K)
  · rw [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact mul_le_mul_of_nonneg_right (hB _ hcball)
      (mul_nonneg (mul_nonneg (by positivity) hδ0) ((norm_nonneg _).trans hK))

/-- **The cap area of a loop near a point.** Let `ω` be a continuous weakly exact two-form on a
boundaryless manifold, `φ` the preferred extended chart at `x`, and suppose that the coordinate
expression of `ω` in `φ` has norm at most `B` on a ball of radius `r` around `φ x` inside the
chart target. If a loop `γ` stays in the chart source, at distance at most `δ < r` from `φ x` in
the chart, and `φ ∘ γ` has speed at most `K`, then its cap area is at most `π / 2 · B · δ · K`.
A loop without a cap has cap area `0`, so no regularity or periodicity of `γ` is assumed. -/
theorem IsWeaklyExact.norm_capArea_le (hω : IsSmoothForm I 0 ω) (hw : IsWeaklyExact ω) {x : M}
    {γ : ℝ → M} {r B δ K : ℝ}
    (hr : ball (extChartAt I x x) r ⊆ (extChartAt I x).target)
    (hB : ∀ z ∈ ball (extChartAt I x x) r, ‖ω.inChartAt x z‖ ≤ B)
    (hsrc : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x).source)
    (hδ : ∀ t ∈ Icc (0 : ℝ) 1, ‖extChartAt I x (γ t) - extChartAt I x x‖ ≤ δ) (hδr : δ < r)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (extChartAt I x ∘ γ) t‖ ≤ K) :
    ‖capArea ω γ‖ ≤ π / 2 * B * δ * K := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 ⟨le_rfl, zero_le_one⟩)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (mem_ball_self (hδ0.trans_lt hδr)))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  by_cases hcap : ∃ u, IsCap I u γ
  swap
  · rw [capArea_of_not_exists_isCap hcap, norm_zero]
    positivity
  -- A loop with a cap is `C²` and periodic, so it stays in the chart at every time.
  obtain ⟨u₀, hu₀⟩ := hcap
  obtain ⟨y, hu₀⟩ := isCap_iff.1 hu₀
  have hper := hu₀.periodic_left
  have hall : ∀ t, γ t ∈ (extChartAt I x).source ∧
      ‖extChartAt I x (γ t) - extChartAt I x x‖ ≤ δ := fun t ↦ by
    obtain ⟨t', ht', he⟩ := hper.exists_mem_Ico₀ one_pos t
    rw [he]
    exact ⟨hsrc t' (Ico_subset_Icc_self ht'), hδ t' (Ico_subset_Icc_self ht')⟩
  rw [hw.capArea_eq hω (isLoopCylinder_chartCap I hr hu₀.contMDiff_left hper
    (fun t ↦ (hall t).1) (fun t ↦ (hall t).2) hδr).isCap, rectangleIntegral_eq]
  dsimp only
  have hinner : ∀ s : ℝ, ‖∫ t in (0 : ℝ)..1, ω (((extChartAt I x).symm ∘ chartCapCoord I x γ)
      (s, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I ((extChartAt I x).symm ∘ chartCapCoord I x γ) (s, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I ((extChartAt I x).symm ∘ chartCapCoord I x γ) (s, t) (0, 1)]‖ ≤
      B * (π / 2 * δ * K) * |(1 : ℝ) - 0| := fun s ↦
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦
      norm_chartCap_integrand_le I hr hB hu₀.contMDiff_left (fun t ↦ (hall t).1)
        (fun t ↦ (hall t).2) hδr s t
        (hK t (Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)))
  calc _ ≤ B * (π / 2 * δ * K) * |(1 : ℝ) - 0| * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s _ ↦ hinner s
    _ = π / 2 * B * δ * K := by rw [sub_zero, abs_one, mul_one, mul_one]; ring

omit [IsManifold I 2 M] in
/-- The coordinate expression of a continuous form in the preferred chart at `x` is bounded on a
ball around `φ x` contained in the chart target. -/
private theorem IsSmoothForm.exists_ball_norm_inChartAt_le [IsManifold I 1 M]
    (hω : IsSmoothForm I 0 ω) (x : M) :
    ∃ r > 0, ∃ B, 0 ≤ B ∧ ball (extChartAt I x x) r ⊆ (extChartAt I x).target ∧
      ∀ z ∈ ball (extChartAt I x x) r, ‖ω.inChartAt x z‖ ≤ B := by
  obtain ⟨r₁, hr₁, hψ⟩ := Metric.continuousAt_iff.1
    ((hω.continuousOn_inChartAt x).continuousAt (extChartAt_target_mem_nhds x)) 1 one_pos
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target x)
    (extChartAt I x x) (mem_extChartAt_target x)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ‖ω.inChartAt x (extChartAt I x x)‖ + 1, by positivity,
    (ball_subset_ball (min_le_right _ _)).trans hball, fun z hz ↦ ?_⟩
  have h := hψ (lt_of_lt_of_le hz (min_le_left _ _))
  rw [dist_eq_norm] at h
  linarith [norm_le_insert' (ω.inChartAt x z) (ω.inChartAt x (extChartAt I x x))]

/-- **Cap areas of loops converging to a constant loop.** Let `ω` be a continuous weakly exact
two-form on a boundaryless manifold. If loops `γ i` converge uniformly on `[0, 1]` to the constant
loop at `x`, and their speeds in the preferred chart at `x` are eventually bounded on `[0, 1]`,
then their cap areas tend to `0`. -/
theorem IsWeaklyExact.tendsto_capArea_nhds_zero (hω : IsSmoothForm I 0 ω) (hw : IsWeaklyExact ω)
    {ι : Type*} {l : Filter ι} {γ : ι → ℝ → M} {x : M}
    (hx : ∀ U ∈ 𝓝 x, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, γ i t ∈ U)
    (hK : ∃ K, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (extChartAt I x ∘ γ i) t‖ ≤ K) :
    Tendsto (fun i ↦ capArea ω (γ i)) l (𝓝 0) := by
  obtain ⟨K, hK⟩ := hK
  set φ := extChartAt I x
  obtain ⟨r, hr, B, hB0, hball, hB⟩ := hω.exists_ball_norm_inChartAt_le x
  set K' := max K 0
  set C := π / 2 * B * K'
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) hB0) (le_max_right _ _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := min (r / 2) (ε / (C + 1))
  have hδ : 0 < δ := lt_min (half_pos hr) (div_pos hε (by positivity))
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hCδ : C * δ < ε := by
    calc C * δ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hU : φ.source ∩ φ ⁻¹' ball (φ x) δ ∈ 𝓝 x :=
    inter_mem (extChartAt_source_mem_nhds x)
      ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ hδ))
  filter_upwards [hx _ hU, hK] with i hxi hKi
  rw [dist_zero_right]
  calc ‖capArea ω (γ i)‖ ≤ π / 2 * B * δ * K' :=
        hw.norm_capArea_le hω hball hB (fun t ht ↦ (hxi t ht).1)
          (fun t ht ↦ by
            have h := (hxi t ht).2
            rw [mem_preimage, mem_ball, dist_eq_norm] at h
            exact h.le) hδr
          fun t ht ↦ (hKi t ht).trans (le_max_left _ _)
    _ = C * δ := by ring
    _ < ε := hCδ

end CapArea

/-! ### The Hamiltonian term -/

/-- **Convergence of the Hamiltonian term.** If Hamiltonians `Ham i` converge uniformly on
`[0, 1] × M` to a Hamiltonian `Ham₀`, jointly continuous at the points of `[0, 1] × {x}`, and
loops `γ i` converge uniformly on `[0, 1]` to the constant loop at `x`, then
`∫₀¹ Ham i (t, γ i t) dt` tends to `∫₀¹ Ham₀ (t, x) dt`, provided the integrands are eventually
integrable. -/
theorem tendsto_intervalIntegral_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {γ : ι → ℝ → M} {x : M} {Ham : ι → ℝ → M → ℝ} {Ham₀ : ℝ → M → ℝ}
    (hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (uncurry Ham₀) (t, x))
    (hunif : TendstoUniformlyOn (fun i ↦ uncurry (Ham i)) (uncurry Ham₀) l
      (Icc (0 : ℝ) 1 ×ˢ univ))
    (hint : ∀ᶠ i in l, IntervalIntegrable (fun t ↦ Ham i t (γ i t)) MeasureTheory.volume 0 1)
    (hx : ∀ U ∈ 𝓝 x, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, γ i t ∈ U) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, Ham i t (γ i t)) l (𝓝 (∫ t in (0 : ℝ)..1, Ham₀ t x)) := by
  have hcx : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun t ↦ Ham₀ t x) t := fun t ht ↦
    (hcont t ht).comp (f := fun s ↦ (s, x)) (continuousAt_id.prodMk continuousAt_const)
  have hint₀ : IntervalIntegrable (fun t ↦ Ham₀ t x) MeasureTheory.volume 0 1 :=
    (ContinuousOn.intervalIntegrable fun t ht ↦ (hcx t (by simpa using ht)).continuousWithinAt)
  -- The integrands converge uniformly on `[0, 1]` to `t ↦ Ham₀ t x`.
  have hunif' : TendstoUniformlyOn (fun i t ↦ Ham i t (γ i t) - Ham₀ t x) 0 l [[0, 1]] := by
    rw [uIcc_of_le zero_le_one, Metric.tendstoUniformlyOn_iff]
    intro ε hε
    -- Near `x`, uniformly in `t ∈ [0, 1]`, the limit Hamiltonian is within `ε / 2` of its value
    -- at `x`, by compactness of `[0, 1]`.
    have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, dist (Ham₀ t y) (Ham₀ t x) < ε / 2 :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦ by
        have h₁ : ContinuousAt (uncurry Ham₀ ∘ fun z : M × ℝ ↦ (z.2, z.1)) (x, t) :=
          (hcont t ht).comp_of_eq (continuousAt_snd.prodMk continuousAt_fst) rfl
        have h₂ : ContinuousAt ((fun s ↦ Ham₀ s x) ∘ Prod.snd) (x, t) :=
          (hcx t ht).comp_of_eq continuousAt_snd rfl
        have h : ContinuousAt (fun z : M × ℝ ↦ Ham₀ z.2 z.1 - Ham₀ z.2 x) (x, t) := h₁.sub h₂
        filter_upwards [h.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 2))]
          with z hz
        simpa [dist_eq_norm, sub_self] using hz
    filter_upwards [hx _ hnear, Metric.tendstoUniformlyOn_iff.1 hunif (ε / 2) (by positivity)]
      with i hi hu t ht
    have h1 := hu (t, γ i t) ⟨ht, mem_univ _⟩
    have h2 := hi t ht t ht
    simp only [uncurry_apply_pair] at h1
    rw [Pi.zero_apply, dist_zero_left, ← dist_eq_norm]
    linarith [dist_triangle (Ham i t (γ i t)) (Ham₀ t (γ i t)) (Ham₀ t x),
      dist_comm (Ham₀ t (γ i t)) (Ham i t (γ i t))]
  refine tendsto_sub_nhds_zero_iff.1
    ((hunif'.tendsto_intervalIntegral_nhds_zero (μ := MeasureTheory.volume)).congr' ?_)
  filter_upwards [hint] with i hi
  exact intervalIntegral.integral_sub hi hint₀

/-! ### Actions -/

section Action

variable [I.Boundaryless] [IsManifold I 2 M] {ω : RoughForm I M ℝ 2}

/-- **Actions of loops converging to a constant loop.** Let `ω` be a continuous weakly exact
two-form on a boundaryless manifold. If loops `γ i` converge uniformly on `[0, 1]` to the constant
loop at `x` with eventually bounded speeds in the preferred chart at `x`, and the Hamiltonian terms
`∫₀¹ Ham i (t, γ i t) dt` converge to `∫₀¹ Ham₀ (t, x) dt` (as they do under
`TauCeti.tendsto_intervalIntegral_of_tendstoUniformlyOn`), then the actions `A_{Ham i}(γ i)`
converge to the action `-∫₀¹ Ham₀ (t, x) dt` of the constant loop at `x`. -/
theorem IsWeaklyExact.tendsto_contractibleLoopAction (hω : IsSmoothForm I 0 ω)
    (hw : IsWeaklyExact ω) {ι : Type*} {l : Filter ι} {γ : ι → ℝ → M} {x : M}
    {Ham : ι → ℝ → M → ℝ} {Ham₀ : ℝ → M → ℝ}
    (hx : ∀ U ∈ 𝓝 x, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, γ i t ∈ U)
    (hK : ∃ K, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (extChartAt I x ∘ γ i) t‖ ≤ K)
    (hHam : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, Ham i t (γ i t)) l
      (𝓝 (∫ t in (0 : ℝ)..1, Ham₀ t x))) :
    Tendsto (fun i ↦ contractibleLoopAction ω (Ham i) (γ i)) l
      (𝓝 (contractibleLoopAction ω Ham₀ fun _ ↦ x)) := by
  rw [hw.contractibleLoopAction_const, ← zero_sub]
  exact ((hw.tendsto_capArea_nhds_zero hω hx hK).sub hHam).congr fun i ↦
    (contractibleLoopAction_def _ _ _).symm

end Action

namespace SmoothTwoForm

open scoped ContDiff

variable [I.Boundaryless] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

/-- **Limits of actions at a constant periodic orbit lie in the spectrum.** Let `σ` be a weakly
exact two-form on a boundaryless manifold, and suppose that the constant loop at `x` is a
contractible `1`-periodic orbit of the Hamiltonian `Ham₀`. If loops `γ i` converge uniformly on
`[0, 1]` to it with eventually bounded speeds in the preferred chart at `x`, the Hamiltonian terms
`∫₀¹ Ham i (t, γ i t) dt` converge to `∫₀¹ Ham₀ (t, x) dt`, and the actions `A_{Ham i}(γ i)`
converge to `a`, then `a` lies in the contractible action spectrum of `Ham₀`. -/
theorem mem_contractibleActionSpectrum_of_tendsto (hw : IsWeaklyExact σ.1) {ι : Type*}
    {l : Filter ι} [l.NeBot] {γ : ι → ℝ → M} {x : M} {Ham : ι → ℝ → M → ℝ}
    {Ham₀ : ℝ → M → ℝ} {a : ℝ}
    (horbit : (fun _ ↦ x) ∈
      contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham₀ t)) 1)
    (hx : ∀ U ∈ 𝓝 x, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, γ i t ∈ U)
    (hK : ∃ K, ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (extChartAt I x ∘ γ i) t‖ ≤ K)
    (hHam : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, Ham i t (γ i t)) l
      (𝓝 (∫ t in (0 : ℝ)..1, Ham₀ t x)))
    (ha : Tendsto (fun i ↦ contractibleLoopAction σ.1 (Ham i) (γ i)) l (𝓝 a)) :
    a ∈ σ.contractibleActionSpectrum Ham₀ := by
  have hω : IsSmoothForm I 0 σ.1 := σ.isSmoothForm.of_le (by simp)
  rw [tendsto_nhds_unique ha (hw.tendsto_contractibleLoopAction hω hx hK hHam)]
  exact hw.contractibleLoopAction_mem_contractibleActionSpectrum horbit
    (isLoopCylinder_const x).isCap

end SmoothTwoForm

end TauCeti
