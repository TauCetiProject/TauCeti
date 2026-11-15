/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.Lp.BilinearMap

/-!
# A Poincaré inequality for Schrödinger forms with a potential positive at infinity

On the whole of a finite-dimensional space no Poincaré inequality `‖u‖₂ ≤ C ‖Du‖₂` holds
(`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`). A nonnegative potential `P` that is
bounded below by a constant `a > 0` outside a ball restores it: there is `c > 0` with

`c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²`

for every compactly supported `C¹` map `u`. In other words the quadratic form of the
Schrödinger operator `-Δ + P` is bounded below by `c` times the squared `L²` norm, so `-Δ + P` has a
spectral gap, although `P` may vanish on a large set inside the ball. The constant depends on
`P` only through `a` and the radius of the ball.

Outside a ball `Ω` containing the ball where `P` may be small, the potential term alone controls
`‖u‖²`. Inside `Ω`, the Poincaré–Wirtinger inequality with the mean taken over the annulus
`S ⊆ Ω` on which `P ≥ a` controls the deviation of `u` from that mean by `Du`, and the mean itself
is controlled by the integral of `‖u‖²` over `S`, hence again by the potential term
(`TauCeti.setIntegral_norm_sq_le_of_convex`).

Such an estimate makes `L L*` coercive for a first-order operator `L` whose Weitzenböck formula
has a potential of this kind.

For an essentially bounded potential `P` on an inner product space, the inequality extends by
density of test functions (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`) to the bounded
Schrödinger form `TauCeti.schrodingerForm`, `(u, v) ↦ ∫ ⟪∇u, ∇v⟫ + ∫ P u v`, on all of
`H¹(E) = W^{1,2}(E)`, which is then coercive.

## Main results

* `TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`:
  the inequality above.
* `TauCeti.schrodingerForm`: the Schrödinger form of a bounded potential as a continuous
  bilinear form on `H¹(E)`.
* `TauCeti.integral_value_mul_eq_schrodingerForm`: testing `u ∈ H¹(E)` against `-Δφ + P φ` for
  a test function `φ` is the Schrödinger form of `u` and `φ`, the link with the weak formulation
  of `-Δh + P h = g`.
* `TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`: the inequality
  on `H¹(E)`, `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ P u²`.
* `TauCeti.isCoercive_schrodingerForm`: the Schrödinger form is coercive on `H¹(E)`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16 (the Poincaré–Wirtinger inequality used inside the ball).
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal

section TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Poincaré inequality for a Schrödinger form.** Let `P` be locally integrable, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of radius
`R`. Then there is `c > 0` such that `c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²` for every compactly
supported `C¹` map `u`. -/
theorem exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
    {P : E → ℝ} (hP : LocallyIntegrable P μ) (hP₀ : ∀ᵐ z ∂μ, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (haP : ∀ᵐ z ∂μ, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      c * ∫ z, ‖u z‖ ^ 2 ∂μ ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ + ∫ z, P z * ‖u z‖ ^ 2 ∂μ := by
  -- `Ω` is a ball beyond the radius `R`, and `S ⊆ Ω` the annulus on which `P ≥ a`.
  set ρ := max R 0
  set Ω := ball (0 : E) (ρ + 1)
  set S := Ω ∩ (closedBall (0 : E) ρ)ᶜ
  have hSΩ : S ⊆ Ω := inter_subset_left
  have hS : MeasurableSet S := measurableSet_ball.inter measurableSet_closedBall.compl
  have hρR : R ≤ ρ := le_max_left R 0
  have haS : ∀ᵐ z ∂μ, z ∈ S → a ≤ P z := haP.mono fun z h hz ↦
    h (hρR.trans_lt (by simpa using hz.2 : ρ < ‖z‖))
  have haΩ : ∀ᵐ z ∂μ, z ∈ Ωᶜ → a ≤ P z := haP.mono fun z h hz ↦ by
    have : ρ + 1 ≤ ‖z‖ := by simpa [Ω] using hz
    exact h (by linarith)
  have hS₀ : μ S ≠ 0 := by
    refine (isOpen_ball.inter isClosed_closedBall.isOpen_compl).measure_ne_zero μ ?_
    obtain ⟨v, hv⟩ := exists_norm_eq E (by positivity : 0 ≤ ρ + 1 / 2)
    exact ⟨v, by simp only [mem_ball_zero_iff, hv]; linarith,
      by simp only [mem_compl_iff, mem_closedBall_zero_iff, hv, not_le]; linarith⟩
  -- The constants of the Poincaré inequality on `Ω` relative to `S`.
  set A := (2 + 4 * μ.real Ω / μ.real S) *
    (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) ^ 2
  set B := 4 * μ.real Ω / μ.real S
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  refine ⟨a / (a * A + B + 1), by positivity, fun u hu hc ↦ ?_⟩
  have hn : HasCompactSupport fun z ↦ ‖u z‖ ^ 2 := hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
  have hI : Integrable (fun z ↦ ‖u z‖ ^ 2) μ :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hn
  have hDc : Continuous fun z ↦ ‖fderiv ℝ u z‖ ^ 2 := (hu.continuous_fderiv one_ne_zero).norm.pow 2
  have hDs : HasCompactSupport fun z ↦ ‖fderiv ℝ u z‖ ^ 2 :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ ‖L‖ ^ 2) (by simp)
  have hD : Integrable (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) μ := hDc.integrable_of_hasCompactSupport hDs
  have hQ : Integrable (fun z ↦ P z * ‖u z‖ ^ 2) μ :=
    hP.integrable_smul_right_of_hasCompactSupport (g := fun z ↦ ‖u z‖ ^ 2)
      (hu.continuous.norm.pow 2) hn
  have hQ₀ : ∀ᵐ z ∂μ, 0 ≤ P z * ‖u z‖ ^ 2 := hP₀.mono fun z h ↦ mul_nonneg h (by positivity)
  -- Inside `Ω`, the Poincaré inequality relative to `S`.
  have hΩ := setIntegral_norm_sq_le_of_convex (μ := μ) (convex_ball 0 (ρ + 1))
    isBounded_ball hu hSΩ hS₀
  have hDΩ : ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 ∂μ ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ :=
    setIntegral_le_integral hD (ae_of_all _ fun _ ↦ by positivity)
  -- Where `P ≥ a`, the potential term controls `‖u‖²`.
  have hpot {T : Set E} (hT : MeasurableSet T) (haT : ∀ᵐ z ∂μ, z ∈ T → a ≤ P z) :
      a * ∫ z in T, ‖u z‖ ^ 2 ∂μ ≤ ∫ z in T, P z * ‖u z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on_ae (hI.integrableOn.const_mul a) hQ.integrableOn hT
      (haT.mono fun z h hz ↦ mul_le_mul_of_nonneg_right (h hz) (by positivity))
  have hYS := (hpot hS haS).trans (setIntegral_mono_set hQ.integrableOn (ae_restrict_of_ae hQ₀)
    hSΩ.eventuallySubset)
  have hYC := hpot measurableSet_ball.compl haΩ
  have hQΩ : 0 ≤ ∫ z in Ω, P z * ‖u z‖ ^ 2 ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hQ₀)
  have hQC : 0 ≤ ∫ z in Ωᶜ, P z * ‖u z‖ ^ 2 ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hQ₀)
  have hD₀ : 0 ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ := integral_nonneg fun _ ↦ by positivity
  -- Combine: `a ∫ ‖u‖² ≤ (a A + B + 1) (∫ ‖Du‖² + ∫ P ‖u‖²)`.
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity),
    ← integral_add_compl measurableSet_ball hI, ← integral_add_compl measurableSet_ball hQ]
  nlinarith [mul_le_mul_of_nonneg_left hΩ ha.le,
    mul_le_mul_of_nonneg_left hDΩ (mul_nonneg ha.le hA), mul_le_mul_of_nonneg_left hYS hB,
    mul_nonneg (by positivity : 0 ≤ a * A + 1) hQΩ,
    mul_nonneg (by positivity : 0 ≤ a * A + B) hQC, mul_nonneg (by positivity : 0 ≤ B + 1) hD₀]

end TestFunction

/-! ### The Schrödinger form on `H¹(E)` -/

section W1p

open Filter TopologicalSpace
open scoped InnerProductSpace RealInnerProductSpace Laplacian Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {P : E → ℝ}

/-- The **Schrödinger form** `(u, v) ↦ ∫ ⟪∇u, ∇v⟫ + ∫ P u v` of an essentially bounded potential
`P`, as a continuous bilinear form on `H¹(E) = W^{1,2}(E)`. It is the `L²` inner product of the
gradients plus the `L∞`-coefficient form `TauCeti.lpBilinearMap` of `P` on the values, pulled
back along `u ↦ (∇u, u)`. -/
noncomputable def schrodingerForm (hP : MemLp P ⊤ (volume : Measure E)) :
    W1p (volume : Measure E) ⊤ 2 →L[ℝ] W1p (volume : Measure E) ⊤ 2 →L[ℝ] ℝ :=
  let μ := (volume : Measure E).restrict (⊤ : Opens E)
  let fst := ContinuousLinearMap.fst ℝ (Lp E 2 μ) (Lp ℝ 2 μ)
  let snd := ContinuousLinearMap.snd ℝ (Lp E 2 μ) (Lp ℝ 2 μ)
  let J := W1p.gradientL.prod W1p.valueL
  let V := lpBilinearMap (p := 2) (q := 2) μ ((hP.restrict _).smul_mul.toLp _)
  ((innerSL ℝ).bilinearComp (σ₁₃ := RingHom.id ℝ) fst fst + V.bilinearComp snd snd).bilinearComp J J

/-- The Schrödinger form is the integral of `⟪∇u, ∇v⟫ + P u v`. -/
theorem schrodingerForm_apply (hP : MemLp P ⊤ (volume : Measure E))
    (u v : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u v = (∫ z, ⟪W1p.gradient u z, W1p.gradient v z⟫) +
      ∫ z, P z * (W1p.value u z * W1p.value v z) := by
  simp only [schrodingerForm, ContinuousLinearMap.bilinearComp_apply, add_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    lpBilinearMap_apply, W1p.gradientL_apply, W1p.valueL_apply]
  rw [innerSL_apply_apply, L2.inner_def]
  have hB := MemLp.coeFn_toLp (E := ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (hP.restrict ((⊤ : Opens E) : Set E)).smul_mul
  simp only [Opens.coe_top, Measure.restrict_univ] at hB ⊢
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hB] with z hz
  simp [hz]

/-- The Schrödinger form on the diagonal is `‖∇u‖₂² + ∫ P u²`. -/
theorem schrodingerForm_self (hP : MemLp P ⊤ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u u = ‖W1p.gradient u‖ ^ 2 + ∫ z, P z * W1p.value u z ^ 2 := by
  rw [schrodingerForm_apply, ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [Opens.coe_top, Measure.restrict_univ, real_inner_self_eq_norm_sq, sq]

/-- For `u ∈ H¹(E)`, testing `u` against `-Δφ + P φ` is the Schrödinger form of `u` and `φ`. -/
theorem integral_value_mul_eq_schrodingerForm (hP : MemLp P ⊤ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      schrodingerForm hP u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) := by
  have hu : MemLp (W1p.value u : E → ℝ) 2 volume := W1p.memLp_value u
  have hφ2 : MemLp (φ : E → ℝ) 2 volume :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hΔ2 : MemLp (Δ (φ : E → ℝ)) 2 volume :=
    (φ.contDiff.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport
      φ.hasCompactSupport.laplacian
  have hibp := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ
  simp only [smul_eq_mul] at hibp
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  have hg := W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_apply]
  have e1 : ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      -(∫ z, Δ (φ : E → ℝ) z * W1p.value u z) + ∫ z, P z * (W1p.value u z * φ z) := by
    rw [← integral_neg, ← integral_add (f := fun z ↦ -(Δ (φ : E → ℝ) z * W1p.value u z))
      (hΔ2.integrable_mul hu).neg
        (memLp_one_iff_integrable.1 (hP.fun_mul (hu.fun_mul hφ2 : MemLp _ 1 volume)))]
    exact integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [e1, hibp, neg_neg]
  congr 1
  · refine integral_congr_ae (hg.mono fun z hz ↦ ?_)
    simp only [hz, real_inner_comm]
  · exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- The Poincaré inequality for the Schrödinger form, extended from test functions to all of
`H¹(E)` by density. -/
private theorem mul_norm_value_sq_le_schrodingerForm [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖W1p.value u‖ ^ 2 ≤ schrodingerForm hP u u := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := volume) (F := ℝ) (hP.locallyIntegrable le_top) hP₀ ha hPa
  refine ⟨c, hc, fun u ↦ ?_⟩
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
    u (isClosed_le (continuous_const.mul
      (((W1p.valueL (mu := volume) (Omega := ⊤) (p := 2)).continuous.congr
        W1p.valueL_apply).norm.pow 2))
      ((schrodingerForm hP).continuous.clm_apply continuous_id)) fun φ ↦ ?_
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_self, W1p.norm_value_ofTestFunctionₗ_top_sq,
    W1p.norm_gradient_ofTestFunctionₗ_top_sq]
  have h := hgap φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  simp only [Real.norm_eq_abs, sq_abs] at h
  convert h using 2
  exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- **The Poincaré inequality for a Schrödinger form on `H¹(E)`.** Let `P` be essentially
bounded, almost everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed
ball of radius `R`. Then there is `c > 0` with `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ P u²` for every
`u ∈ H¹(E)`. -/
theorem exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 + ∫ z, P z * W1p.value u z ^ 2 := by
  obtain ⟨c, hc, hgap⟩ := mul_norm_value_sq_le_schrodingerForm hP hP₀ ha hPa
  refine ⟨min 1 c / 2, by positivity, fun u ↦ ?_⟩
  have hgap := hgap u
  rw [schrodingerForm_self] at hgap
  have hpot : 0 ≤ ∫ z, P z * W1p.value u z ^ 2 :=
    integral_nonneg_of_ae (hP₀.mono fun z hz ↦ by positivity)
  have h1 : min 1 c ≤ 1 := min_le_left _ _
  have h2 : min 1 c ≤ c := min_le_right _ _
  have _ : 0 ≤ min 1 c := le_min zero_le_one hc.le
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  nlinarith [sq_nonneg ‖W1p.value u‖, sq_nonneg ‖W1p.gradient u‖,
    mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖W1p.value u‖),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖W1p.gradient u‖)]

/-- **Coercivity of the Schrödinger form.** Under the hypotheses of
`TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`, the Schrödinger
form is coercive on `H¹(E)`. -/
theorem isCoercive_schrodingerForm [Nontrivial E] (hP : MemLp P ⊤ (volume : Measure E))
    (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    IsCoercive (schrodingerForm hP) := by
  obtain ⟨c, hc, h⟩ :=
    exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq hP hP₀ ha hPa
  exact ⟨c, hc, fun u ↦ by rw [schrodingerForm_self, mul_assoc, ← sq]; exact h u⟩

end W1p

end TauCeti
