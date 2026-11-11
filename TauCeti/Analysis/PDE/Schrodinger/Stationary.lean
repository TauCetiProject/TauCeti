/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
public import TauCeti.Analysis.Sobolev.Poincare.Schrodinger
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.Lp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Analysis.InnerProductSpace.WeakSolution
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The stationary Schrödinger equation with a potential positive at infinity

Let `P` be a continuous nonnegative potential which is at least a constant `a > 0` outside a ball.
The Schrödinger operator `-Δ + P` then has a spectral gap: its quadratic form is bounded below by
a positive multiple of the squared `L²` norm
(`TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`).
This file solves the equation

`Δu = P u + g`

in `L²`, although `P` may vanish on a large set.

* `TauCeti.exists_pos_mul_integral_sq_le_integral_mul_neg_laplacian_add_mul`: on a
  finite-dimensional real inner product space, `c ∫ φ² ≤ ∫ φ (-Δφ + P φ)` for compactly supported
  `C²` functions `φ`, by the spectral gap and Green's identity.
* `TauCeti.exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq`: there is a bounded
  operator `Q` on `L²` such that `Q f` is a weak solution of `-Δu + P u = f`:
  `∫ Q f (-Δφ + P φ) = ∫ f φ` for every compactly supported `C²` function `φ`. Indeed
  `c ‖φ‖₂ ≤ ‖-Δφ + Pφ‖₂`, so
  `LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le` applies.
* `TauCeti.exists_contDiff_laplacian_eq_mul_add`: in the plane, if moreover `P` is bounded and
  `P` and `g` are `Cᵏ` with `k ≥ 1`, and `g ∈ L²`, there is a `Cᵏ⁺¹` solution `u` of
  `Δu = P u + g` at every point with `u ∈ L²`, `Du ∈ L²` and `u → 0` at infinity. The weak
  solution satisfies `-Δu + u = (1 - P) u - g ∈ L²` as a tempered distribution, so it lies in
  `H²` by the resolvent of the Laplacian; `H²` embeds in the continuous functions vanishing at
  infinity in the plane, and the planar Poisson bootstrap
  (`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`) makes the continuous
  representative `Cᵏ⁺¹`.

In the analysis of plane vortices the potential is `P = |α|² / 4`, which vanishes at the zeros of
the section `α` and tends to `1 / 4` at infinity, and the equation `Δη = P η` describes the
kernel of the linearized vortex operator off those zeros.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.2 (weak solutions) and Lemma 4.1.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti

open MeasureTheory Filter Module TemperedDistribution Topology
open scoped Laplacian Gradient RealInnerProductSpace ContDiff ZeroAtInfty SchwartzMap
  Distributions

section WeakSolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {P : E → ℝ}

/-- The compactly supported `C²` test functions on `E`. -/
private abbrev TestFn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  TestFunction (⊤ : TopologicalSpace.Opens E) ℝ 2

omit [Nontrivial E] in
private theorem memLp_schrodinger (hP : Continuous P) (φ : TestFn E) :
    MemLp (fun z ↦ -Δ (φ : E → ℝ) z + P z * φ z) 2 μ :=
  (φ.contDiff.continuous_laplacian.neg.add (hP.mul φ.continuous)).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.laplacian.neg.add φ.hasCompactSupport.mul_left)

omit [Nontrivial E] in
/-- The Schrödinger operator `φ ↦ -Δφ + P φ` on test functions, with values in `L²`. -/
private noncomputable def schrodingerToLp (μ : Measure E) [μ.IsAddHaarMeasure]
    (hP : Continuous P) : TestFn E →ₗ[ℝ] Lp ℝ 2 μ where
  toFun φ := (memLp_schrodinger (μ := μ) hP φ).toLp _
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    have hφ := (φ.contDiff (n := 2)).contDiffAt (x := z)
    have hψ := (ψ.contDiff (n := 2)).contDiffAt (x := z)
    simp only [FunLike.coe_add, Pi.add_apply, hφ.laplacian_add hψ]
    ring
  map_smul' t φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      InnerProductSpace.laplacian_smul t ((φ.contDiff (n := 2)).contDiffAt (x := z))]
    ring

omit [Nontrivial E] in
private theorem schrodingerToLp_apply (hP : Continuous P) (φ : TestFn E) :
    schrodingerToLp μ hP φ = (memLp_schrodinger hP φ).toLp _ :=
  (rfl)

/-- **The Schrödinger operator is bounded below.** Let `P` be continuous and nonnegative, with
`P ≥ a > 0` outside a ball. There is `c > 0` with `c ∫ φ² ≤ ∫ φ (-Δφ + P φ)` for every compactly
supported `C²` function `φ`. -/
theorem exists_pos_mul_integral_sq_le_integral_mul_neg_laplacian_add_mul (hP : Continuous P)
    (hP₀ : ∀ z, 0 ≤ P z) {a R : ℝ} (ha : 0 < a) (haP : ∀ z, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      c * ∫ z, φ z ^ 2 ∂μ ≤ ∫ z, φ z * (-Δ φ z + P z * φ z) ∂μ := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := μ) (F := ℝ) hP.locallyIntegrable (ae_of_all _ hP₀) ha (ae_of_all _ haP)
  refine ⟨c, hc, fun φ hφ hφc ↦ ?_⟩
  -- Green's identity turns `∫ |∇φ|²` into `-∫ φ Δφ`.
  have hgreen := integral_inner_gradient_eq_neg_integral_mul_laplacian (μ := μ) hφ
    (hφ.of_le (by norm_num)) hφc
  have hnorm : ∫ z, ‖fderiv ℝ φ z‖ ^ 2 ∂μ = ∫ z, ⟪∇ φ z, ∇ φ z⟫ ∂μ :=
    integral_congr_ae (ae_of_all _ fun z ↦ by
      simp only [real_inner_self_eq_norm_sq, norm_gradient_eq_norm_fderiv])
  have hint (f : E → ℝ) (hf : Continuous f) : Integrable (fun z ↦ φ z * f z) μ :=
    (hφ.continuous.mul hf).integrable_of_hasCompactSupport hφc.mul_right
  have hP2 : Integrable (fun z ↦ P z * φ z ^ 2) μ :=
    (hint (fun z ↦ P z * φ z) (hP.mul hφ.continuous)).congr (ae_of_all _ fun z ↦ by ring)
  have hsplit : ∫ z, φ z * (-Δ φ z + P z * φ z) ∂μ =
      -∫ z, φ z * Δ φ z ∂μ + ∫ z, P z * φ z ^ 2 ∂μ := by
    rw [neg_add_eq_sub, ← integral_sub hP2 (hint _ hφ.continuous_laplacian)]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  have h := hgap φ (hφ.of_le (by norm_num)) hφc
  simp only [Real.norm_eq_abs, sq_abs] at h
  rwa [hsplit, ← hgreen, ← hnorm]

/-- **Weak solutions of the stationary Schrödinger equation.** Let `P` be continuous and
nonnegative, with `P ≥ a > 0` outside a ball. There is a bounded operator `Q` on `L²(μ)` such
that `Q f` is a weak solution of `-Δu + P u = f` for every `f ∈ L²`:
`∫ Q f (-Δφ + P φ) = ∫ f φ` for every compactly supported `C²` function `φ`. -/
theorem exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq (hP : Continuous P)
    (hP₀ : ∀ z, 0 ≤ P z) {a R : ℝ} (ha : 0 < a) (haP : ∀ z, R < ‖z‖ → a ≤ P z) :
    ∃ Q : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ, ∀ (f : Lp ℝ 2 μ) (φ : E → ℝ), ContDiff ℝ 2 φ →
      HasCompactSupport φ → ∫ z, Q f z * (-Δ φ z + P z * φ z) ∂μ = ∫ z, f z * φ z ∂μ := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_sq_le_integral_mul_neg_laplacian_add_mul (μ := μ) hP hP₀ ha haP
  let S := schrodingerToLp μ hP
  let ι := (TestFunction.ambientToLp 2 μ : TestFn E →L[ℝ] Lp ℝ 2 μ).toLinearMap
  have hS (u : Lp ℝ 2 μ) (φ : TestFn E) :
      ⟪u, S φ⟫ = ∫ z, u z * (-Δ (φ : E → ℝ) z + P z * φ z) ∂μ := by
    rw [schrodingerToLp_apply, L2.inner_toLp u (memLp_schrodinger hP φ)]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  have hι (u : Lp ℝ 2 μ) (φ : TestFn E) : ⟪u, ι φ⟫ = ∫ z, u z * φ z ∂μ := by
    rw [ContinuousLinearMap.coe_coe, TestFunction.inner_ambientToLp]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  -- The lower bound gives `c ‖φ‖₂² ≤ ⟪φ, -Δφ + P φ⟫ ≤ ‖φ‖₂ ‖-Δφ + P φ‖₂`.
  have hbound (φ : TestFn E) : c * ‖ι φ‖ ≤ ‖S φ‖ := by
    have hsq : ‖ι φ‖ ^ 2 = ∫ z, φ z ^ 2 ∂μ := by
      simpa only [ι, ContinuousLinearMap.coe_coe, Real.norm_eq_abs, sq_abs] using
        TestFunction.norm_ambientToLp_sq (ν := μ) φ
    have hae : ∫ z, (ι φ : Lp ℝ 2 μ) z * (-Δ (φ : E → ℝ) z + P z * φ z) ∂μ =
        ∫ z, φ z * (-Δ (φ : E → ℝ) z + P z * φ z) ∂μ :=
      integral_congr_ae ((TestFunction.coeFn_ambientToLp (ν := μ) φ).mono fun z hz ↦ by
        simp only [ι, ContinuousLinearMap.coe_coe] at hz ⊢
        rw [hz])
    have hinner : c * ‖ι φ‖ ^ 2 ≤ ⟪ι φ, S φ⟫ := by
      rw [hS, hae, hsq]
      exact hgap φ φ.contDiff φ.hasCompactSupport
    have hcs := hinner.trans (real_inner_le_norm (ι φ) (S φ))
    rcases (norm_nonneg (ι φ)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · nlinarith
  obtain ⟨Q, -, -, hQ⟩ :=
    LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le S ι hc hbound
  refine ⟨Q, fun f φ hφ hφc ↦ ?_⟩
  have h := hQ f ⟨φ, hφ, hφc, by simp⟩
  rwa [hS, hι] at h

end WeakSolution

section Plane

variable {P g : ℂ → ℝ}

/-- An `L²` weak solution of `-Δu + P u = -g` in the plane, with `P` bounded and `g ∈ L²`, lies in
`H² = W^{2,2}`. -/
private theorem exists_wkp_value_ae_eq {C : ℝ} (hP : Continuous P) (hPC : ∀ z, |P z| ≤ C)
    (hg2 : MemLp g 2) (u : Lp ℝ 2 (volume : Measure ℂ))
    (hu : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, Δ φ z * u z = ∫ z, φ z * (P z * u z + g z)) :
    ∃ W : Wkp (volume : Measure ℂ) ⊤ 2 2, (Wkp.value 2 W : ℂ → ℝ) =ᵐ[volume] u := by
  have hPu : MemLp (fun z ↦ P z * u z) 2 volume :=
    (Lp.memLp u).of_le_mul (c := C) (hP.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
      (ae_of_all _ fun z ↦ by rw [norm_mul, Real.norm_eq_abs]; gcongr; exact hPC z)
  have hR : MemLp (fun z ↦ u z - (P z * u z + g z)) 2 volume :=
    (Lp.memLp u).sub (hPu.add hg2)
  set T : 𝓢'(ℂ, ℂ) := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)
  -- Hence `-Δu + u = u - (P u + g)` as tempered distributions.
  have hT : -Δ T + (1 : ℝ) • T =
      Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (hR.toLp _)) := by
    refine ext_real fun φ hφ ↦ ?_
    have hφ2 := φ.memLp 2 (μ := volume)
    have hu' := hu φ ((φ.smooth ⊤).of_le (by norm_cast)) hφ
    rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM, one_smul]
    simp only [SchwartzMap.laplacian_apply]
    have hR' : ∫ z, φ z * (hR.toLp _ : Lp ℝ 2 volume) z =
        (∫ z, φ z * u z) - ∫ z, φ z * (P z * u z + g z) := by
      have h₁ : Integrable (fun z ↦ φ z * u z) volume := hφ2.integrable_mul (Lp.memLp u)
      have h₂ : Integrable (fun z ↦ φ z * (P z * u z + g z)) volume :=
        hφ2.integrable_mul (hPu.add hg2)
      exact (integral_congr_ae (hR.coeFn_toLp.mono fun z hz ↦ by rw [hz]; dsimp only; ring)).trans
        (integral_sub h₁ h₂)
    rw [hR', hu']
    push_cast
    ring
  have hT2 : MemSobolev ((2 : ℕ) : ℝ) 2 T := by
    have h := (memSobolev_add_two_iff_neg_laplacian_add_smul (s := 0) (c := 1) one_pos).2
      (by rw [hT]; exact memSobolev_zero_iff.2 ⟨_, rfl⟩)
    rwa [zero_add, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
  exact (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num) 2 u).1 hT2

/-- A `C¹` function on the plane agreeing almost everywhere with the value of an `H²` function has
square-integrable derivative. -/
private theorem memLp_fderiv_of_wkp {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v)
    (W : Wkp (volume : Measure ℂ) ⊤ 2 2) (hW : (Wkp.value 2 W : ℂ → ℝ) =ᵐ[volume] v) :
    MemLp (fderiv ℝ v) 2 volume := by
  have hrestrict : (volume : Measure ℂ).restrict ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) =
      volume := by simp
  have hd := W1p.gradient_ae_eq_of_contDiffOn (Wkp.firstOrder 1 W) hv.contDiffOn
    (by rw [Wkp.value_firstOrder]; exact ae_restrict_of_ae hW)
  have hG := Lp.memLp (W1p.gradient (Wkp.firstOrder 1 W))
  -- Forget the dependence of the gradient's type on the restricted measure.
  generalize (W1p.gradient (Wkp.firstOrder 1 W) : ℂ → ℂ) = G at hd hG
  rw [hrestrict] at hd hG
  have h := (InnerProductSpace.toDual ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hG.ae_eq hd)
  exact h.ae_eq (ae_of_all _ fun z ↦ toDual_gradient)

/-- The weak equation `∫ Δφ u = ∫ φ (P u + g)` satisfied by an `L²` weak solution of
`-Δu + P u = -g`. -/
private theorem integral_laplacian_mul_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {P g : E → ℝ} (hP : Continuous P) (hg2 : MemLp g 2 μ)
    {u : Lp ℝ 2 μ} {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hu : ∫ z, u z * (-Δ φ z + P z * φ z) ∂μ = ∫ z, (-hg2.toLp g : Lp ℝ 2 μ) z * φ z ∂μ) :
    ∫ z, Δ φ z * u z ∂μ = ∫ z, φ z * (P z * u z + g z) ∂μ := by
  have hΔ : Integrable (fun z ↦ Δ φ z * u z) μ :=
    (Lp.memLp u).integrable_mul ((hφ.continuous_laplacian).memLp_of_hasCompactSupport (p := 2)
      hφc.laplacian) |>.congr (ae_of_all _ fun z ↦ mul_comm _ _)
  have hPφ : Integrable (fun z ↦ P z * φ z * u z) μ :=
    (Lp.memLp u).integrable_mul ((hP.mul hφ.continuous).memLp_of_hasCompactSupport (p := 2)
      hφc.mul_left) |>.congr (ae_of_all _ fun z ↦ mul_comm _ _)
  have hφg : Integrable (fun z ↦ φ z * g z) μ :=
    (hφ.continuous.memLp_of_hasCompactSupport (p := 2) hφc).integrable_mul hg2
  have hgφ : ∫ z, (-hg2.toLp g : Lp ℝ 2 μ) z * φ z ∂μ = -∫ z, φ z * g z ∂μ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg (hg2.toLp g), hg2.coeFn_toLp] with z h1 h2
    rw [h1, Pi.neg_apply, h2]
    ring
  have hsplit : ∫ z, u z * (-Δ φ z + P z * φ z) ∂μ =
      (∫ z, P z * φ z * u z ∂μ) - ∫ z, Δ φ z * u z ∂μ :=
    (integral_congr_ae (ae_of_all _ fun z ↦ by ring)).trans (integral_sub hPφ hΔ)
  have hsplit' : ∫ z, φ z * (P z * u z + g z) ∂μ =
      (∫ z, P z * φ z * u z ∂μ) + ∫ z, φ z * g z ∂μ :=
    (integral_congr_ae (ae_of_all _ fun z ↦ by ring)).trans (integral_add hPφ hφg)
  rw [hsplit']
  linear_combination hsplit - hu.trans hgφ

/-- **The stationary Schrödinger equation in the plane.** Let `P` be a `Cᵏ` potential, `k ≥ 1`,
which is bounded, nonnegative, and at least `a > 0` outside a ball, and let `g` be a `Cᵏ`
square-integrable source. Then `Δu = P u + g` has a `Cᵏ⁺¹` solution `u` on the plane such that
`u` and its derivative are square integrable and `u → 0` at infinity. -/
theorem exists_contDiff_laplacian_eq_mul_add {k : ℕ∞} (hk : 1 ≤ k) (hP : ContDiff ℝ k P)
    (hP₀ : ∀ z, 0 ≤ P z) {C : ℝ} (hPC : ∀ z, P z ≤ C) {a R : ℝ} (ha : 0 < a)
    (haP : ∀ z, R < ‖z‖ → a ≤ P z) (hg : ContDiff ℝ k g) (hg2 : MemLp g 2) :
    ∃ u : ℂ → ℝ, ContDiff ℝ ((k : ℕ∞ω) + 1) u ∧ MemLp u 2 ∧ MemLp (fderiv ℝ u) 2 ∧
      Tendsto u (cocompact ℂ) (𝓝 0) ∧ ∀ z, Δ u z = P z * u z + g z := by
  have hPc : Continuous P := hP.continuous
  obtain ⟨Q, hQ⟩ := exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq
    (μ := (volume : Measure ℂ)) hPc hP₀ ha haP
  set u := Q (-hg2.toLp g)
  have hu (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      ∫ z, Δ φ z * u z = ∫ z, φ z * (P z * u z + g z) :=
    integral_laplacian_mul_eq hPc hg2 hφ hφc (hQ _ φ hφ hφc)
  obtain ⟨W, hW⟩ := exists_wkp_value_ae_eq hPc (C := max C 0)
    (fun z ↦ by rw [abs_of_nonneg (hP₀ z)]; exact (hPC z).trans (le_max_left _ _)) hg2 u hu
  have hdim : finrank ℝ ℂ < 2 * 2 := by rw [Complex.finrank_real_complex]; norm_num
  set v := Wkp.toZeroAtInfty hdim W
  have huv : (u : ℂ → ℝ) =ᵐ[volume] v := hW.symm.trans (Wkp.value_ae_eq_toZeroAtInfty hdim W)
  -- The continuous representative is a distributional solution, hence `Cᵏ⁺¹` and classical.
  set F : ℂ × ℝ → ℝ := fun p ↦ P p.1 * p.2 + g p.1
  have hF : ContDiff ℝ k F := (hP.comp contDiff_fst).mul contDiff_snd |>.add (hg.comp contDiff_fst)
  have hv (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ)) :
      ∫ x, Δ (φ : ℂ → ℝ) x * v x = ∫ x, φ x * F (x, v x) := by
    have h := hu φ ((φ.contDiff).of_le (by norm_cast)) φ.hasCompactSupport
    have e₁ : ∫ z, Δ (φ : ℂ → ℝ) z * u z = ∫ z, Δ (φ : ℂ → ℝ) z * v z :=
      integral_congr_ae (huv.mono fun z hz ↦ by simp only [hz])
    have e₂ : ∫ z, φ z * (P z * u z + g z) = ∫ z, φ z * F (z, v z) :=
      integral_congr_ae (huv.mono fun z hz ↦ by simp only [hz, F])
    rwa [e₁, e₂] at h
  have hvc : ContinuousOn (v : ℂ → ℝ) (⊤ : TopologicalSpace.Opens ℂ) :=
    v.continuous.continuousOn
  have hsmooth := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp hF.contDiffOn hvc hv
  have heq := eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp
    ((hF.of_le (by exact_mod_cast hk)).contDiffOn) hvc hv
  simp only [TopologicalSpace.Opens.coe_top] at hsmooth heq
  have hv1 : ContDiff ℝ 1 (v : ℂ → ℝ) := (contDiffOn_univ.1 hsmooth).of_le (by
    calc (1 : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hk
      _ ≤ (k : ℕ∞ω) + 1 := le_self_add)
  refine ⟨v, contDiffOn_univ.1 hsmooth, (Lp.memLp u).ae_eq huv,
    memLp_fderiv_of_wkp hv1 W (Wkp.value_ae_eq_toZeroAtInfty hdim W),
    ZeroAtInftyContinuousMap.zero_at_infty' v, fun z ↦ heq (Set.mem_univ z)⟩

end Plane

end TauCeti
