/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Weak
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Complex.Pompeiu.Lp
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.WeakInteriorLp
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Cauchy transform and the divergence-form Laplace equation

Let `ξ` be locally integrable on an open set `Ω ⊆ ℂ` and solve the divergence-form Laplace
equation `Δ ξ = ∂ₛ f + ∂ₜ g` weakly, that is,

`∫ Δφ • ξ = -∫ (∂ₛφ • f + ∂ₜφ • g)` for every test function `φ` on `Ω`.

This file splits `ξ` into a particular solution built from the Cauchy transform
`T h = π⁻¹ ∫ (w - z)⁻¹ h z` and a harmonic remainder, using only `bar∂ (T h) = h` and Weyl's
lemma, with no general second-order theory.

For real `f` and `g` and integrable `h` equal to `f + i g` near the test functions' supports, the
particular solution is `ξ₀ = ½ Re (T h)`. Indeed, for a real test function `φ` put
`ψ = ∂ₛφ - i ∂ₜφ = 2 ∂φ`, so that `bar∂ ψ = Δφ / 2` because `Δ = 4 ∂ bar∂`. The weak form of
`bar∂ (T h) = h` (`TauCeti.integral_conjWirtingerDeriv_smul_cauchyTransform`) gives
`∫ (Δφ / 2) T h = -∫ ψ h`, and taking real parts,
`∫ Δφ • Re (T h) = -2 ∫ (∂ₛφ • Re h + ∂ₜφ • Im h)`
(`TauCeti.integral_laplacian_smul_re_cauchyTransform`). Hence `ξ - ξ₀` is weakly harmonic, and
by Weyl's lemma it agrees almost everywhere with a harmonic function.

In practice `h = χ (f + i g)` for a cutoff `χ` equal to `1` on the region of interest. For
vector-valued data the construction is applied in coordinates, with `χ` the indicator of the
closure of an open set `U ⋐ Ω`: since `f, g ∈ Lʳ_loc(Ω)`, the data is compactly supported and in
`Lʳ`, so `ξ₀` is locally `Lʳ` on the whole plane.

## Main results

* `TauCeti.integral_laplacian_smul_re_cauchyTransform`: `Re (T h)` solves
  `Δ u = 2 (∂ₛ Re h + ∂ₜ Im h)` weakly.
* `TauCeti.integral_laplacian_smul_half_re_cauchyTransform`: `½ Re (T h)` solves
  `Δ u = ∂ₛ f + ∂ₜ g` weakly where `h = f + i g`.
* `TauCeti.weaklyHarmonicOn_sub_half_re_cauchyTransform`: the remainder `ξ - ½ Re (T h)` is
  weakly harmonic.
* `TauCeti.memLpLoc_cauchyTransform`: the Cauchy transform of compactly supported `Lᵖ` data is
  locally `Lᵖ`.
* `TauCeti.exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq`: the
  decomposition `ξ = ξ₀ + v` on every `U ⋐ Ω` for finite-dimensional real coefficients, with
  `ξ₀ ∈ Lʳ_loc` and `v` harmonic.
* `TauCeti.exists_ae_eq_add_harmonicOnNhd_norm_fderiv_le_of_integral_laplacian_smul_eq`: on a
  ball, together with the mean-value bounds on `v` and its derivative on a smaller closed ball,
  with a constant independent of the data.
* `TauCeti.exists_integral_laplacian_smul_re_cauchyTransform_ne`: the factor `½` cannot be
  dropped.

The derivative of `ξ₀` lies in `Lʳ` for `1 < r < ∞` by the boundedness of the Beurling transform
on `Lʳ`; that `W^{1,r}` statement is not part of this file.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2 and B.4.
-/

public noncomputable section

open MeasureTheory Complex Set Metric Function TopologicalSpace InnerProductSpace Laplacian
open scoped ENNReal NNReal Real Distributions ContDiff

namespace TauCeti

/-- `ψ = ∂ₛφ - i ∂ₜφ`, which is `2 ∂φ`, has `bar∂ ψ = Δφ / 2` for a real `C²` function `φ`. -/
private theorem conjWirtingerDeriv_fderiv_sub_I_mul_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (w : ℂ) :
    conjWirtingerDeriv (fun z ↦ (fderiv ℝ φ z 1 : ℂ) - I * (fderiv ℝ φ z I : ℂ)) w 1 =
      (2 : ℂ)⁻¹ * (Δ φ w : ℂ) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero w
  have hline (v : ℂ) : HasFDerivAt (fun z ↦ ((fderiv ℝ φ z v : ℝ) : ℂ))
      (ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ φ) w))) w :=
    ofRealCLM.hasFDerivAt.comp w
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp w hd.hasFDerivAt)
  have hψ : HasFDerivAt (fun z ↦ (fderiv ℝ φ z 1 : ℂ) - I * (fderiv ℝ φ z I : ℂ)) _ w :=
    (hline 1).sub ((hline I).const_mul I)
  have hca : ContDiffAt ℝ 2 φ w := hφ.contDiffAt
  have hsymm := hca.isSymmSndFDerivAt (by simp) I 1
  rw [conjWirtingerDeriv_apply, hψ.fderiv, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, sub_apply,
    smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply, ofRealCLM_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, ofReal_add, smul_eq_mul]
  rw [hsymm]
  ring_nf
  rw [I_sq]
  ring

/-- **The real part of the Cauchy transform against the Laplacian.** For integrable complex data
`h` and a compactly supported real `C²` function `φ`,
`∫ Δφ • Re (T h) = -2 ∫ (∂ₛφ • Re h + ∂ₜφ • Im h)`.
Writing `h = f + i g`, this says that `Re (T h)` solves `Δ u = 2 (∂ₛ f + ∂ₜ g)` weakly; the factor
`2` comes from `Δ = 4 ∂ bar∂` and `bar∂ (T h) = h`. -/
theorem integral_laplacian_smul_re_cauchyTransform {h : ℂ → ℂ} (hh : Integrable h) {φ : ℂ → ℝ}
    (hc : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ) :
    ∫ w, Δ φ w • (cauchyTransform h w).re =
      -(2 : ℝ) * ∫ z, (fderiv ℝ φ z 1 • (h z).re + fderiv ℝ φ z I • (h z).im) := by
  set ψ : ℂ → ℂ := fun z ↦ (fderiv ℝ φ z 1 : ℂ) - I * (fderiv ℝ φ z I : ℂ) with hψ_def
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hline (v : ℂ) : ContDiff ℝ 1 fun z ↦ ((fderiv ℝ φ z v : ℝ) : ℂ) :=
    ofRealCLM.contDiff.comp (hφ1.clm_apply contDiff_const)
  have hψ : ContDiff ℝ 1 ψ := (hline 1).sub (contDiff_const.mul (hline I))
  have hcline (v : ℂ) : HasCompactSupport fun z ↦ ((fderiv ℝ φ z v : ℝ) : ℂ) :=
    ((hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L v) rfl).comp_left ofReal_zero
  have hψc : HasCompactSupport ψ := (hcline 1).sub ((hcline I).mul_left)
  have hcw (w : ℂ) : conjWirtingerDeriv ψ w 1 = (2 : ℂ)⁻¹ * (Δ φ w : ℂ) :=
    conjWirtingerDeriv_fderiv_sub_I_mul_fderiv hφ w
  have key := integral_conjWirtingerDeriv_smul_cauchyTransform hh hψc hψ
  simp only [hcw, smul_eq_mul] at key
  have hΔ : Continuous fun w ↦ (2 : ℂ)⁻¹ * (Δ φ w : ℂ) :=
    continuous_const.mul (continuous_ofReal.comp hφ.continuous_laplacian)
  have hΔc : HasCompactSupport fun w ↦ (2 : ℂ)⁻¹ * (Δ φ w : ℂ) :=
    (hc.laplacian.comp_left ofReal_zero).mul_left
  have hint1 : Integrable fun w ↦ (2 : ℂ)⁻¹ * (Δ φ w : ℂ) * cauchyTransform h w :=
    (locallyIntegrable_cauchyTransform hh).integrable_smul_left_of_hasCompactSupport hΔ hΔc
  have hint2 : Integrable fun z ↦ ψ z * h z := by
    obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    exact hh.bdd_mul hψ.continuous.aestronglyMeasurable (.of_forall hC)
  have e1 : (∫ w, (2 : ℂ)⁻¹ * (Δ φ w : ℂ) * cauchyTransform h w).re =
      ∫ w, (2 : ℝ)⁻¹ * (Δ φ w • (cauchyTransform h w).re) := by
    rw [← RCLike.re_to_complex, ← integral_re hint1]
    congr 1 with w
    simp [mul_assoc]
  have e2 : (∫ z, ψ z * h z).re =
      ∫ z, (fderiv ℝ φ z 1 • (h z).re + fderiv ℝ φ z I • (h z).im) := by
    rw [← RCLike.re_to_complex, ← integral_re hint2]
    congr 1 with z
    simp [ψ]
  have hre := congrArg Complex.re key
  rw [e1, neg_re, e2, integral_const_mul] at hre
  linarith

/-- The Laplacian of a test function on `Ω` against a function locally integrable on `Ω` is
integrable. -/
private theorem integrable_laplacian_smul_of_locallyIntegrableOn {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {Ω : Opens ℂ} {u : ℂ → V} (hu : LocallyIntegrableOn u Ω) (φ : 𝓓(Ω, ℝ)) :
    Integrable fun z ↦ Δ (φ : ℂ → ℝ) z • u z := by
  simpa only [TestFunction.laplacianCLM_apply] using
    TestFunction.integrable_smul (LineDeriv.laplacianCLM ℝ ℂ (𝓓(Ω, ℝ)) φ) hu

/-- Two functions locally integrable on `Ω` with the same distributional Laplacian on `Ω` differ
by a weakly harmonic function. -/
private theorem weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens ℂ} {u₁ u₂ : ℂ → V}
    (h₁ : LocallyIntegrableOn u₁ Ω) (h₂ : LocallyIntegrableOn u₂ Ω)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • u₁ z = ∫ z, Δ (φ : ℂ → ℝ) z • u₂ z) :
    WeaklyHarmonicOn volume Ω (u₁ - u₂) := by
  refine weaklyHarmonicOn_iff.2 ⟨h₁.sub h₂, fun φ ↦ ?_⟩
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub (integrable_laplacian_smul_of_locallyIntegrableOn h₁ φ)
    (integrable_laplacian_smul_of_locallyIntegrableOn h₂ φ), h φ, sub_self]

/-- **The particular solution of the divergence-form Laplace equation.** Let `h` be integrable
complex data with `h = f + i g` on `Ω` for real `f` and `g`. Then `ξ₀ = ½ Re (T h)` solves
`Δ ξ₀ = ∂ₛ f + ∂ₜ g` weakly on `Ω`:
`∫ Δφ • ξ₀ = -∫ (∂ₛφ • f + ∂ₜφ • g)` for every test function `φ` on `Ω`. -/
theorem integral_laplacian_smul_half_re_cauchyTransform {Ω : Opens ℂ} {h : ℂ → ℂ}
    (hh : Integrable h) {f g : ℂ → ℝ} (hfg : ∀ z ∈ Ω, h z = f z + I * g z) (φ : 𝓓(Ω, ℝ)) :
    ∫ w, Δ (φ : ℂ → ℝ) w • ((2 : ℝ)⁻¹ * (cauchyTransform h w).re) =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z) := by
  have hcore := integral_laplacian_smul_re_cauchyTransform hh φ.hasCompactSupport
    (φ.contDiff.of_le (by simp))
  have hfg' : (fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z 1 • (h z).re + fderiv ℝ (φ : ℂ → ℝ) z I • (h z).im) =
      fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z := by
    funext z
    by_cases hz : z ∈ Ω
    · simp [hfg z hz]
    · have hz' : z ∉ tsupport (φ : ℂ → ℝ) := fun h' ↦ hz (φ.tsupport_subset h')
      simp [fderiv_of_notMem_tsupport ℝ hz']
  rw [hfg'] at hcore
  simp_rw [smul_eq_mul, mul_left_comm _ ((2 : ℝ)⁻¹)]
  rw [integral_const_mul]
  simp_rw [smul_eq_mul] at hcore
  rw [hcore]
  ring

/-- **Divergence-form Laplace equation: the harmonic remainder.** Let `ξ` be locally integrable
on `Ω` and solve `Δ ξ = ∂ₛ f + ∂ₜ g` weakly on `Ω`. If integrable complex data `h` agrees with
`f + i g` on an open `Ω'' ≤ Ω`, then `ξ - ½ Re (T h)` is weakly harmonic on `Ω''`. Weyl's lemma
(`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`) then makes it harmonic after modification
on a null set. -/
theorem weaklyHarmonicOn_sub_half_re_cauchyTransform {Ω Ω'' : Opens ℂ} (hΩ : Ω'' ≤ Ω)
    {ξ f g : ℂ → ℝ} (hξ : LocallyIntegrableOn ξ Ω)
    (hdiv : ∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z))
    {h : ℂ → ℂ} (hh : Integrable h) (hfg : ∀ z ∈ Ω'', h z = f z + I * g z) :
    WeaklyHarmonicOn volume Ω'' (ξ - fun w ↦ (2 : ℝ)⁻¹ * (cauchyTransform h w).re) := by
  have hre : LocallyIntegrable fun w ↦ (2 : ℝ)⁻¹ * (cauchyTransform h w).re := by
    refine locallyIntegrable_iff.2 fun K hK ↦ ?_
    have hi := (integrableOn_cauchyTransform hh hK.measure_lt_top.ne).re.const_mul (2 : ℝ)⁻¹
    simpa only [RCLike.re_to_complex, IntegrableOn] using hi
  refine weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq (hξ.mono_set hΩ)
    (hre.locallyIntegrableOn _) fun φ ↦ ?_
  rw [integral_laplacian_smul_half_re_cauchyTransform hh hfg φ]
  exact hdiv ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩

/-- The Cauchy transform of compactly supported `Lᵖ` data, `1 ≤ p ≤ ∞`, is locally `Lᵖ` on every
subset of the plane. -/
theorem memLpLoc_cauchyTransform {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {h : ℂ → F} (hh : MemLp h p) (hc : HasCompactSupport h)
    {U : Set ℂ} : MemLpLoc p U (cauchyTransform h) := by
  have hball (s : Set ℂ) (hs : Bornology.IsBounded s) : ∃ R : ℝ≥0, s ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hs
    exact ⟨R.toNNReal, hR.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal R))⟩
  obtain ⟨r, hr⟩ := hball _ hc.isCompact.isBounded
  refine memLpLoc_iff.2 fun K _ hK ↦ ?_
  obtain ⟨R, hR⟩ := hball K hK.isBounded
  exact (memLp_cauchyTransform (R := R) hp (hh.restrict _)
    ((subset_tsupport h).trans hr)).mono_measure (Measure.restrict_mono hR le_rfl)

/-- The directional derivative of a test function on `Ω` against a function locally integrable on
`Ω` is integrable. -/
private theorem integrable_fderiv_smul_of_locallyIntegrableOn {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {Ω : Opens ℂ} {u : ℂ → V} (hu : LocallyIntegrableOn u Ω) (φ : 𝓓(Ω, ℝ))
    (v : ℂ) : Integrable fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v • u z := by
  have h := TestFunction.integrable_smul (TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) hu
  have hd (z : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) z v = fderiv ℝ (φ : ℂ → ℝ) z v :=
    (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv
  simpa only [TestFunction.coe_lineDerivCLM, hd] using h

/-- **Divergence-form Laplace equation: decomposition.** Let `V` be a finite-dimensional real
normed space, `1 ≤ r ≤ ∞`, and let `ξ`, locally integrable on `Ω`, solve `Δ ξ = ∂ₛ f + ∂ₜ g`
weakly on `Ω` with `f, g ∈ Lʳ_loc(Ω; V)`. On every open `U` with compact closure in `Ω`,
`ξ = ξ₀ + v` almost everywhere, where `ξ₀` is locally `Lʳ` on the whole plane and solves
`Δ ξ₀ = ∂ₛ f + ∂ₜ g` weakly on `U`, `ξ - ξ₀` is weakly harmonic on `U`, and `v` is harmonic on
`U`.

In coordinates, `ξ₀ = ½ Re T (1_{closure U} (f + i g))`, componentwise. -/
theorem exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω U : Opens ℂ}
    (hUc : IsCompact (closure (U : Set ℂ))) (hUΩ : closure (U : Set ℂ) ⊆ Ω) {r : ℝ≥0∞}
    (hr : 1 ≤ r) {ξ f g : ℂ → V}
    (hξ : LocallyIntegrableOn ξ Ω) (hf : MemLpLoc r Ω f) (hg : MemLpLoc r Ω g)
    (hdiv : ∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) :
    ∃ ξ₀ : ℂ → V, MemLpLoc r univ ξ₀ ∧
      (∀ φ : 𝓓(U, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ₀ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) ∧
      WeaklyHarmonicOn volume U (ξ - ξ₀) ∧
      ∃ v : ℂ → V, HarmonicOnNhd v U ∧ ξ =ᵐ[volume.restrict U] ξ₀ + v := by
  classical
  have hLm : MeasurableSet (closure (U : Set ℂ)) := isClosed_closure.measurableSet
  have : IsFiniteMeasure (volume.restrict (closure (U : Set ℂ))) :=
    isFiniteMeasure_restrict.2 hUc.measure_lt_top.ne
  let b := Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  let dat : Fin (Module.finrank ℝ V) → ℂ → ℂ := fun i ↦
    (closure (U : Set ℂ)).indicator fun z ↦ ((c i (f z) : ℝ) : ℂ) + I * ((c i (g z) : ℝ) : ℂ)
  have hdatU (i) : MemLp (fun z ↦ ((c i (f z) : ℝ) : ℂ) + I * ((c i (g z) : ℝ) : ℂ)) r
      (volume.restrict (closure (U : Set ℂ))) :=
    ((c i).comp_memLp' (memLpLoc_iff.1 hf _ hUΩ hUc)).ofReal.add
      (((c i).comp_memLp' (memLpLoc_iff.1 hg _ hUΩ hUc)).ofReal.const_mul I)
  have hdat (i) : MemLp (dat i) r volume :=
    (memLp_indicator_iff_restrict hLm.nullMeasurableSet).2 (hdatU i)
  have hdatc (i) : HasCompactSupport (dat i) :=
    HasCompactSupport.intro hUc fun z hz ↦ indicator_of_notMem hz _
  have hdati (i) : Integrable (dat i) :=
    (integrable_indicator_iff hLm).2 ((hdatU i).integrable hr)
  have hdatfg (i) : ∀ z ∈ U, dat i z = ((c i (f z) : ℝ) : ℂ) + I * ((c i (g z) : ℝ) : ℂ) :=
    fun z hz ↦ indicator_of_mem (subset_closure hz) _
  let ξc : Fin (Module.finrank ℝ V) → ℂ → ℝ := fun i w ↦
    (2 : ℝ)⁻¹ * (cauchyTransform (dat i) w).re
  let ξ₀ : ℂ → V := fun w ↦ ∑ i, ξc i w • b i
  have hξc (i) : MemLpLoc r univ (ξc i) := memLpLoc_iff.2 fun K' hK'u hK' ↦ by
    have h := memLpLoc_iff.1 (memLpLoc_cauchyTransform hr (hdat i) (hdatc i) (U := univ)) K'
      hK'u hK'
    simpa only [RCLike.re_to_complex] using h.re.const_mul (2 : ℝ)⁻¹
  have hξ₀ : MemLpLoc r univ ξ₀ := MemLpLoc.sum _ fun i _ ↦ memLpLoc_iff.2 fun K' hK'u hK' ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (b i)).comp_memLp' (memLpLoc_iff.1 (hξc i) K' hK'u hK')
  have hξ₀i : LocallyIntegrableOn ξ₀ U :=
    (hξ₀.locallyIntegrableOn hr isClosed_univ.isLocallyClosed).mono_set (subset_univ _)
  have hfi : LocallyIntegrableOn f Ω := hf.locallyIntegrableOn hr Ω.isOpen.isLocallyClosed
  have hgi : LocallyIntegrableOn g Ω := hg.locallyIntegrableOn hr Ω.isOpen.isLocallyClosed
  have hid (φ : 𝓓(U, ℝ)) : ∫ z, Δ (φ : ℂ → ℝ) z • ξ₀ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z) := by
    let φ' : 𝓓(Ω, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans (subset_closure.trans hUΩ)⟩
    have hR : Integrable fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z :=
      (integrable_fderiv_smul_of_locallyIntegrableOn hfi φ' 1).add
        (integrable_fderiv_smul_of_locallyIntegrableOn hgi φ' I)
    have hL := integrable_laplacian_smul_of_locallyIntegrableOn hξ₀i φ
    refine b.ext_elem fun i ↦ ?_
    have hci (x : V) : b.repr x i = c i x := rfl
    rw [hci, hci, ← (c i).integral_comp_comm hL, map_neg, ← (c i).integral_comp_comm hR]
    have hξ₀c (w : ℂ) : c i (ξ₀ w) = ξc i w := by
      rw [← hci]
      simp [ξ₀, Finsupp.single_apply]
    simp only [map_smul, map_add, hξ₀c, smul_eq_mul]
    simpa only [smul_eq_mul] using
      integral_laplacian_smul_half_re_cauchyTransform (hdati i) (hdatfg i) φ
  have hwh : WeaklyHarmonicOn volume U (ξ - ξ₀) :=
    weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq
      (hξ.mono_set (subset_closure.trans hUΩ)) hξ₀i fun φ ↦ by
        rw [hid φ]
        exact hdiv ⟨φ, φ.contDiff, φ.hasCompactSupport,
          φ.tsupport_subset.trans (subset_closure.trans hUΩ)⟩
  obtain ⟨v, hv, hξv⟩ := hwh.exists_harmonicOnNhd_ae_eq
  exact ⟨ξ₀, hξ₀, hid, hwh, v, hv, hξv.mono fun z hz ↦ by
    simp only [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel]⟩

/-- **Divergence-form Laplace equation on a ball, with interior bounds.** Under the hypotheses of
`TauCeti.exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq`, if the closed ball
of radius `R` about `c` lies in `Ω` and `ρ < R`, then on the open ball `ξ = ξ₀ + v` almost
everywhere, with `ξ₀` locally `Lʳ` solving `Δ ξ₀ = ∂ₛ f + ∂ₜ g` weakly on the ball and `v`
harmonic there, and by the mean value property `v` and its derivative are bounded on the closed
ball of radius `ρ` by a constant times the `L¹` norm of `ξ - ξ₀` on the ball of radius `R`. The
constant depends only on `c`, `ρ` and `R`, not on `ξ`, `f` or `g`. -/
theorem exists_ae_eq_add_harmonicOnNhd_norm_fderiv_le_of_integral_laplacian_smul_eq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {c : ℂ}
    {ρ R : ℝ} (hρR : ρ < R) (hRΩ : closedBall c R ⊆ Ω) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    ∃ C : ℝ≥0, ∀ {ξ f g : ℂ → V}, LocallyIntegrableOn ξ Ω → MemLpLoc r Ω f → MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      ∃ ξ₀ v : ℂ → V, MemLpLoc r univ ξ₀ ∧
        (∀ φ : 𝓓(⟨ball c R, isOpen_ball⟩, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ₀ z =
          -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) ∧
        HarmonicOnNhd v (ball c R) ∧ ξ =ᵐ[volume.restrict (ball c R)] ξ₀ + v ∧
        ∀ x ∈ closedBall c ρ,
          ‖v x‖ ≤ C * ∫ z in ball c R, ‖ξ z - ξ₀ z‖ ∧
            ‖fderiv ℝ v x‖ ≤ C * ∫ z in ball c R, ‖ξ z - ξ₀ z‖ := by
  let B : Opens ℂ := ⟨ball c R, isOpen_ball⟩
  have hBc : IsCompact (closure (B : Set ℂ)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hBΩ : closure (B : Set ℂ) ⊆ Ω := closure_ball_subset_closedBall.trans hRΩ
  obtain ⟨C, hC⟩ :=
    WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_norm_and_norm_fderiv_le_integral_norm (F := V)
      (μ := volume) (Ω := B) c hρR subset_rfl
  refine ⟨C, fun {ξ f g} hξ hf hg hdiv ↦ ?_⟩
  obtain ⟨ξ₀, hξ₀, hid, hwh, -⟩ :=
    exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq hBc hBΩ hr hξ hf hg hdiv
  have hint : IntegrableOn (ξ - ξ₀) (ball c R) :=
    ((hξ.integrableOn_compact_subset hRΩ (isCompact_closedBall c R)).mono_set
      ball_subset_closedBall).sub
      (((hξ₀.locallyIntegrableOn hr isClosed_univ.isLocallyClosed).integrableOn_compact_subset
        (subset_univ _) (isCompact_closedBall c R)).mono_set ball_subset_closedBall)
  obtain ⟨v, hv, hξv, hN⟩ := hC hwh hint
  exact ⟨ξ₀, v, hξ₀, hid, hv, hξv.mono fun z hz ↦ by
    simp only [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel], fun x hx ↦ hN x hx⟩

/-- **Check: the factor `½` is needed.** Without it, `Re (T h)` does not solve the
divergence-form equation `Δ u = ∂ₛ (Re h) + ∂ₜ (Im h)`: by
`TauCeti.integral_laplacian_smul_re_cauchyTransform` it solves the same equation with right-hand
side doubled, and the two differ for `h = ∂ₛφ` with `φ` a bump function. -/
theorem exists_integral_laplacian_smul_re_cauchyTransform_ne :
    ∃ (h : ℂ → ℂ) (φ : ℂ → ℝ), Integrable h ∧ HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧
      ∫ w, Δ φ w • (cauchyTransform h w).re ≠
        -∫ z, (fderiv ℝ φ z 1 • (h z).re + fderiv ℝ φ z I • (h z).im) := by
  let β : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set φ : ℂ → ℝ := ⇑β
  have hφ : ContDiff ℝ ∞ φ := β.contDiff
  have hc : HasCompactSupport φ := β.hasCompactSupport
  set d : ℂ → ℝ := fun z ↦ fderiv ℝ φ z 1 with hd_def
  have hd : Continuous d := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport d := (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L 1) rfl
  let h : ℂ → ℂ := fun z ↦ (d z : ℂ)
  have hh : Integrable h :=
    (continuous_ofReal.comp hd).integrable_of_hasCompactSupport (hdc.comp_left ofReal_zero)
  refine ⟨h, φ, hh, hc, hφ, ?_⟩
  rw [integral_laplacian_smul_re_cauchyTransform hh hc (hφ.of_le (by simp))]
  simp only [h, ofReal_re, ofReal_im, mul_zero, add_zero, smul_eq_mul]
  change -2 * ∫ z, d z * d z ≠ -∫ z, d z * d z
  obtain ⟨x, hx⟩ : ∃ x, d x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ ↦ φ t) (d t) t := by
      have := ((hφ.differentiable (by simp)) (t : ℂ)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_id t).ofReal_comp
      convert this using 1
      rfl
    have hconst := is_const_of_deriv_eq_zero (fun t ↦ (hderiv t).differentiableAt)
      (fun t ↦ by rw [(hderiv t).deriv, hcon])
    have h0 : φ ((0 : ℝ) : ℂ) = 1 := β.one_of_mem_closedBall (by simp [β])
    have h3 : φ ((3 : ℝ) : ℂ) = 0 := β.zero_of_le_dist (by norm_num [β])
    have := hconst 0 3
    rw [h0, h3] at this
    exact one_ne_zero this
  have hpos : 0 < ∫ z, d z * d z :=
    (hd.mul hd).integral_pos_of_hasCompactSupport_nonneg_ne_zero hdc.mul_left
      (fun z ↦ mul_self_nonneg (d z)) (mul_self_ne_zero.2 hx)
  linarith

end TauCeti
