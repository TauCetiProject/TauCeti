/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Laplacian
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.Sobolev.BesselPotential.Basic

/-!
# `W^{2,p}` regularity for Poisson's equation

For `1 < p < ∞`, this file proves that a solution of Poisson's equation `Δu = f` with `f ∈ Lᵖ`
has its second weak derivatives in `Lᵖ`, first on a whole finite-dimensional real inner product
space `E` and then in the interior of an open set.

* **The whole space** (`TauCeti.exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq`). If
  `u, f ∈ Lᵖ(E)` and `∫ Δφ u = ∫ φ f` for every smooth compactly supported `φ`, then `u` is the
  value of an element `w` of `W^{2,p}(E)`, and `tr D²w = f` almost everywhere.
* **Interior regularity**
  (`TauCeti.W1p.exists_wkp_two_value_ae_eq_of_integral_laplacian_smul_eq`). If
  `u ∈ W^{1,p}(Ω)`, `f ∈ Lᵖ(Ω)` and `Δu = f` against the test functions on `Ω`, then on every open
  `U` whose closure is a compact subset of `Ω`, `u` is the value of an element `w` of `W^{2,p}(U)`,
  and `tr D²w = f` almost everywhere in `U`.

Together with the a priori estimate `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}` on `W^{2,p}(E)`
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq`), this is the
constant-coefficient Calderón–Zygmund theory of the Laplacian: estimate and regularity.

## The argument

On the whole space the statement is a computation with tempered distributions. The distributional
Laplacian of `u` is `f`, tested against the real compactly supported Schwartz functions, which
determine a tempered distribution (`TemperedDistribution.ext_real`). The Bessel potential of order
two is `1 - (2π)⁻² Δ` (`TemperedDistribution.besselPotential_two_eq_sub_laplacian`), so it maps
`u` to the `Lᵖ` function `u - (2π)⁻² f`, and `u` lies in the Bessel-potential space `H^{2,p}(E)`.
By Calderón's theorem `H^{2,p}(E) = W^{2,p}(E)`
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), whose proof is where the
singular integral estimates enter, through the Mihlin–Hörmander multiplier theorem.

For interior regularity choose a smooth cutoff `χ`, equal to one near the closure of `U` and
supported in `Ω`, and let `∇u` be the weak gradient of `u`. By the Leibniz rule for the Laplacian,
`χ Δφ = Δ(χ φ) - 2 ⟪∇χ, ∇φ⟫ - φ Δχ` for every smooth compactly supported `φ`, and the middle term
is `div (φ ∇χ) - φ Δχ`. Testing `Δu = f` against `χ φ` and the weak gradient of `u` against the
components of `φ ∇χ`, both supported in `Ω`, gives

`Δ(χ u) = χ f + 2 ⟪∇χ, ∇u⟫ + u Δχ`

against every smooth compactly supported `φ` on `E`. The right-hand side lies in `Lᵖ(E)`, since
`χ` vanishes off a compact subset of `Ω`, so the whole-space theorem applies to `χ u`; restricting
to `U`, where `χ u = u`, finishes the proof.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.4.
* A.-P. Calderón, *Lebesgue spaces of differentiable functions and distributions*, Proc. Sympos.
  Pure Math. **4** (1961), 33–49.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.3 and Chapter V, §3.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory TemperedDistribution TopologicalSpace
open scoped ENNReal Real Laplacian SchwartzMap Distributions Gradient ContDiff Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`W^{2,p}` regularity for Poisson's equation on the whole space.** Let `1 < p < ∞` and let
`u, f ∈ Lᵖ(E)` satisfy `Δu = f` in the sense of distributions: `∫ Δφ u = ∫ φ f` for every smooth
compactly supported `φ`. Then `u` is the value of an element `w` of `W^{2,p}(E)`, and `w` solves
`Δw = f` strongly: the trace of its weak Hessian is `f` almost everywhere. -/
theorem exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    {u f : E → ℝ} (hu : MemLp u p volume) (hf : MemLp f p volume)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, Δ φ x * u x = ∫ x, φ x * f x) :
    ∃ w : Wkp (volume : Measure E) ⊤ p 2, (Wkp.value 2 w : E → ℝ) =ᵐ[volume] u ∧
      (fun x ↦ LinearMap.trace ℝ E (Wkp.iteratedGradient 1 w x)) =ᵐ[volume] f := by
  set U := hu.toLp u
  set F := hf.toLp f
  set T : 𝓢'(E, ℂ) := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp U)
  -- The distributional Laplacian of `u` is `f`, tested against real compactly supported
  -- Schwartz functions.
  have hΔ : Δ T = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp F) := by
    refine ext_real fun φ hφ ↦ ?_
    rw [laplacian_apply_apply, laplacian_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM]
    congr 1
    calc ∫ x, (Δ φ) x * U x = ∫ x, Δ (φ : E → ℝ) x * u x :=
          integral_congr_ae (hu.coeFn_toLp.mono fun x hx ↦ by
            simp only [U, hx, SchwartzMap.laplacian_apply])
      _ = ∫ x, φ x * f x := h φ (φ.smooth ⊤) hφ
      _ = ∫ x, φ x * F x := integral_congr_ae (hf.coeFn_toLp.mono fun x hx ↦ by simp only [F, hx])
  -- The Bessel potential of order two maps `u` to the `Lᵖ` function `u - (2π)⁻² f`.
  have hT : MemSobolev ((2 : ℕ) : ℝ) p T := by
    have h0 : MemSobolev 0 p (besselPotential E ℂ 2 T) := by
      rw [besselPotential_two_eq_sub_laplacian, hΔ]
      exact (memSobolev_zero_iff.2 ⟨_, rfl⟩).sub
        ((memSobolev_zero_iff.2 ⟨_, rfl⟩).smul_of_tower _)
    simpa using memSobolev_besselPotential_iff.1 h0
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top 2 U).1 hT
  have hwu : (Wkp.value 2 w : E → ℝ) =ᵐ[volume] u := hw.trans hu.coeFn_toLp
  refine ⟨w, hwu, ?_⟩
  -- The strong equation follows from the weak one, as `w` lies in `W^{2,p}`.
  have hloc : LocallyIntegrableOn f ((⊤ : Opens E) : Set E) volume :=
    (hf.locallyIntegrable hp.le).locallyIntegrableOn _
  have htr := (Wkp.forall_integral_laplacian_smul_value_eq_iff w hloc).1 fun φ ↦
    calc ∫ x, Δ (φ : E → ℝ) x • Wkp.value 2 w x = ∫ x, Δ (φ : E → ℝ) x * u x :=
          integral_congr_ae (hwu.mono fun x hx ↦ by simp only [smul_eq_mul, hx])
      _ = ∫ x, (φ : E → ℝ) x * f x := h φ φ.contDiff φ.hasCompactSupport
      _ = ∫ x, (φ : E → ℝ) x • f x := by simp only [smul_eq_mul]
  simpa only [Opens.coe_top, Measure.restrict_univ] using htr

/-! ### Interior regularity -/

section Interior

/-- A continuous function vanishing off a compact subset `K` of `Ω`, times a function locally
integrable on `Ω`, is integrable on the whole space: the form of
`MeasureTheory.LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport` used for the
coefficients of the cutoff argument, which vanish off the support of the cutoff. -/
private theorem integrable_mul_of_forall_notMem {Ω K : Set E} {c q : E → ℝ} (hc : Continuous c)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hcK : ∀ x ∉ K, c x = 0)
    (hq : LocallyIntegrableOn q Ω volume) : Integrable (fun x ↦ c x * q x) := by
  have hsupp : Function.support c ⊆ K := fun x hx ↦ by
    by_contra hxK
    exact hx (hcK x hxK)
  simpa only [smul_eq_mul] using hq.integrable_smul_left_of_hasCompactSupport hc
    (HasCompactSupport.intro hK hcK) ((closure_minimal hsupp hK.isClosed).trans hKΩ)

/-- The vector form of `integrable_mul_of_forall_notMem`, for the inner product of a continuous
vector field vanishing off `K` with a measurable field locally integrable on `Ω`. -/
private theorem integrable_inner_of_forall_notMem {Ω K : Set E} {c q : E → E} (hc : Continuous c)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hcK : ∀ x ∉ K, c x = 0)
    (hq : LocallyIntegrableOn q Ω volume) (hqm : AEStronglyMeasurable q volume) :
    Integrable (fun x ↦ ⟪c x, q x⟫_ℝ) :=
  (integrable_mul_of_forall_notMem hc.norm hK hKΩ (fun x hx ↦ by simp [hcK x hx]) hq.norm).mono'
    (hc.aestronglyMeasurable.inner hqm) (ae_of_all _ fun x ↦ norm_inner_le_norm _ _)

omit [Fact (1 ≤ p)] in
/-- A function vanishing off a measurable set `Ω` and in `Lᵖ(Ω)` is in `Lᵖ` of the whole space. -/
private theorem memLp_of_memLp_restrict_of_forall_notMem {Ω : Set E} (hΩ : MeasurableSet Ω)
    {q : E → ℝ} (hq : MemLp q p (volume.restrict Ω)) (h0 : ∀ x ∉ Ω, q x = 0) :
    MemLp q p volume := by
  have hq' : Ω.indicator q = q :=
    Set.indicator_eq_self.2 fun x hx ↦ by
      by_contra hxΩ
      exact hx (h0 x hxΩ)
  rw [← hq', memLp_indicator_iff_restrict hΩ.nullMeasurableSet]
  exact hq

omit [MeasurableSpace E] [BorelSpace E] in
/-- A real function, its gradient and its Laplacian vanish off its topological support. -/
private theorem eq_zero_and_gradient_eq_zero_and_laplacian_eq_zero {χ : E → ℝ} {x : E}
    (hx : x ∉ tsupport χ) : χ x = 0 ∧ ∇ χ x = 0 ∧ Δ χ x = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport hx, gradient_of_notMem_tsupport hx,
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_laplacian_subset χ h)⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pairing of a gradient with a vector, expanded in an orthonormal basis:
`⟪∇f(x), w⟫ = ∑ᵢ Df(x) bᵢ ⟪w, bᵢ⟫`. -/
private theorem inner_gradient_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : E → ℝ) (x w : E) : ⟪∇ f x, w⟫_ℝ = ∑ i, fderiv ℝ f x (b i) * ⟪w, b i⟫_ℝ := by
  rw [← b.sum_inner_mul_inner (∇ f x) w]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [inner_gradient_left, real_inner_comm]

/-- **Integration by parts against a cutoff gradient.** Let `v` have weak gradient `g` on `Ω` and
let `χ` be smooth with compact support in `Ω`. Then for every smooth `φ`,
`∫ (⟪∇φ, ∇χ⟫ + φ Δχ) v = -∫ φ ⟪∇χ, g⟫`: the left side pairs `v` with `div (φ ∇χ)`, and `φ ∇χ` is
supported in `Ω`. -/
private theorem integral_inner_gradient_add_mul_laplacian_mul_eq {Ω : Opens E} {v : E → ℝ}
    {g : E → E} (hv : HasWeakFDerivOn volume Ω v fun x ↦ innerSL ℝ (g x)) {χ φ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hφ : ContDiff ℝ ∞ φ) :
    ∫ x, (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x = -∫ x, φ x * ⟪∇ χ x, g x⟫_ℝ := by
  set b := stdOrthonormalBasis ℝ E
  have hdχ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ χ x (b i) := fun i ↦
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  -- The test functions `ψᵢ = φ ∂ᵢχ`, supported in the support of `χ`.
  have hts : ∀ i, tsupport (fun x ↦ φ x * fderiv ℝ χ x (b i)) ⊆ tsupport χ := fun i ↦
    closure_minimal
      (fun x hx ↦ support_fderiv_subset ℝ fun h ↦ Function.mem_support.1 hx (by simp [h]))
      (isClosed_tsupport χ) |>.trans' tsupport_mul_subset_right
  let ψ : Fin (Module.finrank ℝ E) → 𝓓(Ω, ℝ) := fun i ↦
    ⟨fun x ↦ φ x * fderiv ℝ χ x (b i), hφ.mul (hdχ i),
      hχc.of_isClosed_subset (isClosed_tsupport _) (hts i), (hts i).trans hχΩ⟩
  have hψcoe : ∀ i, (ψ i : E → ℝ) = fun x ↦ φ x * fderiv ℝ χ x (b i) := fun _ ↦ rfl
  have hψ : ∀ i x, lineDeriv ℝ (ψ i : E → ℝ) x (b i) =
      fderiv ℝ φ x (b i) * fderiv ℝ χ x (b i) +
        φ x * fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) := fun i x ↦ by
    have hφd := (hφ.differentiable (by simp)) x
    have hdd := ((hdχ i).differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y ↦ φ y * fderiv ℝ χ y (b i)) x := hφd.mul hdd
    rw [hψcoe, hmul.lineDeriv_eq_fderiv, fderiv_fun_mul hφd hdd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- Summing the weak derivative identities `∫ ∂ᵢψᵢ v = -∫ ψᵢ gᵢ` over an orthonormal basis.
  have hdir : ∀ i, ∫ x, lineDeriv ℝ (ψ i : E → ℝ) x (b i) * v x =
      -∫ x, (ψ i : E → ℝ) x * ⟪g x, b i⟫_ℝ := fun i ↦ by
    simpa only [smul_eq_mul, innerSL_apply_apply] using
      (hv.hasWeakLineDerivOn (b i)).integral_lineDeriv_smul_eq_neg_integral_smul (ψ i)
  have hint₁ : ∀ i, Integrable fun x ↦ lineDeriv ℝ (ψ i : E → ℝ) x (b i) * v x := fun i ↦ by
    simpa only [smul_eq_mul] using
      integrable_lineDeriv_smul_of_locallyIntegrableOn hv.locallyIntegrableOn (ψ i) (b i)
  have hint₂ : ∀ i, Integrable fun x ↦ (ψ i : E → ℝ) x * ⟪g x, b i⟫_ℝ := fun i ↦ by
    simpa only [smul_eq_mul, innerSL_apply_apply] using
      (ψ i).integrable_smul (hv.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv
  calc ∫ x, (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x
      = ∑ i, ∫ x, lineDeriv ℝ (ψ i : E → ℝ) x (b i) * v x := by
        rw [← integral_finsetSum _ fun i _ ↦ hint₁ i]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        have hΔ := laplacian_eq_sum_fderiv_fderiv_apply b
          (((hχ.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x)
        simp only [hψ, inner_gradient_eq_sum b φ x, inner_gradient_left, hΔ, Finset.mul_sum,
          ← Finset.sum_add_distrib, Finset.sum_mul]
    _ = -∑ i, ∫ x, (ψ i : E → ℝ) x * ⟪g x, b i⟫_ℝ := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ hdir i
    _ = -∫ x, φ x * ⟪∇ χ x, g x⟫_ℝ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint₂ i]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [hψcoe, inner_gradient_eq_sum b χ x, Finset.mul_sum, mul_assoc]

/-- **The Laplacian of a cutoff of a solution.** Let `v` have weak gradient `g` on `Ω` and solve
`Δv = f` against the test functions on `Ω`, and let `χ` be smooth with compact support in `Ω`.
Then `Δ(χ v) = χ f + 2 ⟪∇χ, g⟫ + v Δχ` against every smooth function on the whole space; no
support condition is needed on it, since `χ` has compact support. -/
private theorem integral_laplacian_mul_cutoff_mul_eq {Ω : Opens E} {v f : E → ℝ} {g : E → E}
    (hv : HasWeakFDerivOn volume Ω v fun x ↦ innerSL ℝ (g x))
    (hgm : AEStronglyMeasurable g volume) (hf : LocallyIntegrableOn f Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • v x = ∫ x, (φ : E → ℝ) x • f x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∫ x, Δ φ x * (χ x * v x) = ∫ x, φ x * (χ x * f x + 2 * ⟪∇ χ x, g x⟫_ℝ + Δ χ x * v x) := by
  have hv' := hv.locallyIntegrableOn
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have h0 := fun x (hx : x ∉ tsupport χ) ↦ eq_zero_and_gradient_eq_zero_and_laplacian_eq_zero hx
  have hleib : ∀ x, Δ (fun y ↦ χ y * φ y) x =
      χ x * Δ φ x + 2 * ⟪∇ χ x, ∇ φ x⟫_ℝ + φ x * Δ χ x := fun x ↦
    hχ2.contDiffAt.laplacian_fun_mul hφ2.contDiffAt
  have hcgχ : Continuous (∇ χ) := (hχ.gradient_right (m := 0) (by simp)).continuous
  -- Integrability of the five terms, each a smooth coefficient vanishing off `tsupport χ`.
  have I₁ : Integrable fun x ↦ Δ (fun y ↦ χ y * φ y) x * v x :=
    integrable_mul_of_forall_notMem ((hχ2.mul hφ2).continuous_laplacian) hχc hχΩ
      (fun x hx ↦ by simp [hleib, h0 x hx]) hv'
  have I₂ : Integrable fun x ↦ (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x :=
    integrable_mul_of_forall_notMem
      (((hφ.gradient_right (m := 0) (by simp)).continuous.inner hcgχ).add
        (hφ.continuous.mul hχ2.continuous_laplacian)) hχc hχΩ (fun x hx ↦ by simp [h0 x hx]) hv'
  have I₃ : Integrable fun x ↦ φ x * Δ χ x * v x :=
    integrable_mul_of_forall_notMem (hφ.continuous.mul hχ2.continuous_laplacian) hχc hχΩ
      (fun x hx ↦ by simp [h0 x hx]) hv'
  have I₄ : Integrable fun x ↦ χ x * φ x * f x :=
    integrable_mul_of_forall_notMem (hχ.continuous.mul hφ.continuous) hχc hχΩ
      (fun x hx ↦ by simp [h0 x hx]) hf
  have I₅ : Integrable fun x ↦ φ x * ⟪∇ χ x, g x⟫_ℝ := by
    simpa only [real_inner_smul_left] using integrable_inner_of_forall_notMem
      (c := fun x ↦ φ x • ∇ χ x) (hφ.continuous.smul hcgχ) hχc hχΩ (fun x hx ↦ by simp [h0 x hx])
      hv.locallyIntegrableOn_gradient hgm
  -- Poisson's equation against `χ φ`, and integration by parts against `φ ∇χ`.
  let ψ : 𝓓(Ω, ℝ) := ⟨fun x ↦ χ x * φ x, hχ.mul hφ, hχc.mul_right,
    tsupport_mul_subset_left.trans hχΩ⟩
  have hB : ∫ x, Δ (fun y ↦ χ y * φ y) x * v x = ∫ x, χ x * φ x * f x := by
    have hψ : (ψ : E → ℝ) = fun x ↦ χ x * φ x := rfl
    simpa only [hψ, smul_eq_mul] using h ψ
  -- Split both sides by linearity, then substitute the two identities.
  have e₁ : ∫ x, Δ φ x * (χ x * v x) = (∫ x, Δ (fun y ↦ χ y * φ y) x * v x) -
      2 * (∫ x, (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x) + ∫ x, φ x * Δ χ x * v x := by
    rw [← integral_const_mul, ← integral_sub I₁ (I₂.const_mul 2),
      ← integral_add (f := fun x ↦ Δ (fun y ↦ χ y * φ y) x * v x -
        2 * ((⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x)) (I₁.sub (I₂.const_mul 2)) I₃]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hleib, real_inner_comm (∇ φ x) (∇ χ x)]
    ring
  have e₂ : ∫ x, φ x * (χ x * f x + 2 * ⟪∇ χ x, g x⟫_ℝ + Δ χ x * v x) =
      (∫ x, χ x * φ x * f x) + 2 * (∫ x, φ x * ⟪∇ χ x, g x⟫_ℝ) + ∫ x, φ x * Δ χ x * v x := by
    rw [← integral_const_mul, ← integral_add I₄ (I₅.const_mul 2),
      ← integral_add (f := fun x ↦ χ x * φ x * f x + 2 * (φ x * ⟪∇ χ x, g x⟫_ℝ))
        (I₄.add (I₅.const_mul 2)) I₃]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  rw [e₁, e₂, hB, integral_inner_gradient_add_mul_laplacian_mul_eq hv hχ hχc hχΩ hφ]
  ring

/-- **Interior `W^{2,p}` regularity for Poisson's equation.** Let `1 < p < ∞`, let `Ω` be an open
set, and let `u ∈ W^{1,p}(Ω)` solve `Δu = f` weakly, with `f ∈ Lᵖ(Ω)`: `∫ Δφ u = ∫ φ f` for every
test function `φ` on `Ω`. Then on every open set `U` whose closure is a compact subset of `Ω`, `u`
is the value of an element `w` of `W^{2,p}(U)`, and `w` solves `Δw = f` strongly: the trace of its
weak Hessian is `f` almost everywhere in `U`. -/
theorem W1p.exists_wkp_two_value_ae_eq_of_integral_laplacian_smul_eq (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Ω U : Opens E} (hU : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) (u : W1p (volume : Measure E) Ω p) {f : E → ℝ}
    (hf : MemLp f p (volume.restrict Ω))
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • W1p.value u x = ∫ x, (φ : E → ℝ) x • f x) :
    ∃ w : Wkp (volume : Measure E) U p 2,
      (Wkp.value 2 w : E → ℝ) =ᵐ[volume.restrict U] W1p.value u ∧
      (fun x ↦ LinearMap.trace ℝ E (Wkp.iteratedGradient 1 w x)) =ᵐ[volume.restrict U] f := by
  obtain ⟨χ, hχ, -, hχ1, hχc, hχΩ⟩ := hU.exists_contDiff_cutoff Ω.isOpen hUΩ
  -- The cutoff `χ` and its derivatives vanish off `tsupport χ ⊆ Ω`, and `χ = 1` near `U`.
  have h0 := fun x (hx : x ∉ tsupport χ) ↦ eq_zero_and_gradient_eq_zero_and_laplacian_eq_zero hx
  have hχU : ∀ x ∈ (U : Set E), χ =ᶠ[𝓝 x] fun _ ↦ 1 := fun x hx ↦
    mem_interior_iff_mem_nhds.1 (hχ1 (subset_closure hx))
  have hbd : ∀ c : E → ℝ, Continuous c → (∀ x ∉ tsupport χ, c x = 0) →
      MemLp c ⊤ (volume.restrict Ω) := fun c hc hc0 ↦
    hc.memLp_top_of_hasCompactSupport (HasCompactSupport.intro hχc hc0) _
  have hcgχ : Continuous (∇ χ) := (hχ.gradient_right (m := 0) (by simp)).continuous
  -- The cutoff `χ u` and the right-hand side of its equation lie in `Lᵖ` of the whole space.
  have hw : MemLp (fun x ↦ χ x * W1p.value u x) p volume :=
    memLp_of_memLp_restrict_of_forall_notMem Ω.isOpen.measurableSet
      ((hbd χ hχ.continuous fun x hx ↦ (h0 x hx).1).mul (Lp.memLp _))
      fun x hx ↦ by simp [(h0 x fun h ↦ hx (hχΩ h)).1]
  have hgrad : MemLp (fun x ↦ ⟪∇ χ x, W1p.gradient u x⟫_ℝ) p (volume.restrict Ω) :=
    ((hbd _ hcgχ.norm fun x hx ↦ by simp [h0 x hx]).mul (Lp.memLp (W1p.gradient u)).norm).of_le
      (hcgχ.aestronglyMeasurable.inner (Lp.aestronglyMeasurable _))
      (ae_of_all _ fun x ↦ by
        simp only [Pi.mul_apply, norm_mul, norm_norm]
        exact norm_inner_le_norm (𝕜 := ℝ) _ _)
  have hr : MemLp (fun x ↦ χ x * f x + 2 * ⟪∇ χ x, W1p.gradient u x⟫_ℝ +
      Δ χ x * W1p.value u x) p volume :=
    memLp_of_memLp_restrict_of_forall_notMem Ω.isOpen.measurableSet
      ((((hbd χ hχ.continuous fun x hx ↦ (h0 x hx).1).mul hf).add (hgrad.const_mul 2)).add
        ((hbd _ (hχ.of_le (m := 2) (by simp)).continuous_laplacian
          fun x hx ↦ (h0 x hx).2.2).mul (Lp.memLp _)))
      fun x hx ↦ by simp [h0 x fun h ↦ hx (hχΩ h)]
  obtain ⟨W, hWv, hWtr⟩ := exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq hp hp_top hw hr
    fun φ hφ _ ↦ integral_laplacian_mul_cutoff_mul_eq (W1p.hasWeakFDerivOn u)
      (Lp.stronglyMeasurable _).aestronglyMeasurable
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable Fact.out)) h hχ hχc
      hχΩ hφ
  -- Restrict to `U`, where `χ u = u` and the right-hand side is `f`.
  refine ⟨Wkp.restrictL le_top 2 W, ?_, ?_⟩
  · filter_upwards [Wkp.value_restrictL_ae le_top 2 W, ae_restrict_of_ae hWv,
      ae_restrict_mem U.isOpen.measurableSet] with x h₁ h₂ hx
    rw [h₁, h₂, (hχU x hx).eq_of_nhds, one_mul]
  · filter_upwards [Wkp.iteratedGradient_restrictL_ae le_top 1 W, ae_restrict_of_ae hWtr,
      ae_restrict_mem U.isOpen.measurableSet] with x h₁ h₂ hx
    have hd : ∇ χ x = 0 := by
      rw [_root_.gradient, (hχU x hx).fderiv_eq]
      simp
    have hΔ : Δ χ x = 0 := by simp [(laplacian_congr_nhds (hχU x hx)).eq_of_nhds]
    simp [h₁, h₂, (hχU x hx).eq_of_nhds, hd, hΔ]

end Interior

end TauCeti
