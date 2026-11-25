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
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
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
vector field `φ ∇χ`, both supported in `Ω`, gives

`Δ(χ u) = χ f + 2 ⟪∇χ, ∇u⟫ + u Δχ`

against every smooth compactly supported `φ` on `E`
(`TauCeti.HasWeakFDerivOn.integral_laplacian_mul_cutoff_mul_eq`). The right-hand side lies in
`Lᵖ(E)`, since `χ` vanishes off a compact subset of `Ω`, so the whole-space theorem applies to
`χ u`; restricting to `U`, where `χ u = u`, finishes the proof.

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
    rw [laplacian_apply_apply, SchwartzMap.laplacian_postcompCLM,
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
  have hχU : ∀ x ∈ (U : Set E), χ =ᶠ[𝓝 x] fun _ ↦ 1 := fun x hx ↦
    mem_interior_iff_mem_nhds.1 (hχ1 (subset_closure hx))
  have hbd : ∀ c : E → ℝ, Continuous c → (∀ x ∉ tsupport χ, c x = 0) →
      MemLp c ⊤ (volume.restrict Ω) := fun c hc hc0 ↦
    hc.memLp_top_of_hasCompactSupport (HasCompactSupport.intro hχc hc0) _
  have hsupp : ∀ c : E → ℝ, (∀ x ∉ tsupport χ, c x = 0) → Function.support c ⊆ Ω :=
    fun _ hc0 ↦ (Function.support_subset_iff'.2 hc0).trans hχΩ
  have hcgχ : Continuous (∇ χ) := (hχ.gradient_right (m := 0) (by simp)).continuous
  -- The cutoff `χ u` and the right-hand side of its equation lie in `Lᵖ` of the whole space.
  have hw : MemLp (fun x ↦ χ x * W1p.value u x) p volume :=
    ((hbd χ hχ.continuous fun _ ↦ image_eq_zero_of_notMem_tsupport).mul
      (Lp.memLp _)).of_restrict_of_support_subset Ω.isOpen.measurableSet.nullMeasurableSet
      (hsupp _ fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx])
  have hgrad : MemLp (fun x ↦ ⟪∇ χ x, W1p.gradient u x⟫_ℝ) p (volume.restrict Ω) :=
    ((hbd _ hcgχ.norm fun x hx ↦ by simp [gradient_of_notMem_tsupport hx]).mul
      (Lp.memLp (W1p.gradient u)).norm).of_le
      (hcgχ.aestronglyMeasurable.inner (Lp.aestronglyMeasurable _))
      (ae_of_all _ fun x ↦ by
        simp only [Pi.mul_apply, norm_mul, norm_norm]
        exact norm_inner_le_norm (𝕜 := ℝ) _ _)
  have hr : MemLp (fun x ↦ χ x * f x + 2 * ⟪∇ χ x, W1p.gradient u x⟫_ℝ +
      Δ χ x * W1p.value u x) p volume :=
    ((((hbd χ hχ.continuous fun _ ↦ image_eq_zero_of_notMem_tsupport).mul hf).add
      (hgrad.const_mul 2)).add
        ((hbd _ (hχ.of_le (m := 2) (by simp)).continuous_laplacian
          fun _ ↦ laplacian_of_notMem_tsupport).mul
          (Lp.memLp _))).of_restrict_of_support_subset
      Ω.isOpen.measurableSet.nullMeasurableSet (hsupp _ fun x hx ↦ by
        simp [image_eq_zero_of_notMem_tsupport hx, gradient_of_notMem_tsupport hx,
          laplacian_of_notMem_tsupport hx])
  obtain ⟨W, hWv, hWtr⟩ := exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq hp hp_top hw hr
    fun φ hφ _ ↦ (W1p.hasWeakFDerivOn u).integral_laplacian_mul_cutoff_mul_eq
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
