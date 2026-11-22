/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Strichartz
public import TauCeti.Analysis.PDE.Strichartz.Endpoint
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

/-!
# The endpoint Strichartz estimate for the Schrödinger equation

On a real inner product space `E` of dimension `n ≥ 3`, let `S(t) = exp(itΔ)` be the Schrödinger
propagator and let `r = 2n / (n - 2)` be the endpoint exponent, the spatial exponent of the
admissible pair `(2, r)`: `2 / 2 + n / r = n / 2`. Let `r'` be its Hölder conjugate. This file
proves the **endpoint Strichartz estimate** of Keel and Tao,

`‖S(t) f‖_{L²_t L^r_x} ≤ C ‖f‖₂`

(`TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_le_of_endpoint`), together with its dual form
`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L²_t L^{r'}_x}`
(`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint`) and its weak form
tested against `L²`-valued functions
(`TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le_of_endpoint`).

The abstract endpoint theorem `TauCeti.exists_enorm_integral_adjoint_le_of_endpoint` applies with
the decay rate `σ = n / 2 > 1`: the propagator is unitary, it satisfies the dispersive estimate
`‖S(s) S(t)* g‖_∞ ≤ (4π|s - t|)^{-n/2} ‖g‖₁` (`TauCeti.eLpNorm_schrodingerPropagator_le_of_memLp`),
and it satisfies the non-endpoint dual estimate at the admissible pair `(4, 2n / (n - 1))`
(`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le`). In dimension `n = 2` the endpoint
`(2, ∞)` is excluded, and in dimension `1` the admissible pair with `q = 2` does not exist.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Theorem 1.2 and Corollary 1.3.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {r : ℝ≥0∞}

/-- The dispersive estimate in the form of the abstract endpoint theorem: the time pairings
`S(s) S(t)* = S(s - t)` decay from `L¹` to `L^∞` like `(4π|s - t|)^{-n/2}`. -/
private theorem eLpNorm_schrodingerPropagator_adjoint_le_top {s t : ℝ} (hst : s ≠ t)
    (g : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm (schrodingerPropagator ℂ s (((schrodingerPropagator ℂ t)†) g)) ∞ volume ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-((Module.finrank ℝ E : ℝ) / 2))) *
        ‖s - t‖ₑ ^ (-((Module.finrank ℝ E : ℝ) / 2)) * eLpNorm g 1 volume := by
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have hk : ENNReal.ofReal ((4 * Real.pi) ^ (-((Module.finrank ℝ E : ℝ) / 2))) *
      ‖s - t‖ₑ ^ (-((Module.finrank ℝ E : ℝ) / 2)) =
        ENNReal.ofReal ((4 * Real.pi * |s - t|) ^
          (-(Module.finrank ℝ E : ℝ) * (1 / 2 - ((∞ : ℝ≥0∞)⁻¹).toReal))) := by
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos (abs_pos.2 hst'),
      ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by positivity) (abs_nonneg _)]
    congr 2 <;> simp [div_eq_mul_inv]
  rw [schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator,
    ← phasePropagator_add_apply, ← sub_eq_add_neg, ← schrodingerPropagator_def, hk]
  by_cases hg : MemLp g 1 volume
  · exact eLpNorm_schrodingerPropagator_le_of_memLp hst' le_top g hg
  · rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)), ENNReal.mul_top (by positivity)]
    exact le_top

/-- **The endpoint dual Strichartz estimate for the Schrödinger equation.** In dimension
`n ≥ 3`, let `r` be the endpoint exponent, `1 + n / r = n / 2`, with Hölder conjugate `r'`. There is
`C` such that for every integrable `F : ℝ → L²(E)`,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L²_t L^{r'}_x}`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint {r' : ℝ≥0∞}
    [r'.HolderConjugate r] (hn : 2 < Module.finrank ℝ E)
    (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
      ‖∫ s, schrodingerPropagator ℂ (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn' : 2 < n := by simp only [n]; exact_mod_cast hn
  have hxp : 0 ≤ 2⁻¹ + (2 * n)⁻¹ := by positivity
  have hxm : 0 ≤ 2⁻¹ - (2 * n)⁻¹ := by
    rw [sub_nonneg]; exact inv_anti₀ two_pos (by linarith)
  -- The non-endpoint admissible pair `(4, r₄)`, `1 / r₄ = 1/2 - 1/(2n)`, with dual exponent `b`.
  set r₄ : ℝ≥0∞ := (ENNReal.ofReal (2⁻¹ - (2 * n)⁻¹))⁻¹
  set b : ℝ≥0∞ := (ENNReal.ofReal (2⁻¹ + (2 * n)⁻¹))⁻¹
  have : b.HolderConjugate r₄ := ENNReal.holderConjugate_iff.2 (by
    rw [inv_inv, inv_inv, ← ENNReal.ofReal_add hxp hxm, add_add_sub_cancel]
    norm_num)
  have hqr : 2 / ((4 : ℝ≥0) : ℝ) + n * (r₄⁻¹).toReal = n / 2 := by
    rw [inv_inv, ENNReal.toReal_ofReal hxm]; push_cast; field_simp; ring
  obtain ⟨K, hK⟩ := exists_enorm_integral_schrodingerPropagator_neg_le (E := E) (p := 4 / 3)
    (r := r₄) (r' := b) (by norm_num : (2 : ℝ≥0) < 4)
    (by rw [← NNReal.holderConjugate_coe_iff, Real.holderConjugate_iff]; norm_num) hqr
  -- The exponents of the abstract endpoint theorem, with `σ = n / 2`.
  have hbinv : b.toReal⁻¹ = 2⁻¹ + (2 * n)⁻¹ := by
    rw [ENNReal.toReal_inv, inv_inv, ENNReal.toReal_ofReal hxp]
  have hr'inv : r'.toReal⁻¹ = (n / 2 + 1) / (2 * (n / 2)) := by
    have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one r' r)
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r' r))
      (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')), ENNReal.toReal_one] at h
    rw [← ENNReal.toReal_inv]
    have hn0 : n ≠ 0 := by positivity
    field_simp
    nlinarith
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le_of_endpoint (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (μ := (volume : Measure E)) (σ := n / 2)
    (p := ((4 / 3 : ℝ≥0) : ℝ≥0∞)) (b := b) (r' := r') (by linarith)
    (by rw [hbinv]; linarith [inv_pos.2 (by positivity : (0 : ℝ) < 2 * n)])
    (by rw [hbinv]; field_simp; linarith) (by rw [hbinv]; norm_num; field_simp; ring) hr'inv
    ((4 * Real.pi) ^ (-((Module.finrank ℝ E : ℝ) / 2))).toNNReal 1 K
  refine ⟨C, fun F hF ↦ ?_⟩
  have h := hC (schrodingerPropagator ℂ)
    (fun t ↦ by
      rw [ENNReal.coe_one, ← ofReal_norm]
      exact ENNReal.ofReal_le_one.2 (norm_phasePropagator_le _ _))
    (fun s t hst g ↦ eLpNorm_schrodingerPropagator_adjoint_le_top hst g)
    (fun G hG hUG ↦ by
      simp_rw [adjoint_schrodingerPropagator] at hUG ⊢
      exact hK G hG hUG)
    (fun G hG ↦ by
      simp_rw [adjoint_schrodingerPropagator]
      exact aestronglyMeasurable_phasePropagator_apply laplacianSymbol
        continuous_neg.aestronglyMeasurable hG) F hF
  simpa only [adjoint_schrodingerPropagator] using h

/-- **The endpoint Strichartz estimate for the Schrödinger equation, in weak form.** In dimension
`n ≥ 3`, let `r` be the endpoint exponent, `1 + n / r = n / 2`, with Hölder conjugate `r'`. There is
`C` such that for every `f ∈ L²(E)` and every integrable `G : ℝ → L²(E)`,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L²_t L^{r'}_x}`. -/
theorem exists_enorm_integral_inner_schrodingerPropagator_le_of_endpoint {r' : ℝ≥0∞}
    [r'.HolderConjugate r] (hn : 2 < Module.finrank ℝ E)
    (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
      Integrable G → ‖∫ t, ⟪schrodingerPropagator ℂ t f, G t⟫_ℂ‖ₑ ≤
        C * ‖f‖ₑ * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint (r' := r') hn hr
  refine ⟨C, fun f G hG ↦ ?_⟩
  have hSG : Integrable fun t ↦ schrodingerPropagator ℂ (-t) (G t) :=
    integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hG
  simp_rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_schrodingerPropagator]
  rw [integral_inner hSG]
  calc _ ≤ ‖f‖ₑ * ‖∫ t, schrodingerPropagator ℂ (-t) (G t)‖ₑ := eNorm_inner_le_eNorm _ _
    _ ≤ ‖f‖ₑ * (C * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2) := by gcongr; exact hC G hG
    _ = _ := by ring

/-- **The endpoint Strichartz estimate for the Schrödinger equation** of Keel and Tao. In dimension
`n ≥ 3`, let `r = 2n / (n - 2)` be the endpoint exponent, `1 + n / r = n / 2`. There is `C` such
that for every `f ∈ L²(E)`,

`‖S(t) f‖_{L²_t L^r_x} ≤ C ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerPropagator_le_of_endpoint
    (hn : 2 < Module.finrank ℝ E)
    (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) 2 volume ≤ C * ‖f‖ₑ := by
  have hn' : (2 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hn
  have hrinv : (r⁻¹).toReal = 2⁻¹ - (Module.finrank ℝ E : ℝ)⁻¹ := by
    field_simp
    linarith
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, ENNReal.inv_zero, ENNReal.toReal_top, mul_zero, add_zero] at hr
    linarith
  have hr2 : 2 ≤ r := ENNReal.two_le_of_toReal_inv_le hr0 (by
    rw [hrinv]; linarith [inv_pos.2 (two_pos.trans hn')])
  -- Test against `L^{r'}` with `r'` the Hölder conjugate of `r`.
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_schrodingerPropagator_le_of_endpoint
    (r' := (1 - r⁻¹)⁻¹) hn hr
  exact ⟨C, fun f ↦ (continuous_phasePropagator_apply laplacianSymbol f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (q' := 2) (r' := (1 - r⁻¹)⁻¹)
      ENNReal.ofNat_ne_top hr2 fun G hG _ ↦ hC f G hG⟩

end TauCeti
