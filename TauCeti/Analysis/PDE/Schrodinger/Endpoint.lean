/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Strichartz
public import TauCeti.Analysis.PDE.Strichartz.Endpoint
import TauCeti.Analysis.PDE.Strichartz.Retarded
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Integral.Kernel.Pairing
import TauCeti.MeasureTheory.Integral.Prod

/-!
# The endpoint Strichartz estimate for the Schrödinger equation

On a real inner product space `E` of dimension `n ≥ 3`, let `S(t) = exp(itΔ)` be the Schrödinger
propagator and let `r = 2n / (n - 2)` be the endpoint exponent, the spatial exponent of the
admissible pair `(2, r)`: `2 / 2 + n / r = n / 2`. Let `r'` be its Hölder conjugate. This file
proves the **endpoint Strichartz estimate** of Keel and Tao in weak form,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L²_t L^{r'}_x}`

(`TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le_of_endpoint`), together with its dual
form `‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L²_t L^{r'}_x}`
(`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint`), and the **retarded
endpoint estimate** for the Duhamel integral, with the endpoint pair on both sides, in weak form,

`|∫ ∫_{s < t} ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L²_t L^{r'}_x} ‖G‖_{L²_t L^{r'}_x}`

(`TauCeti.exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_endpoint`).
The retarded estimate comes from the bound
`|∫∫_R ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L²_t L^{r'}_x} ‖G‖_{L²_t L^{r'}_x}` on every
measurable region `R` of pairs of times
(`TauCeti.exists_enorm_setIntegral_inner_schrodingerPropagator_sub_le_of_endpoint`) for the half
plane `R = {s < t}`; the dual estimate, and with it the weak homogeneous estimate, come from the
same bound for `R = Set.univ` and `G = F`.

The abstract endpoint theorem `TauCeti.exists_enorm_setIntegral_inner_adjoint_le_of_endpoint`
applies with the decay rate `σ = n / 2 > 1`: the propagator is unitary, it satisfies the
dispersive estimate `‖S(s) S(t)* g‖_∞ ≤ (4π|s - t|)^{-n/2} ‖g‖₁`
(`TauCeti.eLpNorm_schrodingerPropagator_le_of_memLp`), and it satisfies the non-endpoint dual
estimate at the admissible pair `(4, 2n / (n - 1))`
(`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le`). In dimension `n = 2` the endpoint
`(2, ∞)` is excluded, and in dimension `1` the admissible pair with `q = 2` does not exist.

## Every admissible pair with a finite time exponent

An admissible pair `(q, r)`, `2 / q + n / r = n / 2`, with `2 ≤ q < ∞` is either a non-endpoint
pair, `2 < q`, or the endpoint pair, `q = 2` and `n ≥ 3`. For all of them this file states the dual
estimate `‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{q'}_t L^{r'}_x}`
(`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le`), and for any two of them,
`(q, r)` and `(q₁, r₁)`, the retarded estimate in weak form,

`|∫ ∫_{s < t} ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L^{q₁'}_t L^{r₁'}_x} ‖G‖_{L^{q'}_t L^{r'}_x}`

(`TauCeti.exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_integrable`),
which is `‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^{q₁'}_t L^{r₁'}_x}` tested against
`G`. When both pairs are at the endpoint this is the Keel–Tao estimate above. Otherwise
`q₁' < q`, and the Christ–Kiselev lemma passes the bound on the untruncated pairing, which the two
dual estimates give, to the region `s < t`
(`TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le`).
In particular the endpoint pair may be combined with any non-endpoint pair, in either order.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Theorem 1.2 and Corollary 1.3.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3.
* M. Christ and A. Kiselev, *Maximal functions associated to filtrations*, J. Funct. Anal. 179
  (2001), 409–425.
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

/-- **The endpoint Strichartz estimate for the Schrödinger equation on a region of times.** In
dimension `n ≥ 3`, let `r` be the endpoint exponent, `1 + n / r = n / 2`, with Hölder conjugate
`r'`. There is `C` such that for every measurable set `R` of pairs of times and all integrable
`F, G : ℝ → L²(E)`,

`|∫∫_R ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L²_t L^{r'}_x} ‖G‖_{L²_t L^{r'}_x}`. -/
theorem exists_enorm_setIntegral_inner_schrodingerPropagator_sub_le_of_endpoint {r' : ℝ≥0∞}
    [r'.HolderConjugate r] (hn : 2 < Module.finrank ℝ E)
    (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ R : Set (ℝ × ℝ), MeasurableSet R →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F → Integrable G →
        ‖∫ z in R, ⟪schrodingerPropagator ℂ (z.2 - z.1) (F z.1), G z.2⟫_ℂ ∂(volume.prod volume)‖ₑ ≤
          C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 := by
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
  obtain ⟨C, hC⟩ := exists_enorm_setIntegral_inner_adjoint_le_of_endpoint_of_four_thirds
    (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E)) (μ := (volume : Measure E)) (E := ℂ)
    (σ := n / 2) (b := b) (r' := r') (by linarith) (by rw [hbinv]; ring) hr'inv
    ((4 * Real.pi) ^ (-((Module.finrank ℝ E : ℝ) / 2))).toNNReal 1 K
  refine ⟨C, fun R hR F G hF hG ↦ ?_⟩
  simp_rw [inner_schrodingerPropagator_sub_apply, ← adjoint_schrodingerPropagator]
  refine hC (schrodingerPropagator ℂ)
    (fun t ↦ by
      rw [ENNReal.coe_one, ← ofReal_norm]
      exact ENNReal.ofReal_le_one.2 (norm_phasePropagator_le _ _))
    (fun s t hst g ↦ eLpNorm_schrodingerPropagator_adjoint_le_top hst g)
    (fun G hG _ ↦ by
      simp_rw [adjoint_schrodingerPropagator]
      exact hK G hG)
    (fun G hG ↦ by
      simp_rw [adjoint_schrodingerPropagator]
      exact aestronglyMeasurable_phasePropagator_apply laplacianSymbol
        continuous_neg.aestronglyMeasurable hG) R hR F G hF hG

/-- **The endpoint dual Strichartz estimate for the Schrödinger equation.** In dimension
`n ≥ 3`, let `r` be the endpoint exponent, `1 + n / r = n / 2`, with Hölder conjugate `r'`. There is
`C` such that for every almost everywhere strongly measurable `F : ℝ → L²(E)`,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L²_t L^{r'}_x}`.

No integrability of `s ↦ S(-s) F(s)` is assumed: without it the Bochner integral is `0`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint {r' : ℝ≥0∞}
    [r'.HolderConjugate r] (hn : 2 < Module.finrank ℝ E)
    (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      ‖∫ s, schrodingerPropagator ℂ (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_setIntegral_inner_schrodingerPropagator_sub_le_of_endpoint
    (r' := r') hn hr
  refine ⟨NNReal.sqrt C, fun F _ ↦ ?_⟩
  by_cases hSF : Integrable fun s ↦ schrodingerPropagator ℂ (-s) (F s)
  · -- `F(s) = S(s) (S(-s) F(s))` is integrable, since `S(s)` is unitary.
    have hF : Integrable F := (integrable_phasePropagator_apply_iff laplacianSymbol
      continuous_neg.aestronglyMeasurable).1 hSF
    refine enorm_integral_le_sqrt_mul_of_enorm_integral_inner_le (𝕜 := ℂ) hSF ?_
    have h := hC Set.univ MeasurableSet.univ F F hF hF
    simp_rw [inner_schrodingerPropagator_sub_apply, Measure.restrict_univ] at h
    exact h
  · simp [integral_undef hSF]

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
    _ ≤ ‖f‖ₑ * (C * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2) := by
        gcongr; exact hC G hG.aestronglyMeasurable
    _ = _ := by ring

/-- **The retarded endpoint Strichartz estimate for the Schrödinger equation, in weak form.** In
dimension `n ≥ 3`, let `r` be the endpoint exponent, `1 + n / r = n / 2`, with Hölder conjugate
`r'`. There is `C` such that for all integrable `F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L²_t L^{r'}_x} ‖G‖_{L²_t L^{r'}_x}`.

This is the Duhamel estimate `‖∫_{s < t} S(t - s) F(s) ds‖_{L²_t L^r_x} ≤ C ‖F‖_{L²_t L^{r'}_x}`
tested against `G`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_endpoint
    {r' : ℝ≥0∞} [r'.HolderConjugate r] (hn : 2 < Module.finrank ℝ E)
    (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F → Integrable G →
      ‖∫ t, ∫ s in Set.Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_setIntegral_inner_schrodingerPropagator_sub_le_of_endpoint
    (r' := r') hn hr
  refine ⟨C, fun F G hF hG ↦ ?_⟩
  -- The pairing is integrable on the plane, since `S(t - s) F(s)` pairs with `G(t)` as
  -- `S(-s) F(s)` with `S(-t) G(t)`.
  have hφ : Integrable (fun z : ℝ × ℝ ↦
      ⟪schrodingerPropagator ℂ (z.2 - z.1) (F z.1), G z.2⟫_ℂ) (volume.prod volume) := by
    simp_rw [inner_schrodingerPropagator_sub_apply]
    exact (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hF).inner_fst_snd
      (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hG)
  rw [integral_setIntegral_Iio_eq_setIntegral hφ.integrableOn]
  exact hC _ (measurableSet_lt measurable_fst measurable_snd) F G hF hG

/-! ### Every admissible pair with a finite time exponent -/

section TwoPairs

variable {p q p₁ q₁ : ℝ≥0} {r' r₁ r₁' : ℝ≥0∞}

/-- **The dual Strichartz estimate for the Schrödinger equation at every admissible pair with a
finite time exponent**: `2 ≤ q < ∞` and `2 / q + n / r = n / 2`, with `n ≥ 3` when `q = 2`, where
`p` and `r'` are the Hölder conjugates of `q` and `r`. There is `C` such that for every almost
everywhere strongly measurable `F : ℝ → L²(E)`,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^p_t L^{r'}_x}`.

For `q = 2` this is the endpoint estimate
`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint`, and for `2 < q` the
non-endpoint estimate `TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le [r'.HolderConjugate r]
    (hq : 2 ≤ q) (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      ‖∫ s, schrodingerPropagator ℂ (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  rcases hq.eq_or_lt with rfl | hq
  · obtain rfl := hpq.eq_two
    simpa using exists_enorm_integral_schrodingerPropagator_neg_le_of_endpoint (r' := r')
      (hn rfl) (by simpa using hqr)
  · exact exists_enorm_integral_schrodingerPropagator_neg_le hq hpq hqr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Two admissible pairs at the endpoint have the same spatial exponent. -/
private theorem eq_of_endpoint {r : ℝ≥0∞} (hn : 2 < Module.finrank ℝ E) (hr0 : r ≠ 0)
    (hr₁0 : r₁ ≠ 0) (hr : 1 + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hr₁ : 1 + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) : r = r₁ := by
  have hn0 : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast zero_lt_two.trans hn
    exact this.ne'
  have h : (r⁻¹).toReal = (r₁⁻¹).toReal := mul_left_cancel₀ hn0 (by linarith)
  exact inv_injective ((ENNReal.toReal_eq_toReal_iff' (ENNReal.inv_ne_top.2 hr0)
    (ENNReal.inv_ne_top.2 hr₁0)).1 h)

/-- **The inhomogeneous Strichartz estimate for the Schrödinger equation** in every dimension `n`,
in weak form, for any two admissible pairs with finite time exponents: `2 ≤ q, q₁ < ∞` with
`2 / q + n / r = n / 2` and `2 / q₁ + n / r₁ = n / 2`, and `n ≥ 3` when `q = 2` or `q₁ = 2`, where
`p`, `p₁`, `r'` and `r₁'` are the Hölder conjugates of `q`, `q₁`, `r` and `r₁`. There is `C` such
that for all almost everywhere strongly measurable `F, G : ℝ → L²(E)` for which `s ↦ S(-s) F(s)`
and `t ↦ S(-t) G(t)` are integrable,

`|∫ ∫_{s < t} ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L^{p₁}_t L^{r₁'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^{p₁}_t L^{r₁'}_x}` tested against `G`; for
`F` vanishing on negative times the inner integral runs over `(0, t)`. Either pair, or both, may
be the endpoint pair, and on the line either may be `(4, ∞)`. The integrability hypotheses are
qualitative: `C` does not depend on them. For a single non-endpoint pair,
`TauCeti.exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le` gives the
bound without them. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_integrable
    [r'.HolderConjugate r] [r₁'.HolderConjugate r₁]
    (hq : 2 ≤ q) (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hq₁ : 2 ≤ q₁) (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G → Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) →
      Integrable (fun t ↦ schrodingerPropagator ℂ (-t) (G t)) →
      ‖∫ t, ∫ s in Set.Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  by_cases h22 : q = 2 ∧ q₁ = 2
  · -- Both pairs at the endpoint: the estimate of Keel and Tao.
    obtain ⟨rfl, rfl⟩ := h22
    obtain rfl := hpq.eq_two
    obtain rfl := hpq₁.eq_two
    obtain rfl : r = r₁ := eq_of_endpoint (hn rfl) (ENNReal.HolderConjugate.ne_zero r r')
      (ENNReal.HolderConjugate.ne_zero r₁ r₁') (by simpa using hqr) (by simpa using hqr₁)
    have : r.HolderConjugate r' := (inferInstance : r'.HolderConjugate r).symm
    have : r.HolderConjugate r₁' := (inferInstance : r₁'.HolderConjugate r).symm
    obtain rfl : r' = r₁' := ENNReal.HolderConjugate.unique (p := r) (q := r') r₁'
    obtain ⟨C, hC⟩ :=
      exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_endpoint
        (r' := r') (hn rfl) (by simpa using hqr)
    -- `F` and `G` are integrable along with `s ↦ S(-s) F(s)` and `t ↦ S(-t) G(t)`.
    refine ⟨C, fun F G _ _ hSF hSG ↦ ?_⟩
    simpa using hC F G
      ((integrable_phasePropagator_apply_iff laplacianSymbol
        continuous_neg.aestronglyMeasurable).1 hSF)
      ((integrable_phasePropagator_apply_iff laplacianSymbol
        continuous_neg.aestronglyMeasurable).1 hSG)
  -- Otherwise `q₁' < q`, and the Christ–Kiselev lemma passes the bound on the untruncated pairing,
  -- which the two dual estimates give, to the region `s < t`.
  have := hpq.coe_ennreal
  have := hpq₁.coe_ennreal
  have h2 : 2 < (q : ℝ≥0∞) ∨ 2 < (q₁ : ℝ≥0∞) := by
    rw [not_and_or] at h22
    exact_mod_cast h22.imp hq.lt_of_ne' hq₁.lt_of_ne'
  obtain ⟨C₁, hC₁⟩ := exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le (E := E)
    (r' := r₁') hq₁ hn₁ hpq₁ hqr₁
  obtain ⟨C, hC⟩ := exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le (E := E)
    (r' := r') hq hn hpq hqr
  refine ⟨((1 - (2 : ℝ≥0∞) ^ (-((p₁ : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ - 1).toReal))⁻¹).toNNReal * C₁ * C,
    fun F G hF hG hSF hSG ↦ ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_mul]
  simp_rw [inner_schrodingerPropagator_sub_apply, ← adjoint_schrodingerPropagator]
  simp_rw [← adjoint_schrodingerPropagator] at hC₁ hC hSF hSG
  exact enorm_integral_setIntegral_Iio_inner_adjoint_le_of_holderConjugate
    (by exact_mod_cast hq) (by exact_mod_cast hq₁) h2 (fun F hF _ ↦ hC₁ F hF)
    (fun G hG _ ↦ hC G hG) hF hG hSF hSG

end TwoPairs

end TauCeti
