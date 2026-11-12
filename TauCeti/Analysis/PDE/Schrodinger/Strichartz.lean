/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Dispersive
public import TauCeti.Analysis.PDE.Strichartz.TTStar
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional

/-!
# Strichartz estimates for the Schrödinger equation

Let `S(t) = exp(itΔ)` be the Schrödinger propagator on a finite-dimensional real inner product
space `E` of dimension `n`. A pair `(q, r)` with `2 ≤ q, r ≤ ∞` is *admissible* when
`2 / q + n / r = n / 2`, and *non-endpoint* when moreover `q > 2`. This file proves the
Strichartz estimates at the non-endpoint admissible pairs with `q < ∞`, by the `TT*` argument of
`TauCeti.Analysis.PDE.Strichartz.TTStar`: the time pairings `S(s) S(t)* = S(s - t)` decay from
`L^{r'}` to `L^r` like `|s - t| ^ (-n (1/2 - 1/r)) = |s - t| ^ (-2 / q)`.

* **On the line, at `(4, ∞)`.** For `n = 1` the dispersive estimate
  `‖S(t) g‖_∞ ≤ (4π|t|)^(-1/2) ‖g‖₁` (`TauCeti.eLpNorm_schrodingerPropagator_le`) is already the
  decay of the pairings from `L¹` to `L^∞`, with no interpolation, so the estimates at `(4, ∞)`
  hold for functions with values in any complex Hilbert space `V`.
* **In every dimension.** For scalar functions the decay of the pairings is the dispersive
  estimate in `L^r` (`TauCeti.eLpNorm_schrodingerPropagator_le_of_memLp`), obtained from the
  `L¹ → L^∞` estimate and conservation of the `L²` norm by the Riesz–Thorin theorem. This gives,
  for every non-endpoint admissible pair `(q, r)` with `q < ∞`, the dual estimate
  `‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{q'}_t L^{r'}_x}`, the homogeneous estimate
  `‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` in weak form, and the two estimates for the Duhamel term
  `∫_0^t S(t - s) F(s) ds` of the inhomogeneous equation `i ∂ₜu + Δu = F` with forcing in
  `L^{q'}_t L^{r'}_x`: its bound in `L^∞_t L²_x` and, in weak form, in `L^q_t L^r_x`. Since the
  `TT*` argument bounds the absolute values of the time pairings, the latter holds for every
  truncation `s ∈ A(t)` of the Duhamel integral.

## Main declarations

* `TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le`: the dual estimate on the line.
* `TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le`: the homogeneous estimate on the
  line in weak form.
* `TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_admissible`: the dual estimate
  in every dimension.
* `TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le_of_admissible`: the homogeneous
  estimate in every dimension, in weak form.
* `TauCeti.exists_enorm_setIntegral_schrodingerPropagator_sub_le_of_admissible`: the Duhamel term
  in `L^∞_t L²_x`.
* `TauCeti.exists_enorm_integral_inner_setIntegral_schrodingerPropagator_sub_le_of_admissible`:
  the retarded estimate, the Duhamel term in `L^q_t L^r_x`, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- On the line, the time pairings of the Schrödinger propagator decay from `L¹` to `L^∞` like
`|s - t| ^ (-1/2)`. -/
private theorem eLpNorm_schrodingerPropagator_adjoint_le (hE : Module.finrank ℝ E = 1)
    {s t : ℝ} (hst : s ≠ t) (g : Lp V 2 (volume : Measure E)) :
    eLpNorm (schrodingerPropagator V s (((schrodingerPropagator V t)†) g)) ∞ volume ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) *
        ‖s - t‖ₑ ^ (-(2 / (4 : ℝ≥0) : ℝ)) * eLpNorm g 1 volume := by
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have hk : ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) * ‖s - t‖ₑ ^ (-(2 / (4 : ℝ≥0) : ℝ)) =
      ENNReal.ofReal ((4 * Real.pi * |s - t|) ^ (-(Module.finrank ℝ E : ℝ) / 2)) := by
    rw [hE, ← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_pos (abs_pos.2 hst'), ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow (by positivity) (abs_nonneg _)]
    norm_num
  rw [schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator,
    ← phasePropagator_add_apply, ← sub_eq_add_neg, ← schrodingerPropagator_def, hk]
  by_cases hg : Integrable g
  · exact eLpNorm_schrodingerPropagator_le hst' g hg
  · have hg' : eLpNorm g 1 volume = ∞ := by
      by_contra h
      exact hg (memLp_one_iff_integrable.1 (lt_top_iff_ne_top.2 h))
    rw [hg', ENNReal.mul_top (by positivity)]
    exact le_top

private theorem holderConjugate_four_div_three_four : (4 / 3 : ℝ≥0).HolderConjugate 4 := by
  rw [← NNReal.holderConjugate_coe_iff, Real.holderConjugate_iff]
  norm_num

/-- **The dual Strichartz estimate for the Schrödinger equation on the line**, at the admissible
pair `(4, ∞)`. There is `C` such that for every almost everywhere strongly measurable
`F : ℝ → L²(E, V)` on a one-dimensional space `E` for which `s ↦ S(-s) F(s)` is integrable,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{4/3}_t L¹_x}`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le (hE : Module.finrank ℝ E = 1) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp V 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ schrodingerPropagator V (-s) (F s)) →
      ‖∫ s, schrodingerPropagator V (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s : ℝ ↦ eLpNorm (F s) 1 (volume : Measure E)) ((4 / 3 : ℝ≥0) : ℝ≥0∞)
          volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp V 2 (volume : Measure E))
    (E := V) (X := E) (μ := volume) (r := ∞) (r' := 1) (by norm_num : (2 : ℝ≥0) < 4)
    holderConjugate_four_div_three_four
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun F hF hSF => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  simpa only [adjoint_phasePropagator] using hC (schrodingerPropagator V) _
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le hE hst g) F hF
    (by simpa only [adjoint_phasePropagator] using hSF)

/-- **The Strichartz estimate for the Schrödinger equation on the line**, at the admissible pair
`(4, ∞)`, in weak form. There is `C` such that for every `f ∈ L²(E, V)` on a one-dimensional space
`E` and every almost everywhere strongly measurable `G : ℝ → L²(E, V)` for which
`t ↦ S(-t) G(t)` is integrable,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L^{4/3}_t L¹_x}`.

This is `‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_schrodingerPropagator_le (hE : Module.finrank ℝ E = 1) :
    ∃ C : ℝ≥0, ∀ (f : Lp V 2 (volume : Measure E)) (G : ℝ → Lp V 2 (volume : Measure E)),
      AEStronglyMeasurable G → Integrable (fun t ↦ schrodingerPropagator V (-t) (G t)) →
      ‖∫ t, ⟪schrodingerPropagator V t f, G t⟫_ℂ‖ₑ ≤
        C * ‖f‖ₑ * eLpNorm (fun t : ℝ ↦ eLpNorm (G t) 1 (volume : Measure E))
          ((4 / 3 : ℝ≥0) : ℝ≥0∞) volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp V 2 (volume : Measure E)) (E := V) (X := E) (μ := volume) (r := ∞) (r' := 1)
    (by norm_num : (2 : ℝ≥0) < 4) holderConjugate_four_div_three_four
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun f G hG hSG => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  exact hC (schrodingerPropagator V) _
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le hE hst g) f G hG
    (by simpa only [adjoint_phasePropagator] using hSG)

/-! ### Every dimension -/

section EveryDimension

variable {q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- Along the admissible line `2 / q + n / r = n / 2` in dimension `n`, the time pairings of the
Schrödinger propagator decay from `L^{r'}` to `L^r` like `|s - t| ^ (-2 / q)`, with constant
`(4π) ^ (-2 / q)`. -/
private theorem eLpNorm_schrodingerPropagator_adjoint_le_of_admissible (hq : 0 < q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * r⁻¹.toReal = Module.finrank ℝ E / 2)
    {s t : ℝ} (hst : s ≠ t) (g : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm (schrodingerPropagator ℂ s (((schrodingerPropagator ℂ t)†) g)) r volume ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) *
        eLpNorm g r' volume := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have hexp : n * (1 / 2 - r⁻¹.toReal) = 2 / q := by linarith
  -- Admissibility with `q < ∞` forces `2 ≤ r`, so the dispersive estimate in `L^r` applies.
  have h2r : 2 ≤ r := by
    have hpos : 0 < n * (1 / 2 - r⁻¹.toReal) := hexp ▸ by positivity
    have hlt : r⁻¹.toReal < 2⁻¹ := by
      have := pos_of_mul_pos_right hpos (by positivity)
      linarith
    have hr : r⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')
    rw [← ENNReal.inv_le_inv, ← ENNReal.ofReal_toReal hr]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlt |>.le.trans_eq
      (by rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat])
  have hk : ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) =
      ENNReal.ofReal ((4 * Real.pi * |s - t|) ^ (-n * (1 / 2 - r⁻¹.toReal))) := by
    rw [neg_mul, hexp, ← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_pos (abs_pos.2 hst'), ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow (by positivity) (abs_nonneg _)]
  rw [schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator,
    ← phasePropagator_add_apply, ← sub_eq_add_neg, ← schrodingerPropagator_def, hk]
  rcases eq_or_ne (eLpNorm g r' volume) ∞ with hg | hg
  · rw [hg, ENNReal.mul_top (by positivity)]
    exact le_top
  · exact eLpNorm_schrodingerPropagator_le_of_memLp hst' h2r g (lt_top_iff_ne_top.2 hg)

variable {p : ℝ≥0}

/-- **The dual Strichartz estimate for the Schrödinger equation**, in every dimension `n` and at
every non-endpoint admissible pair: let `2 < q < ∞` with Hölder conjugate `p`, and let `r` with
Hölder conjugate `r'` satisfy `2 / q + n / r = n / 2`. There is `C` such that for every almost
everywhere strongly measurable `F : ℝ → L²(E)` for which `s ↦ S(-s) F(s)` is integrable,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le_of_admissible (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * r⁻¹.toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) →
      ‖∫ s, schrodingerPropagator ℂ (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s : ℝ ↦ eLpNorm (F s) r' (volume : Measure E)) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E))
    (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun F hF hSF => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  simpa only [adjoint_phasePropagator] using hC (schrodingerPropagator ℂ) _
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le_of_admissible
      (zero_lt_two.trans hq) hqr hst g) F hF
    (by simpa only [adjoint_phasePropagator] using hSF)

/-- **The Strichartz estimate for the Schrödinger equation**, in every dimension `n` and at every
non-endpoint admissible pair, in weak form: let `2 < q < ∞` with Hölder conjugate `p`, and let `r`
with Hölder conjugate `r'` satisfy `2 / q + n / r = n / 2`. There is `C` such that for every
`f ∈ L²(E)` and every almost everywhere strongly measurable `G : ℝ → L²(E)` for which
`t ↦ S(-t) G(t)` is integrable,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_schrodingerPropagator_le_of_admissible (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * r⁻¹.toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
      AEStronglyMeasurable G → Integrable (fun t ↦ schrodingerPropagator ℂ (-t) (G t)) →
      ‖∫ t, ⟪schrodingerPropagator ℂ t f, G t⟫_ℂ‖ₑ ≤
        C * ‖f‖ₑ * eLpNorm (fun t : ℝ ↦ eLpNorm (G t) r' (volume : Measure E)) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun f G hG hSG => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  exact hC (schrodingerPropagator ℂ) _
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le_of_admissible
      (zero_lt_two.trans hq) hqr hst g) f G hG
    (by simpa only [adjoint_phasePropagator] using hSG)

/-- **The energy estimate for the Duhamel term**, at every non-endpoint admissible pair in every
dimension `n`: let `2 < q < ∞` with Hölder conjugate `p`, and let `r` with Hölder conjugate `r'`
satisfy `2 / q + n / r = n / 2`. There is `C` such that for every almost everywhere strongly
measurable `F : ℝ → L²(E)` for which `s ↦ S(-s) F(s)` is integrable, every time `t` and every
measurable set `A` of times,

`‖∫_A S(t - s) F(s) ds‖₂ ≤ C ‖F‖_{L^p_t L^{r'}_x}`.

With `A = (0, t]` this bounds the Duhamel term `∫_0^t S(t - s) F(s) ds` of the inhomogeneous
equation `i ∂ₜu + Δu = F` in `L^∞_t L²_x`, uniformly in `t`. -/
theorem exists_enorm_setIntegral_schrodingerPropagator_sub_le_of_admissible (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * r⁻¹.toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) → ∀ (t : ℝ) {A : Set ℝ},
      MeasurableSet A →
      ‖∫ s in A, schrodingerPropagator ℂ (t - s) (F s)‖ₑ ≤
        C * eLpNorm (fun s : ℝ ↦ eLpNorm (F s) r' (volume : Measure E)) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_schrodingerPropagator_neg_le_of_admissible (E := E)
    (r' := r') hq hpq hqr
  refine ⟨C, fun F hF hSF t A hA => ?_⟩
  have hind : (fun s ↦ schrodingerPropagator ℂ (-s) (A.indicator F s)) =
      A.indicator (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) := by
    ext1 s
    by_cases hs : s ∈ A <;> simp [hs]
  -- `S(t - s) = S(t) S(-s)`, and `S(t)` is unitary.
  have hrw : ∫ s in A, schrodingerPropagator ℂ (t - s) (F s) =
      schrodingerPropagator ℂ t (∫ s, schrodingerPropagator ℂ (-s) (A.indicator F s)) := by
    simp_rw [sub_eq_add_neg, schrodingerPropagator_def, phasePropagator_add_apply,
      ← schrodingerPropagator_def]
    rw [hind, integral_indicator hA,
      ← ContinuousLinearMap.integral_comp_comm _ hSF.integrableOn]
  rw [hrw, ← ofReal_norm, norm_phasePropagator_apply, ofReal_norm]
  refine (hC _ (hF.indicator hA) (hind ▸ hSF.indicator hA)).trans ?_
  gcongr
  refine eLpNorm_mono_enorm (AEStronglyMeasurable.aemeasurable_eLpNorm_Lp (hF.indicator hA) .rfl
    r').aestronglyMeasurable fun s ↦ ?_
  by_cases hs : s ∈ A
  · simp [hs]
  · simp [hs, eLpNorm_congr_ae AEEqFun.coeFn_zero]

/-- **The retarded Strichartz estimate for the Schrödinger equation**, at every non-endpoint
admissible pair in every dimension `n`, in weak form: let `2 < q < ∞` with Hölder conjugate `p`,
and let `r` with Hölder conjugate `r'` satisfy `2 / q + n / r = n / 2`. There is `C` such that for
all almost everywhere strongly measurable `F, G : ℝ → L²(E)` for which `s ↦ S(-s) F(s)` is
integrable, and every family `A(t)` of sets of times,

`|∫ ⟪∫_{A(t)} S(t - s) F(s) ds, G(t)⟫ dt| ≤ C ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

With `A(t) = (0, t]` this is `‖∫_0^t S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^p_t L^{r'}_x}`,
the estimate for the Duhamel term of `i ∂ₜu + Δu = F`, tested against `G`. -/
theorem exists_enorm_integral_inner_setIntegral_schrodingerPropagator_sub_le_of_admissible
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * r⁻¹.toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G → Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) →
      ∀ A : ℝ → Set ℝ,
      ‖∫ t, ⟪∫ s in A t, schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s : ℝ ↦ eLpNorm (F s) r' (volume : Measure E)) p volume *
          eLpNorm (fun t : ℝ ↦ eLpNorm (G t) r' (volume : Measure E)) p volume := by
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  set K := ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ)))
  refine ⟨C * K.toNNReal, fun F G hF hG hSF A => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  -- `S(t - s) = S(t) S(-s)`.
  have hS (t s : ℝ) (f : Lp ℂ 2 (volume : Measure E)) : schrodingerPropagator ℂ (t - s) f =
      schrodingerPropagator ℂ t (schrodingerPropagator ℂ (-s) f) := by
    rw [sub_eq_add_neg, schrodingerPropagator_def, phasePropagator_add_apply]
  -- These are the `TT*` pairings: `⟪S(t - s) F(s), G(t)⟫ = ⟪S(-s) F(s), S(-t) G(t)⟫`.
  have hpair (t s : ℝ) : ‖⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ =
      ‖⟪((schrodingerPropagator ℂ t)†) (G t), ((schrodingerPropagator ℂ s)†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left, schrodingerPropagator_def s,
      adjoint_phasePropagator, ← schrodingerPropagator_def, ← hS, ← ofReal_norm, ← ofReal_norm,
      norm_inner_symm]
  calc ‖∫ t, ⟪∫ s in A t, schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ
      ≤ ∫⁻ t, ‖⟪∫ s in A t, schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t, ∫⁻ s, ‖⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ := by
        refine lintegral_mono fun t ↦ ?_
        have hint : IntegrableOn (fun s ↦ schrodingerPropagator ℂ (t - s) (F s)) (A t) := by
          simp_rw [hS t]
          exact ((schrodingerPropagator ℂ t).integrable_comp hSF).integrableOn
        rw [← ofReal_norm, norm_inner_symm, ofReal_norm, ← integral_inner hint]
        refine (enorm_integral_le_lintegral_enorm _).trans
          ((setLIntegral_le_lintegral _ _).trans_eq (lintegral_congr fun s ↦ ?_))
        rw [← ofReal_norm, norm_inner_symm, ofReal_norm]
    _ = ∫⁻ t, ∫⁻ s, ‖⟪((schrodingerPropagator ℂ t)†) (G t),
          ((schrodingerPropagator ℂ s)†) (F s)⟫_ℂ‖ₑ := by simp_rw [hpair]
    _ ≤ C * K * eLpNorm (fun t : ℝ ↦ eLpNorm (G t) r' (volume : Measure E)) p volume *
          eLpNorm (fun s : ℝ ↦ eLpNorm (F s) r' (volume : Measure E)) p volume :=
        hC (schrodingerPropagator ℂ) K
          (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le_of_admissible
            (zero_lt_two.trans hq) hqr hst g) G F hG hF
    _ = _ := by ring

end EveryDimension

end TauCeti
