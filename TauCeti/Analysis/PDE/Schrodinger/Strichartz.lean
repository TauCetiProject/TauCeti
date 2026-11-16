/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Dispersive
public import TauCeti.Analysis.PDE.Strichartz.TTStar

/-!
# Strichartz estimates for the Schrödinger equation

On a one-dimensional real inner product space, the dispersive estimate
`‖S(t) g‖_∞ ≤ (4π|t|)^(-1/2) ‖g‖₁` for the Schrödinger propagator `S(t) = exp(itΔ)`
(`TauCeti.eLpNorm_schrodingerPropagator_le`) is already an `L¹ → L^∞` bound for the time pairings
`S(s) S(t)* = S(s - t)` with decay `|s - t| ^ (-1/2) = |s - t| ^ (-2 / 4)`. So the `TT*` argument of
`TauCeti.Analysis.PDE.Strichartz.TTStar` applies with `(q, r) = (4, ∞)`, the admissible pair of
dimension one with `r = ∞`, without any interpolation. It gives the dual Strichartz estimate

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{4/3}_t L¹_x}`

and the Strichartz estimate `‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂` tested against
`G ∈ L^{4/3}_t L¹_x`, for functions with values in any complex Hilbert space.

In every dimension `n`, the dispersive estimate from `L^{r'}` to `L^r`,
`‖S(t) g‖_r ≤ (4π|t|)^(-n (1/2 - 1/r)) ‖g‖_{r'}`
(`TauCeti.eLpNorm_schrodingerPropagator_le_of_memLp`), obtained from the Riesz–Thorin theorem for
complex-valued functions, decays like `|t| ^ (-2 / q)` exactly when `(q, r)` is admissible,

`2 / q + n / r = n / 2`.

For every such pair with `2 < q < ∞`, that is every admissible pair other than the energy pair
`(∞, 2)` and the endpoint `q = 2`, the `TT*` argument gives the dual estimate
`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{q'}_t L^{r'}_x}`, the homogeneous estimate
`‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` in weak form, and the bilinear bound on the Duhamel pairings
`⟪S(t - s) F(s), G(t)⟫`, whose restriction to `s < t` is the retarded (inhomogeneous) estimate
`‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^{q'}_t L^{r'}_x}` in weak form.

## Main declarations

* `TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_finrank_eq_one`: the dual
  estimate on the line at `(4, ∞)`.
* `TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le_of_finrank_eq_one`: the
  homogeneous estimate on the line at `(4, ∞)`, in weak form.
* `TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le`: the dual estimate in every
  dimension.
* `TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le`: the homogeneous estimate in
  every dimension, in weak form.
* `TauCeti.exists_lintegral_lintegral_enorm_inner_schrodingerPropagator_sub_le`: the bilinear
  estimate for the Duhamel pairings in every dimension.
* `TauCeti.exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le`: the retarded
  estimate in every dimension, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
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
private theorem eLpNorm_schrodingerPropagator_adjoint_le_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 1) {s t : ℝ} (hst : s ≠ t) (g : Lp V 2 (volume : Measure E)) :
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
theorem exists_enorm_integral_schrodingerPropagator_neg_le_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 1) :
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
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le_of_finrank_eq_one hE hst g) F hF
    (by simpa only [adjoint_phasePropagator] using hSF)

/-- **The Strichartz estimate for the Schrödinger equation on the line**, at the admissible pair
`(4, ∞)`, in weak form. There is `C` such that for every `f ∈ L²(E, V)` on a one-dimensional space
`E` and every almost everywhere strongly measurable `G : ℝ → L²(E, V)` for which
`t ↦ S(-t) G(t)` is integrable,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L^{4/3}_t L¹_x}`.

This is `‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_schrodingerPropagator_le_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 1) :
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
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le_of_finrank_eq_one hE hst g) f G hG
    (by simpa only [adjoint_phasePropagator] using hSG)

/-! ### Every dimension, at the non-endpoint admissible pairs -/

section Admissible

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- In every dimension `n`, the time pairings `S(s) S(t)* = S(s - t)` of the Schrödinger
propagator decay from `L^{r'}` to `L^r` like `|s - t| ^ (-2 / q)` along an admissible pair
`2 / q + n / r = n / 2` with `2 < q`. -/
private theorem eLpNorm_schrodingerPropagator_adjoint_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    {s t : ℝ} (hst : s ≠ t) (g : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm (schrodingerPropagator ℂ s (((schrodingerPropagator ℂ t)†) g)) r volume ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) *
        eLpNorm g r' volume := by
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  -- Admissibility with `2 < q` forces `n > 0`, hence `1 / r < 1 / 2`, so `2 ≤ r`.
  have hr : 2 ≤ r := by
    have hlt : (r⁻¹).toReal < 2⁻¹ := by nlinarith
    rw [← ENNReal.inv_le_inv,
      ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')),
      ← ENNReal.ofReal_toReal (a := 2⁻¹) (by simp)]
    exact ENNReal.ofReal_le_ofReal (hlt.le.trans_eq (by simp))
  have hk : ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) =
      ENNReal.ofReal ((4 * Real.pi * |s - t|) ^
        (-(Module.finrank ℝ E : ℝ) * (1 / 2 - (r⁻¹).toReal))) := by
    have hexp : -(Module.finrank ℝ E : ℝ) * (1 / 2 - (r⁻¹).toReal) = -(2 / q : ℝ) := by
      linarith
    rw [hexp, ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos (abs_pos.2 hst'),
      ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by positivity) (abs_nonneg _)]
  rw [schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator,
    ← phasePropagator_add_apply, ← sub_eq_add_neg, ← schrodingerPropagator_def, hk]
  by_cases hg : MemLp g r' volume
  · exact eLpNorm_schrodingerPropagator_le_of_memLp hst' hr g hg
  · rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)), ENNReal.mul_top (by positivity)]
    exact le_top

/-- **The bilinear Strichartz estimate for the Schrödinger equation** in every dimension `n`, at
a non-endpoint admissible pair: `2 < q < ∞` and `2 / q + n / r = n / 2`, with `p` and `r'` the
Hölder conjugates of `q` and `r`. There is `C` such that for all almost everywhere strongly
measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪S(t - s) F(s), G(t)⟫| ds dt ≤ C ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(s, t)` plane, such as the retarded region `s < t`
(`TauCeti.exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le`). -/
theorem exists_lintegral_lintegral_enorm_inner_schrodingerPropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ∫⁻ t, ∫⁻ s, ‖⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ)))).toNNReal, fun F G hF hG => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  -- The Duhamel pairing `⟪S(t - s) F(s), G(t)⟫` is the time pairing `⟪S(t)* G(t), S(s)* F(s)⟫`
  -- up to complex conjugation.
  have hpair (s t : ℝ) : ‖⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ =
      ‖⟪((schrodingerPropagator ℂ t)†) (G t), ((schrodingerPropagator ℂ s)†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left, schrodingerPropagator_def,
      schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator,
      ← phasePropagator_add_apply, ← sub_eq_add_neg, ← ofReal_norm, ← ofReal_norm,
      norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC (schrodingerPropagator ℂ) _
        (fun s t hst g ↦ eLpNorm_schrodingerPropagator_adjoint_le hq hqr hst g)
        G F hG hF
    _ = _ := by ring

/-- **The retarded Strichartz estimate for the Schrödinger equation** in every dimension `n`, in
weak form, at a non-endpoint admissible pair: `2 < q < ∞` and `2 / q + n / r = n / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. There is `C` such that for all almost everywhere
strongly measurable `F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate `‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^p_t L^{r'}_x}`
tested against `G`; for `F` vanishing on negative times the inner integral runs over `(0, t)`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ‖∫ t, ∫ s in Set.Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    exists_lintegral_lintegral_enorm_inner_schrodingerPropagator_sub_le (r' := r') hq hpq hqr
  refine ⟨C, fun F G hF hG => ?_⟩
  calc _ ≤ ∫⁻ t, ‖∫ s in Set.Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s in Set.Iio t, ‖⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s, ‖⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ setLIntegral_le_lintegral _ _
    _ ≤ _ := hC F G hF hG

/-- **The dual Strichartz estimate for the Schrödinger equation** in every dimension `n`, at a
non-endpoint admissible pair: `2 < q < ∞` and `2 / q + n / r = n / 2`, with `p` and `r'` the
Hölder conjugates of `q` and `r`. There is `C` such that for every almost everywhere strongly
measurable `F : ℝ → L²(E)` for which `s ↦ S(-s) F(s)` is integrable,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) →
      ‖∫ s, schrodingerPropagator ℂ (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E))
    (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun F hF hSF => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  simpa only [adjoint_phasePropagator] using hC (schrodingerPropagator ℂ) _
    (fun s t hst g ↦ eLpNorm_schrodingerPropagator_adjoint_le hq hqr hst g) F hF
    (by simpa only [adjoint_phasePropagator] using hSF)

/-- **The Strichartz estimate for the Schrödinger equation** in every dimension `n`, in weak
form, at a non-endpoint admissible pair: `2 < q < ∞` and `2 / q + n / r = n / 2`, with `p` and
`r'` the Hölder conjugates of `q` and `r`. There is `C` such that for every `f ∈ L²(E)` and every
almost everywhere strongly measurable `G : ℝ → L²(E)` for which `t ↦ S(-t) G(t)` is integrable,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_schrodingerPropagator_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
      AEStronglyMeasurable G → Integrable (fun t ↦ schrodingerPropagator ℂ (-t) (G t)) →
      ‖∫ t, ⟪schrodingerPropagator ℂ t f, G t⟫_ℂ‖ₑ ≤
        C * ‖f‖ₑ * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2 / q : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun f G hG hSG => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  exact hC (schrodingerPropagator ℂ) _
    (fun s t hst g ↦ eLpNorm_schrodingerPropagator_adjoint_le hq hqr hst g) f G hG
    (by simpa only [adjoint_phasePropagator] using hSG)

end Admissible

end TauCeti
