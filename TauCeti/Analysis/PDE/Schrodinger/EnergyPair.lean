/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Duhamel
public import TauCeti.Analysis.PDE.Schrodinger.Strichartz
import TauCeti.Analysis.PDE.Schrodinger.Endpoint
import TauCeti.Analysis.PDE.Strichartz.EnergyPair
import TauCeti.MeasureTheory.Integral.ChristKiselev

/-!
# The energy pair in the Strichartz estimates for the Schrödinger equation

Besides the admissible pairs `(q, r)` with `2 ≤ q < ∞` and `2 / q + n / r = n / 2`, the
Strichartz estimates for the Schrödinger equation `i ∂ₜu + Δu = F`, `u(0) = f`, include the
**energy pair** `(∞, 2)`, whose dual exponents are `(1, 2)`. Along the energy pair alone the
estimate is the energy estimate `‖u(t)‖₂ ≤ ‖f‖₂ + ∫ ‖F(s)‖₂ ds`
(`TauCeti.norm_schrodingerDuhamel_le`), with constant `1`. This file proves the inhomogeneous
estimates in which the energy pair is combined with an admissible pair `(q, r)` with a finite time
exponent, in either order; for `q = 2`, in dimension `n ≥ 3`, this is the endpoint pair of Keel and
Tao. Write `S(t) = exp(itΔ)` for the Schrödinger propagator
`TauCeti.schrodingerPropagator`, and `p`, `r'` for the Hölder conjugates of `q`, `r`, so that
`L^p_t L^{r'}_x` is the dual Strichartz space of `(q, r)`. The pair `r = ∞` is allowed, so on the
line the pair `(4, ∞)` is covered.

* **forcing in `L¹_t L²_x`, solution in `L^q_t L^r_x`**: the retarded estimate
  `‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L¹_t L²_x}`, in weak form;
* **forcing in `L^p_t L^{r'}_x`, solution in `L^∞_t L²_x`**: the bound
  `‖∫_I S(t - s) F(s) ds‖₂ ≤ C ‖F‖_{L^p(I; L^{r'})}` for every set of times `I` and every time
  `t`, and with it the energy bound `‖u(t)‖₂ ≤ ‖f‖₂ + C ‖F‖_{L^p(Ι(0, t); L^{r'})}` for the
  solution `u` given by Duhamel's formula, with `C` independent of `t`.

Both estimates hold for every unitary group `exp(itω(D))` satisfying a dual estimate, see
`TauCeti.Analysis.PDE.Strichartz.EnergyPair`; here they are instantiated with the dual Strichartz
estimate at `(q, r)` (`TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le`). The
retarded
estimate (`TauCeti.enorm_integral_setIntegral_Iio_inner_phasePropagator_sub_le_eLpNorm_one`)
combines it with the energy pair's dual estimate `‖∫ S(-s) F(s) ds‖₂ ≤ ‖F‖_{L¹_t L²_x}` through
the Christ–Kiselev lemma, and the `L^∞_t L²_x` bound
(`TauCeti.enorm_setIntegral_phasePropagator_sub_le`) follows from it and the unitarity of `S(t)`.

## Main declarations

* `TauCeti.exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_eLpNorm_one`:
  the retarded estimate with forcing in `L¹_t L²_x`, in weak form.
* `TauCeti.exists_enorm_setIntegral_schrodingerPropagator_sub_le`: the `L^∞_t L²_x` bound for
  forcing in a dual Strichartz space.
* `TauCeti.exists_enorm_schrodingerDuhamel_le`: the energy bound for the solution given by
  Duhamel's formula with forcing in a dual Strichartz space.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* M. Christ and A. Kiselev, *Maximal functions associated to filtrations*, J. Funct. Anal. 179
  (2001), 409–425.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- **The inhomogeneous Strichartz estimate for the Schrödinger equation with forcing in the
energy space**, in every dimension `n`, in weak form: forcing in `L¹_t L²_x`, the dual space of
the energy pair `(∞, 2)`, and solution measured along an admissible pair with a finite time
exponent, `2 ≤ q < ∞` and `2 / q + n / r = n / 2`, with `n ≥ 3` when `q = 2`, where `p` and `r'` are
the Hölder conjugates of `q` and `r`. There is
`C` such that for all almost everywhere strongly measurable `F, G : ℝ → L²(E)` for which
`s ↦ S(-s) F(s)` and `t ↦ S(-t) G(t)` are integrable,

`|∫ ∫_{s < t} ⟪S(t - s) F(s), G(t)⟫ ds dt| ≤ C ‖F‖_{L¹_t L²_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate `‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L¹_t L²_x}`
tested against `G`. The integrability hypotheses are qualitative: `C` does not depend on them. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_eLpNorm_one
    (hq : 2 ≤ q) (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G → Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) →
      Integrable (fun t ↦ schrodingerPropagator ℂ (-t) (G t)) →
      ‖∫ t, ∫ s in Set.Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) 2 volume) 1 volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le (E := E)
    (r' := r') hq hn hpq hqr
  have hp : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hpq.lt.le
  set K : ℝ≥0∞ := (1 - 2 ^ (-(p : ℝ≥0∞)⁻¹.toReal))⁻¹
  have hK : K ≠ ∞ := inv_one_sub_two_rpow_neg_toReal_inv_ne_top
    (ENNReal.coe_ne_zero.2 hpq.ne_zero) ENNReal.coe_ne_top
  refine ⟨K.toNNReal * C, fun F G hF hG hSF hSG ↦ ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hK]
  exact enorm_integral_setIntegral_Iio_inner_phasePropagator_sub_le_eLpNorm_one hp
    ENNReal.coe_ne_top (fun G hG _ ↦ hC G hG) hF hG hSF hSG

/-- **The energy bound for the inhomogeneous Schrödinger equation with forcing in a dual
Strichartz space**, in every dimension `n`: solution measured along the energy pair `(∞, 2)` and
forcing in the dual space of an admissible pair with a finite time exponent, `2 ≤ q < ∞` and
`2 / q + n / r = n / 2`, with `n ≥ 3` when `q = 2`, where `p` and `r'` are the Hölder conjugates of
`q` and `r`. There is `C` such that for every `F : ℝ → L²(E)`, every measurable set of times `I` on
which `F` is almost everywhere strongly measurable and `s ↦ S(-s) F(s)` is integrable, and every
time `t`,

`‖∫_I S(t - s) F(s) ds‖₂ ≤ C ‖F‖_{L^p(I; L^{r'})}`.

For `I = (-∞, t)` this is the retarded estimate
`‖∫_{s < t} S(t - s) F(s) ds‖_{L^∞_t L²_x} ≤ C ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_setIntegral_schrodingerPropagator_sub_le (hq : 2 ≤ q)
    (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (F : ℝ → Lp ℂ 2 (volume : Measure E)) {I : Set ℝ}, MeasurableSet I →
      AEStronglyMeasurable F (volume.restrict I) →
      IntegrableOn (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) I →
      ∀ t : ℝ, ‖∫ s in I, schrodingerPropagator ℂ (t - s) (F s)‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p (volume.restrict I) := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_schrodingerPropagator_neg_le_of_two_le (E := E)
    (r' := r') hq hn hpq hqr
  exact ⟨C, fun F I hI hF hSF t ↦
    enorm_setIntegral_phasePropagator_sub_le (fun F hF _ ↦ hC F hF) hI hF hSF t⟩

/-- **The energy bound for Duhamel's formula with forcing in a dual Strichartz space**, in every
dimension `n`, along an admissible pair with a finite time exponent: `2 ≤ q < ∞` and
`2 / q + n / r = n / 2`, with `n ≥ 3` when `q = 2`, where `p` and `r'` are the Hölder conjugates of
`q` and `r`. There is `C` such that for every
`f ∈ L²(E)`, every `F : ℝ → L²(E)` and every time `t` such that, on `Ι(0, t)`, `F` is almost
everywhere strongly measurable and `s ↦ S(-s) F(s)` is integrable, the solution
`u(t) = S(t) f - i ∫_0^t S(t - s) F(s) ds` of `i ∂ₜu + Δu = F`, `u(0) = f`, satisfies

`‖u(t)‖₂ ≤ ‖f‖₂ + C ‖F‖_{L^p(Ι(0, t); L^{r'})}`,

where `Ι(0, t)` is `(0, t]` for `t ≥ 0` and `(t, 0]` for `t ≤ 0`. The constant does not depend on
`t`, so this is the bound `‖u‖_{L^∞(I; L²)} ≤ ‖f‖₂ + C ‖F‖_{L^p(I; L^{r'})}` on every time
interval `I` containing `0`. -/
theorem exists_enorm_schrodingerDuhamel_le (hq : 2 ≤ q) (hn : q = 2 → 2 < Module.finrank ℝ E)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (F : ℝ → Lp ℂ 2 (volume : Measure E)) (t : ℝ),
      AEStronglyMeasurable F (volume.restrict (uIoc 0 t)) →
      IntegrableOn (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) (uIoc 0 t) →
      ‖schrodingerDuhamel f F t‖ₑ ≤
        ‖f‖ₑ + C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p (volume.restrict (uIoc 0 t)) := by
  obtain ⟨C, hC⟩ := exists_enorm_setIntegral_schrodingerPropagator_sub_le (E := E) (r' := r') hq
    hn hpq hqr
  refine ⟨C, fun f F t hF hSF ↦ ?_⟩
  have hint : ‖∫ s in (0 : ℝ)..t, schrodingerPropagator ℂ (t - s) (F s)‖ₑ =
      ‖∫ s in uIoc 0 t, schrodingerPropagator ℂ (t - s) (F s)‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  rw [schrodingerDuhamel_def]
  refine eNorm_sub_le.trans (add_le_add ?_ ?_)
  · rw [schrodingerPropagator_def, enorm_phasePropagator_apply]
  · rw [← ofReal_norm, norm_smul, Complex.norm_I, one_mul, ofReal_norm, hint]
    exact hC F measurableSet_uIoc hF hSF t

end TauCeti
