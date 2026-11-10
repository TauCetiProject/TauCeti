/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.PDE.Schrodinger.Basic
import TauCeti.Analysis.PDE.Schrodinger.Dispersive
import TauCeti.Analysis.PDE.Strichartz.TTStar

/-!
# The `TT*` estimates for the Schrödinger equation

On a real inner product space `E` of finite dimension `n`, a pair of exponents `2 ≤ q, r ≤ ∞` is
**Schrödinger admissible** when `2/q + n/r = n/2`. This file proves, for the admissible pairs
with `2 < q < ∞`, the two estimates of the `TT*` argument for the Schrödinger propagator
`S(t) = exp(itΔ)` (`TauCeti.schrodingerPropagator`) on `L²(E)`:

* **the bilinear estimate**
  (`TauCeti.exists_lintegral_lintegral_enorm_inner_schrodingerPropagator_le`)

  `∫∫ |⟪F(s), S(s - t) G(t)⟫| ds dt ≤ C ‖F‖_{L^{q'}_t L^{r'}_x} ‖G‖_{L^{q'}_t L^{r'}_x}`;

* **the dual homogeneous Strichartz estimate**
  (`TauCeti.exists_enorm_integral_schrodingerPropagator_le`)

  `‖∫ S(-t) G(t) dt‖_{L²} ≤ C ‖G‖_{L^{q'}_t L^{r'}_x}`,

with `C` depending only on `n` and `q`. By duality the second is the homogeneous Strichartz
estimate `‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{L²}`, and the first bounds the retarded double integral
over `s < t` behind the inhomogeneous estimates. Both are instances of the abstract `TT*` estimates
of `TauCeti.Analysis.PDE.Strichartz.TTStar` with `U(t) = S(t)`, for which
`U(s) U(t)* = S(s - t)`, with the energy bound `‖S(t)‖ ≤ 1` and the dispersive estimate
`‖S(t) g‖_∞ ≤ (4π|t|)^(-n/2) ‖g‖₁` (`TauCeti.eLpNorm_schrodingerPropagator_le`), so that the
decay exponent is `σ = n/2`. The admissible pairs left out are the energy pair `(∞, 2)`, where
both estimates are immediate from `‖S(t)‖ = 1`, and those with `q = 2`: the endpoint
`(2, 2n/(n - 2))` for `n ≥ 3` and the forbidden pair `(2, ∞)` for `n = 2`. In dimension `n = 1`
every admissible pair has `q ≥ 4`, and `(4, ∞)` is covered.

## Main declarations

* `TauCeti.exists_lintegral_lintegral_enorm_inner_schrodingerPropagator_le`: the bilinear
  estimate.
* `TauCeti.exists_enorm_integral_schrodingerPropagator_le`: the dual homogeneous Strichartz
  estimate.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. **120** (1998), 955–980,
  Theorem 1.2 and Section 3.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3.
-/

public section

noncomputable section

open MeasureTheory Module Real
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

/-- Schrödinger admissibility `2/q + n/r = n/2` with `q < ∞` forces `r > 2`. -/
private theorem two_le_of_two_mul_add_mul_eq {n : ℕ} {q r : ℝ≥0∞} (hq_top : q ≠ ∞)
    (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hqr : 2 * q⁻¹.toReal + n * r⁻¹.toReal = n / 2) : 2 ≤ r := by
  have ha : 0 < q⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hq_top) (ENNReal.inv_ne_top.2 hq0)
  have hn : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg (α := ℝ) n).eq_or_lt with h | h
    · rw [← h] at hqr
      linarith
    · exact h
  have hb : r⁻¹.toReal ≤ 2⁻¹ :=
    ((mul_lt_mul_iff_right₀ hn).1 (by linarith : (n : ℝ) * r⁻¹.toReal < n * 2⁻¹)).le
  rw [← ENNReal.inv_le_inv, ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hr0)]
  simpa using ENNReal.ofReal_le_ofReal hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The dispersive estimate in the form of the `TT*` argument:
`‖S(s) S(t)* g‖_∞ ≤ (4π)^(-n/2) |s - t|^(-n/2) ‖g‖₁` for `s ≠ t`. -/
private theorem eLpNorm_schrodingerPropagator_apply_adjoint_apply_le {s t : ℝ} (hst : s ≠ t)
    (g : Lp ℂ 2 (volume : Measure E)) (hg : Integrable g) :
    eLpNorm (schrodingerPropagator ℂ s
        (ContinuousLinearMap.adjoint (schrodingerPropagator ℂ t) g)) ∞ volume ≤
      ↑((4 * π) ^ (-(finrank ℝ E : ℝ) / 2)).toNNReal * ‖s - t‖ₑ ^ (-((finrank ℝ E : ℝ) / 2)) *
        eLpNorm g 1 volume := by
  rw [schrodingerPropagator_def, schrodingerPropagator_def, ← ContinuousLinearMap.comp_apply,
    phasePropagator_comp_adjoint, ← schrodingerPropagator_def]
  refine (eLpNorm_schrodingerPropagator_le (sub_ne_zero.2 hst) g hg).trans_eq ?_
  rw [Real.mul_rpow (by positivity) (abs_nonneg _), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos (abs_pos.2 (sub_ne_zero.2 hst)), ← Real.enorm_eq_ofReal_abs,
    neg_div, ENNReal.ofNNReal_toNNReal]

/-- **The bilinear `TT*` estimate for the Schrödinger equation, non-endpoint case.** Let
`2 < q < ∞` and `r` satisfy the admissibility condition `2/q + n/r = n/2`, `n = dim E`, with
Hölder conjugates `q'` and `r'`. There is a constant `C`, depending only on `n` and `q`, such that
for all `F, G : ℝ → L²(E)` with values almost everywhere in `L^{r'}`,

`∫∫ |⟪F(s), S(s - t) G(t)⟫| ds dt ≤ C ‖F‖_{L^{q'}L^{r'}} ‖G‖_{L^{q'}L^{r'}}`,

where `‖F‖_{L^{q'}L^{r'}}` is the `L^{q'}` norm of `s ↦ ‖F(s)‖_{r'}`. -/
theorem exists_lintegral_lintegral_enorm_inner_schrodingerPropagator_le {q q' r r' : ℝ≥0∞}
    [q.HolderConjugate q'] [r.HolderConjugate r'] (hq : 2 < q) (hq_top : q ≠ ∞)
    (hqr : 2 * q⁻¹.toReal + finrank ℝ E * r⁻¹.toReal = finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ {F G : ℝ → Lp ℂ 2 (volume : Measure E)},
      (∀ᵐ s, MemLp (F s) r' volume) → (∀ᵐ t, MemLp (G t) r' volume) →
        ∫⁻ s, ∫⁻ t, ‖⟪F s, schrodingerPropagator ℂ (s - t) (G t)⟫_ℂ‖ₑ ≤
          C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) q' *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) q' := by
  have hr := two_le_of_two_mul_add_mul_eq hq_top
    (ENNReal.HolderConjugate.ne_zero q q') (ENNReal.HolderConjugate.ne_zero r r') hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_apply_le
    (H := Lp ℂ 2 (volume : Measure E)) (μ := (volume : Measure E)) (σ := finrank ℝ E / 2)
    (q' := q') (r' := r') hq hq_top hr (by linear_combination hqr / 2)
  set D : ℝ≥0 := ((4 * π) ^ (-(finrank ℝ E : ℝ) / 2)).toNNReal
  refine ⟨C * D ^ (1 - 2 * r⁻¹.toReal), fun {F G} hF hG => ?_⟩
  have h := hC (M := 1) (D := D) (U := schrodingerPropagator ℂ)
    (fun t => by simpa using norm_phasePropagator_le (E := E) (F := ℂ) laplacianSymbol t)
    (fun s t hst g hg => eLpNorm_schrodingerPropagator_apply_adjoint_apply_le hst g hg) hF hG
  simp only [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply,
    phasePropagator_comp_adjoint, NNReal.one_rpow, mul_one] at h
  exact h.trans_eq (by push_cast; ring)

/-- **The dual homogeneous Strichartz estimate for the Schrödinger equation, non-endpoint case.**
Let `2 < q < ∞` and `r` satisfy the admissibility condition `2/q + n/r = n/2`, `n = dim E`, with
Hölder conjugates `q'` and `r'`. There is a constant `C`, depending only on `n` and `q`, such that

`‖∫ S(-t) G(t) dt‖_{L²} ≤ C ‖G‖_{L^{q'}L^{r'}}`

for every `G : ℝ → L²(E)` with values almost everywhere in `L^{r'}`. The integral is the Bochner
integral, which is `0` unless `t ↦ S(-t) G(t)` is integrable. -/
theorem exists_enorm_integral_schrodingerPropagator_le {q q' r r' : ℝ≥0∞}
    [q.HolderConjugate q'] [r.HolderConjugate r'] (hq : 2 < q) (hq_top : q ≠ ∞)
    (hqr : 2 * q⁻¹.toReal + finrank ℝ E * r⁻¹.toReal = finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ {G : ℝ → Lp ℂ 2 (volume : Measure E)}, (∀ᵐ t, MemLp (G t) r' volume) →
        ‖∫ t, schrodingerPropagator ℂ (-t) (G t)‖ₑ ≤
          C * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) q' := by
  have hr := two_le_of_two_mul_add_mul_eq hq_top
    (ENNReal.HolderConjugate.ne_zero q q') (ENNReal.HolderConjugate.ne_zero r r') hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_apply_le
    (H := Lp ℂ 2 (volume : Measure E)) (μ := (volume : Measure E)) (σ := finrank ℝ E / 2)
    (q' := q') (r' := r') hq hq_top hr (by linear_combination hqr / 2)
  set D : ℝ≥0 := ((4 * π) ^ (-(finrank ℝ E : ℝ) / 2)).toNNReal
  refine ⟨C * D ^ (2⁻¹ - r⁻¹.toReal), fun {G} hG => ?_⟩
  have hadj (t : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
      ContinuousLinearMap.adjoint (schrodingerPropagator ℂ t) g =
        schrodingerPropagator ℂ (-t) g := by
    rw [schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator]
  have h := hC (M := 1) (D := D) (U := schrodingerPropagator ℂ)
    (fun t => by simpa using norm_phasePropagator_le (E := E) (F := ℂ) laplacianSymbol t)
    (fun s t hst g hg => eLpNorm_schrodingerPropagator_apply_adjoint_apply_le hst g hg) hG
  simp only [hadj, NNReal.one_rpow, mul_one] at h
  exact h.trans_eq (by push_cast; ring)

end TauCeti
