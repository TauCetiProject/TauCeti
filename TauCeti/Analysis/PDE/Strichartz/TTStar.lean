/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Integral.RieszPotential
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional

/-!
# The non-endpoint `TT*` argument

Let `U(t) : H → L²(X, μ)`, `t ∈ ℝ`, be a family of bounded operators from a Hilbert space into
an `L²` space, for instance a unitary propagator `exp(itΔ)` on `H = L²(ℝⁿ)`. Strichartz estimates
bound `t ↦ U(t) f` in the mixed norm `L^q_t L^r_x`. By duality, they are equivalent to bounds on
`∫ U(s)* F(s) ds` in `H` for `F` in the dual mixed norm `L^{q'}_t L^{r'}_x`, and the `TT*`
argument reduces those to the time pairings `U(s) U(t)*`:

`‖∫ U(s)* F(s) ds‖² = ∫∫ ⟪U(s)* F(s), U(t)* F(t)⟫ ds dt = ∫∫ ⟪F(s), U(s) U(t)* F(t)⟫ ds dt`.

Suppose these pairings decay like `|s - t| ^ (-2 / q)` from `L^{r'}` to `L^r`:

`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}`,  `s ≠ t`.

For a family with the energy bound `‖U(t)‖ ≤ 1` and the dispersive bound
`‖U(s) U(t)* g‖_∞ ≤ |s - t| ^ (-σ) ‖g‖₁`, Riesz–Thorin interpolation gives this with
`2 / q = σ (1 - 2 / r)`, which is exactly the condition `1 / q + σ / r = σ / 2` that `(q, r)` be
`σ`-admissible. For the Schrödinger propagator on `ℝⁿ`, `σ = n / 2`.

Hölder's inequality in space then bounds each pairing by
`A |s - t| ^ (-2 / q) ‖F(s)‖_{r'} ‖G(t)‖_{r'}`, and when `2 < q < ∞` the time integral of this
kernel is a fractional integral of order `1 - 2 / q` on `ℝ`. The Hardy–Littlewood–Sobolev
inequality maps `L^{q'}` to `L^q` under it, so the double integral is at most
`C A ‖F‖_{L^{q'} L^{r'}} ‖G‖_{L^{q'} L^{r'}}`, with `C` independent of the family `U`, of `A`
and of `F` and `G`. The bound is on the double integral of the absolute values of the pairings, so
it also controls every truncation of the double integral, for instance to `s < t`, which is the
form taken by retarded (Duhamel) estimates.

The mixed norm of a function `F : ℝ → L²(X, μ)` is written
`eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p volume`; for almost everywhere strongly measurable `F` the
inner norm is an almost everywhere measurable function of time
(`MeasureTheory.AEStronglyMeasurable.aemeasurable_eLpNorm_Lp`).

The endpoint `q = 2`, where the time kernel `|s - t| ^ (-1)` is not locally integrable and
Hardy–Littlewood–Sobolev fails, needs the Keel–Tao argument instead.

## Main declarations

* `TauCeti.exists_lintegral_lintegral_enorm_inner_adjoint_le`: the bilinear `TT*` estimate
  `∫∫ |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤ C A ‖F‖_{L^{q'} L^{r'}} ‖G‖_{L^{q'} L^{r'}}`.
* `TauCeti.exists_enorm_integral_adjoint_le`: the dual homogeneous estimate
  `‖∫ U(s)* F(s) ds‖ ≤ C A ^ (1 / 2) ‖F‖_{L^{q'} L^{r'}}`.
* `TauCeti.exists_enorm_integral_inner_apply_le`: the homogeneous estimate in weak form,
  `|∫ ⟪U(t) f, G(t)⟫ dt| ≤ C A ^ (1 / 2) ‖f‖ ‖G‖_{L^{q'} L^{r'}}`.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
* J. Ginibre and G. Velo, *The global Cauchy problem for the nonlinear Schrödinger equation
  revisited*, Ann. Inst. H. Poincaré Anal. Non Linéaire 2 (1985), 309–327.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- A single time pairing: Hölder's inequality in space and the decay of `U(s) U(t)*` bound
`|⟪U(s)* f, U(t)* g⟫|` by `A |s - t| ^ (-γ) ‖f‖_{r'} ‖g‖_{r'}`. -/
private theorem enorm_inner_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞} {γ : ℝ}
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {s t : ℝ} (hst : s ≠ t) (f g : Lp E 2 μ) :
    ‖⟪((U s)†) f, ((U t)†) g⟫_𝕜‖ₑ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm f r' μ * eLpNorm g r' μ := by
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  calc _ ≤ eLpNorm f r' μ * eLpNorm (U s (((U t)†) g)) r μ := enorm_integral_inner_le
    _ ≤ eLpNorm f r' μ * (A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ) := by
        gcongr
        exact hU s t hst g
    _ = _ := by ring

/-- **The bilinear `TT*` estimate.** Let `2 < q < ∞` with Hölder conjugate `p`, and let
`U(t) : H → L²(X, μ)` be bounded operators whose time pairings decay from `L^{r'}` to `L^r`,
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for almost everywhere strongly
measurable `F, G : ℝ → L²(X, μ)`,

`∫∫ |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤ C A ‖F‖_{L^p L^{r'}} ‖G‖_{L^p L^{r'}}`,

with `C` independent of the family `U`, of `A` and of `F` and `G`. Since the integrand is the
absolute value of the pairing, the same bound holds for the integral over any part of the
`(s, t)` plane, such as `s < t`. -/
theorem exists_lintegral_lintegral_enorm_inner_adjoint_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ F G : ℝ → Lp E 2 μ, AEStronglyMeasurable F → AEStronglyMeasurable G →
        ∫⁻ s, ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p *
            eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_two.trans hq
  have hp : 1 < p := hpq.lt
  -- The time exponents fit the Hardy–Littlewood–Sobolev inequality of order `1 - 2 / q` on `ℝ`.
  have hpq' : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (1 - 2 / q) / Module.finrank ℝ ℝ := by
    have h := hpq.coe.inv_add_inv_eq_one
    rw [Module.finrank_self, Nat.cast_one, div_one]
    field_simp at h ⊢
    linarith
  obtain ⟨C, hC⟩ := exists_eLpNorm_rieszPotential_le (F := ℝ≥0∞) (volume : Measure ℝ)
    (α := 1 - 2 / q) (by rw [sub_pos, div_lt_one hq0]; exact_mod_cast hq) hp hpq'
  refine ⟨C, fun U A hU F G hF hG => ?_⟩
  set a := fun s ↦ eLpNorm (F s) r' μ
  set b := fun t ↦ eLpNorm (G t) r' μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl r'
  have hb : AEMeasurable b := hG.aemeasurable_eLpNorm_Lp .rfl r'
  set I := rieszPotential volume (1 - 2 / q) b
  have hI : AEMeasurable I := aemeasurable_rieszPotential (by simpa using hb)
  -- For each `s`, the integral over `t` is bounded by the fractional integral of `b` at `s`.
  have hinner (s : ℝ) : ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤ A * a s * I s := by
    have hk : AEMeasurable fun t : ℝ ↦ ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * b t :=
      (by fun_prop : Measurable fun t : ℝ ↦ ‖s - t‖ₑ ^ (-(2 / q : ℝ))).aemeasurable.mul hb
    calc ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
        ≤ ∫⁻ t, A * a s * (‖s - t‖ₑ ^ (-(2 / q : ℝ)) * b t) := by
          -- The diagonal `t = s` is a null set.
          refine lintegral_mono_ae ?_
          filter_upwards [ae_iff.2 (by simp : volume {t : ℝ | ¬ t ≠ s} = 0)] with t ht
          calc _ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * a s * b t :=
                enorm_inner_adjoint_le hU (Ne.symm ht) _ _
            _ = _ := by ring
      _ = A * a s * I s := by
          rw [lintegral_const_mul'' _ hk]
          congr 1
          simp only [I, rieszPotential_def, eNorm_eq_self, Module.finrank_self]
          refine lintegral_congr fun t ↦ ?_
          congr 2
          push_cast
          ring
  -- Hölder's inequality in time, then Hardy–Littlewood–Sobolev.
  calc ∫⁻ s, ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
      ≤ ∫⁻ s, A * (a s * I s) := lintegral_mono fun s ↦ (hinner s).trans_eq (mul_assoc _ _ _)
    _ = A * ∫⁻ s, a s * I s := lintegral_const_mul'' _ (ha.mul hI)
    _ ≤ A * (eLpNorm a p * eLpNorm I q) := by
        gcongr
        have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq.coe ha hI
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by positivity) ENNReal.coe_ne_top
            ha.aestronglyMeasurable,
          eLpNorm_eq_lintegral_rpow_eNorm_toReal (by positivity) ENNReal.coe_ne_top
            hI.aestronglyMeasurable]
        simpa only [eNorm_eq_self, ENNReal.coe_toReal, Pi.mul_apply] using h
    _ ≤ A * (eLpNorm a p * (C * eLpNorm b p)) := by
        gcongr
        exact hC b
    _ = _ := by ring

variable [NormedSpace ℝ H]

/-- **The dual homogeneous `TT*` estimate.** Let `2 < q < ∞` with Hölder conjugate `p`, and let
`U(t) : H → L²(X, μ)` be bounded operators with
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for every almost everywhere
strongly measurable `F : ℝ → L²(X, μ)` for which `s ↦ U(s)* F(s)` is integrable,

`‖∫ U(s)* F(s) ds‖ ≤ C A ^ (1 / 2) ‖F‖_{L^p L^{r'}}`,

with `C` independent of the family `U`, of `A` and of `F`. -/
theorem exists_enorm_integral_adjoint_le {p q : ℝ≥0} (hq : 2 < q) (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
        ‖∫ s, ((U s)†) (F s)‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p := by
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := 𝕜) (H := H)
    (E := E) (μ := μ) (r := r) (r' := r') hq hpq
  refine ⟨NNReal.sqrt C, fun U A hU F hF hUF => ?_⟩
  set v := ∫ s, ((U s)†) (F s)
  set a := eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p
  -- `‖v‖² = ⟪v, v⟫` expands into the double integral of the time pairings.
  have hsq : ‖v‖ₑ ^ (2 : ℝ) ≤ C * A * a * a := by
    calc ‖v‖ₑ ^ (2 : ℝ) = ‖⟪v, v⟫_𝕜‖ₑ := by
          rw [inner_self_eq_norm_sq_to_K, eNorm_pow, ← ENNReal.rpow_natCast]
          simp
      _ = ‖∫ s, ⟪v, ((U s)†) (F s)⟫_𝕜‖ₑ := by rw [integral_inner hUF]
      _ ≤ ∫⁻ s, ‖⟪v, ((U s)†) (F s)⟫_𝕜‖ₑ := eNorm_integral_le_lintegral_eNorm _
      _ = ∫⁻ s, ‖∫ t, ⟪((U s)†) (F s), ((U t)†) (F t)⟫_𝕜‖ₑ := by
          refine lintegral_congr fun s ↦ ?_
          rw [← ofReal_norm, norm_inner_symm, ofReal_norm, integral_inner hUF]
      _ ≤ ∫⁻ s, ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (F t)⟫_𝕜‖ₑ :=
          lintegral_mono fun s ↦ eNorm_integral_le_lintegral_eNorm _
      _ ≤ C * A * a * a := hC U A hU F F hF hF
  have hrhs : ((NNReal.sqrt C : ℝ≥0∞) * A ^ (2⁻¹ : ℝ) * a) ^ (2 : ℝ) = C * A * a * a := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
      ← ENNReal.rpow_mul, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one, ENNReal.rpow_two,
      ENNReal.rpow_two, ← ENNReal.coe_pow, NNReal.sq_sqrt, sq]
    ring
  rwa [← ENNReal.rpow_le_rpow_iff (z := 2) two_pos, hrhs]

/-- **The homogeneous `TT*` estimate in weak form.** Let `2 < q < ∞` with Hölder conjugate `p`,
and let `U(t) : H → L²(X, μ)` be bounded operators with
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for every `f ∈ H` and every
almost everywhere strongly measurable `G : ℝ → L²(X, μ)` for which `t ↦ U(t)* G(t)` is
integrable,

`|∫ ⟪U(t) f, G(t)⟫ dt| ≤ C A ^ (1 / 2) ‖f‖ ‖G‖_{L^p L^{r'}}`,

with `C` independent of the family `U`, of `A`, of `f` and of `G`. This is the estimate
`‖U(·) f‖_{L^q L^r} ≤ C A ^ (1 / 2) ‖f‖` tested against `G`. -/
theorem exists_enorm_integral_inner_apply_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ (f : H) (G : ℝ → Lp E 2 μ), AEStronglyMeasurable G →
        Integrable (fun t ↦ ((U t)†) (G t)) →
        ‖∫ t, ⟪U t f, G t⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * ‖f‖ₑ * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := 𝕜) (H := H) (E := E) (μ := μ)
    (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A hU f G hG hUG => ?_⟩
  simp_rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [integral_inner hUG]
  calc _ ≤ ‖f‖ₑ * ‖∫ t, ((U t)†) (G t)‖ₑ := eNorm_inner_le_eNorm _ _
    _ ≤ ‖f‖ₑ * (C * A ^ (2⁻¹ : ℝ) * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p) := by
        gcongr
        exact hC U A hU G hG hUG
    _ = _ := by ring

end TauCeti
