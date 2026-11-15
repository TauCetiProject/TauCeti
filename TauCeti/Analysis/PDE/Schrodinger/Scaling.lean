/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Basic
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# Scaling of the Schrödinger equation and the admissible Strichartz exponents

If `u(x, t)` solves the free Schrödinger equation `i ∂ₜu + Δu = 0` on a real inner product space
`E` of dimension `n`, then so does `u(x / λ, t / λ²)` for every `λ > 0`. For the propagator
`S(t) = exp(itΔ)` (`TauCeti.schrodingerPropagator`) and the normalized dilation
`D_λ f = λ ^ (-n/2) • f (λ⁻¹ • ·)` of `L²` (`MeasureTheory.Measure.dilateLp`), which preserves the
`L²` norm, this is the identity

`S(t) (D_λ f) = D_λ (S(t / λ²) f)`

(`TauCeti.schrodingerPropagator_dilateLp`). It follows from the general fact that conjugating an
`L²` Fourier multiplier by a dilation dilates its symbol
(`MeasureTheory.Lp.fourierMultiplierCLM_dilateLp`), since the symbol `exp(-4π² i t ‖ξ‖²)` of
`S(t)` is homogeneous of degree two in `ξ` jointly with `t`.

Taking `Lʳ` norms in space and then `L^q` norms in time, the dilation multiplies the Strichartz
norm `‖S(t) f‖_{L^q_t L^r_x}` by `λ ^ (2/q + n/r - n/2)`
(`TauCeti.eLpNorm_eLpNorm_schrodingerPropagator_dilateLp`). A global-in-time Strichartz estimate
`‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` is therefore possible only on the **admissible line**
`2/q + n/r = n/2`
(`TauCeti.two_mul_inv_add_finrank_mul_inv_eq_of_eLpNorm_schrodingerPropagator_le`): otherwise
dilating a fixed nonzero datum by `λ → 0` or `λ → ∞` makes the left side unbounded while the
right side does not change. This is the converse of the Strichartz estimates in
`TauCeti.Analysis.PDE.Schrodinger.Strichartz`, which hold on that line.

## Main declarations

* `TauCeti.schrodingerPropagator_dilateLp`: the scaling law `S(t) D_λ = D_λ S(t / λ²)`.
* `TauCeti.eLpNorm_schrodingerPropagator_dilateLp`: the scaling of the `Lʳ` norms at a fixed
  time.
* `TauCeti.eLpNorm_eLpNorm_schrodingerPropagator_dilateLp`: the scaling of the mixed norms.
* `TauCeti.two_mul_inv_add_finrank_mul_inv_eq_of_eLpNorm_schrodingerPropagator_le`: a
  Strichartz estimate forces `2/q + n/r = n/2`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (the scaling heuristic for Strichartz
  estimates).
* M. Keel, T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open scoped ENNReal NNReal SchwartzMap
open MeasureTheory MeasureTheory.Measure Module Filter

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Dilating the Schrödinger symbol in frequency by `r⁻¹` rescales time by `r⁻²`. -/
private theorem dilateLp_toLp_phaseSymbol_laplacianSymbol {r : ℝ} (hr : 0 < r) (t : ℝ) :
    dilateLp volume ∞ r hr ((memLp_phaseSymbol (E := E) laplacianSymbol t).toLp _) =
      (memLp_phaseSymbol laplacianSymbol (t / r ^ 2)).toLp _ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilateLp (μ := volume) (p := ∞) hr
      ((memLp_phaseSymbol (E := E) laplacianSymbol t).toLp _),
    (quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).ae_eq_comp
      (memLp_phaseSymbol (E := E) laplacianSymbol t).coeFn_toLp,
    (memLp_phaseSymbol (E := E) laplacianSymbol (t / r ^ 2)).coeFn_toLp] with ξ h₁ h₂ h₃
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, ENNReal.toReal_top, div_zero, neg_zero, Real.rpow_zero, one_smul,
    phaseSymbol_apply, phaseSymbol_apply, laplacianSymbol_smul]
  congr 3
  field_simp

/-- **The scaling law of the Schrödinger equation.** If `u(x, t)` solves `i ∂ₜu + Δu = 0`, so does
`u(x / r, t / r²)`. For the propagator `S(t) = exp(itΔ)` and the normalized dilation
`D_r f = r ^ (-n/2) • f (r⁻¹ • ·)` of `L²`, this reads `S(t) (D_r f) = D_r (S(t / r²) f)`. -/
theorem schrodingerPropagator_dilateLp {r : ℝ} (hr : 0 < r) (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator F t (dilateLp volume 2 r hr f) =
      dilateLp volume 2 r hr (schrodingerPropagator F (t / r ^ 2) f) := by
  rw [schrodingerPropagator_def, phasePropagator_def, Lp.fourierMultiplierCLM_dilateLp,
    dilateLp_toLp_phaseSymbol_laplacianSymbol, ← phasePropagator_def, ← schrodingerPropagator_def]

/-- **Scaling of the `Lʳ` norms.** At a fixed time, the `Lʳ` norm of `S(t) (D_λ f)` is
`λ ^ (n/r - n/2)` times the `Lʳ` norm of `S(t / λ²) f`, where `n / r` is `n / r.toReal`, which is
`0` for `r = ∞`. -/
theorem eLpNorm_schrodingerPropagator_dilateLp {l : ℝ} (hl : 0 < l) (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) (r : ℝ≥0∞) :
    eLpNorm (schrodingerPropagator F t (dilateLp volume 2 l hl f)) r volume =
      ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2)) *
        eLpNorm (schrodingerPropagator F (t / l ^ 2) f) r volume := by
  set g := schrodingerPropagator F (t / l ^ 2) f
  set c : ℝ := l ^ (-((finrank ℝ E : ℝ) / (2 : ℝ≥0∞).toReal))
  have h : (fun x : E ↦ c • g (l⁻¹ • x)) = c • fun x ↦ g (l⁻¹ • x) := rfl
  rw [schrodingerPropagator_dilateLp, eLpNorm_congr_ae (coeFn_dilateLp hl g), h,
    eLpNorm_const_smul, eLpNorm_comp_inv_smul volume _ hl.ne', ← mul_assoc, abs_of_pos hl,
    Real.eNorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add hl, ENNReal.toReal_ofNat]
  congr 3
  ring

/-- **Scaling of the Strichartz norms.** For `q ≠ 0`, dilating the datum by `λ` multiplies the
mixed norm `‖S(t) f‖_{L^q_t L^r_x}`, `t ∈ ℝ`, by `λ ^ (n/r - n/2 + 2/q)`, where `n / r` and `2 / q`
are `n / r.toReal` and `2 / q.toReal`, which are `0` for an infinite exponent. -/
theorem eLpNorm_eLpNorm_schrodingerPropagator_dilateLp {l : ℝ} (hl : 0 < l)
    (f : Lp F 2 (volume : Measure E)) {q : ℝ≥0∞} (hq : q ≠ 0) (r : ℝ≥0∞) :
    eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator F t (dilateLp volume 2 l hl f)) r volume) q
        volume =
      ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2 + 2 / q.toReal)) *
        eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator F t f) r volume) q volume := by
  have h : (fun t ↦ eLpNorm (schrodingerPropagator F t (dilateLp volume 2 l hl f)) r volume) =
      fun t ↦ ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2)) *
        eLpNorm (schrodingerPropagator F ((l ^ 2)⁻¹ • t) f) r volume := by
    funext t
    rw [eLpNorm_schrodingerPropagator_dilateLp hl, smul_eq_mul, inv_mul_eq_div]
  rw [h, eLpNorm_const_mul_ennreal_of_pos (pos_iff_ne_zero.2 hq),
    eLpNorm_comp_inv_smul (volume : Measure ℝ)
      (fun s ↦ eLpNorm (schrodingerPropagator F s f) r volume) (pow_ne_zero 2 hl.ne'),
    finrank_self, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (pow_pos hl 2),
    ← Real.rpow_natCast, ← Real.rpow_mul hl.le, ← Real.rpow_add hl]
  congr 3
  push_cast
  ring

/-- The Strichartz norm of the evolution of a nonzero datum is nonzero. -/
private theorem eLpNorm_eLpNorm_schrodingerPropagator_ne_zero {q r : ℝ≥0∞} (hq : q ≠ 0)
    (hr : r ≠ 0) {f : Lp F 2 (volume : Measure E)} (hf : f ≠ 0) :
    eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator F t f) r volume) q volume ≠ 0 := by
  intro h0
  rw [eLpNorm_eq_zero_iff hq] at h0
  obtain ⟨t, ht⟩ := h0.exists
  rw [Pi.zero_apply, eLpNorm_eq_zero_iff hr] at ht
  have hS : schrodingerPropagator F t f = 0 := Lp.ext (ht.trans (Lp.coeFn_zero _ _ _).symm)
  have hn := norm_phasePropagator_apply (F := F) (laplacianSymbol (E := E)) t f
  rw [← schrodingerPropagator_def, hS, norm_zero] at hn
  exact hf (norm_eq_zero.1 hn.symm)

/-- A power `λ ^ a` that stays bounded for all `λ > 0` has exponent `a = 0`. -/
private theorem eq_zero_of_forall_rpow_mul_le {a A B : ℝ} (hA : 0 < A)
    (h : ∀ l : ℝ, 0 < l → l ^ a * A ≤ B) : a = 0 := by
  by_contra ha
  have h1 := h ((|B| / A + 1) ^ a⁻¹) (by positivity)
  rw [Real.rpow_inv_rpow (by positivity) ha, add_mul, div_mul_cancel₀ _ hA.ne'] at h1
  linarith [le_abs_self B]

/-- **The admissibility condition is necessary for the Strichartz estimate.** Let `E` have
dimension `n` and let `q, r` be nonzero exponents. If the global-in-time homogeneous Strichartz
estimate

`‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂`, `t ∈ ℝ`,

holds for the Schrödinger propagator `S(t) = exp(itΔ)` and every `f ∈ L²(E)`, with a constant
independent of `f`, then `(q, r)` lies on the admissible line `2/q + n/r = n/2`, where `1 / ∞ = 0`.
Replacing `f` by its dilate `D_λ f`, which has the same `L²` norm, multiplies the left side by
`λ ^ (2/q + n/r - n/2)` (`TauCeti.eLpNorm_eLpNorm_schrodingerPropagator_dilateLp`), and this
factor is unbounded in `λ > 0` off the admissible line. -/
theorem two_mul_inv_add_finrank_mul_inv_eq_of_eLpNorm_schrodingerPropagator_le {q r : ℝ≥0∞}
    (hq : q ≠ 0) (hr : r ≠ 0)
    (h : ∃ C : ℝ≥0, ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) q volume ≤ C * ‖f‖ₑ) :
    2 * (q⁻¹).toReal + finrank ℝ E * (r⁻¹).toReal = finrank ℝ E / 2 := by
  obtain ⟨C, hC⟩ := h
  set N : Lp ℂ 2 (volume : Measure E) → ℝ≥0∞ :=
    fun g ↦ eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t g) r volume) q volume
  -- A nonzero datum: the Gaussian `exp(-π ‖x‖²)`.
  have hπ : 0 < (Real.pi : ℂ).re := by simpa using Real.pi_pos
  set f : Lp ℂ 2 (volume : Measure E) := (SchwartzMap.gaussian (V := E) hπ).toLp 2
  have hf : f ≠ 0 := by
    intro h0
    have h1 : SchwartzMap.gaussian (V := E) hπ = 0 := SchwartzMap.injective_toLp 2 volume
      (h0.trans (by simpa using (map_zero (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E))).symm))
    simpa [SchwartzMap.gaussian_apply] using congr($h1 0)
  have hN0 : N f ≠ 0 := eLpNorm_eLpNorm_schrodingerPropagator_ne_zero hq hr hf
  have hNtop : N f ≠ ∞ := ne_top_of_le_ne_top (by finiteness) (hC f)
  -- The dilates of `f` all have the norm of `f`, so the scaling factor stays bounded.
  set a : ℝ := (finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2 + 2 / q.toReal
  have ha : a = 0 := by
    refine eq_zero_of_forall_rpow_mul_le (B := C * ‖f‖) (ENNReal.toReal_pos hN0 hNtop) fun l hl ↦ ?_
    have h1 := hC (dilateLp volume 2 l hl f)
    rw [eLpNorm_eLpNorm_schrodingerPropagator_dilateLp hl f hq, ← ofReal_norm,
      LinearIsometryEquiv.norm_map, ofReal_norm] at h1
    have h2 := ENNReal.toReal_mono (by finiteness) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
      ENNReal.coe_toReal, toReal_eNorm] at h2
  simp only [a, ENNReal.toReal_inv] at ha ⊢
  linear_combination ha

end TauCeti
