/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Basic
public import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Scaling of the Schrödinger equation

If `u(x, t)` solves the free Schrödinger equation `i ∂ₜu + Δu = 0` on a real inner product space
`E` of dimension `n`, then so does `u(x / λ, t / λ²)` for every `λ > 0`. For the propagator
`S(t) = exp(itΔ)` (`TauCeti.schrodingerPropagator`) and the normalized dilation
`D_λ f = λ ^ (-n/2) • f (λ⁻¹ • ·)` of `L²` (`MeasureTheory.Measure.dilateLp`), which preserves the
`L²` norm, this is the identity

`S(t) (D_λ f) = D_λ (S(t / λ²) f)`

(`TauCeti.schrodingerPropagator_dilateLp`). It is the case `k = 2` of the scaling law of a phase
propagator whose phase is positively homogeneous of degree `k`
(`TauCeti.phasePropagator_dilateLp`), since the phase `-4π² ‖ξ‖²` of `S(t)` is homogeneous of
degree two.

Taking `Lʳ` norms in space and then `L^q` norms in time, the dilation multiplies the Strichartz
norm `‖S(t) f‖_{L^q_t L^r_x}` by `λ ^ (2/q + n/r - n/2)`
(`TauCeti.eLpNorm_eLpNorm_schrodingerPropagator_dilateLp`), while it preserves `‖f‖₂`. This is
the scaling heuristic behind the admissible line `2/q + n/r = n/2`: off that line, dilating a
fixed nonzero datum by `λ → 0` or `λ → ∞` makes the left side of a global-in-time estimate
`‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` unbounded while the right side does not change. The resulting
necessity of the admissible line is
`TauCeti.two_mul_inv_add_finrank_mul_inv_eq_of_eLpNorm_schrodingerPropagator_le`, proved with
Gaussian data in `TauCeti.Analysis.PDE.Schrodinger.Gaussian`.

## Main declarations

* `TauCeti.schrodingerPropagator_dilateLp`: the scaling law `S(t) D_λ = D_λ S(t / λ²)`.
* `TauCeti.eLpNorm_schrodingerPropagator_dilateLp`: the scaling of the `Lʳ` norms at a fixed
  time.
* `TauCeti.eLpNorm_eLpNorm_schrodingerPropagator_dilateLp`: the scaling of the mixed norms.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (the scaling heuristic for Strichartz
  estimates).
-/

public section

noncomputable section

open scoped ENNReal
open MeasureTheory MeasureTheory.Measure Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The scaling law of the Schrödinger equation.** If `u(x, t)` solves `i ∂ₜu + Δu = 0`, so does
`u(x / r, t / r²)`. For the propagator `S(t) = exp(itΔ)` and the normalized dilation
`D_r f = r ^ (-n/2) • f (r⁻¹ • ·)` of `L²`, this reads `S(t) (D_r f) = D_r (S(t / r²) f)`. -/
theorem schrodingerPropagator_dilateLp {r : ℝ} (hr : 0 < r) (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator F t (dilateLp volume ℝ 2 r hr f) =
      dilateLp volume ℝ 2 r hr (schrodingerPropagator F (t / r ^ 2) f) :=
  phasePropagator_dilateLp (fun c _ ξ ↦ laplacianSymbol_smul c ξ) hr t f

/-- **Scaling of the `Lʳ` norms.** At a fixed time, the `Lʳ` norm of `S(t) (D_λ f)` is
`λ ^ (n/r - n/2)` times the `Lʳ` norm of `S(t / λ²) f`, where `n / r` is `n / r.toReal`, which is
`0` for `r = ∞`. -/
theorem eLpNorm_schrodingerPropagator_dilateLp {l : ℝ} (hl : 0 < l) (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) (r : ℝ≥0∞) :
    eLpNorm (schrodingerPropagator F t (dilateLp volume ℝ 2 l hl f)) r volume =
      ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2)) *
        eLpNorm (schrodingerPropagator F (t / l ^ 2) f) r volume :=
  eLpNorm_phasePropagator_dilateLp (fun c _ ξ ↦ laplacianSymbol_smul c ξ) hl t f r

/-- **Scaling of the Strichartz norms.** For `q ≠ 0`, dilating the datum by `λ` multiplies the
mixed norm `‖S(t) f‖_{L^q_t L^r_x}`, `t ∈ ℝ`, by `λ ^ (n/r - n/2 + 2/q)`, where `n / r` and `2 / q`
are `n / r.toReal` and `2 / q.toReal`, which are `0` for an infinite exponent. -/
theorem eLpNorm_eLpNorm_schrodingerPropagator_dilateLp {l : ℝ} (hl : 0 < l)
    (f : Lp F 2 (volume : Measure E)) {q : ℝ≥0∞} (hq : q ≠ 0) (r : ℝ≥0∞) :
    eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator F t (dilateLp volume ℝ 2 l hl f)) r volume) q
        volume =
      ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2 + 2 / q.toReal)) *
        eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator F t f) r volume) q volume := by
  have h : (fun t ↦ eLpNorm (schrodingerPropagator F t (dilateLp volume ℝ 2 l hl f)) r volume) =
      fun t ↦ ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2)) *
        eLpNorm (schrodingerPropagator F ((l ^ 2)⁻¹ • t) f) r volume := by
    funext t
    rw [eLpNorm_schrodingerPropagator_dilateLp hl, smul_eq_mul, inv_mul_eq_div]
  rw [h, eLpNorm_const_mul_ennreal_of_pos (pos_iff_ne_zero.2 hq),
    eLpNorm_comp_inv_smul (volume : Measure ℝ)
      (fun s ↦ eLpNorm (schrodingerPropagator F s f) r volume) (pow_ne_zero 2 hl.ne'),
    finrank_self, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (pow_pos hl 2),
    ← Real.rpow_natCast_mul hl.le, ← Real.rpow_add hl]
  congr 3
  ring

end TauCeti
