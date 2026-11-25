/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Family
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Polynomial
import TauCeti.Analysis.PDE.Vortex.Reduced.HigherSmoothness
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty

/-!
# Joint smoothness of the plane vortices in the divisor and the point

For `c ∈ ℂᵐ` let `P_c = TauCeti.Polynomial.monicOfCoeff c`, the monic polynomial of degree `m`
with lower coefficients `c`; the coefficients are symmetric coordinates on the divisor space
`Sym^m ℂ`, collisions of zeros included. Taubes's plane vortex with zero divisor `P_c` is the field
`TauCeti.Vortex.polynomialVortex P_c`, reconstructed from the amplitude `u₀ + w_c` and the section
`P_c`, where `u₀ = -log (1 + ‖P_c‖²) / 2` is the background amplitude and `w_c` the reduced
solution. This file proves that the vortex fields form a smooth family of smooth fields:

* the reduced solution `(c, z) ↦ w_c(z)` is `C^∞` jointly in `c` and `z`
  (`TauCeti.Vortex.contDiff_reducedSolution_monicOfCoeff`);
* so is the vortex field `(c, z) ↦ x_c(z)`
  (`TauCeti.Vortex.contDiff_polynomialVortex_monicOfCoeff`);
* so is the normalized vortex `(c, z) ↦ y_c(z)`, where `y_c = g_c · x_c`
  (`TauCeti.Vortex.normalizedVortex`) is the end normalization of `x_c` by the polynomial gauge
  `g_c` (`TauCeti.Vortex.polynomialGauge`), whose section has the fixed winding phase `(z / |z|)ᵐ`
  outside a disc (`TauCeti.Vortex.contDiff_normalizedVortex_uncurry`).

In particular all mixed derivatives of the vortex fields in the symmetric coordinates `c` and in
the point `z` exist and are continuous, over the whole divisor space, collisions included. These
are the derivatives in which the decay of the normalized families over compact divisor windows is
measured, and the regularity a vortex field inserted along a curve needs when its divisor varies
with the point of the curve.

**The proof.** The reduced solution `w_c` depends smoothly on `c` in every Sobolev space `H^s(ℂ)`
(`TauCeti.Vortex.contDiff_ofRealSobolevFunction_reducedSolution`). For `s > n + 1` the Sobolev
embedding of a `Cⁿ` family in `H^s(ℂ)` is `Cⁿ` jointly in the parameter and the point
(`ContDiff.toZeroAtInfty_apply`), so `(c, z) ↦ w_c(z)` is `Cⁿ` for every `n`. The background
amplitude and the polynomial gauge are explicit and jointly smooth, and the fields are built from
them by derivatives in `z` and smooth operations.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex MeasureTheory Module
open TauCeti.Polynomial BesselPotentialSpace
open scoped ContDiff BesselPotentialSpace

namespace TauCeti.Vortex

variable {m : ℕ}

/-- **The reduced solution is jointly smooth in the divisor and the point.** The solution `w_c` of
the reduced equation for the monic polynomial `P_c` with lower coefficients `c` satisfies:
`(c, z) ↦ w_c(z)` is `C^∞`. -/
theorem contDiff_reducedSolution_monicOfCoeff :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ reducedSolution (monicOfCoeff p.1) p.2 := by
  refine contDiff_infty.2 fun n ↦ ?_
  have hn : (finrank ℝ ℂ : ℝ) + 2 * n < 2 * (n + 2) := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  have h := ContDiff.toZeroAtInfty_apply hn
    (((contDiff_ofRealSobolevFunction_reducedSolution (m := m) (by positivity)).of_le
      (by exact_mod_cast le_top)).comp contDiff_fst) contDiff_snd
  convert reCLM.contDiff.comp h using 1
  ext p
  simp only [Function.comp_apply, reCLM_apply]
  rw [coe_toZeroAtInfty_ofRealSobolevFunction (contDiff_reducedSolution _).continuous, ofReal_re]

/-- **The plane vortices are jointly smooth in the divisor and the point.** The vortex field
`x_c` with zero divisor `P_c` (`TauCeti.Vortex.polynomialVortex`) satisfies: `(c, z) ↦ x_c(z)` is
`C^∞`. -/
theorem contDiff_polynomialVortex_monicOfCoeff :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ polynomialVortex (monicOfCoeff p.1) p.2 := by
  have hP : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ (monicOfCoeff p.1).eval p.2 :=
    (contDiff_eval_monicOfCoeff contDiff_fst contDiff_snd).restrict_scalars ℝ
  simp only [polynomialVortex_def]
  exact contDiff_parametric_amplitudeField (n := ⊤)
    (u := fun c z ↦
      backgroundAmplitude (monicOfCoeff c).eval z + reducedSolution (monicOfCoeff c) z)
    (f := fun c ↦ (monicOfCoeff c).eval)
    (((contDiff_parametric_backgroundAmplitude (f := fun c ↦ (monicOfCoeff c).eval) hP).add
      contDiff_reducedSolution_monicOfCoeff).of_le (by simp)) hP

/-- **The normalized plane vortex** with divisor coefficients `c ∈ ℂᵐ`: Taubes's vortex
`TauCeti.Vortex.polynomialVortex` of the monic polynomial `P_c = monicOfCoeff c`, followed by its
end-normalizing gauge `TauCeti.Vortex.polynomialGauge c`, so that outside a disc its section is a
positive multiple of the winding phase `(z / |z|)ᵐ`. -/
def normalizedVortex (c : Fin m → ℂ) : ℂ → EuclideanSpace ℝ (Fin 4) :=
  gaugeTransform (polynomialGauge c) (polynomialVortex (monicOfCoeff c))

theorem normalizedVortex_def (c : Fin m → ℂ) :
    normalizedVortex c = gaugeTransform (polynomialGauge c) (polynomialVortex (monicOfCoeff c)) :=
  (rfl)

/-- **The normalized plane vortices are jointly smooth in the divisor and the point.** The
vortex field `x_c` with zero divisor `P_c`, transformed by the polynomial gauge `g_c`
(`TauCeti.Vortex.polynomialGauge`), whose section has the winding phase `(z / |z|)ᵐ` outside a disc,
satisfies: `(c, z) ↦ (g_c · x_c)(z)` is `C^∞`. -/
theorem contDiff_normalizedVortex_uncurry :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ normalizedVortex p.1 p.2 :=
  contDiff_parametric_gaugeTransform (n := ∞) (x := fun c ↦ polynomialVortex (monicOfCoeff c))
    (contDiff_polynomialGauge.of_le (by simp)) contDiff_polynomialVortex_monicOfCoeff

/-- The normalized vortex is smooth. -/
theorem contDiff_normalizedVortex (c : Fin m → ℂ) : ContDiff ℝ ∞ (normalizedVortex c) :=
  contDiff_normalizedVortex_uncurry.comp (contDiff_const.prodMk contDiff_id)

end TauCeti.Vortex
