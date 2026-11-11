/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Functional
public import TauCeti.Analysis.PDE.Vortex.Reconstruction
public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
public import Mathlib.Analysis.Complex.Isometry
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean and line-frame symmetries of Taubes's reduced vortex problem

Taubes constructs the plane vortex with zero divisor `P`, a complex polynomial, from a minimizer
`w` of the functional `I_P = TauCeti.Vortex.sobolevReducedFunctional P` on `H¹(ℂ)`: the field
`amplitudeField (u₀ + w) P`, with `u₀` the background amplitude of `P`, has section
`exp (u₀ + w) P`. This file shows that the reduced problem and the reconstruction transform
naturally under the symmetries of the plane and of the line at infinity.

The functional depends on `P` only through the norms `‖P‖` and `‖P'‖`. Hence if `g` is an
affine isometry of the plane and `Q` is a polynomial with `‖Q‖ = ‖P ∘ g‖` and
`‖Q'‖ = ‖P' ∘ g‖`, then `I_Q (u ∘ g) = I_P u` for every `u ∈ H¹(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional_compAffineIsometryEquivL`), since `g` preserves the
Lebesgue measure and the norm of the gradient. Consequently `u` minimizes `I_P` exactly when
`u ∘ g` minimizes `I_Q`
(`TauCeti.Vortex.forall_sobolevReducedFunctional_compAffineIsometryEquivL_le_iff`).
The three cases of interest are:

* **translations**, `Q = P.comp (X + C a)` and `g z = z + a`, which translate the divisor by
  `-a`;
* **rotations**, `Q = P.comp (C u * X)` with `‖u‖ = 1` and `g z = u z`;
* **line frames**, `Q = C c * P` with `‖c‖ = 1` and `g` the identity: the reduced problem does not
  see a constant change of phase of the section.

On the reconstruction side, `amplitudeField` intertwines the pullback of the amplitude and of the
holomorphic factor with the actions of `TauCeti.Analysis.PDE.Vortex.Symmetry`:
translating or rotating `(u, f)` translates or rotates the field
(`TauCeti.Vortex.translateField_amplitudeField`, `TauCeti.Vortex.rotateField_amplitudeField`),
and multiplying `f` by a unit constant `c` is the constant gauge transformation by `c`
(`TauCeti.Vortex.amplitudeField_const_mul`). The background amplitude
`-log (1 + ‖P‖²) / 2` of `P ∘ g` is that of `P` composed with `g`, so the amplitude `u₀ + w` moves
with the divisor exactly as `w` does in the variational statements above.

Together with uniqueness of the minimizer, these laws make the solution `w_P` of the reduced
problem, and the vortex reconstructed from it, equivariant under translations, rotations and
constant changes of the frame of the line. They concern the reduced problem on `H¹(ℂ)` and the
pointwise reconstruction; the regularity of the minimizer is not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Polynomial TopologicalSpace
open scoped ENNReal

/-! ### Invariance of Taubes's functional -/

section Functional

variable {P Q : Polynomial ℂ}

/-- **Isometry invariance of Taubes's functional.** If an affine isometry `g` of the plane
carries the norms of `P` and `P'` to those of `Q` and `Q'`, then precomposition with `g` carries
Taubes's functional for `P` to that for `Q`. -/
theorem sobolevReducedFunctional_compAffineIsometryEquivL (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (hQ : ∀ z, ‖Q.eval z‖ = ‖P.eval (g z)‖)
    (hQ' : ∀ z, ‖Q.derivative.eval z‖ = ‖P.derivative.eval (g z)‖)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional Q (W1p.compAffineIsometryEquivL g (by simp) u) =
      sobolevReducedFunctional P u := by
  have hUV : ((⊤ : Opens ℂ) : Set ℂ) = g ⁻¹' (⊤ : Opens ℂ) := by simp
  have hmp : MeasurePreserving g volume volume := g.measurePreserving
  have hemb : MeasurableEmbedding g := g.toHomeomorph.measurableEmbedding
  have hv : (W1p.value (W1p.compAffineIsometryEquivL g hUV u) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ W1p.value u (g z) := by
    simpa using W1p.value_compAffineIsometryEquivL_ae g hUV u
  -- The Dirichlet energy.
  have hD := W1p.norm_gradient_compAffineIsometryEquivL g hUV u
  -- The linear term.
  have hL : ∫ z, (2 * ‖Q.derivative.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) ^ 2 -
        (1 + ‖Q.eval z‖ ^ 2)⁻¹ / 8) * W1p.value (W1p.compAffineIsometryEquivL g hUV u) z =
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := by
    let c : ℂ → ℝ := fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z
    rw [integral_congr_ae (g := fun z ↦ c (g z)) (hv.mono fun z hz ↦ by simp only [c, hz, hQ, hQ'])]
    exact hmp.integral_comp hemb c
  -- The potential.
  have hV : ∫⁻ z, ENNReal.ofReal (‖Q.eval z‖ ^ 2 / (1 + ‖Q.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value (W1p.compAffineIsometryEquivL g hUV u) z) - 1 -
          2 * W1p.value (W1p.compAffineIsometryEquivL g hUV u) z)) =
      ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) := by
    let V : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))
    rw [lintegral_congr_ae (g := fun z ↦ V (g z)) (hv.mono fun z hz ↦ by simp only [V, hz, hQ])]
    exact hmp.lintegral_comp_emb hemb V
  rw [sobolevReducedFunctional_def, sobolevReducedFunctional_def, hD, hL, hV]

/-- **Isometry invariance of the minimizers of Taubes's functional.** Under the hypotheses of
`TauCeti.Vortex.sobolevReducedFunctional_compAffineIsometryEquivL`, `u ∘ g` minimizes Taubes's
functional for `Q` exactly when `u` minimizes Taubes's functional for `P`. -/
theorem forall_sobolevReducedFunctional_compAffineIsometryEquivL_le_iff (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (hQ : ∀ z, ‖Q.eval z‖ = ‖P.eval (g z)‖)
    (hQ' : ∀ z, ‖Q.derivative.eval z‖ = ‖P.derivative.eval (g z)‖)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    (∀ v, sobolevReducedFunctional Q (W1p.compAffineIsometryEquivL g (by simp) u) ≤
        sobolevReducedFunctional Q v) ↔
      ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v := by
  have hVU : ((⊤ : Opens ℂ) : Set ℂ) = g.symm ⁻¹' (⊤ : Opens ℂ) := by simp
  have hI := sobolevReducedFunctional_compAffineIsometryEquivL g hQ hQ'
  rw [hI u]
  refine ⟨fun h v ↦ (h _).trans_eq (hI v), fun h v ↦ ?_⟩
  -- Every `v` is `(v ∘ g⁻¹) ∘ g`.
  have hv := W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL g.symm hVU
    (by simp) v
  rw [AffineIsometryEquiv.symm_symm] at hv
  rw [← hv, hI]
  exact h _

/-- Taubes's functional is invariant under translations: for `Q = P.comp (X + C a)`, whose
zeros are those of `P` translated by `-a`, it takes the value of `P`'s functional at `u` on
`u (· + a)`. -/
theorem sobolevReducedFunctional_comp_X_add_C (a : ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional (P.comp (X + C a))
        (W1p.compAffineIsometryEquivL (AffineIsometryEquiv.vaddConst ℝ a) (by simp) u) =
      sobolevReducedFunctional P u :=
  sobolevReducedFunctional_compAffineIsometryEquivL _ (fun z ↦ by simp)
    (fun z ↦ by simp [derivative_comp]) u

/-- Taubes's functional is invariant under rotations: for `Q = P.comp (C u * X)` with `u` on the
unit circle, it takes the value of `P`'s functional at `w` on `w (u ·)`. -/
theorem sobolevReducedFunctional_comp_C_mul_X (u : Circle)
    (w : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional (P.comp (C (u : ℂ) * X))
        (W1p.compAffineIsometryEquivL (rotation u).toAffineIsometryEquiv (by simp) w) =
      sobolevReducedFunctional P w :=
  sobolevReducedFunctional_compAffineIsometryEquivL _ (fun z ↦ by simp)
    (fun z ↦ by simp [derivative_comp]) w

/-- Taubes's functional does not see a constant unit factor of the polynomial: the line-frame
law of the reduced problem. -/
theorem sobolevReducedFunctional_C_mul {c : ℂ} (hc : ‖c‖ = 1)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional (C c * P) u = sobolevReducedFunctional P u := by
  have hQ (z : ℂ) : ‖(C c * P).eval z‖ = ‖P.eval z‖ := by simp [hc]
  have hQ' (z : ℂ) : ‖(C c * P).derivative.eval z‖ = ‖P.derivative.eval z‖ := by simp [hc]
  simp only [sobolevReducedFunctional_def, hQ, hQ']

/-- A function minimizes Taubes's functional for `P` exactly when its translate by `a`
minimizes Taubes's functional for `P.comp (X + C a)`. -/
theorem forall_sobolevReducedFunctional_comp_X_add_C_le_iff (a : ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    (∀ v, sobolevReducedFunctional (P.comp (X + C a))
        (W1p.compAffineIsometryEquivL (AffineIsometryEquiv.vaddConst ℝ a) (by simp) u) ≤
          sobolevReducedFunctional (P.comp (X + C a)) v) ↔
      ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v :=
  forall_sobolevReducedFunctional_compAffineIsometryEquivL_le_iff _ (fun z ↦ by simp)
    (fun z ↦ by simp [derivative_comp]) u

/-- A function minimizes Taubes's functional for `P` exactly when its rotation by `u` minimizes
Taubes's functional for `P.comp (C u * X)`. -/
theorem forall_sobolevReducedFunctional_comp_C_mul_X_le_iff (u : Circle)
    (w : W1p (volume : Measure ℂ) ⊤ 2) :
    (∀ v, sobolevReducedFunctional (P.comp (C (u : ℂ) * X))
        (W1p.compAffineIsometryEquivL (rotation u).toAffineIsometryEquiv (by simp) w) ≤
          sobolevReducedFunctional (P.comp (C (u : ℂ) * X)) v) ↔
      ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v :=
  forall_sobolevReducedFunctional_compAffineIsometryEquivL_le_iff _ (fun z ↦ by simp)
    (fun z ↦ by simp [derivative_comp]) w

end Functional

/-! ### Equivariance of the reconstruction -/

/-- Translating the amplitude and the holomorphic factor translates the reconstructed field. -/
@[simp]
theorem translateField_amplitudeField (a : ℂ) (u : ℂ → ℝ) (f : ℂ → ℂ) :
    translateField a (amplitudeField u f) =
      amplitudeField (fun z ↦ u (z + a)) (fun z ↦ f (z + a)) := by
  ext z i
  fin_cases i <;> simp [fderiv_comp_add_right]

/-- Rotating the amplitude and the holomorphic factor rotates the reconstructed field: the
connection `i (-∂₂u ds + ∂₁u dt)` of the rotated amplitude is the pullback of the connection of
`u`. -/
@[simp]
theorem rotateField_amplitudeField (v : Circle) (u : ℂ → ℝ) (f : ℂ → ℂ) :
    rotateField v (amplitudeField u f) =
      amplitudeField (fun z ↦ u (v * z)) (fun z ↦ f (v * z)) := by
  -- The chain rule, with the rotated direction expanded in the real basis `(1, I)`.
  have h (z w : ℂ) : fderiv ℝ (fun z ↦ u (v * z)) z w =
      (v * w).re * fderiv ℝ u (v * z) 1 + (v * w).im * fderiv ℝ u (v * z) I := by
    have hc := fderiv_comp_smul_apply (𝕜 := ℝ) u (v : ℂ) z w
    have hL := LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ u (v * z) : ℂ →ₗ[ℝ] ℝ) (v * w)
    simp only [smul_eq_mul, ContinuousLinearMap.coe_coe] at hc hL
    rw [hc, hL]
  ext z i
  fin_cases i <;> simp [h]

/-- Multiplying the holomorphic factor by a unit constant `c` is the constant gauge
transformation by `c` of the reconstructed field. -/
theorem amplitudeField_const_mul (c : Circle) (u : ℂ → ℝ) (f : ℂ → ℂ) :
    amplitudeField u (fun z ↦ c * f z) = gaugeTransform (fun _ ↦ c) (amplitudeField u f) := by
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply, mul_re, mul_im] <;> ring

end TauCeti.Vortex
