/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The planar Laplacian under holomorphic maps

The Laplacian `Δ = ∂ₓ² + ∂ᵧ²` of the plane is conformally covariant: if `m` is holomorphic at `z`
and `f` is a real `C²` function near `m z`, then

`Δ (f ∘ m) z = ‖m' z‖² • Δ f (m z)`.

The real derivative of `m` is multiplication by `m' z`, a rotation followed by a dilation by
`‖m' z‖`, and the trace of the Hessian of `f` over the orthogonal pair `m' z, i m' z` is
`‖m' z‖²` times its trace over `1, i`. The second derivative of `m` contributes the term
`Df (m z) (Δ m z)`, which vanishes because holomorphic functions are harmonic.

For a holomorphic factor `J` the product rule takes the form
`Δ (J H) = J ΔH + 4 J' \bar∂H`, where `\bar∂H = (∂ₓH + i ∂ᵧH) / 2` is the conjugate Wirtinger
derivative, since `J` is harmonic and its partial derivatives are `J'` and `i J'`.

These are the two rules by which Möbius transformations of the upper half-plane, and the automorphy
factors of a slash action, pass through the hyperbolic Laplacian.

## Main results

* `TauCeti.laplacian_comp_eq_norm_deriv_sq_smul`: `Δ (f ∘ m) z = ‖m' z‖² • Δ f (m z)` for `m`
  holomorphic at `z`.
* `TauCeti.laplacian_fun_mul_eq_mul_laplacian_add_deriv_mul`: the product rule
  `Δ (J H) = J ΔH + 4 J' \bar∂H` for a holomorphic factor `J`.

## References

* L. V. Ahlfors, *Complex Analysis*, third edition, Chapter 4, Section 6.1 (the Laplacian of a
  composition with an analytic function).
-/

public section

open Complex Filter InnerProductSpace Laplacian Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a real bilinear map `B` on `ℂ` with `B 1 I = B I 1`, the trace over the orthogonal pair
`a, I a` is `‖a‖²` times the trace over `1, I`. -/
private theorem apply_add_apply_I_mul_eq_norm_sq_smul (B : ℂ →L[ℝ] ℂ →L[ℝ] F) (hB : B 1 I = B I 1)
    (a : ℂ) :
    B a a + B (I * a) (I * a) = ‖a‖ ^ 2 • (B 1 1 + B I I) := by
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℝ, a = p • (1 : ℂ) + q • I :=
    ⟨a.re, a.im, by simp⟩
  have hIa : I * (p • (1 : ℂ) + q • I) = (-q) • (1 : ℂ) + p • I := by
    simp [Complex.ext_iff]
  have hn : ‖p • (1 : ℂ) + q • I‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  rw [hIa, hn]
  simp only [map_add, map_smul, add_apply, smul_apply, hB]
  module

/-- **Conformal covariance of the planar Laplacian.** If `m` is holomorphic (complex `C²`) at `z`
and `f` is real `C²` at `m z`, then `Δ (f ∘ m) z = ‖m' z‖² • Δ f (m z)`. -/
theorem laplacian_comp_eq_norm_deriv_sq_smul {f : ℂ → F} {m : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f (m z)) (hm : ContDiffAt ℂ 2 m z) :
    Δ (f ∘ m) z = ‖deriv m z‖ ^ 2 • Δ f (m z) := by
  have hmℝ : ContDiffAt ℝ 2 m z := hm.restrict_scalars ℝ
  have hd (v : ℂ) : fderiv ℝ m z v = v * deriv m z :=
    (hm.differentiableAt (by norm_num)).fderiv_restrictScalars_eq_smul_deriv ℝ v
  -- The second derivative of `m` enters only through `Δ m z`, which is zero.
  have hΔm : Δ m z = 0 := hm.harmonicAt.2.self_of_nhds
  have hsymm := (hf.isSymmSndFDerivAt (by simp)) 1 I
  rw [laplacian_eq_iteratedFDeriv_complexPlane] at hΔm ⊢
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hΔm ⊢
  rw [fderiv_fderiv_comp_apply hf hmℝ, fderiv_fderiv_comp_apply hf hmℝ, hd, hd,
    add_add_add_comm, ← map_add, hΔm, map_zero, add_zero]
  simpa [mul_comm] using
    apply_add_apply_I_mul_eq_norm_sq_smul (fderiv ℝ (fderiv ℝ f) (m z)) hsymm (deriv m z)

/-- **The Laplacian of a product with a holomorphic factor.** If `J` is holomorphic (complex `C²`)
at `z` and `H` is real `C²` at `z`, then `Δ (J H) z = J z ΔH z + 4 J' z \bar∂H z`, where
`\bar∂H z = (∂ₓH z + i ∂ᵧH z) / 2` is the conjugate Wirtinger derivative. -/
theorem laplacian_fun_mul_eq_mul_laplacian_add_deriv_mul {J H : ℂ → ℂ} {z : ℂ}
    (hJ : ContDiffAt ℂ 2 J z) (hH : ContDiffAt ℝ 2 H z) :
    Δ (fun w ↦ J w * H w) z = J z * Δ H z + 4 * deriv J z * conjWirtingerDeriv H z 1 := by
  have hd (v : ℂ) : fderiv ℝ J z v = v * deriv J z :=
    (hJ.differentiableAt (by norm_num)).fderiv_restrictScalars_eq_smul_deriv ℝ v
  have h := fderiv_apply_one_add_I_smul_fderiv_apply_I H z
  rw [smul_eq_mul, smul_eq_mul] at h
  rw [(hJ.restrict_scalars ℝ).laplacian_fun_mul_complex hH, hJ.harmonicAt.2.self_of_nhds, hd, hd,
    Pi.zero_apply]
  linear_combination (2 * deriv J z) * h

end TauCeti
