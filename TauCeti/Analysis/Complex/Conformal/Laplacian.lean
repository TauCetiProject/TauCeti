/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The planar Laplacian under holomorphic maps

The Laplacian `Δ = ∂ₓ² + ∂ᵧ²` of the plane is conformally covariant: if `m` is holomorphic at `z`
and `f` is a real `C²` function near `m z`, then

`Δ (f ∘ m) z = ‖m' z‖² • Δ f (m z)`.

The real derivative of `m` is multiplication by `m' z`, a rotation followed by a dilation by
`‖m' z‖`, and the trace of the Hessian of `f` over the orthogonal pair `m' z, i m' z` is
`‖m' z‖²` times its trace over `1, i`. The second derivative of `m` contributes the term
`Df (m z) (Δ m z)`, which vanishes because holomorphic functions are harmonic.

This is the rule by which Möbius transformations of the upper half-plane pass through the
hyperbolic Laplacian; the automorphy factors of a slash action pass through it by the product rule
with a holomorphic factor
(`TauCeti.laplacian_fun_mul_eq_mul_laplacian_add_deriv_mul_conjWirtingerDeriv`).

## Main results

* `TauCeti.laplacian_comp_eq_norm_deriv_sq_smul`: `Δ (f ∘ m) z = ‖m' z‖² • Δ f (m z)` for `m`
  holomorphic at `z`.

## References

* L. V. Ahlfors, *Complex Analysis*, third edition, Chapter 4, Section 6.1 (the Laplacian of a
  composition with an analytic function).
-/

public section

open Complex Filter InnerProductSpace Laplacian Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

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
    (fderiv ℝ (fderiv ℝ f) (m z)).apply_add_apply_I_mul_eq_norm_sq_smul hsymm (deriv m z)

end TauCeti
