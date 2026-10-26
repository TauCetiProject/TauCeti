/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import TauCeti.Analysis.Complex.Pseudoconvex

/-!
# Squared distance along a differentiable map

For a map `i : V → E` into a real inner product space and a point `a : E`, this file computes the
first and second derivatives of the squared-distance function

`x ↦ ‖i x - a‖ ^ 2`.

A point is critical exactly when the displacement from `a` is orthogonal to the range of `Di`.
The Hessian is twice the sum of the pullback metric term and the pairing of the displacement
with `D²i`. For a holomorphic map between complex normed spaces, the latter terms cancel between
`v` and `I • v`. Consequently the Levi diagonal is exactly `‖Di(v)‖²`, and a holomorphic immersion
pulls squared distance back to a strictly plurisubharmonic function.

These formulas are the local inner-product-space calculation behind squared-distance
exhaustions of closed complex submanifolds. No immersion hypothesis is needed until strict
positivity is deduced.

## Main results

* `TauCeti.fderiv_norm_sq_sub_comp`: the first derivative of squared distance along a map.
* `TauCeti.fderiv_norm_sq_sub_comp_eq_zero_iff`: the critical-point normal-vector test.
* `TauCeti.fderiv_fderiv_norm_sq_sub_comp_apply`: the full Hessian formula.
* `TauCeti.fderiv_fderiv_norm_sq_apply_complex`: the real second derivative of complex squared
  norm is twice the real part of the inner product.
* `TauCeti.fderiv_fderiv_norm_sq_sub_comp_add_I_smul`: the complex Hessian identity.
* `TauCeti.re_leviForm_norm_sq_sub_comp_apply_self`: the Levi diagonal of squared distance.
* `TauCeti.isStrictlyPlurisubharmonicAt_norm_sq_sub_comp`: strict plurisubharmonicity along a
  holomorphic immersion.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Complex Function Module
open scoped RealInnerProductSpace

namespace TauCeti

section Real

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {i : V → E} {a : E} {x : V}

/-- The derivative of squared distance from `a` along a differentiable map `i` is the pairing
with `2 • (i x - a)`, precomposed with the derivative of `i`. -/
theorem fderiv_norm_sq_sub_comp (hi : DifferentiableAt ℝ i x) :
    fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2) x =
      2 • (innerSL ℝ (i x - a)).comp (fderiv ℝ i x) := by
  exact ((hi.hasFDerivAt.sub_const a).norm_sq).fderiv

/-- **The critical-point normal-vector test.** Squared distance from `a` along `i` is critical at
`x` exactly when the displacement `i x - a` is orthogonal to the range of `Di(x)`. -/
theorem fderiv_norm_sq_sub_comp_eq_zero_iff (hi : DifferentiableAt ℝ i x) :
    fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2) x = 0 ↔
      i x - a ∈ (fderiv ℝ i x).rangeᗮ := by
  rw [fderiv_norm_sq_sub_comp hi, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    have hv := congrArg (fun L : V →L[ℝ] ℝ ↦ L v) h
    rw [real_inner_comm]
    rw [inner_sub_left]
    simpa using hv
  · intro h
    ext v
    have hv := h (fderiv ℝ i x v) ⟨v, rfl⟩
    have hv' : inner ℝ (i x - a) (fderiv ℝ i x v) = 0 := by
      rw [real_inner_comm]
      exact hv
    rw [inner_sub_left] at hv'
    simpa using hv'

/-- The second derivative of squared norm is twice the inner product. -/
theorem fderiv_fderiv_norm_sq_apply (y u v : E) :
    fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ 2)) y u v = 2 * inner ℝ u v := by
  have hsnd : fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ 2)) y =
      (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv
  rw [hsnd]
  simp only [two_smul, add_apply]
  rw [innerSL_apply_apply]
  ring

/-- **The Hessian of squared distance along a map.** It is twice the sum of the pullback inner
product and the pairing of the displacement with the second derivative of the map. -/
theorem fderiv_fderiv_norm_sq_sub_comp_apply (hi : ContDiffAt ℝ 2 i x) (v w : V) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2)) x v w =
      2 * (inner ℝ (fderiv ℝ i x v) (fderiv ℝ i x w) +
        inner ℝ (i x - a) (fderiv ℝ (fderiv ℝ i) x v w)) := by
  let φ : V → E := fun y ↦ i y - a
  have hφ : ContDiffAt ℝ 2 φ x := hi.sub contDiffAt_const
  have hcomp : (fun y ↦ ‖i y - a‖ ^ 2) = (fun z : E ↦ ‖z‖ ^ 2) ∘ φ := rfl
  have hD2 : fderiv ℝ (fderiv ℝ φ) x = fderiv ℝ (fderiv ℝ i) x := by
    congr 1
    exact funext fun _ ↦ fderiv_sub_const a
  rw [hcomp, fderiv_fderiv_comp_apply (contDiff_norm_sq ℝ).contDiffAt hφ]
  simp only [φ, fderiv_sub_const, hD2]
  rw [fderiv_fderiv_norm_sq_apply, fderiv_norm_sq_apply]
  simp only [map_sub, smul_apply, sub_apply, coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [inner_sub_left]
  ring

end Real

section Complex

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {i : V → E} {a : E} {x : V}

/-- The real second derivative of the squared norm of a complex inner product space is
`2 * Re ⟪v, w⟫_ℂ`. -/
theorem fderiv_fderiv_norm_sq_apply_complex (x v w : E) :
    fderiv ℝ (fderiv ℝ fun z : E ↦ ‖z‖ ^ 2) x v w = 2 * (inner ℂ v w).re := by
  -- The real inner product of the underlying real inner product space is `Re ⟪v, w⟫_ℂ` by
  -- definition (`real_inner_eq_re_inner`); it is not a global instance, to avoid diamonds.
  let := InnerProductSpace.complexToReal (G := E)
  exact fderiv_fderiv_norm_sq_apply x v w

/-- **The complex Hessian identity for squared distance.** For a holomorphic `C²` map, the sum
of the real Hessian on `v` and `I • v` is four times the squared norm of the complex derivative.
The identity holds at every point; at a critical point it is the intrinsic Hessian identity used
in the squared-distance Morse-index estimate. -/
theorem fderiv_fderiv_norm_sq_sub_comp_add_I_smul (hi : ContDiffAt ℂ 2 i x) (v : V) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2)) x v v +
        fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2)) x (I • v) (I • v) =
      4 * ‖fderiv ℂ i x v‖ ^ 2 := by
  let _ : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hiR : ContDiffAt ℝ 2 i x := hi.restrict_scalars ℝ
  rw [fderiv_fderiv_norm_sq_sub_comp_apply hiR,
    fderiv_fderiv_norm_sq_sub_comp_apply hiR]
  have hD : fderiv ℝ i x = (fderiv ℂ i x).restrictScalars ℝ :=
    (hi.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ
  have hD2 (u w : V) :
      fderiv ℝ (fderiv ℝ i) x u w = fderiv ℂ (fderiv ℂ i) x u w :=
    hi.fderiv_fderiv_restrictScalars_apply u w
  rw [hD]
  simp only [map_smul, hD2]
  simp [inner_smul_right, real_inner_eq_re_inner, norm_smul]
  ring

/-- The Levi diagonal of squared distance along a holomorphic `C²` map is the squared norm of its
complex derivative. -/
theorem re_leviForm_norm_sq_sub_comp_apply_self (hi : ContDiffAt ℂ 2 i x) (v : V) :
    (leviForm (fun y ↦ ‖i y - a‖ ^ 2) x v v).re = ‖fderiv ℂ i x v‖ ^ 2 := by
  rw [re_leviForm_apply]
  have h := fderiv_fderiv_norm_sq_sub_comp_add_I_smul (a := a) hi v
  linarith

/-- Squared distance pulled back along a holomorphic immersion is strictly plurisubharmonic at
the point of immersion. -/
theorem isStrictlyPlurisubharmonicAt_norm_sq_sub_comp (hi : ContDiffAt ℂ 2 i x)
    (hi' : Injective (fderiv ℂ i x)) :
    IsStrictlyPlurisubharmonicAt (fun y ↦ ‖i y - a‖ ^ 2) x := by
  rw [isStrictlyPlurisubharmonicAt_iff]
  intro v hv
  rw [re_leviForm_norm_sq_sub_comp_apply_self hi]
  exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero_iff _ hi').2 hv))

end Complex

end TauCeti
