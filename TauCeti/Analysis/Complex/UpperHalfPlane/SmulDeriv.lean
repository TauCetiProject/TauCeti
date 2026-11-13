/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation

import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The derivative of the `PSL(2, ℝ)`- and `GL(2, ℝ)`-actions on the upper half-plane

A Möbius transformation of the upper half-plane is holomorphic, with derivative
`det g / denom g z ^ 2` at `z`, where `denom g z = c * z + d` is Mathlib's automorphy factor
(`UpperHalfPlane.hasStrictDerivAt_smul`). A representative in `SL(2, ℝ)` has determinant `1`, so
the derivative is `(denom g z ^ 2)⁻¹`; squaring the automorphy factor cancels the sign ambiguity
of the representative, so this depends only on the class in `PSL(2, ℝ)`. That well-defined
derivative is `Matrix.ProjectiveSpecialLinearGroup.smulDeriv`, the quantity the effective
projective action attaches to a point.

By the chain rule the derivative is a cocycle for the action
(`Matrix.ProjectiveSpecialLinearGroup.smulDeriv_mul`); restricted to the stabilizer of a point
it therefore becomes a character, which is what governs the stabilizers of a discrete subgroup.

Viewing `ℍ` as a real manifold, every `g ∈ GL(2, ℝ)` acts, antiholomorphically when
`det g < 0`, with real derivative Mathlib's `UpperHalfPlane.smulFDeriv g z`: multiplication by
`det g/(cz + d)²`, followed by complex conjugation when `det g < 0`. It multiplies every length by
`|det g|/|cz + d|²`, which is the ratio `Im(g • z)/Im z` by `UpperHalfPlane.im_smul_eq_div_normSq`.

## Main declarations

* `Matrix.ProjectiveSpecialLinearGroup.smulDeriv`: the derivative at `z : ℍ` of the Möbius
  transformation attached to `q : PSL(2, ℝ)`.
* `Matrix.ProjectiveSpecialLinearGroup.hasStrictDerivAt_coe_smul` and
  `Matrix.ProjectiveSpecialLinearGroup.deriv_coe_smul`: it is the complex derivative of that
  transformation, read through Mathlib's partial inverse `UpperHalfPlane.ofComplex` of the
  inclusion `ℍ → ℂ`.
* `Matrix.ProjectiveSpecialLinearGroup.deriv_smul_mul_smulDeriv_of_eventuallyEq`: the derivative
  of a function invariant under a Möbius transformation.
* `Matrix.ProjectiveSpecialLinearGroup.smulDeriv_mul`: the chain rule
  `(q₁ * q₂)' z = q₁' (q₂ • z) * q₂' z`, and
  `Matrix.ProjectiveSpecialLinearGroup.smulDeriv_inv` for the inverse.
* `Matrix.ProjectiveSpecialLinearGroup.norm_smulDeriv_of_smul_eq_self`: the derivative at a
  fixed point is unimodular, so a transformation fixing a point rotates about it.
* `Matrix.SpecialLinearGroup.conj_denom_eq_inv_of_smul_eq_self`: at a fixed point of
  `g ∈ SL(2, ℝ)` the automorphy factor is unimodular, so its conjugate is its inverse.
* `Matrix.ProjectiveSpecialLinearGroup.smulDeriv_dilation`: the dilation `z ↦ exp s * z` has
  derivative `exp s`.
* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: in model coordinates, the differential of
  the action of `g ∈ GL(2, ℝ)`, smooth by `UpperHalfPlane.instContMDiffConstSMulGL2Real`, is
  `UpperHalfPlane.smulFDeriv`.
* `UpperHalfPlane.norm_smulFDeriv_apply` and `UpperHalfPlane.inner_smulFDeriv_apply`:
  `UpperHalfPlane.smulFDeriv g z` multiplies lengths by `Im(g • z)/Im z` and real inner products
  by `(Im(g • z)/Im z)²`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 7.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of
  Chicago Press, 1992, §§2.1–2.4.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- The automorphy factor changes sign along with its matrix, so squaring it gives a function of
the class in `PSL(2, ℝ)`. -/
theorem denom_mapGL_neg (g : SL(2, ℝ)) (z : ℂ) :
    denom (mapGL ℝ (-g)) z = -denom (mapGL ℝ g) z := by
  simp [denom]
  ring

/-- **The automorphy factor at a fixed point is unimodular.** The imaginary part of `g • z` is
`im z` divided by the squared modulus of the automorphy factor, so fixing `z` forces that
modulus to be `1`. -/
theorem normSq_denom_eq_one_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z) :
    Complex.normSq (denom (mapGL ℝ g) (z : ℂ)) = 1 := by
  have him := UpperHalfPlane.im_smul_eq_div_normSq (mapGL ℝ g) z
  have hmapGL : mapGL ℝ g • z = z := by
    rwa [MulAction.compHom_smul_def] at hz
  rw [hmapGL, det_mapGL] at him
  have hne := UpperHalfPlane.normSq_denom_ne_zero (mapGL ℝ g) z.im_ne_zero
  rw [Units.val_one, abs_one, one_mul, eq_div_iff hne] at him
  exact mul_left_cancel₀ z.im_ne_zero (by rw [him, mul_one])

open scoped ComplexConjugate in
/-- At a fixed point the automorphy factor is unimodular
(`Matrix.SpecialLinearGroup.normSq_denom_eq_one_of_smul_eq_self`), so its conjugate is its
inverse. -/
theorem conj_denom_eq_inv_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z) :
    conj (denom (mapGL ℝ g) (z : ℂ)) = (denom (mapGL ℝ g) (z : ℂ))⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [mul_comm, Complex.mul_conj, normSq_denom_eq_one_of_smul_eq_self hz, Complex.ofReal_one]

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The derivative at `z : ℍ` of the Möbius transformation of the upper half-plane attached to
`q : PSL(2, ℝ)`; see `Matrix.ProjectiveSpecialLinearGroup.deriv_coe_smul`. On a representative
`g : SL(2, ℝ)` it is `(denom g z ^ 2)⁻¹`, independent of the representative by
`Matrix.SpecialLinearGroup.denom_mapGL_neg`. -/
def smulDeriv (q : PSL(2, ℝ)) (z : ℍ) : ℂ :=
  Quotient.liftOn' q (fun g : SL(2, ℝ) ↦ (denom (mapGL ℝ g) (z : ℂ) ^ 2)⁻¹) <| by
    rintro a b hab
    rw [QuotientGroup.leftRel_apply, mem_center_iff_eq_one_or_eq_neg_one] at hab
    rcases hab with h | h
    · rw [inv_mul_eq_one] at h
      rw [h]
    · have hb : b = -a := by simpa using congrArg (a * ·) h
      subst hb
      rw [Matrix.SpecialLinearGroup.denom_mapGL_neg, neg_sq]

end Matrix.ProjectiveSpecialLinearGroup

namespace Matrix.SpecialLinearGroup

/-- The derivative of the transformation of a representative, in terms of its automorphy
factor. -/
@[simp]
theorem smulDeriv_coe (g : SL(2, ℝ)) (z : ℍ) :
    Matrix.ProjectiveSpecialLinearGroup.smulDeriv (g : PSL(2, ℝ)) z =
      (denom (mapGL ℝ g) (z : ℂ) ^ 2)⁻¹ := (rfl)

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- A Möbius transformation of `ℍ` has nowhere vanishing derivative. -/
@[simp]
theorem smulDeriv_ne_zero (q : PSL(2, ℝ)) (z : ℍ) : smulDeriv q z ≠ 0 := by
  induction q using QuotientGroup.induction_on with | _ g =>
  simp [denom_ne_zero]

/-- **A Möbius transformation of `ℍ` fixing a point is a rotation there**: its derivative at a
fixed point has modulus one. -/
theorem norm_smulDeriv_of_smul_eq_self {q : PSL(2, ℝ)} {z : ℍ} (hz : q • z = z) :
    ‖smulDeriv q z‖ = 1 := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have h := Matrix.SpecialLinearGroup.normSq_denom_eq_one_of_smul_eq_self
    (by rwa [pslMk_smul] at hz)
  rw [Complex.normSq_eq_norm_sq] at h
  rw [smulDeriv_coe, norm_inv, norm_pow, h, inv_one]

/-- The identity transformation has derivative `1`. -/
@[simp]
theorem smulDeriv_one (z : ℍ) : smulDeriv 1 z = 1 := by
  have h : ((1 : SL(2, ℝ)) : PSL(2, ℝ)) = 1 := map_one (QuotientGroup.mk' _)
  rw [← h, smulDeriv_coe]
  simp

/-- **The chain rule for the `PSL(2, ℝ)`-action**: the derivative is a cocycle. -/
@[simp]
theorem smulDeriv_mul (q₁ q₂ : PSL(2, ℝ)) (z : ℍ) :
    smulDeriv (q₁ * q₂) z = smulDeriv q₁ (q₂ • z) * smulDeriv q₂ z := by
  induction q₁ using QuotientGroup.induction_on with | _ a =>
  induction q₂ using QuotientGroup.induction_on with | _ b =>
  have hmul : ((a : PSL(2, ℝ)) * (b : PSL(2, ℝ))) = ((a * b : SL(2, ℝ)) : PSL(2, ℝ)) :=
    (map_mul (QuotientGroup.mk' _) a b).symm
  have hb : ((b : PSL(2, ℝ)) • z) = (mapGL ℝ b) • z := by
    rw [pslMk_smul]
    rfl
  rw [hmul, smulDeriv_coe, smulDeriv_coe, hb, smulDeriv_coe, map_mul, denom_cocycle_σ,
    σ_eq_refl_of_det_pos (by simp)]
  simp [mul_pow, mul_comm]

/-- The inverse transformation has the inverse derivative at the image point. -/
@[simp]
theorem smulDeriv_inv (q : PSL(2, ℝ)) (z : ℍ) :
    smulDeriv q⁻¹ (q • z) = (smulDeriv q z)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← smulDeriv_mul, inv_mul_cancel, smulDeriv_one]

/-- **`smulDeriv` is the derivative of the Möbius transformation.** The transformation is read
on `ℂ` through Mathlib's partial inverse `UpperHalfPlane.ofComplex` of the inclusion `ℍ → ℂ`,
which is the identity on the upper half-plane and so does not affect the derivative there. -/
theorem hasStrictDerivAt_coe_smul (q : PSL(2, ℝ)) (z : ℍ) :
    HasStrictDerivAt (fun w : ℂ ↦ ((q • ofComplex w : ℍ) : ℂ)) (smulDeriv q z) (z : ℂ) := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have h := UpperHalfPlane.hasStrictDerivAt_smul (g := mapGL ℝ g) (by simp) z
  have hfun : (fun w : ℂ ↦ (((g : PSL(2, ℝ)) • ofComplex w : ℍ) : ℂ)) =
      fun w : ℂ ↦ ((mapGL ℝ g • ofComplex w : ℍ) : ℂ) := by
    funext w
    rw [pslMk_smul]
    rfl
  rw [hfun, smulDeriv_coe]
  simpa [one_div] using h

/-- The derivative of a Möbius transformation of `ℍ`, in the form `deriv`. -/
@[simp]
theorem deriv_coe_smul (q : PSL(2, ℝ)) (z : ℍ) :
    deriv (fun w : ℂ ↦ ((q • ofComplex w : ℍ) : ℂ)) (z : ℂ) = smulDeriv q z :=
  (hasStrictDerivAt_coe_smul q z).hasDerivAt.deriv

/-- **The derivative of an invariant function.** If a function `W` on `ℂ` is unchanged near `z`
by the Möbius transformation attached to `q`, read on `ℂ` through `UpperHalfPlane.ofComplex`, then
by the chain rule its derivative at `z` is its derivative at `q • z` times `smulDeriv q z`. (If `W`
is not differentiable at `q • z`, then by invariance it is not differentiable at `z` either, and
both sides vanish.) -/
theorem deriv_smul_mul_smulDeriv_of_eventuallyEq {W : ℂ → ℂ} (q : PSL(2, ℝ)) {z : ℍ}
    (hW : (fun w : ℂ ↦ W ((q • ofComplex w : ℍ) : ℂ)) =ᶠ[nhds (z : ℂ)] W) :
    deriv W ((q • z : ℍ) : ℂ) * smulDeriv q z = deriv W z := by
  by_cases hd : DifferentiableAt ℂ W ((q • z : ℍ) : ℂ)
  · have h := hd.hasDerivAt.comp_of_eq (z : ℂ) (hasStrictDerivAt_coe_smul q z).hasDerivAt
      (by rw [ofComplex_apply])
    rw [← hW.deriv_eq, ← h.deriv, Function.comp_def]
  · have hz : ¬ DifferentiableAt ℂ W (z : ℂ) := fun hz ↦ hd (by
      -- the invariance runs both ways, so `W` is differentiable at `q • z` if it is at `z`
      have hg := (hasStrictDerivAt_coe_smul q⁻¹ (q • z)).hasDerivAt
      have hc := hz.hasDerivAt.comp_of_eq ((q • z : ℍ) : ℂ) hg
        (by rw [ofComplex_apply, inv_smul_smul])
      refine hc.differentiableAt.congr_of_eventuallyEq ?_
      have hW' : ∀ᶠ y in nhds (((q⁻¹ • ofComplex ((q • z : ℍ) : ℂ) : ℍ)) : ℂ),
          W ((q • ofComplex y : ℍ) : ℂ) = W y := by
        rwa [ofComplex_apply, inv_smul_smul]
      filter_upwards [hg.continuousAt.eventually hW',
        isOpen_upperHalfPlaneSet.mem_nhds (q • z).2] with u hu hu'
      simp only [Function.comp_apply]
      rw [ofComplex_apply, smul_inv_smul, ofComplex_apply_of_im_pos hu'] at hu
      rw [ofComplex_apply_of_im_pos hu']
      exact hu)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hz, zero_mul]

-- Not `@[simp]`: `smulDeriv_coe` rewrites the left-hand side first. Use it via `rw`.
/-- The derivative of the dilation `z ↦ exp s * z` is `exp s`. -/
theorem smulDeriv_dilation (s : ℝ) (z : ℍ) : smulDeriv (↑(dilation s)) z = Real.exp s := by
  rw [smulDeriv_coe]
  simp only [denom, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.algebraMap_self_apply, coe_dilation, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero,
    zero_mul, zero_add]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_inj, ← Real.exp_nat_mul,
    ← Real.exp_neg]
  congr 1
  push_cast
  ring

end Matrix.ProjectiveSpecialLinearGroup

namespace UpperHalfPlane

open Manifold

open scoped Manifold

/-- In the model coordinates of the inclusion chart, the differential of the action of
`g ∈ GL(2, ℝ)` on `ℍ` is Mathlib's real derivative `UpperHalfPlane.smulFDeriv g z`. -/
theorem tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    (contMDiff_const_smul (n := 1) g).mdifferentiableAt one_ne_zero
  rw [hg.tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • ·)
      =ᶠ[nhds (z : ℂ)] fun w ↦ ↑(g • ofComplex w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have hsymm : (extChartAt 𝓘(ℝ, ℂ) z).symm w = ofComplex w := by
      rw [ofComplex_apply_of_im_pos hw]
      exact (extChartAt 𝓘(ℝ, ℂ) z).left_inv (x := ⟨w, hw⟩) (by simp)
    simp only [writtenInExtChartAt, Function.comp_apply, hsymm]
    simp
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- The real derivative of the action of `g ∈ GL(2, ℝ)` multiplies lengths by
`Im(g • z)/Im z`. -/
theorem norm_smulFDeriv_apply (g : GL (Fin 2) ℝ) (z : ℍ) (v : ℂ) :
    ‖smulFDeriv g z v‖ = (g • z).im / z.im * ‖v‖ := by
  have hz := z.im_pos.ne'
  have hd := denom_ne_zero g z
  rw [im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  simp only [smulFDeriv, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    ContinuousAlgEquiv.toContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, norm_σ,
    norm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  field_simp

/-- The real derivative of the action of `g ∈ GL(2, ℝ)` multiplies real inner products by
`(Im(g • z)/Im z)²`. -/
theorem inner_smulFDeriv_apply (g : GL (Fin 2) ℝ) (z : ℍ) (v w : ℂ) :
    inner ℝ (smulFDeriv g z v) (smulFDeriv g z w) = ((g • z).im / z.im) ^ 2 * inner ℝ v w := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
    norm_smulFDeriv_apply, norm_smulFDeriv_apply, norm_smulFDeriv_apply]
  ring

end UpperHalfPlane
