/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Derivatives of the Schur complements of a family of block operators

Let `A y : E₁ →L[𝕜] F₁`, `B y : E₂ →L[𝕜] F₁`, `C y : E₁ →L[𝕜] F₂` and `D y : E₂ →L[𝕜] F₂` be the
blocks of a family of block operators `(A y B y; C y D y) : E₁ × E₂ → F₁ × F₂`, depending on a
parameter `y` in a normed space `X`, with `E₁` complete. Where the upper left block `A y` is
invertible, the reduction of the block operator to its second component is governed by the Schur
complement

`S y = D y - C y (A y)⁻¹ B y : E₂ →L[𝕜] F₂`,

which is `ContinuousLinearEquiv.schurComplement` of any equivalence with underlying map `A y`
(`ContinuousLinearEquiv.schurComplement_eq_sub_comp_inverse`). This is the slow operator of a
Lyapunov–Schmidt or adiabatic reduction, whose fast block `A y` is inverted directly; when the
blocks depend on parameters (the moduli of the reduction, or a coordinate along the base of an
adiabatic limit), so does the slow operator. This file differentiates it in the parameter.

* **Derivative.** If the blocks are differentiable at `x` and `A x` is invertible, then `S` is
  differentiable at `x`, with derivative along `v`
  `S' v = D' v - C' v A⁻¹ B + C A⁻¹ (A' v) A⁻¹ B - C A⁻¹ B' v`, all blocks taken at `x`
  (`HasFDerivAt.clm_schurComplement`, `DifferentiableAt.clm_schurComplement`,
  `fderiv_clm_schurComplement_apply`, and `HasDerivAt.clm_schurComplement` for a scalar
  parameter). The derivative `-A⁻¹ A' A⁻¹` of the inverse is
  `HasFDerivAt.clm_inverse_of_completeSpace`.
* **Smoothness.** If the blocks are `C^n` and `A` is invertible at the points considered, then
  `S` is `C^n` there (`ContDiffWithinAt.clm_schurComplement`, `ContDiffAt.clm_schurComplement`,
  `ContDiffOn.clm_schurComplement`, `ContDiff.clm_schurComplement`), since inversion is smooth on
  the invertible maps (`ContDiffAt.clm_inverse`).

The variation of the Schur complement between two parameters, without derivatives, is
`ContinuousLinearEquiv.norm_schurComplement_sub_schurComplement_le`.
-/

public section

open ContinuousLinearMap

section Parameter

variable {𝕜 X E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {A : X → E₁ →L[𝕜] F₁} {B : X → E₂ →L[𝕜] F₁} {C : X → E₁ →L[𝕜] F₂} {D : X → E₂ →L[𝕜] F₂}
  {x : X}

/-- The Schur complement `y ↦ D y - C y (A y)⁻¹ B y` of a family of block operators is
differentiable at a point where the blocks are differentiable and `A` is invertible. -/
theorem DifferentiableAt.clm_schurComplement (hA : DifferentiableAt 𝕜 A x)
    (hB : DifferentiableAt 𝕜 B x) (hC : DifferentiableAt 𝕜 C x) (hD : DifferentiableAt 𝕜 D x)
    (hx : (A x).IsInvertible) :
    DifferentiableAt 𝕜 (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) x :=
  hD.sub (hC.clm_comp ((hA.clm_inverse_of_completeSpace hx).clm_comp hB))

/-- **The derivative of a Schur complement**, as a formula for `fderiv`: along `v`, the Schur
complement `y ↦ D y - C y (A y)⁻¹ B y` has derivative
`D' v - C' v A⁻¹ B + C A⁻¹ (A' v) A⁻¹ B - C A⁻¹ (B' v)`, where `A' = fderiv 𝕜 A x` and so on and
the blocks are taken at `x`. -/
theorem fderiv_clm_schurComplement_apply (hA : DifferentiableAt 𝕜 A x)
    (hB : DifferentiableAt 𝕜 B x) (hC : DifferentiableAt 𝕜 C x) (hD : DifferentiableAt 𝕜 D x)
    (hx : (A x).IsInvertible) (v : X) :
    fderiv 𝕜 (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) x v =
      fderiv 𝕜 D x v - fderiv 𝕜 C x v ∘L (A x).inverse ∘L B x +
        C x ∘L (A x).inverse ∘L fderiv 𝕜 A x v ∘L (A x).inverse ∘L B x -
        C x ∘L (A x).inverse ∘L fderiv 𝕜 B x v := by
  have h : HasFDerivAt (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) _ x :=
    hD.hasFDerivAt.sub (hC.hasFDerivAt.clm_comp
      ((hA.hasFDerivAt.clm_inverse_of_completeSpace hx).clm_comp hB.hasFDerivAt))
  rw [h.fderiv]
  ext w
  simp only [sub_apply, add_apply, comp_apply, compL_apply, flip_apply, neg_apply, map_add, map_neg,
    bilinearRestrictScalars_apply_apply]
  abel

/-- **The derivative of a Schur complement.** If the blocks `A`, `B`, `C`, `D` of a family of
block operators have derivatives `A'`, `B'`, `C'`, `D'` at `x`, and `A x` is invertible, then the
Schur complement `y ↦ D y - C y (A y)⁻¹ B y` has at `x` the derivative `S'` with
`S' v = D' v - C' v A⁻¹ B + C A⁻¹ (A' v) A⁻¹ B - C A⁻¹ (B' v)`, the blocks taken at `x`. -/
theorem HasFDerivAt.clm_schurComplement {A' : X →L[𝕜] E₁ →L[𝕜] F₁}
    {B' : X →L[𝕜] E₂ →L[𝕜] F₁} {C' : X →L[𝕜] E₁ →L[𝕜] F₂} {D' : X →L[𝕜] E₂ →L[𝕜] F₂}
    {S' : X →L[𝕜] E₂ →L[𝕜] F₂} (hA : HasFDerivAt A A' x) (hB : HasFDerivAt B B' x)
    (hC : HasFDerivAt C C' x) (hD : HasFDerivAt D D' x) (hx : (A x).IsInvertible)
    (hS' : ∀ v, S' v = D' v - C' v ∘L (A x).inverse ∘L B x +
      C x ∘L (A x).inverse ∘L A' v ∘L (A x).inverse ∘L B x - C x ∘L (A x).inverse ∘L B' v) :
    HasFDerivAt (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) S' x := by
  refine (hA.differentiableAt.clm_schurComplement hB.differentiableAt hC.differentiableAt
    hD.differentiableAt hx).hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  rw [hS', fderiv_clm_schurComplement_apply hA.differentiableAt hB.differentiableAt
    hC.differentiableAt hD.differentiableAt hx, hA.fderiv, hB.fderiv, hC.fderiv, hD.fderiv]

/-- The Schur complement `y ↦ D y - C y (A y)⁻¹ B y` of a `C^n` family of block operators is
`C^n` within `s` at a point where `A` is invertible. -/
theorem ContDiffWithinAt.clm_schurComplement {s : Set X} {n : WithTop ℕ∞}
    (hA : ContDiffWithinAt 𝕜 n A s x) (hB : ContDiffWithinAt 𝕜 n B s x)
    (hC : ContDiffWithinAt 𝕜 n C s x) (hD : ContDiffWithinAt 𝕜 n D s x)
    (hx : (A x).IsInvertible) :
    ContDiffWithinAt 𝕜 n (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) s x :=
  hD.sub (hC.clm_comp ((hA.clm_inverse hx).clm_comp hB))

/-- The Schur complement `y ↦ D y - C y (A y)⁻¹ B y` of a `C^n` family of block operators is
`C^n` at a point where `A` is invertible. -/
theorem ContDiffAt.clm_schurComplement {n : WithTop ℕ∞} (hA : ContDiffAt 𝕜 n A x)
    (hB : ContDiffAt 𝕜 n B x) (hC : ContDiffAt 𝕜 n C x) (hD : ContDiffAt 𝕜 n D x)
    (hx : (A x).IsInvertible) :
    ContDiffAt 𝕜 n (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) x :=
  hD.sub (hC.clm_comp ((hA.clm_inverse hx).clm_comp hB))

/-- The Schur complement `y ↦ D y - C y (A y)⁻¹ B y` of a family of block operators is `C^n` on
every set on which the blocks are `C^n` and `A` is invertible. -/
theorem ContDiffOn.clm_schurComplement {s : Set X} {n : WithTop ℕ∞} (hA : ContDiffOn 𝕜 n A s)
    (hB : ContDiffOn 𝕜 n B s) (hC : ContDiffOn 𝕜 n C s) (hD : ContDiffOn 𝕜 n D s)
    (hinv : ∀ y ∈ s, (A y).IsInvertible) :
    ContDiffOn 𝕜 n (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) s :=
  fun y hy ↦ (hA y hy).clm_schurComplement (hB y hy) (hC y hy) (hD y hy) (hinv y hy)

/-- The Schur complement `y ↦ D y - C y (A y)⁻¹ B y` of a `C^n` family of block operators whose
upper left block is everywhere invertible is `C^n`. -/
theorem ContDiff.clm_schurComplement {n : WithTop ℕ∞} (hA : ContDiff 𝕜 n A)
    (hB : ContDiff 𝕜 n B) (hC : ContDiff 𝕜 n C) (hD : ContDiff 𝕜 n D)
    (hinv : ∀ y, (A y).IsInvertible) :
    ContDiff 𝕜 n (fun y ↦ D y - C y ∘L (A y).inverse ∘L B y) :=
  contDiff_iff_contDiffAt.2 fun y ↦
    hA.contDiffAt.clm_schurComplement hB.contDiffAt hC.contDiffAt hD.contDiffAt (hinv y)

end Parameter

section Scalar

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {A : 𝕜 → E₁ →L[𝕜] F₁} {B : 𝕜 → E₂ →L[𝕜] F₁} {C : 𝕜 → E₁ →L[𝕜] F₂} {D : 𝕜 → E₂ →L[𝕜] F₂}
  {A' : E₁ →L[𝕜] F₁} {B' : E₂ →L[𝕜] F₁} {C' : E₁ →L[𝕜] F₂} {D' : E₂ →L[𝕜] F₂} {t : 𝕜}

/-- **The derivative of a Schur complement along a scalar parameter.** If the blocks of a family
of block operators have derivatives `A'`, `B'`, `C'`, `D'` at `t` and `A t` is invertible, then
the Schur complement `s ↦ D s - C s (A s)⁻¹ B s` has derivative
`D' - C' A⁻¹ B + C A⁻¹ A' A⁻¹ B - C A⁻¹ B'` at `t`, the blocks taken at `t`. -/
theorem HasDerivAt.clm_schurComplement (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hC : HasDerivAt C C' t) (hD : HasDerivAt D D' t) (ht : (A t).IsInvertible) :
    HasDerivAt (fun s ↦ D s - C s ∘L (A s).inverse ∘L B s)
      (D' - C' ∘L (A t).inverse ∘L B t + C t ∘L (A t).inverse ∘L A' ∘L (A t).inverse ∘L B t -
        C t ∘L (A t).inverse ∘L B') t := by
  simpa using (hA.hasFDerivAt.clm_schurComplement hB.hasFDerivAt hC.hasFDerivAt hD.hasFDerivAt ht
    (S' := smulRight (1 : 𝕜 →L[𝕜] 𝕜) (D' - C' ∘L (A t).inverse ∘L B t +
      C t ∘L (A t).inverse ∘L A' ∘L (A t).inverse ∘L B t - C t ∘L (A t).inverse ∘L B'))
    fun v ↦ by ext w; simp [smul_sub, smul_add]).hasDerivAt

end Scalar
