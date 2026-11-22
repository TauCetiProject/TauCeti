/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Gauge identities for smooth connections

A connection on (an open subset of) a normed space `E` with values in a normed algebra `𝔸` is an
`𝔸`-valued one-form `A`, here a map `A : E → E →L[𝕜] 𝔸`; in coordinates `A_j = A x eⱼ`. For
matrix groups `𝔸` is the matrix algebra and `A` takes values in the Lie algebra `𝔤`. This file
sets up the pointwise calculus of such connections in the conventions of Oh and Tataru, and
proves the identities of smooth gauge theory: the gauge action is a group action, curvature and
covariant derivatives transform by `Ad`, and the Ricci and Bianchi identities hold.

For a map `O : E → 𝔸` with invertible values (a gauge transformation), write
`O;v = (∂ᵥO) O⁻¹` for its right Maurer–Cartan form. The gauge action is
`O·A = Ad(O) A - O;x`, that is `(O·A)_v = O A_v O⁻¹ - (∂ᵥO) O⁻¹`. The curvature of `A` is the
bilinear map `F_{vw} = ∂ᵥA_w - ∂_wA_v + [A_v, A_w]`, that is `F = dA + ½[A ∧ A]`, and the
covariant derivative of an `𝔸`-valued function `B` is `D_v B = ∂ᵥB + [A_v, B]`. Inverses are
`Ring.inverse`, so no unit-valued type of maps is needed; the identities involving `O⁻¹` assume
that the relevant values of `O` are units.

All identities are pointwise: they hold at a point `x` under differentiability hypotheses at `x`
only, so they apply verbatim to connections on an open subset. With this sign convention the
gauge action is a left action and curvature transforms by `Ad(O)`.

## Main definitions

* `TauCeti.rightMaurerCartan`: the right Maurer–Cartan form `O;x = (∂O) O⁻¹`.
* `TauCeti.gaugeAction`: the gauge action `O·A = Ad(O) A - O;x`.
* `TauCeti.connectionCurvature`: the curvature `F_{vw} = ∂ᵥA_w - ∂_wA_v + [A_v, A_w]`.
* `TauCeti.connectionCovariantDeriv`: the covariant derivative `D_v B = ∂ᵥB + [A_v, B]`.

## Main results

* `TauCeti.gaugeAction_one`, `TauCeti.gaugeAction_gaugeAction`: `1·A = A` and
  `O·(O'·A) = (OO')·A`.
* `TauCeti.rightMaurerCartan_mul`, `TauCeti.rightMaurerCartan_ringInverse`:
  `(OO');x = O;x + Ad(O)(O';x)` and `(O⁻¹);x = -Ad(O⁻¹)(O;x)`.
* `TauCeti.fderiv_mul_mul_ringInverse_apply`: `∂ᵥ(Ad(O)B) = Ad(O)∂ᵥB + [O;v, Ad(O)B]`.
* `TauCeti.connectionCovariantDeriv_gaugeAction`: `D(O·A)(Ad(O)B) = Ad(O)(D(A)B)`.
* `TauCeti.connectionCurvature_gaugeAction`: `F[O·A] = Ad(O) F[A]`.
* `TauCeti.connectionCovariantDeriv_sub_connectionCovariantDeriv_swap`: the Ricci identity
  `D_vD_wB - D_wD_vB = [F_{vw}, B]`.
* `TauCeti.connectionCurvature_bianchi`: the Bianchi identity
  `D_uF_{vw} + D_vF_{wu} + D_wF_{uv} = 0`.
* `TauCeti.gaugeAction_eq_sub`, `TauCeti.connectionCurvature_apply_of_comm`: for commutative
  coefficients, as for `U(1)`, `O·A = A - O;x` and `F = dA`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 1.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Sections 1 and 3
  (Lemma 3.4, the Leibniz rules for gauge transformations).
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Ring

namespace TauCeti

variable (𝕜 : Type*) {E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]

/-! ### Definitions -/

/-- The **right Maurer–Cartan form** `O;x = (∂O) O⁻¹` of a map `O : E → 𝔸` at `x`: the one-form
`v ↦ (∂ᵥO)(x) (O x)⁻¹`. -/
def rightMaurerCartan (O : E → 𝔸) (x : E) : E →L[𝕜] 𝔸 :=
  (mul 𝕜 𝔸).flip (O x)⁻¹ʳ ∘L fderiv 𝕜 O x

/-- The **gauge action** `O·A = Ad(O) A - O;x` of a map `O : E → 𝔸` on an `𝔸`-valued one-form
`A`: `(O·A)_v = O A_v O⁻¹ - (∂ᵥO) O⁻¹`. -/
def gaugeAction (O : E → 𝔸) (A : E → E →L[𝕜] 𝔸) (x : E) : E →L[𝕜] 𝔸 :=
  mulLeftRight 𝕜 𝔸 (O x) (O x)⁻¹ʳ ∘L A x - rightMaurerCartan 𝕜 O x

/-- The **curvature** `F = dA + ½[A ∧ A]` of an `𝔸`-valued one-form `A`, as the bilinear map
`F_{vw} = ∂ᵥA_w - ∂_wA_v + [A_v, A_w]`. -/
def connectionCurvature (A : E → E →L[𝕜] 𝔸) (x : E) : E →L[𝕜] E →L[𝕜] 𝔸 :=
  fderiv 𝕜 A x - (fderiv 𝕜 A x).flip +
    ((mul 𝕜 𝔸).bilinearComp (A x) (A x) - ((mul 𝕜 𝔸).bilinearComp (A x) (A x)).flip)

/-- The **covariant derivative** `D_v B = ∂ᵥB + [A_v, B]` of an `𝔸`-valued function `B` for the
connection `A`, acting on `B` through the adjoint representation `ad(A_v) = [A_v, ·]`. -/
def connectionCovariantDeriv (A : E → E →L[𝕜] 𝔸) (B : E → 𝔸) (x : E) : E →L[𝕜] 𝔸 :=
  fderiv 𝕜 B x + ((mul 𝕜 𝔸).flip (B x) - mul 𝕜 𝔸 (B x)) ∘L A x

variable {𝕜}

@[simp]
theorem rightMaurerCartan_apply (O : E → 𝔸) (x v : E) :
    rightMaurerCartan 𝕜 O x v = fderiv 𝕜 O x v * (O x)⁻¹ʳ :=
  (rfl)

@[simp]
theorem gaugeAction_apply (O : E → 𝔸) (A : E → E →L[𝕜] 𝔸) (x v : E) :
    gaugeAction 𝕜 O A x v = O x * A x v * (O x)⁻¹ʳ - rightMaurerCartan 𝕜 O x v :=
  (rfl)

@[simp]
theorem connectionCurvature_apply (A : E → E →L[𝕜] 𝔸) (x v w : E) :
    connectionCurvature 𝕜 A x v w = fderiv 𝕜 A x v w - fderiv 𝕜 A x w v + ⁅A x v, A x w⁆ := by
  simp [connectionCurvature, Ring.lie_def]

@[simp]
theorem connectionCovariantDeriv_apply (A : E → E →L[𝕜] 𝔸) (B : E → 𝔸) (x v : E) :
    connectionCovariantDeriv 𝕜 A B x v = fderiv 𝕜 B x v + ⁅A x v, B x⁆ := by
  simp [connectionCovariantDeriv, Ring.lie_def]

/-- The curvature is antisymmetric: `F_{wv} = -F_{vw}`. -/
theorem connectionCurvature_apply_swap (A : E → E →L[𝕜] 𝔸) (x v w : E) :
    connectionCurvature 𝕜 A x w v = -connectionCurvature 𝕜 A x v w := by
  simp only [connectionCurvature_apply, Ring.lie_def]
  abel

/-! ### Constant gauge transformations -/

/-- A constant map has vanishing Maurer–Cartan form. -/
@[simp]
theorem rightMaurerCartan_const (c : 𝔸) : rightMaurerCartan 𝕜 (fun _ : E ↦ c) = 0 := by
  ext x v
  simp

/-- A constant gauge transformation `c` acts by `Ad(c)`. -/
theorem gaugeAction_const (c : 𝔸) (A : E → E →L[𝕜] 𝔸) :
    gaugeAction 𝕜 (fun _ ↦ c) A = fun x ↦ mulLeftRight 𝕜 𝔸 c c⁻¹ʳ ∘L A x := by
  ext x v
  simp

/-- The identity gauge transformation acts trivially: `1·A = A`. -/
@[simp]
theorem gaugeAction_one (A : E → E →L[𝕜] 𝔸) : gaugeAction 𝕜 (fun _ ↦ (1 : 𝔸)) A = A := by
  ext x v
  simp

/-! ### Commutative coefficients -/

section Comm

variable {R : Type*} [NormedCommRing R] [NormedAlgebra 𝕜 R]

/-- For commutative coefficients, as for the structure group `U(1)`, the adjoint action is
trivial, so a gauge transformation acts by `A ↦ A - O;x`. -/
theorem gaugeAction_eq_sub {O : E → R} {x : E} (hOx : IsUnit (O x)) (A : E → E →L[𝕜] R) :
    gaugeAction 𝕜 O A x = A x - rightMaurerCartan 𝕜 O x := by
  ext v
  rw [gaugeAction_apply, sub_apply, mul_comm (O x), mul_assoc, Ring.mul_inverse_cancel _ hOx,
    mul_one]

/-- For commutative coefficients the curvature is the exterior derivative,
`F_{vw} = ∂ᵥA_w - ∂_wA_v`. -/
theorem connectionCurvature_apply_of_comm (A : E → E →L[𝕜] R) (x v w : E) :
    connectionCurvature 𝕜 A x v w = fderiv 𝕜 A x v w - fderiv 𝕜 A x w v := by
  simp [Ring.lie_def, mul_comm]

end Comm

/-! ### The Maurer–Cartan form of products and inverses -/

variable {O O' : E → 𝔸} {x : E}

/-- **The Maurer–Cartan form of a product**: `(OO');x = O;x + Ad(O)(O';x)`. -/
theorem rightMaurerCartan_mul (hO : DifferentiableAt 𝕜 O x) (hO' : DifferentiableAt 𝕜 O' x)
    (hO'x : IsUnit (O' x)) :
    rightMaurerCartan 𝕜 (fun y ↦ O y * O' y) x =
      rightMaurerCartan 𝕜 O x + mulLeftRight 𝕜 𝔸 (O x) (O x)⁻¹ʳ ∘L rightMaurerCartan 𝕜 O' x := by
  ext v
  simp [fderiv_fun_mul' hO hO', Ring.inverse_mul (.inr hO'x), add_mul, mul_assoc,
    Ring.mul_inverse_cancel_left _ _ hO'x]
  abel

/-- **The gauge action is a left action**: `O·(O'·A) = (OO')·A`. Only the first derivatives of
`O` and `O'` at `x` enter; the one-form `A` is not differentiated. -/
theorem gaugeAction_gaugeAction (hO : DifferentiableAt 𝕜 O x) (hO' : DifferentiableAt 𝕜 O' x)
    (hO'x : IsUnit (O' x)) (A : E → E →L[𝕜] 𝔸) :
    gaugeAction 𝕜 O (gaugeAction 𝕜 O' A) x = gaugeAction 𝕜 (fun y ↦ O y * O' y) A x := by
  ext v
  rw [gaugeAction_apply, gaugeAction_apply, gaugeAction_apply,
    rightMaurerCartan_mul hO hO' hO'x, Ring.inverse_mul (.inr hO'x)]
  simp only [add_apply, comp_apply, mulLeftRight_apply, mul_sub, sub_mul, mul_assoc]
  abel

variable [HasSummableGeomSeries 𝔸]

/-- **The Maurer–Cartan form of the inverse**: `(O⁻¹);x = -Ad(O⁻¹)(O;x)`. -/
theorem rightMaurerCartan_ringInverse (hO : DifferentiableAt 𝕜 O x) (hOx : IsUnit (O x)) :
    rightMaurerCartan 𝕜 (fun y ↦ (O y)⁻¹ʳ) x =
      -(mulLeftRight 𝕜 𝔸 (O x)⁻¹ʳ (O x) ∘L rightMaurerCartan 𝕜 O x) := by
  ext v
  have h := (hO.hasFDerivAt.ringInverse hOx).fderiv
  rw [rightMaurerCartan_apply, h, Ring.inverse_inverse hOx]
  simp [mul_assoc, Ring.inverse_mul_cancel _ hOx]

/-- **The Leibniz rule for the adjoint action**: `∂ᵥ(Ad(O)B) = Ad(O)∂ᵥB + [O;v, Ad(O)B]`. The
second term is `[O;v, Ad(O)B]`, not `Ad(O)[O;v, B]` as in Oh–Tataru (2019), Lemma 3.4(3). -/
theorem fderiv_mul_mul_ringInverse_apply {B : E → 𝔸} (hO : DifferentiableAt 𝕜 O x)
    (hOx : IsUnit (O x)) (hB : DifferentiableAt 𝕜 B x) (v : E) :
    fderiv 𝕜 (fun y ↦ O y * B y * (O y)⁻¹ʳ) x v =
      O x * fderiv 𝕜 B x v * (O x)⁻¹ʳ + ⁅rightMaurerCartan 𝕜 O x v, O x * B x * (O x)⁻¹ʳ⁆ := by
  have h := ((hO.hasFDerivAt.fun_mul' hB.hasFDerivAt).fun_mul'
    (hO.hasFDerivAt.ringInverse hOx)).fderiv
  rw [h]
  simp [Ring.lie_def, mul_assoc, Ring.inverse_mul_cancel_left _ _ hOx]
  abel

/-- **Covariance of the covariant derivative**: `D(O·A)(Ad(O)B) = Ad(O)(D(A)B)`. -/
theorem connectionCovariantDeriv_gaugeAction {B : E → 𝔸} (hO : DifferentiableAt 𝕜 O x)
    (hOx : IsUnit (O x)) (hB : DifferentiableAt 𝕜 B x) (A : E → E →L[𝕜] 𝔸) :
    connectionCovariantDeriv 𝕜 (gaugeAction 𝕜 O A) (fun y ↦ O y * B y * (O y)⁻¹ʳ) x =
      mulLeftRight 𝕜 𝔸 (O x) (O x)⁻¹ʳ ∘L connectionCovariantDeriv 𝕜 A B x := by
  ext v
  rw [connectionCovariantDeriv_apply, fderiv_mul_mul_ringInverse_apply hO hOx hB]
  simp [Ring.lie_def, mul_sub, sub_mul, mul_add, add_mul, mul_assoc,
    Ring.inverse_mul_cancel_left _ _ hOx]
  abel

/-- The gauge transform of a differentiable one-form by a map with differentiable derivative and
invertible value at `x` is differentiable at `x`. -/
theorem differentiableAt_gaugeAction {A : E → E →L[𝕜] 𝔸} (hO : DifferentiableAt 𝕜 O x)
    (hdO : DifferentiableAt 𝕜 (fderiv 𝕜 O) x) (hOx : IsUnit (O x))
    (hA : DifferentiableAt 𝕜 A x) : DifferentiableAt 𝕜 (gaugeAction 𝕜 O A) x := by
  unfold gaugeAction rightMaurerCartan
  fun_prop (disch := assumption)

/-- **Curvature transforms by the adjoint action**: `F[O·A] = Ad(O) F[A]`, for a gauge
transformation `O` that is twice continuously differentiable at `x`. -/
theorem connectionCurvature_gaugeAction {n : ℕ∞ω} {A : E → E →L[𝕜] 𝔸} (hO : ContDiffAt 𝕜 n O x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hOx : IsUnit (O x)) (hA : DifferentiableAt 𝕜 A x) (v w : E) :
    connectionCurvature 𝕜 (gaugeAction 𝕜 O A) x v w =
      O x * connectionCurvature 𝕜 A x v w * (O x)⁻¹ʳ := by
  have hn2 : (2 : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  have hO1 : DifferentiableAt 𝕜 O x := hO.differentiableAt (zero_lt_two.trans_le hn2).ne'
  have hG := differentiableAt_gaugeAction hO1 (hO.hasFDerivAt_fderiv hn2).differentiableAt hOx hA
  have hfun (u : E) : (fun y ↦ gaugeAction 𝕜 O A y u) =
      fun y ↦ O y * A y u * (O y)⁻¹ʳ - fderiv 𝕜 O y u * (O y)⁻¹ʳ := by
    funext y
    simp
  have hP := hO1.hasFDerivAt.ringInverse hOx
  have hderiv (u : E) :=
    (((hO1.hasFDerivAt.fun_mul' (hA.hasFDerivAt.clm_apply (hasFDerivAt_const u x))).fun_mul'
      hP).fun_sub ((hO.hasFDerivAt_fderiv_apply hn2 u).fun_mul' hP)).fderiv
  rw [connectionCurvature_apply, ← fderiv_clm_apply_const_apply hG w v,
    ← fderiv_clm_apply_const_apply hG v w, hfun, hfun, hderiv, hderiv]
  -- The second derivatives of `O` cancel by symmetry; the remaining terms cancel after `O⁻¹ O = 1`.
  simp [hO.isSymmSndFDerivAt hn w v, Ring.lie_def, mul_sub, sub_mul, mul_add, add_mul, mul_assoc,
    Ring.inverse_mul_cancel_left _ _ hOx]
  abel

/-! ### The Ricci and Bianchi identities -/

omit [HasSummableGeomSeries 𝔸]

/-- **The Ricci identity**: covariant derivatives commute up to curvature,
`D_v(D_w B) - D_w(D_v B) = [F_{vw}, B]`, for `B` twice continuously differentiable at `x`. -/
theorem connectionCovariantDeriv_sub_connectionCovariantDeriv_swap {n : ℕ∞ω} {A : E → E →L[𝕜] 𝔸}
    {B : E → 𝔸} (hB : ContDiffAt 𝕜 n B x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hA : DifferentiableAt 𝕜 A x) (v w : E) :
    connectionCovariantDeriv 𝕜 A (fun y ↦ connectionCovariantDeriv 𝕜 A B y w) x v -
        connectionCovariantDeriv 𝕜 A (fun y ↦ connectionCovariantDeriv 𝕜 A B y v) x w =
      ⁅connectionCurvature 𝕜 A x v w, B x⁆ := by
  have hn2 : (2 : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  have hB1 : HasFDerivAt B (fderiv 𝕜 B x) x :=
    (hB.differentiableAt (zero_lt_two.trans_le hn2).ne').hasFDerivAt
  have hAu (u : E) := hA.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have hderiv (u : E) := ((hB.hasFDerivAt_fderiv_apply hn2 u).fun_add
    (((hAu u).fun_mul' hB1).fun_sub (hB1.fun_mul' (hAu u)))).fderiv
  simp only [connectionCovariantDeriv_apply, connectionCurvature_apply, Ring.lie_def]
  rw [hderiv, hderiv]
  -- The second derivatives of `B` cancel by symmetry; the rest is the Jacobi identity.
  simp [hB.isSymmSndFDerivAt hn w v, mul_sub, sub_mul, mul_add, add_mul, mul_assoc]
  abel

/-- **The Bianchi identity** `D_uF_{vw} + D_vF_{wu} + D_wF_{uv} = 0`, for a one-form `A` that is
twice continuously differentiable at `x`. -/
theorem connectionCurvature_bianchi {n : ℕ∞ω} {A : E → E →L[𝕜] 𝔸} (hA : ContDiffAt 𝕜 n A x)
    (hn : minSmoothness 𝕜 2 ≤ n) (u v w : E) :
    connectionCovariantDeriv 𝕜 A (fun y ↦ connectionCurvature 𝕜 A y v w) x u +
        connectionCovariantDeriv 𝕜 A (fun y ↦ connectionCurvature 𝕜 A y w u) x v +
        connectionCovariantDeriv 𝕜 A (fun y ↦ connectionCurvature 𝕜 A y u v) x w = 0 := by
  have hn2 : (2 : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  have hA1 : HasFDerivAt A (fderiv 𝕜 A x) x :=
    (hA.differentiableAt (zero_lt_two.trans_le hn2).ne').hasFDerivAt
  have hAa (a : E) := hA1.clm_apply (hasFDerivAt_const a x)
  have hdA (a b : E) :=
    ((hA.hasFDerivAt_fderiv hn2).clm_apply (hasFDerivAt_const a x)).clm_apply
      (hasFDerivAt_const b x)
  have hderiv (a b : E) := (((hdA a b).fun_sub (hdA b a)).fun_add
    (((hAa a).fun_mul' (hAa b)).fun_sub ((hAa b).fun_mul' (hAa a)))).fderiv
  have hS (a b : E) : fderiv 𝕜 (fderiv 𝕜 A) x a b = fderiv 𝕜 (fderiv 𝕜 A) x b a :=
    hA.isSymmSndFDerivAt hn a b
  simp only [connectionCovariantDeriv_apply, connectionCurvature_apply, Ring.lie_def]
  rw [hderiv, hderiv, hderiv]
  -- The second derivatives of `A` cancel by symmetry; the rest is the Jacobi identity.
  simp [hS v u, hS w u, hS w v, mul_sub, sub_mul, mul_add, add_mul, mul_assoc]
  abel

end TauCeti
