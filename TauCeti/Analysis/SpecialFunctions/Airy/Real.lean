/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Scorer
import TauCeti.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Airy.Equation
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The Airy functions on the real line

The series `₀F₁(; b; z)` has real coefficients for real `b`, so `Ai` and `Bi` commute with
complex conjugation: `Ai(conj z) = conj Ai(z)` and `Bi(conj z) = conj Bi(z)`, and so do their
derivatives. Hence `Ai`, `Bi`, `Ai′`, `Bi′` are real on the real line, and the real restrictions
`Real.airyAi x = Re Ai(x)` and `Real.airyBi x = Re Bi(x)` recover the complex values. Since
`Gi = Bi − Hi` and `Hi` is real on the real line, so is `Gi`.

On `[0, ∞)` the series of `Bi` and `Bi′` have positive terms, so `Bi > 0` and `Bi′ > 0` there,
and `Bi(x) ≥ 3^{−5/6} x / Γ(4/3)` gives `Bi(x) → ∞` as `x → ∞`.

## Main results

* `Complex.airyAi_conj`, `Complex.airyBi_conj`, `Complex.deriv_airyAi_conj`,
  `Complex.deriv_airyBi_conj` — conjugation symmetry.
* `Real.airyAi`, `Real.airyBi` — the real restrictions, with `Real.ofReal_real_airyAi`,
  `Real.ofReal_real_airyBi` — `Ai(x)` and `Bi(x)` are the casts of their real restrictions.
* `Real.hasDerivAt_airyAi`, `Real.hasDerivAt_airyBi` — the derivatives of the real restrictions,
  and `Real.ofReal_deriv_real_airyAi`, `Real.ofReal_deriv_real_airyBi` — `Ai′(x)` and
  `Bi′(x)` are real.
* `Real.ofReal_real_scorerGi` — `Gi(x)` is the cast of its real restriction.
* `Real.airyBi_pos`, `Real.deriv_airyBi_pos` — `Bi > 0` and `Bi′ > 0` on `[0, ∞)`.
* `Real.tendsto_airyBi_atTop` — `Bi(x) → ∞` as `x → ∞`.

## References

* NIST Digital Library of Mathematical Functions, §§9.2, 9.4, <https://dlmf.nist.gov/9.2>,
  <https://dlmf.nist.gov/9.4>.

The conjugation symmetry is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Airy/Basic/Properties.lean`. The positivity
of `Bi` and `Bi′` and the limit of `Bi` are proved here from the series, rather than through the
zero locations (`DLMF/Airy/Zeros/RealAndAi.lean`, `DLMF/Airy/RealOrderProperties.lean`) and
convexity (`DLMF/Airy/Products.lean`) used in lean-DLMF.
-/

public section

noncomputable section

open Complex Filter
open scoped ComplexConjugate

namespace TauCeti

/-! ### Conjugation symmetry -/

/-- `conj (3 ^ s) = 3 ^ conj s`, the case `r = 3` of `TauCeti.ofReal_cpow_conj`. -/
private theorem conj_three_cpow (s : ℂ) : conj ((3 : ℂ) ^ s) = 3 ^ conj s := by
  simpa using (ofReal_cpow_conj (r := 3) (by norm_num) s).symm

/-- For real `b`, `z ↦ ₀F₁(; b; z³/9)` commutes with conjugation. -/
private theorem airy_hypergeometric_conj (b : ℝ) (z : ℂ) :
    regularizedHGFun 0 {(b : ℂ)} (conj z ^ 3 / 9) =
      conj (regularizedHGFun 0 {(b : ℂ)} (z ^ 3 / 9)) := by
  rw [← regularizedHGFun_zero_ofReal_singleton_conj, map_div₀, map_pow, map_ofNat]

/-- `Ai(conj z) = conj Ai(z)`. -/
theorem _root_.Complex.airyAi_conj (z : ℂ) : airyAi (conj z) = conj (airyAi z) := by
  have h1 := airy_hypergeometric_conj (2 / 3) z
  have h2 := airy_hypergeometric_conj (4 / 3) z
  push_cast at h1 h2
  simp [airyAi_def, conj_three_cpow, h1, h2, map_div₀, map_ofNat]

/-- `Bi(conj z) = conj Bi(z)`. -/
theorem _root_.Complex.airyBi_conj (z : ℂ) : airyBi (conj z) = conj (airyBi z) := by
  have h1 := airy_hypergeometric_conj (2 / 3) z
  have h2 := airy_hypergeometric_conj (4 / 3) z
  push_cast at h1 h2
  simp [airyBi_def, conj_three_cpow, h1, h2, map_div₀, map_ofNat]

/-- `Ai′(conj z) = conj Ai′(z)`. -/
theorem _root_.Complex.deriv_airyAi_conj (z : ℂ) :
    deriv airyAi (conj z) = conj (deriv airyAi z) :=
  deriv_conj_of_forall_conj airyAi_conj z

/-- `Bi′(conj z) = conj Bi′(z)`. -/
theorem _root_.Complex.deriv_airyBi_conj (z : ℂ) :
    deriv airyBi (conj z) = conj (deriv airyBi z) :=
  deriv_conj_of_forall_conj airyBi_conj z

/-! ### The real restrictions -/

/-- The real restriction of `Ai`. -/
def _root_.Real.airyAi (x : ℝ) : ℝ := (TauCeti.airyAi x).re

/-- The defining expression of the real restriction of `Ai`. -/
theorem _root_.Real.airyAi_def (x : ℝ) : Real.airyAi x = (TauCeti.airyAi x).re := (rfl)

/-- The real restriction of `Bi`. -/
def _root_.Real.airyBi (x : ℝ) : ℝ := (TauCeti.airyBi x).re

/-- The defining expression of the real restriction of `Bi`. -/
theorem _root_.Real.airyBi_def (x : ℝ) : Real.airyBi x = (TauCeti.airyBi x).re := (rfl)

/-- On the real line `Ai` is real: `Ai(x)` is the cast of `Real.airyAi x`. -/
@[simp, norm_cast]
theorem _root_.Real.ofReal_real_airyAi (x : ℝ) : ((Real.airyAi x : ℝ) : ℂ) = airyAi x :=
  ofReal_re_apply_of_forall_conj airyAi_conj x

/-- On the real line `Bi` is real: `Bi(x)` is the cast of `Real.airyBi x`. -/
@[simp, norm_cast]
theorem _root_.Real.ofReal_real_airyBi (x : ℝ) : ((Real.airyBi x : ℝ) : ℂ) = airyBi x :=
  ofReal_re_apply_of_forall_conj airyBi_conj x

/-- On the real line `Gi` is real: `Gi(x)` is the cast of `Real.scorerGi x`. -/
@[simp, norm_cast]
theorem _root_.Real.ofReal_real_scorerGi (x : ℝ) : ((Real.scorerGi x : ℝ) : ℂ) = scorerGi x := by
  rw [Real.scorerGi_def, Complex.scorerGi_def, Real.scorerHi_ofReal, ← Real.ofReal_real_airyBi,
    ← ofReal_sub, ofReal_re]

/-- The derivative of the real restriction of `Ai` is `Re Ai′(x)`. -/
theorem _root_.Real.hasDerivAt_airyAi (x : ℝ) :
    HasDerivAt Real.airyAi (deriv TauCeti.airyAi x).re x :=
  (TauCeti.differentiable_airyAi (x : ℂ)).hasDerivAt.real_of_complex

/-- The derivative of the real restriction of `Bi` is `Re Bi′(x)`. -/
theorem _root_.Real.hasDerivAt_airyBi (x : ℝ) :
    HasDerivAt Real.airyBi (deriv TauCeti.airyBi x).re x :=
  (TauCeti.differentiable_airyBi (x : ℂ)).hasDerivAt.real_of_complex

/-- The real restriction of `Ai` is differentiable. -/
@[fun_prop]
theorem _root_.Real.differentiable_airyAi : Differentiable ℝ Real.airyAi := fun x =>
  (Real.hasDerivAt_airyAi x).differentiableAt

/-- The real restriction of `Bi` is differentiable. -/
@[fun_prop]
theorem _root_.Real.differentiable_airyBi : Differentiable ℝ Real.airyBi := fun x =>
  (Real.hasDerivAt_airyBi x).differentiableAt

/-- On the real line `Ai′` is real: `Ai′(x)` is the cast of the derivative of `Real.airyAi`. -/
@[simp, norm_cast]
theorem _root_.Real.ofReal_deriv_real_airyAi (x : ℝ) :
    ((deriv Real.airyAi x : ℝ) : ℂ) = deriv airyAi x := by
  rw [(Real.hasDerivAt_airyAi x).deriv]
  exact ofReal_re_apply_of_forall_conj deriv_airyAi_conj x

/-- On the real line `Bi′` is real: `Bi′(x)` is the cast of the derivative of `Real.airyBi`. -/
@[simp, norm_cast]
theorem _root_.Real.ofReal_deriv_real_airyBi (x : ℝ) :
    ((deriv Real.airyBi x : ℝ) : ℂ) = deriv airyBi x := by
  rw [(Real.hasDerivAt_airyBi x).deriv]
  exact ofReal_re_apply_of_forall_conj deriv_airyBi_conj x

/-! ### Positivity and growth of `Bi` -/

/-- `Re (3 ^ s * w) = 3 ^ s * Re w` for real `s`. -/
private theorem re_three_cpow_mul (s : ℝ) (w : ℂ) :
    ((3 : ℂ) ^ (s : ℂ) * w).re = (3 : ℝ) ^ s * w.re := by
  rw [← ofReal_ofNat 3, ← ofReal_cpow (by norm_num), re_ofReal_mul]

/-- `Real.airyBi` through the real parts of the `₀F₁` series. -/
private theorem real_airyBi_eq (x : ℝ) :
    Real.airyBi x = (3 : ℝ) ^ (-1 / 6 : ℝ) * (regularizedHGFun 0 {((2 / 3 : ℝ) : ℂ)}
      ((x ^ 3 / 9 : ℝ) : ℂ)).re + (3 : ℝ) ^ (-5 / 6 : ℝ) * x *
      (regularizedHGFun 0 {((4 / 3 : ℝ) : ℂ)} ((x ^ 3 / 9 : ℝ) : ℂ)).re := by
  have h := re_three_cpow_mul (-1 / 6)
  have h' := re_three_cpow_mul (-5 / 6)
  push_cast at h h' ⊢
  rw [Real.airyBi, airyBi_def, add_re, h, mul_assoc, h', re_ofReal_mul, mul_assoc]

/-- The derivative of `Real.airyBi` through the real parts of the `₀F₁` series. -/
private theorem deriv_real_airyBi_eq (x : ℝ) :
    deriv Real.airyBi x = (3 : ℝ) ^ (1 / 6 : ℝ) * (regularizedHGFun 0 {((1 / 3 : ℝ) : ℂ)}
      ((x ^ 3 / 9 : ℝ) : ℂ)).re + (3 : ℝ) ^ (-1 / 6 : ℝ) * (x ^ 2 / 3) *
      (regularizedHGFun 0 {((5 / 3 : ℝ) : ℂ)} ((x ^ 3 / 9 : ℝ) : ℂ)).re := by
  have h := re_three_cpow_mul (1 / 6)
  have h' := re_three_cpow_mul (-1 / 6)
  push_cast at h h' ⊢
  have hx : (x : ℂ) ^ 2 / 3 = ((x ^ 2 / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [(Real.hasDerivAt_airyBi x).deriv, deriv_airyBi, add_re, h, mul_assoc, h', hx,
    re_ofReal_mul, mul_assoc]

/-- `Bi(x) > 0` for `x ≥ 0`. -/
theorem _root_.Real.airyBi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < Real.airyBi x := by
  rw [real_airyBi_eq]
  have h1 := regularizedHGFun_zero_singleton_ofReal_re_pos (b := 2 / 3) (y := x ^ 3 / 9)
    (by norm_num) (by positivity)
  have h2 := regularizedHGFun_zero_singleton_ofReal_re_pos (b := 4 / 3) (y := x ^ 3 / 9)
    (by norm_num) (by positivity)
  positivity

/-- `Bi′(x) > 0` for `x ≥ 0`. -/
theorem _root_.Real.deriv_airyBi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < deriv Real.airyBi x := by
  rw [deriv_real_airyBi_eq]
  have h1 := regularizedHGFun_zero_singleton_ofReal_re_pos (b := 1 / 3) (y := x ^ 3 / 9)
    (by norm_num) (by positivity)
  have h2 := regularizedHGFun_zero_singleton_ofReal_re_pos (b := 5 / 3) (y := x ^ 3 / 9)
    (by norm_num) (by positivity)
  positivity

/-- `Bi(x) → ∞` as `x → ∞`. -/
theorem _root_.Real.tendsto_airyBi_atTop : Tendsto Real.airyBi atTop atTop := by
  -- For `x ≥ 0`, dropping the first series and bounding `₀F₁(; 4/3; x³/9) ≥ 1/Γ(4/3)` gives
  -- the linear lower bound `Bi(x) ≥ 3^{−5/6} Γ(4/3)⁻¹ x`.
  have hc : 0 < (3 : ℝ) ^ (-5 / 6 : ℝ) * (Real.Gamma (4 / 3))⁻¹ := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    positivity
  refine tendsto_atTop_mono' _ ((eventually_ge_atTop 0).mono fun x hx => ?_)
    (tendsto_id.const_mul_atTop hc)
  have h1 := regularizedHGFun_zero_singleton_ofReal_re_pos (b := 2 / 3) (y := x ^ 3 / 9)
    (by norm_num) (by positivity)
  have h2 := inv_Gamma_le_regularizedHGFun_zero_singleton_ofReal_re (b := 4 / 3)
    (y := x ^ 3 / 9) (by norm_num) (by positivity)
  rw [real_airyBi_eq, id]
  have : 0 ≤ (3 : ℝ) ^ (-5 / 6 : ℝ) * x := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 this, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
    (-1 / 6 : ℝ)]

end TauCeti
