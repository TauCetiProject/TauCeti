/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.L1Norm

import TauCeti.Algebra.Polynomial.Taylor

/-!
# Values of Thue's auxiliary polynomials near `α`

Let `P` and `Q` be polynomials of degree at most `δ r` with coefficient lengths at most `C₁ ^ r`,
where `r > 0`, and suppose that `Dᵏ P - α Dᵏ Q = V (X - α) ^ m` for a Hasse derivative `Dᵏ` and
some `m`. Then on the closed unit ball around `α` both `V` and `Dᵏ Q` are bounded by `C₂ ^ r`,
where `C₂ = 2 ^ δ (1 + ‖α‖) ^ (1 + δ) C₁`.

For Thue's auxiliary polynomials (`TauCeti.exists_thue_auxiliary_polynomials`), mapped from
`ℤ[X]` to `ℂ[X]` (which preserves coefficient length by `Polynomial.l1Norm_map`), one takes
`δ = (1 / 2 + ε) d`, where `d` is the degree of `α`, and `m = r - k`. In Thue's gap principle the
bound is applied at a good rational approximation `ξ₁` of `α`: there
`Dᵏ P (ξ₁) - ξ₂ Dᵏ Q (ξ₁) = V (ξ₁) (ξ₁ - α) ^ (r - k) + (α - ξ₂) Dᵏ Q (ξ₁)`. The factors
`V (ξ₁)` and `Dᵏ Q (ξ₁)` are at most `C₂ ^ r`, while `ξ₁ - α` and `α - ξ₂` are small.

If `(X - α) ^ r` divides `P - α Q`, the two bounds combine to
`‖Dᵏ P (z) - w Dᵏ Q (z)‖ ≤ C₂ ^ r (‖z - α‖ ^ (r - k) + ‖w - α‖)` for `‖z - α‖ ≤ 1` and every `w`.

The derivative bound holds over any seminormed ring whose norm preserves one. The quotient bound
also assumes commutativity, as in the motivating example `ℂ`.

## Main results

* `TauCeti.norm_eval_hasseDeriv_le_pow_of_norm_sub_le_one`: the bound for `Dᵏ Q`.
* `TauCeti.norm_eval_le_pow_of_hasseDeriv_sub_eq_mul`: the bound for `V`.
* `TauCeti.norm_eval_hasseDeriv_sub_mul_le`: the bound for `Dᵏ P (z) - w Dᵏ Q (z)`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Lemma 6.13.
-/

public section

open Polynomial

namespace TauCeti

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

/-- **Values of Hasse derivatives near `α`** (Evertse, Lemma 6.13). Let `Q` have degree at most
`δ r` and coefficient length at most `C₁ ^ r`. Then every Hasse derivative `Dᵏ Q` is bounded by
`C₂ ^ r` on the closed unit ball around `α`, where `C₂ = 2 ^ δ (1 + ‖α‖) ^ (1 + δ) C₁`. -/
theorem norm_eval_hasseDeriv_le_pow_of_norm_sub_le_one {Q : R[X]} {α z : R} {k r : ℕ}
    {δ C₁ : ℝ} (hQ : (Q.natDegree : ℝ) ≤ δ * r) (hQC : Q.l1Norm ≤ C₁ ^ r)
    (hz : ‖z - α‖ ≤ 1) :
    ‖(hasseDeriv k Q).eval z‖ ≤ (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by
  have hα : 1 ≤ 1 + ‖α‖ := le_add_of_nonneg_right (norm_nonneg α)
  have hC₁ : 0 ≤ C₁ ^ r := Q.l1Norm_nonneg.trans hQC
  -- On the ball, `max 1 ‖z‖ ≤ 1 + ‖α‖`.
  have hzα : max 1 ‖z‖ ≤ 1 + ‖α‖ :=
    max_le hα <| (norm_le_norm_add_norm_sub' z α).trans (by rw [add_comm]; gcongr)
  calc
    ‖(hasseDeriv k Q).eval z‖ ≤
        (hasseDeriv k Q).l1Norm * max 1 ‖z‖ ^ (hasseDeriv k Q).natDegree :=
      norm_eval_le_l1Norm_mul _ _
    _ ≤ (2 ^ δ) ^ r * C₁ ^ r * (1 + ‖α‖) ^ Q.natDegree :=
      mul_le_mul (l1Norm_hasseDeriv_le_pow hQ hQC)
        ((pow_le_pow_left₀ (by positivity) hzα _).trans
          (pow_le_pow_right₀ hα ((natDegree_hasseDeriv_le Q k).trans tsub_le_self)))
        (by positivity) (by positivity)
    _ ≤ (2 ^ δ) ^ r * C₁ ^ r * ((1 + ‖α‖) ^ (1 + δ)) ^ r := by
      gcongr
      exact (Real.pow_le_rpow_pow_of_le_mul hα hQ).trans <| by
        gcongr
        linarith
    _ = (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by ring

end SeminormedRing

section SeminormedCommRing

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R]

/-- **Values of Thue's quotient polynomial near `α`** (Evertse, Lemma 6.13). Let `r > 0`, let
`P` and `Q` have degree at most `δ r` and coefficient length at most `C₁ ^ r`, and suppose that
`Dᵏ P - α Dᵏ Q = V (X - α) ^ m`. Then `V` is bounded by `C₂ ^ r` on the closed unit ball around
`α`, where `C₂ = 2 ^ δ (1 + ‖α‖) ^ (1 + δ) C₁`. -/
theorem norm_eval_le_pow_of_hasseDeriv_sub_eq_mul {P Q V : R[X]} {α z : R} {k m r : ℕ}
    {δ C₁ : ℝ} (hr : 0 < r) (hP : (P.natDegree : ℝ) ≤ δ * r) (hQ : (Q.natDegree : ℝ) ≤ δ * r)
    (hPC : P.l1Norm ≤ C₁ ^ r) (hQC : Q.l1Norm ≤ C₁ ^ r)
    (hV : hasseDeriv k P - C α * hasseDeriv k Q = V * (X - C α) ^ m) (hz : ‖z - α‖ ≤ 1) :
    ‖V.eval z‖ ≤ (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by
  set W := hasseDeriv k P - C α * hasseDeriv k Q
  have hα : 1 ≤ 1 + ‖α‖ := le_add_of_nonneg_right (norm_nonneg α)
  have hC₁ : 0 ≤ C₁ ^ r := P.l1Norm_nonneg.trans hPC
  have hW : W.l1Norm ≤ (2 ^ δ) ^ r * C₁ ^ r * (1 + ‖α‖) :=
    calc
      W.l1Norm ≤ (hasseDeriv k P).l1Norm + ‖α‖ * (hasseDeriv k Q).l1Norm := by
        refine (l1Norm_sub_le _ _).trans ?_
        grw [l1Norm_mul_le, l1Norm_C]
      _ ≤ (2 ^ δ) ^ r * C₁ ^ r + ‖α‖ * ((2 ^ δ) ^ r * C₁ ^ r) := by
        grw [l1Norm_hasseDeriv_le_pow hP hPC, l1Norm_hasseDeriv_le_pow hQ hQC]
      _ = (2 ^ δ) ^ r * C₁ ^ r * (1 + ‖α‖) := by ring
  have hWdeg : (W.natDegree : ℝ) ≤ δ * r := by
    refine le_trans ?_ (max_le hP hQ)
    have := (natDegree_sub_le _ _).trans <| max_le_max
      ((natDegree_hasseDeriv_le P k).trans tsub_le_self)
      ((natDegree_C_mul_le α _).trans ((natDegree_hasseDeriv_le Q k).trans tsub_le_self))
    exact_mod_cast this
  calc
    ‖V.eval z‖ ≤ W.l1Norm * (1 + ‖α‖) ^ W.natDegree :=
      norm_eval_le_l1Norm_mul_of_mul_X_sub_C_pow_eq hV.symm hz
    _ ≤ (2 ^ δ) ^ r * C₁ ^ r * (1 + ‖α‖) * ((1 + ‖α‖) ^ δ) ^ r := by
      gcongr
      exact Real.pow_le_rpow_pow_of_le_mul hα hWdeg
    _ ≤ (2 ^ δ) ^ r * C₁ ^ r * (1 + ‖α‖) ^ r * ((1 + ‖α‖) ^ δ) ^ r := by
      gcongr
      exact le_self_pow₀ hα hr.ne'
    _ = (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by
      rw [Real.rpow_add (by linarith), Real.rpow_one, mul_pow, mul_pow, mul_pow]
      ring

/-- **Values of Thue's auxiliary polynomials at two points near `α`** (Evertse, proof of
Theorem 6.14). Let `r > 0`, let `P` and `Q` have degree at most `δ r` and coefficient length at
most `C₁ ^ r`, and suppose that `(X - α) ^ r` divides `P - α Q`. If `‖z - α‖ ≤ 1`, then for every
`k` and `w`, `‖Dᵏ P (z) - w Dᵏ Q (z)‖ ≤ C₂ ^ r (‖z - α‖ ^ (r - k) + ‖w - α‖)`, where
`C₂ = 2 ^ δ (1 + ‖α‖) ^ (1 + δ) C₁`. -/
theorem norm_eval_hasseDeriv_sub_mul_le {P Q : R[X]} {α z : R} (w : R) (k : ℕ) {r : ℕ}
    {δ C₁ : ℝ} (hr : 0 < r) (hP : (P.natDegree : ℝ) ≤ δ * r) (hQ : (Q.natDegree : ℝ) ≤ δ * r)
    (hPC : P.l1Norm ≤ C₁ ^ r) (hQC : Q.l1Norm ≤ C₁ ^ r) (hdvd : (X - C α) ^ r ∣ P - C α * Q)
    (hz : ‖z - α‖ ≤ 1) :
    ‖(hasseDeriv k P).eval z - w * (hasseDeriv k Q).eval z‖ ≤
      (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r * (‖z - α‖ ^ (r - k) + ‖w - α‖) := by
  obtain ⟨V, hV⟩ := pow_sub_dvd_hasseDeriv_of_pow_dvd k hdvd
  rw [map_sub, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, mul_comm _ V] at hV
  have hVz := norm_eval_le_pow_of_hasseDeriv_sub_eq_mul hr hP hQ hPC hQC hV hz
  have hQz := norm_eval_hasseDeriv_le_pow_of_norm_sub_le_one (k := k) hQ hQC hz
  -- Evaluating `Dᵏ P - α Dᵏ Q = V (X - α) ^ (r - k)` at `z` splits the value in two terms.
  have hsplit : (hasseDeriv k P).eval z - w * (hasseDeriv k Q).eval z =
      V.eval z * (z - α) ^ (r - k) + (α - w) * (hasseDeriv k Q).eval z := by
    have := congrArg (eval z) hV
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at this
    linear_combination this
  rw [hsplit, norm_sub_rev w α]
  calc
    _ ≤ ‖V.eval z‖ * ‖z - α‖ ^ (r - k) + ‖α - w‖ * ‖(hasseDeriv k Q).eval z‖ := by
      grw [norm_add_le, norm_mul_le, norm_mul_le, norm_pow_le]
    _ ≤ (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r * ‖z - α‖ ^ (r - k) +
          ‖α - w‖ * (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by
      grw [hVz, hQz]
    _ = _ := by ring

end SeminormedCommRing

end TauCeti
