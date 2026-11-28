/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.Basic
public import TauCeti.Analysis.HeisenbergModel.Fock.PolynomialVector
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.Deriv.Matrix
import TauCeti.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.HeisenbergModel.Fock.Differentiability
import TauCeti.Analysis.HeisenbergModel.Fock.Fischer

/-!
# The derivative of the Weil representation on polynomial vectors

Let `ω_ε` be the Weil representation of `U(ε)` on the Fock space `𝓕(ε)` and `v_P` the polynomial
vector of a complex polynomial `P`. The orbit `t ↦ ω_ε(γ t) v_P` along a differentiable curve `γ`
in `U(ε)` is differentiable (`TauCeti.Fock.differentiableAt_weilRep_polyVector`); this file
computes its derivative. If `γ t = 1` and the matrix of `γ` has derivative `Y` at `t`, then the
derivative of `s ↦ ω_ε(γ s) v_P` at `t` is the polynomial vector `v_{dω(Y) P}`, where

`dω(Y) = ∑ a, ∑ b, Y a b • A_a B_b`

is the quadratic operator in the raising and lowering operators `A_a`, `B_b`
(`TauCeti.Fock.raiseOp`, `TauCeti.Fock.lowerOp`). These are the oscillator operators `R a`, `L b`
with the indices of sign `1` as the even variables (`TauCeti.Fock.raiseOp_eq_oscRaise`,
`TauCeti.Fock.lowerOp_eq_oscLower`),
so `dω(Y)` is the oscillator representation `TauCeti.oscillatorHom` of `Y`: the infinitesimal
Weil representation in the Fock model is the oscillator representation of `gl ι` on polynomials.
At a general point the representation law moves the derivative to the identity: the derivative
is `ω_ε(γ t) v_{dω(γ(t)⁻¹ Y) P}`.

Both sides are compared through their inner products with the dense family of polynomial
vectors. Differentiating the commutation rules `TauCeti.Fock.innerSL_weilRep_raiseOp` and
`TauCeti.Fock.innerSL_weilRep_lowerOp` along `γ` shows that the sesquilinear form
`B(Q, P) = ⟨v_Q, D P - v_{dω(Y) P}⟩`, with `D P` the derivative of the orbit of `v_P`, moves `X_j`
from one side to `∂_j` on the other; the commutators of `dω(Y)` with `R j` and `L j`
(`TauCeti.oscillatorHom_mul_oscRaise`, `TauCeti.oscillatorHom_mul_oscLower`) and the
skew-adjointness of `Y` for the form of `ε` supply the terms involving `Y`. At `(1, 1)` both
sides are `-tr(Y₋₋)`, the derivative of the vacuum coefficient `(ω_ε(γ s) e)(0) = det((γ s)₋₋)⁻¹`.
Such a form vanishes (`MvPolynomial.eq_zero_of_X_mul_adjoint_pderiv`), so `D P = v_{dω(Y) P}` by
density.

## Main results

* `TauCeti.Fock.raiseOp_eq_oscRaise`, `TauCeti.Fock.lowerOp_eq_oscLower`: the raising and lowering
  operators are the oscillator operators.
* `TauCeti.Fock.hasDerivAt_weilRep_polyVector_of_eq_one`: along a curve through the identity
  with velocity `Y`, the orbit of `v_P` has derivative `v_{dω(Y) P}`.
* `TauCeti.Fock.hasDerivAt_weilRep_polyVector`: the derivative at a general point.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit 72fead1, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/Lib/Weil/Fock/PolynomialVectors.lean`, declaration
`New.Fock.hasDerivAt_realWeil` (with `New.Fock.weilDeriv` from `src/Lib/Weil/Fock/Basic.lean`,
here `TauCeti.oscillatorHom`), which is the case `γ 0 = 1`; its private steps
`hasDerivAt_det_posProj_add_mul`, `star_mul_sign_eq_neg_sign_mul_of_hasDerivAt`,
`fockInner_raiseOp_eq_of_hasDerivAt` and `fockInner_lowerOp_eq_of_hasDerivAt` are followed in the
private lemmas here. The method, testing the derivative against polynomial vectors with the
differentiated commutation rules, follows the source.

## References

* M. Kashiwara, M. Vergne, *On the Segal–Shale–Weil representations and harmonic polynomials*,
  Invent. Math. 44 (1978), 1–48.
* G. B. Folland, *Harmonic analysis in phase space*, Ann. of Math. Stud. 122 (1989), Chapter 4.
-/

public noncomputable section

open Complex Finset MvPolynomial Matrix
open scoped ComplexConjugate Matrix.Norms.L2Operator

namespace TauCeti.Fock

open ReproducingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### The raising and lowering operators as oscillator operators -/

omit [Fintype ι] [DecidableEq ι] in
/-- The raising operator `A_i` of the Fock model is the oscillator operator `R i` for the
variables of sign `1` as the even ones. -/
theorem raiseOp_eq_oscRaise (i : ι) : raiseOp ε i = oscRaise ℂ (fun j ↦ ε j = 1) i := by
  refine LinearMap.ext fun P ↦ ?_
  rcases Int.units_eq_one_or (ε i) with hi | hi
  · simp [hi]
  · simp [hi, oscRaise_apply_of_neg (p := fun j ↦ ε j = 1) (by simp [hi] : ¬ε i = 1)]

omit [Fintype ι] [DecidableEq ι] in
/-- The lowering operator `B_i` of the Fock model is the oscillator operator `L i` for the
variables of sign `1` as the even ones. -/
theorem lowerOp_eq_oscLower (i : ι) : lowerOp ε i = oscLower ℂ (fun j ↦ ε j = 1) i := by
  refine LinearMap.ext fun P ↦ ?_
  rcases Int.units_eq_one_or (ε i) with hi | hi
  · simp [hi]
  · simp [hi, oscLower_apply_of_neg (p := fun j ↦ ε j = 1) (by simp [hi] : ¬ε i = 1)]

/-! ### The derivative -/

variable {γ : ℝ → unitaryGroup ε} {Y : Matrix ι ι ℂ} {t : ℝ}

/-- The velocity `Y` at the identity of a curve in `U(ε)` is skew-adjoint for the form of `ε`:
`conj (Y i j) = -(ε_i ε_j Y j i)`. -/
private theorem conj_eq_neg_sign_mul_sign_mul_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t) (i j : ι) :
    conj (Y i j) = -(((ε i : ℤ) : ℂ) * ((ε j : ℤ) : ℂ) * Y j i) := by
  -- The case `f t = 1` of `star f' * J * f t + star (f t) * J * f' = 0`, read at `(j, i)`.
  have h := hγ.star_mul_mul_add_star_mul_mul_eq_zero
    (.of_forall fun s ↦ mem_unitaryGroupOf_iff.mp (γ s).property)
  rw [h₀] at h
  have h_entry := congr($h j i)
  simp only [Units.val_one, OneMemClass.coe_one, mul_one, star_one, one_mul, Matrix.add_apply,
    signMatrix_eq_diagonal, mul_diagonal, diagonal_mul, Matrix.star_apply, Matrix.zero_apply,
    ← starRingEnd_apply] at h_entry
  linear_combination ((ε i : ℤ) : ℂ) * h_entry - conj (Y i j) * sign_mul_sign (ε := ε) i

/-- The vacuum coefficient `⟨e, ω_ε(γ s) e⟩ = det((γ s)₋₋)⁻¹` has derivative `-tr(Y₋₋)` at a
point `t` with `γ t = 1`, if the matrix of `γ` has derivative `Y` there. -/
private theorem hasDerivAt_innerSL_vacuum_weilRep_vacuum (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t) :
    HasDerivAt (fun s ↦ innerSL (vacuum : FockSpace ε) (weilRep ε (γ s) vacuum))
      (-∑ i with ¬ε i = 1, Y i i) t := by
  have h_one : negBlock ε (1 : Matrix ι ι ℂ) = 1 := by
    ext i j
    simp [Matrix.one_apply, Subtype.ext_iff]
  -- Jacobi's formula at the identity: `det((γ s)₋₋)` has derivative `tr(Y₋₋)`.
  have h_det := hasDerivAt_det_of_entries_adjugate (A := fun s ↦
      negBlock ε ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) (A' := negBlock ε Y) (t := t)
    fun i j ↦ by simpa using hasDerivAt_pi.mp (hasDerivAt_pi.mp hγ i) j
  simp only [h₀, OneMemClass.coe_one, Units.val_one, h_one, adjugate_one, one_mul] at h_det
  -- `tr(Y₋₋)` is the sum of the diagonal entries of `Y` at the indices of sign `-1`.
  have h_trace : (negBlock ε Y).trace = ∑ i with ¬ε i = 1, Y i i := by
    simp only [trace, diag_apply, negBlock_apply]
    exact (sum_subtype _ (fun i ↦ by simp [Int.units_ne_iff_eq_neg]) fun i ↦ Y i i).symm
  simpa [innerSL_vacuum, h₀, h_one, h_trace] using h_det.fun_inv (by simp [h₀, h_one])

/-- The raising rule `TauCeti.Fock.innerSL_weilRep_raiseOp` differentiated along a curve `γ`
through the identity with velocity `Y`, where `D P` is the derivative of the orbit of `v_P`:
`⟨v_Q, D(A_j P)⟩ = ∑ i, Y i j ε_i ⟨v_{B_i Q}, v_P⟩ + ε_j ⟨v_{B_j Q}, D P⟩`. -/
private theorem innerSL_raiseOp_eq_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ → FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t)
    (j : ι) (P Q : MvPolynomial ι ℂ) :
    innerSL (polyVector ε Q) (D (raiseOp ε j P)) =
      ∑ i, Y i j * ((ε i : ℤ) : ℂ) * innerSL (polyVector ε (lowerOp ε i Q)) (polyVector ε P) +
        ((ε j : ℤ) : ℂ) * innerSL (polyVector ε (lowerOp ε j Q)) (D P) := by
  have h_entry (a b : ι) : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ) a b) (Y a b) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hγ a) b
  -- The right side of the raising rule at `γ s`, differentiated by the product rule.
  have h_sum := HasDerivAt.fun_sum (u := univ) fun i _ ↦
    ((h_entry i j).mul_const ((ε i : ℤ) : ℂ)).fun_mul (hD (lowerOp ε i Q) P)
  -- The raising rule says that the two curves agree, so their derivatives do; at `γ t = 1` only
  -- the term `i = j` of the second sum remains.
  have h := (hD Q (raiseOp ε j P)).unique (h_sum.congr_of_eventuallyEq
    (.of_forall fun s ↦ innerSL_weilRep_raiseOp (γ s) P Q j))
  simpa [h₀, Matrix.one_apply, sum_add_distrib] using h

/-- The lowering rule `TauCeti.Fock.innerSL_weilRep_lowerOp` differentiated along a curve `γ`
through the identity with velocity `Y`, where `D P` is the derivative of the orbit of `v_P`:
`⟨v_Q, D(B_j P)⟩ = ε_j (∑ i, conj (Y i j) ⟨v_{A_i Q}, v_P⟩ + ⟨v_{A_j Q}, D P⟩)`. -/
private theorem innerSL_lowerOp_eq_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ → FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t)
    (j : ι) (P Q : MvPolynomial ι ℂ) :
    innerSL (polyVector ε Q) (D (lowerOp ε j P)) =
      ((ε j : ℤ) : ℂ) * (∑ i, conj (Y i j) *
          innerSL (polyVector ε (raiseOp ε i Q)) (polyVector ε P) +
        innerSL (polyVector ε (raiseOp ε j Q)) (D P)) := by
  have h_entry (a b : ι) : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ) a b) (Y a b) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hγ a) b
  -- The right side of the lowering rule at `γ s`, differentiated by the product rule; the rule
  -- is written with `conj`, the derivative of an entry with `star`.
  have h_sum := (HasDerivAt.fun_sum (u := univ) fun i _ ↦
    (h_entry i j).star.fun_mul (hD (raiseOp ε i Q) P)).const_mul ((ε j : ℤ) : ℂ)
  -- The lowering rule says that the two curves agree, so their derivatives do; at `γ t = 1` only
  -- the term `i = j` of the second sum remains.
  have h := (hD Q (lowerOp ε j P)).unique (h_sum.congr_of_eventuallyEq
    (.of_forall fun s ↦ by simp only [innerSL_weilRep_lowerOp, starRingEnd_apply]))
  simpa [h₀, Matrix.one_apply, sum_add_distrib, ← starRingEnd_apply] using h

/-- The raising operator `A_j` moves across the form `⟨v_Q, D P - v_{dω(Y) P}⟩` as `ε_j B_j`,
where `D P` is the derivative of the orbit of `v_P` along a curve through the identity with
velocity `Y`. -/
private theorem innerSL_sub_raiseOp_eq_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ → FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t)
    (j : ι) (P Q : MvPolynomial ι ℂ) :
    innerSL (polyVector ε Q) (D (raiseOp ε j P)) -
        innerSL (polyVector ε Q)
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y (raiseOp ε j P))) =
      ((ε j : ℤ) : ℂ) * (innerSL (polyVector ε (lowerOp ε j Q)) (D P) -
        innerSL (polyVector ε (lowerOp ε j Q))
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P))) := by
  -- The commutator of `dω(Y)` with `A_j`, read through `A_a = R a` and `B_b = L b`.
  have h_comm : oscillatorHom ℂ (fun i ↦ ε i = 1) Y (raiseOp ε j P) =
      raiseOp ε j (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P) + ∑ a, Y a j • raiseOp ε a P := by
    have h := congr($(oscillatorHom_mul_oscRaise (K := ℂ) (p := fun i ↦ ε i = 1) Y j) P)
    simpa only [raiseOp_eq_oscRaise, mul_apply_eq_comp, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply] using h
  -- The terms with `Y` from the differentiated rule and from the commutator of `dω(Y)` cancel.
  simp only [innerSL_raiseOp_eq_of_hasDerivAt h₀ hγ hD, h_comm, map_add, map_sum,
    map_smul, smul_eq_mul, innerSL_polyVector_raiseOp, mul_sub, mul_assoc]
  ring

/-- The lowering operator `B_j` moves across the form `⟨v_Q, D P - v_{dω(Y) P}⟩` as `ε_j A_j`,
where `D P` is the derivative of the orbit of `v_P` along a curve through the identity with
velocity `Y`. -/
private theorem innerSL_sub_lowerOp_eq_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ → FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t)
    (j : ι) (P Q : MvPolynomial ι ℂ) :
    innerSL (polyVector ε Q) (D (lowerOp ε j P)) -
        innerSL (polyVector ε Q)
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y (lowerOp ε j P))) =
      ((ε j : ℤ) : ℂ) * (innerSL (polyVector ε (raiseOp ε j Q)) (D P) -
        innerSL (polyVector ε (raiseOp ε j Q))
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P))) := by
  -- By skew-adjointness, the terms with `conj Y` from the differentiated rule are those with `Y`
  -- from the commutator of `dω(Y)`, and they cancel.
  have h_cancel : ∑ i, conj (Y i j) * innerSL (polyVector ε (raiseOp ε i Q)) (polyVector ε P) =
      -(((ε j : ℤ) : ℂ) * ∑ b, Y j b * (((ε b : ℤ) : ℂ) *
        innerSL (polyVector ε (raiseOp ε b Q)) (polyVector ε P))) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [conj_eq_neg_sign_mul_sign_mul_of_hasDerivAt h₀ hγ]
    ring
  -- The commutator of `dω(Y)` with `B_j`, read through `A_a = R a` and `B_b = L b`.
  have h_comm : oscillatorHom ℂ (fun i ↦ ε i = 1) Y (lowerOp ε j P) =
      lowerOp ε j (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P) - ∑ b, Y j b • lowerOp ε b P := by
    have h := congr($(oscillatorHom_mul_oscLower (K := ℂ) (p := fun i ↦ ε i = 1) Y j) P)
    simpa only [lowerOp_eq_oscLower, mul_apply_eq_comp, LinearMap.sub_apply,
      LinearMap.sum_apply, LinearMap.smul_apply] using h
  simp only [innerSL_lowerOp_eq_of_hasDerivAt h₀ hγ hD, h_comm, map_sub, map_sum,
    map_smul, smul_eq_mul, innerSL_polyVector_lowerOp, h_cancel, mul_sub, mul_add, mul_sum,
    mul_neg, ← mul_assoc, sign_mul_sign, one_mul]
  ring

/-- Multiplication by `X j` on the left of the form `⟨v_Q, D P - v_{dω(Y) P}⟩` is `∂_j` on the
right, where `D P` is the derivative of the orbit of `v_P` along a curve through the identity with
velocity `Y`: it is the move of `B_j` if `ε j = 1` and of `A_j` if `ε j = -1`. -/
private theorem innerSL_sub_X_mul_left_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ →ₗ[ℂ] FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t)
    (j : ι) (Q P : MvPolynomial ι ℂ) :
    innerSL (polyVector ε (X j * Q)) (D P) -
        innerSL (polyVector ε (X j * Q)) (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P)) =
      innerSL (polyVector ε Q) (D (pderiv j P)) -
        innerSL (polyVector ε Q)
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y (pderiv j P))) := by
  rcases Int.units_eq_one_or (ε j) with hj | hj
  · simpa [hj] using (innerSL_sub_lowerOp_eq_of_hasDerivAt h₀ hγ hD j P Q).symm
  · have h := innerSL_sub_raiseOp_eq_of_hasDerivAt h₀ hγ hD j P Q
    simp only [hj, raiseOp_apply_of_eq_neg_one, lowerOp_apply_of_eq_neg_one, map_neg,
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h
    linear_combination h

/-- Multiplication by `X j` on the right of the form `⟨v_Q, D P - v_{dω(Y) P}⟩` is `∂_j` on the
left, where `D P` is the derivative of the orbit of `v_P` along a curve through the identity with
velocity `Y`: it is the move of `A_j` if `ε j = 1` and of `B_j` if `ε j = -1`. -/
private theorem innerSL_sub_X_mul_right_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ →ₗ[ℂ] FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t)
    (j : ι) (Q P : MvPolynomial ι ℂ) :
    innerSL (polyVector ε Q) (D (X j * P)) -
        innerSL (polyVector ε Q)
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y (X j * P))) =
      innerSL (polyVector ε (pderiv j Q)) (D P) -
        innerSL (polyVector ε (pderiv j Q))
          (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P)) := by
  rcases Int.units_eq_one_or (ε j) with hj | hj
  · simpa [hj] using innerSL_sub_raiseOp_eq_of_hasDerivAt h₀ hγ hD j P Q
  · have h := innerSL_sub_lowerOp_eq_of_hasDerivAt h₀ hγ hD j P Q
    simp only [hj, raiseOp_apply_of_eq_neg_one, lowerOp_apply_of_eq_neg_one, map_neg,
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, _root_.neg_apply] at h
    linear_combination h

/-- At the vacuum both sides of the derivative formula pair to `-tr(Y₋₋)` with the vacuum:
`⟨e, D 1⟩ = ⟨e, v_{dω(Y) 1}⟩`, where `D P` is the derivative of the orbit of `v_P` along a curve
through the identity with velocity `Y`. -/
private theorem innerSL_one_eq_of_hasDerivAt (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t)
    {D : MvPolynomial ι ℂ → FockSpace ε}
    (hD : ∀ Q P, HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t) :
    innerSL (polyVector ε 1) (D 1) =
      innerSL (polyVector ε 1) (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y 1)) := by
  have h_zero : holomorphicCoord ε 0 = 0 := by
    ext i
    simp [holomorphicCoord_apply]
  rw [(hD 1 1).unique (by simpa using hasDerivAt_innerSL_vacuum_weilRep_vacuum h₀ hγ),
    polyVector_one, innerSL_vacuum, polyVector_apply, h_zero, eval_zero_oscillatorHom_one]
  simp [gaussian_apply]

/-- **The derivative of the Weil representation on polynomial vectors.** If `γ` is a curve in
`U(ε)` with `γ t = 1` whose matrix has derivative `Y` at `t`, then `s ↦ ω_ε(γ s) v_P` has
derivative `v_{dω(Y) P}` at `t` in the Fock space, where `dω(Y) = ∑ a, ∑ b, Y a b • A_a B_b` is
the oscillator representation `TauCeti.oscillatorHom` of `Y` with the indices of sign `1` as the
even variables. -/
theorem hasDerivAt_weilRep_polyVector_of_eq_one (h₀ : γ t = 1)
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun s ↦ weilRep ε (γ s) (polyVector ε P))
      (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P)) t := by
  have h_diff (P : MvPolynomial ι ℂ) :
      DifferentiableAt ℝ (fun s ↦ weilRep ε (γ s) (polyVector ε P)) t :=
    differentiableAt_weilRep_polyVector hγ.differentiableAt P
  -- `D P` is the derivative of the orbit of `v_P`; it is linear in `P`.
  let D : MvPolynomial ι ℂ →ₗ[ℂ] FockSpace ε :=
    { toFun P := deriv (fun s ↦ weilRep ε (γ s) (polyVector ε P)) t
      map_add' P Q := by simpa only [map_add] using deriv_fun_add (h_diff P) (h_diff Q)
      map_smul' c P := by
        simpa only [map_smul, RingHom.id_apply] using deriv_fun_const_smul c (h_diff P) }
  -- (`rfl`: `D` is the bundled map whose underlying function was just written down.)
  have hD_apply (P : MvPolynomial ι ℂ) :
      D P = deriv (fun s ↦ weilRep ε (γ s) (polyVector ε P)) t := (rfl)
  have hD (Q P : MvPolynomial ι ℂ) : HasDerivAt
      (fun s ↦ innerSL (polyVector ε Q) (weilRep ε (γ s) (polyVector ε P)))
      (innerSL (polyVector ε Q) (D P)) t := by
    rw [hD_apply]
    exact ((innerSL (polyVector ε Q)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (h_diff P).hasDerivAt
  -- The form `B Q P = ⟨v_Q, D P - v_{dω(Y) P}⟩`, conjugate-linear in `Q` and linear in `P`.
  let B : MvPolynomial ι ℂ →ₗ⋆[ℂ] MvPolynomial ι ℂ →ₗ[ℂ] ℂ :=
    (ContinuousLinearMap.toLinearMap₁₂ innerSL ∘ₛₗ polyVector ε).compl₂
      (D - polyVector ε ∘ₗ oscillatorHom ℂ (fun i ↦ ε i = 1) Y)
  have hB (Q P : MvPolynomial ι ℂ) :
      B Q P = innerSL (polyVector ε Q) (D P) -
        innerSL (polyVector ε Q) (polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P)) := by
    simp [B]
  -- `B` vanishes at `(1, 1)` and moves `X j` on one side to `∂_j` on the other, so `B = 0`.
  have hB_zero := eq_zero_of_X_mul_adjoint_pderiv
    (by rw [hB, innerSL_one_eq_of_hasDerivAt h₀ hγ hD, sub_self])
    (fun j Q P ↦ by simpa only [hB] using innerSL_sub_X_mul_left_of_hasDerivAt h₀ hγ hD j Q P)
    (fun j Q P ↦ by simpa only [hB] using innerSL_sub_X_mul_right_of_hasDerivAt h₀ hγ hD j Q P)
  -- So `D P - v_{dω(Y) P}` is orthogonal to the polynomial vectors, hence zero.
  have h_eq : D P = polyVector ε (oscillatorHom ℂ (fun i ↦ ε i = 1) Y P) :=
    sub_eq_zero.1 <| eq_zero_of_forall_innerSL_polyVector_eq_zero fun Q ↦ by
      simpa [hB, map_sub] using congr($hB_zero Q P)
  exact (h_diff P).hasDerivAt.congr_deriv ((hD_apply P).symm.trans h_eq)

/-- **The derivative of the Weil representation on polynomial vectors**, at a general point. If
the matrix of a curve `γ` in `U(ε)` has derivative `Y` at `t`, then `s ↦ ω_ε(γ s) v_P` has
derivative `ω_ε(γ t) v_{dω(γ(t)⁻¹ Y) P}` at `t`. -/
theorem hasDerivAt_weilRep_polyVector
    (hγ : HasDerivAt (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) Y t) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun s ↦ weilRep ε (γ s) (polyVector ε P))
      (weilRep ε (γ t) (polyVector ε
        (oscillatorHom ℂ (fun i ↦ ε i = 1)
          ((((γ t)⁻¹ : unitaryGroup ε) : GL ι ℂ) * Y : Matrix ι ι ℂ) P))) t := by
  -- Move the general point `γ t` to the identity using the representation law.
  let η (s : ℝ) := (γ t)⁻¹ * γ s
  have hη : HasDerivAt (fun s ↦ ((η s : GL ι ℂ) : Matrix ι ι ℂ))
      ((((γ t)⁻¹ : unitaryGroup ε) : GL ι ℂ) * Y : Matrix ι ι ℂ) t := by
    simpa [η] using hγ.const_mul ((((γ t)⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)
  have hd := hasDerivAt_weilRep_polyVector_of_eq_one (γ := η) (by simp [η]) hη P
  have h := ((weilRep ε (γ t)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have h_move (s : ℝ) : weilRep ε (γ s) (polyVector ε P) =
      weilRep ε (γ t) (weilRep ε (η s) (polyVector ε P)) := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  rw [funext h_move]
  exact h

end TauCeti.Fock
