/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Analysis.SpecialFunctions.Airy.Equation
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedDeriv.SymmetricSquare

/-!
# The product equation of Airy's equation

If `f` and `g` are entire solutions of Airy's equation `w'' = z w`, then their product
`w = f g` solves the third-order linear equation

$$w''' - 4 z w' - 2 w = 0$$

(DLMF 9.11.1). Differentiating this equation `n` times gives
`w^{(n+3)}(z) = 4 z w^{(n+1)}(z) + (4 n + 2) w^{(n)}(z)`, so at the origin the derivatives of
an entire solution satisfy `w^{(n+3)}(0) = (4 n + 2) w^{(n)}(0)`. An entire solution is
therefore determined by `w(0)`, `w'(0)` and `w''(0)`: its Taylor series at the origin is fixed
by them.

The Wronskian of `f²`, `f g` and `g²`, the determinant of the matrix of their values and first
two derivatives, is `2 𝒲³`, where `𝒲 = f g' - f' g`
(`TauCeti.det_iteratedDeriv_sq_mul_sq`). For `Ai` and `Bi`, with `𝒲 = 1/π`, it is `2/π³`
(DLMF 9.11.2). When `𝒲 ≠ 0` this matrix is invertible at the origin, so a combination of `f²`,
`f g` and `g²` matches any prescribed `w(0)`, `w'(0)` and `w''(0)`. With the uniqueness above
and the linear independence of `f²`, `f g`, `g²` (`TauCeti.linearIndependent_sq_mul_sq`), these
three functions form a basis of the entire solutions of the product equation.

## Main results

* `TauCeti.productEquation_mul_of_airy_ode`: the product of two entire solutions of Airy's
  equation solves `w''' - 4 z w' - 2 w = 0` (DLMF 9.11.1).
* `TauCeti.iteratedDeriv_add_three_of_productEquation`: the differentiated equation
  `w^{(n+3)}(z) = 4 z w^{(n+1)}(z) + (4 n + 2) w^{(n)}(z)`.
* `TauCeti.eq_of_productEquation`: two entire solutions with the same `w(0)`, `w'(0)` and
  `w''(0)` are equal.
* `TauCeti.wronskian_airyAi_sq_airyAi_mul_airyBi_airyBi_sq`: the Wronskian of `Ai²`, `Ai Bi`
  and `Bi²` is `2/π³` (DLMF 9.11.2).
* `TauCeti.exists_eq_sq_mul_sq_of_productEquation`: for entire solutions `f`, `g` of Airy's
  equation with `𝒲 ≠ 0`, every entire solution of the product equation is a combination of
  `f²`, `f g` and `g²`.
* `TauCeti.linearIndependent_airyAi_sq_airyAi_mul_airyBi_airyBi_sq`,
  `TauCeti.exists_eq_airyAi_sq_airyAi_mul_airyBi_airyBi_sq_of_productEquation`: `Ai²`, `Ai Bi`
  and `Bi²` form a basis of the entire solutions of the product equation.

## References

* NIST Digital Library of Mathematical Functions, §9.11(i), <https://dlmf.nist.gov/9.11.i>.

The proof of DLMF 9.11.1 is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMFMathlib/Analysis/ODE/SymmetricSquare.lean`
and `DLMF/Airy/Products.lean`, and that of DLMF 9.11.2 from `airy_product_wronskian` in
`DLMF/Airy/Products.lean`; the uniqueness and basis proofs are new.
-/

public section

open scoped Real

namespace TauCeti

/-- If `f` and `g` are entire solutions of Airy's equation `w'' = z w`, then their product
`w = f g` satisfies `w''' - 4 z w' - 2 w = 0` (DLMF 9.11.1). -/
theorem productEquation_mul_of_airy_ode {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfe : ∀ z, deriv^[2] f z = z * f z)
    (hge : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    deriv^[3] (fun t => f t * g t) z - 4 * z * deriv (fun t => f t * g t) z -
      2 * (f z * g z) = 0 := by
  have hf' := hasDerivAt_deriv_of_airy_ode hf hfe
  have hg' := hasDerivAt_deriv_of_airy_ode hg hge
  have hd1 : deriv (fun t => f t * g t) = fun t => deriv f t * g t + f t * deriv g t :=
    funext fun t => ((hf t).hasDerivAt.mul (hg t).hasDerivAt).deriv
  have hd2 : deriv (deriv fun t => f t * g t) =
      fun t => 2 * t * (f t * g t) + 2 * (deriv f t * deriv g t) := by
    rw [hd1]
    funext t
    exact (((hf' t).mul (hg t).hasDerivAt).add ((hf t).hasDerivAt.mul (hg' t))).deriv.trans
      (by ring)
  have hd3 : deriv (fun t => 2 * t * (f t * g t) + 2 * (deriv f t * deriv g t)) z =
      2 * (f z * g z) + 4 * z * (deriv f z * g z + f z * deriv g z) :=
    ((((hasDerivAt_id' z).const_mul 2).mul ((hf z).hasDerivAt.mul (hg z).hasDerivAt)).add
      (((hf' z).mul (hg' z)).const_mul 2)).deriv.trans (by rw [Pi.mul_apply]; ring)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, hd2, hd1,
    hd3]
  ring

/-- Differentiating `w''' - 4 z w' - 2 w = 0` `n` times: for an entire solution `w`,
`w^{(n+3)}(z) = 4 z w^{(n+1)}(z) + (4 n + 2) w^{(n)}(z)`. -/
theorem iteratedDeriv_add_three_of_productEquation {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hwe : ∀ z, deriv^[3] w z - 4 * z * deriv w z - 2 * w z = 0) (n : ℕ) (z : ℂ) :
    iteratedDeriv (n + 3) w z =
      4 * z * iteratedDeriv (n + 1) w z + (4 * n + 2) * iteratedDeriv n w z := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, iteratedDeriv_eq_iterate, Function.iterate_one,
      Function.iterate_zero_apply, Nat.cast_zero]
    linear_combination hwe z
  | succ n ih =>
    have hd (k : ℕ) (t : ℂ) : HasDerivAt (iteratedDeriv k w) (iteratedDeriv (k + 1) w t) t := by
      rw [iteratedDeriv_succ]
      exact ((hw.contDiff.differentiable_iteratedDeriv' k) t).hasDerivAt
    rw [Nat.add_right_comm n 1 3, iteratedDeriv_succ, funext ih]
    refine ((((hasDerivAt_id z).const_mul 4).mul (hd (n + 1) z)).add
      ((hd n z).const_mul (4 * (n : ℂ) + 2))).deriv.trans ?_
    simp only [id, Nat.cast_add, Nat.cast_one]
    ring

/-- An entire solution of `w''' - 4 z w' - 2 w = 0` is determined by `w(0)`, `w'(0)` and
`w''(0)` (DLMF §9.11(i)). -/
theorem eq_of_productEquation {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfe : ∀ z, deriv^[3] f z - 4 * z * deriv f z - 2 * f z = 0)
    (hge : ∀ z, deriv^[3] g z - 4 * z * deriv g z - 2 * g z = 0)
    (h₀ : f 0 = g 0) (h₁ : deriv f 0 = deriv g 0) (h₂ : deriv^[2] f 0 = deriv^[2] g 0) :
    f = g := by
  have hsub (n : ℕ) (z : ℂ) : deriv^[n] (f - g) z = deriv^[n] f z - deriv^[n] g z := by
    simp only [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt
  have hw := hf.sub hg
  have hwe (z : ℂ) : deriv^[3] (f - g) z - 4 * z * deriv (f - g) z - 2 * (f - g) z = 0 := by
    rw [hsub, ← Function.iterate_one deriv, hsub, Function.iterate_one, Pi.sub_apply]
    linear_combination hfe z - hge z
  have h0 (n : ℕ) : iteratedDeriv n (f - g) 0 = 0 := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp [h₀]
      | 1, _ => rw [iteratedDeriv_eq_iterate, hsub, Function.iterate_one, h₁, sub_self]
      | 2, _ => rw [iteratedDeriv_eq_iterate, hsub, h₂, sub_self]
      | n + 3, ih =>
        rw [iteratedDeriv_add_three_of_productEquation hw hwe, ih n (by omega)]
        ring
  funext z
  rw [← sub_eq_zero, ← Pi.sub_apply, ← Complex.taylorSeries_eq_of_entire' 0 z hw]
  simp [h0]

/-- **The Wronskian** of `Ai²`, `Ai Bi` and `Bi²`, the determinant of the matrix of their values
and first two derivatives, is `2/π³` (DLMF 9.11.2). -/
theorem wronskian_airyAi_sq_airyAi_mul_airyBi_airyBi_sq (z : ℂ) :
    (Matrix.of fun i j : Fin 3 => iteratedDeriv i
      (![fun t => airyAi t ^ 2, fun t => airyAi t * airyBi t, fun t => airyBi t ^ 2] j) z).det =
      2 / π ^ 3 := by
  rw [det_iteratedDeriv_sq_mul_sq differentiable_airyAi.contDiff.contDiffAt
    differentiable_airyBi.contDiff.contDiffAt, wronskian_airyAi_airyBi]
  ring

/-- If `f` and `g` are entire solutions of Airy's equation with nonzero Wronskian
`f g' - f' g`, then every entire solution of `w''' - 4 z w' - 2 w = 0` is a linear combination of
`f²`, `f g` and `g²`. -/
theorem exists_eq_sq_mul_sq_of_productEquation {f g w : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfe : ∀ z, deriv^[2] f z = z * f z)
    (hge : ∀ z, deriv^[2] g z = z * g z) (hW : f 0 * deriv g 0 - deriv f 0 * g 0 ≠ 0)
    (hw : Differentiable ℂ w) (hwe : ∀ z, deriv^[3] w z - 4 * z * deriv w z - 2 * w z = 0) :
    ∃ a b c : ℂ, w = fun z => a * f z ^ 2 + b * (f z * g z) + c * g z ^ 2 := by
  set u : Fin 3 → ℂ → ℂ := ![fun t => f t ^ 2, fun t => f t * g t, fun t => g t ^ 2] with hu_def
  have hu (j : Fin 3) (_ : j ∈ Finset.univ) : Differentiable ℂ (u j) := by
    fin_cases j <;>
      simp only [hu_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop
  have hsol (j : Fin 3) (z : ℂ) : deriv^[3] (u j) z - 4 * z * deriv (u j) z - 2 * u j z = 0 := by
    fin_cases j <;>
      simp only [hu_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, sq]
    · exact productEquation_mul_of_airy_ode hf hf hfe hfe z
    · exact productEquation_mul_of_airy_ode hf hg hfe hge z
    · exact productEquation_mul_of_airy_ode hg hg hge hge z
  have hM : (Matrix.of fun i j : Fin 3 => iteratedDeriv i (u j) 0).det ≠ 0 := by
    rw [det_iteratedDeriv_sq_mul_sq hf.contDiff.contDiffAt hg.contDiff.contDiffAt]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 3 hW)
  -- The coefficients solve the linear system given by the nonsingular Wronskian matrix at `0`.
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hM.isUnit) ![w 0, deriv w 0, deriv^[2] w 0]
  have hjet (n : ℕ) (z : ℂ) : deriv^[n] (∑ j, c j • u j) z = ∑ j, c j * deriv^[n] (u j) z := by
    simp only [← iteratedDeriv_eq_iterate, smul_eq_mul,
      iteratedDeriv_sum_smul fun j hj => (hu j hj).contDiff.contDiffAt]
  have hjet0 (i : Fin 3) : deriv^[i] (∑ j, c j • u j) 0 = ![w 0, deriv w 0, deriv^[2] w 0] i := by
    rw [hjet, ← hc]
    simp [Matrix.mulVec, dotProduct, mul_comm, iteratedDeriv_eq_iterate]
  have hS : w = ∑ j, c j • u j := by
    refine eq_of_productEquation hw (Differentiable.sum fun j hj => (hu j hj).const_smul (c j))
      hwe (fun z => ?_) (by simpa using (hjet0 0).symm) (by simpa using (hjet0 1).symm)
      (by simpa using (hjet0 2).symm)
    have h0 := hjet 0 z
    rw [Function.iterate_zero_apply] at h0
    rw [hjet 3 z, ← Function.iterate_one deriv, hjet 1 z, h0]
    simp only [Fin.sum_univ_three, Function.iterate_zero_apply, Function.iterate_one]
    linear_combination c 0 * hsol 0 z + c 1 * hsol 1 z + c 2 * hsol 2 z
  refine ⟨c 0, c 1, c 2, hS.trans (funext fun z => ?_)⟩
  simp [hu_def, Fin.sum_univ_three]

/-- `Ai²`, `Ai Bi` and `Bi²` are linearly independent. -/
theorem linearIndependent_airyAi_sq_airyAi_mul_airyBi_airyBi_sq :
    LinearIndependent ℂ
      ![fun t => airyAi t ^ 2, fun t => airyAi t * airyBi t, fun t => airyBi t ^ 2] :=
  linearIndependent_sq_mul_sq (x := 0) differentiable_airyAi.contDiff.contDiffAt
    differentiable_airyBi.contDiff.contDiffAt
    (by rw [wronskian_airyAi_airyBi]; simp [Real.pi_ne_zero])

/-- **The basis of the product equation** (DLMF §9.11(i)): every entire solution of
`w''' - 4 z w' - 2 w = 0` is a linear combination of `Ai²`, `Ai Bi` and `Bi²`, which are
linearly independent by `TauCeti.linearIndependent_airyAi_sq_airyAi_mul_airyBi_airyBi_sq`. -/
theorem exists_eq_airyAi_sq_airyAi_mul_airyBi_airyBi_sq_of_productEquation {w : ℂ → ℂ}
    (hw : Differentiable ℂ w) (hwe : ∀ z, deriv^[3] w z - 4 * z * deriv w z - 2 * w z = 0) :
    ∃ a b c : ℂ, w = fun z => a * airyAi z ^ 2 + b * (airyAi z * airyBi z) + c * airyBi z ^ 2 :=
  exists_eq_sq_mul_sq_of_productEquation differentiable_airyAi differentiable_airyBi airyAi_ode
    airyBi_ode (by rw [wronskian_airyAi_airyBi]; simp [Real.pi_ne_zero]) hw hwe

end TauCeti
