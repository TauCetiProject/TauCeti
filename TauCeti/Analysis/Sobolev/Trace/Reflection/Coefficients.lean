/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Coefficients for higher-order reflection

To extend a function from the upper half-space, use the values at normal coordinates
`-t / (j + 1)` below the boundary, weighted by `higherReflectionCoeff k j`, for `j : Fin k`.
The coefficients satisfy `∑ j, c j * (-(j + 1)⁻¹)^i = 1` for `i < k`. Thus normal derivatives
of order `i < k` match across the boundary provided the input is `Cⁱ`. The coefficients are the
Lagrange interpolation
weights at `1` for the nodes `-(j + 1)⁻¹`; this also proves their uniqueness and polynomial
reproduction. The first two cases are the even reflection and the coefficients `-3, 4`.

`higherReflectionLower` is the linear combination used below the boundary, defined on the
whole normal line. Its derivative of order `i < k` at zero agrees with that of a `Cⁱ` input.
For `k = 0` the lower branch is zero and no derivative matching is asserted.
This file supplies the coefficients and matching identities, not the weak Sobolev gluing theorem.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Chapter 5, extension theorems.
-/

public section

noncomputable section

open Finset Polynomial

namespace TauCeti

/-- The normal-coordinate dilation for the `j`th term of a higher-order reflection. -/
def higherReflectionNode {k : ℕ} (j : Fin k) : ℝ := -((j : ℝ) + 1)⁻¹

/-- The explicit dilation factor, with indices starting at zero. -/
theorem higherReflectionNode_eq {k : ℕ} (j : Fin k) :
    higherReflectionNode j = -((j : ℝ) + 1)⁻¹ := by
  rw [higherReflectionNode]

/-- Each reflected dilation sends negative normal coordinates to positive ones. -/
theorem higherReflectionNode_neg {k : ℕ} (j : Fin k) : higherReflectionNode j < 0 := by
  rw [higherReflectionNode, neg_neg_iff_pos, inv_pos]
  positivity

/-- The reflection nodes are pairwise distinct. -/
theorem higherReflectionNode_injective (k : ℕ) :
    Function.Injective (higherReflectionNode (k := k)) := by
  intro i j h
  simp only [higherReflectionNode, neg_inj, inv_inj, add_left_inj] at h
  exact Fin.ext (Nat.cast_injective h)

/-- Lagrange interpolation weights at `1` for the reflected normal dilations. -/
def higherReflectionCoeff (k : ℕ) (j : Fin k) : ℝ :=
  (Lagrange.basis univ higherReflectionNode j).eval 1

/-- The weights reproduce evaluation at `1` for every polynomial of degree less than `k`. -/
theorem sum_higherReflectionCoeff_mul_eval {k : ℕ} (P : ℝ[X]) (hP : P.degree < k) :
    ∑ j : Fin k, higherReflectionCoeff k j * P.eval (higherReflectionNode j) = P.eval 1 := by
  have h := congrArg (Polynomial.eval 1)
    (Lagrange.eq_interpolate (higherReflectionNode_injective k).injOn
      (by simpa using hP) : P = Lagrange.interpolate univ higherReflectionNode
        (fun j : Fin k ↦ P.eval (higherReflectionNode j)))
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C] at h
  simpa only [higherReflectionCoeff, mul_comm] using h.symm

/-- The moment equations that match all normal derivatives of order less than `k`. -/
theorem sum_higherReflectionCoeff_mul_pow {k i : ℕ} (hi : i < k) :
    ∑ j : Fin k, higherReflectionCoeff k j * higherReflectionNode j ^ i = 1 := by
  simpa using sum_higherReflectionCoeff_mul_eval (X ^ i : ℝ[X]) (by simpa using hi)

/-- The reflection coefficients sum to one. -/
@[simp]
theorem sum_higherReflectionCoeff {k : ℕ} (hk : 0 < k) :
    ∑ j : Fin k, higherReflectionCoeff k j = 1 := by
  simpa using sum_higherReflectionCoeff_mul_pow hk

/-- The moment equations uniquely determine the reflection coefficients. -/
theorem eq_higherReflectionCoeff_iff {k : ℕ} (c : Fin k → ℝ) :
    c = higherReflectionCoeff k ↔
      ∀ i < k, ∑ j : Fin k, c j * higherReflectionNode j ^ i = 1 := by
  constructor
  · rintro rfl i hi
    exact sum_higherReflectionCoeff_mul_pow hi
  · intro h
    have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (higherReflectionNode_injective k) (v := c - higherReflectionCoeff k) fun i ↦ by
        simp only [Pi.sub_apply, sub_mul, sum_sub_distrib, h i i.isLt,
          sum_higherReflectionCoeff_mul_pow i.isLt, sub_self]
    exact sub_eq_zero.mp hz

/-- At first order the coefficient is one: the extension is even reflection. -/
@[simp]
theorem higherReflectionCoeff_one (j : Fin 1) : higherReflectionCoeff 1 j = 1 := by
  have h := sum_higherReflectionCoeff (k := 1) (by decide)
  simpa [Subsingleton.elim j 0] using h

/-- The first coefficient at second order is `-3`. -/
@[simp]
theorem higherReflectionCoeff_two_zero : higherReflectionCoeff 2 0 = -3 := by
  have h := (eq_higherReflectionCoeff_iff (![(-3 : ℝ), 4])).2 (by
    intro i hi
    interval_cases i <;> norm_num [Fin.sum_univ_two, higherReflectionNode])
  exact (congrFun h 0).symm

/-- The second coefficient at second order is `4`. -/
@[simp]
theorem higherReflectionCoeff_two_one : higherReflectionCoeff 2 1 = 4 := by
  have h₀ := sum_higherReflectionCoeff (k := 2) (by decide)
  rw [Fin.sum_univ_two, higherReflectionCoeff_two_zero] at h₀
  linarith

section Lower

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The lower-branch formula for higher-order reflection in the normal coordinate.
When `t < 0`, it only samples positive normal coordinates. -/
def higherReflectionLower (k : ℕ) (f : ℝ → F) (t : ℝ) : F :=
  ∑ j : Fin k, higherReflectionCoeff k j • f (higherReflectionNode j * t)

theorem higherReflectionLower_apply (k : ℕ) (f : ℝ → F) (t : ℝ) :
    higherReflectionLower k f t =
      ∑ j : Fin k, higherReflectionCoeff k j • f (higherReflectionNode j * t) := by
  rw [higherReflectionLower]

/-- The first-order lower branch is the even reflection. -/
@[simp]
theorem higherReflectionLower_one (f : ℝ → F) (t : ℝ) :
    higherReflectionLower 1 f t = f (-t) := by
  simp [higherReflectionLower, higherReflectionNode]

/-- The second-order lower branch is `-3 f(-t) + 4 f(-t/2)`. -/
theorem higherReflectionLower_two (f : ℝ → F) (t : ℝ) :
    higherReflectionLower 2 f t = (-3 : ℝ) • f (-t) + (4 : ℝ) • f (-t / 2) := by
  simp [higherReflectionLower, Fin.sum_univ_two, higherReflectionNode]
  congr 2
  ring

/-- The lower branch is linear in the input function. -/
theorem higherReflectionLower_add (k : ℕ) (f g : ℝ → F) :
    higherReflectionLower k (f + g) = higherReflectionLower k f + higherReflectionLower k g := by
  funext t
  simp [higherReflectionLower, smul_add, sum_add_distrib]

/-- The lower branch commutes with scalar multiplication. -/
theorem higherReflectionLower_smul (k : ℕ) (c : ℝ) (f : ℝ → F) :
    higherReflectionLower k (c • f) = c • higherReflectionLower k f := by
  funext t
  simp only [higherReflectionLower, Pi.smul_apply, Finset.smul_sum]
  apply sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- The two branch values agree at the boundary. -/
@[simp]
theorem higherReflectionLower_zero {k : ℕ} (hk : 0 < k) (f : ℝ → F) :
    higherReflectionLower k f 0 = f 0 := by
  simp [higherReflectionLower, ← Finset.sum_smul, sum_higherReflectionCoeff hk]

/-- Higher-order reflection preserves regularity on each branch. -/
theorem _root_.ContDiff.higherReflectionLower {k : ℕ} {n : WithTop ℕ∞} {f : ℝ → F}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (higherReflectionLower k f) := by
  exact ContDiff.sum fun j _ ↦ (hf.comp (contDiff_const.mul contDiff_id)).const_smul _

/-- The normal derivatives of the lower branch are the weighted dilations of the derivatives. -/
theorem iteratedDeriv_higherReflectionLower {k i : ℕ} {f : ℝ → F}
    (hf : ContDiff ℝ i f) (t : ℝ) :
    iteratedDeriv i (higherReflectionLower k f) t =
      ∑ j : Fin k, (higherReflectionCoeff k j * higherReflectionNode j ^ i) •
        iteratedDeriv i f (higherReflectionNode j * t) := by
  -- The lower branch is a linear combination; expose its pointwise finite-sum function.
  change iteratedDeriv i (fun t ↦ ∑ j : Fin k,
    higherReflectionCoeff k j • f (higherReflectionNode j * t)) t = _
  rw [iteratedDeriv_fun_sum]
  · apply sum_congr rfl
    intro j _
    rw [iteratedDeriv_fun_const_smul_field, iteratedDeriv_comp_const_smul hf, smul_smul]
  · intro j _
    exact ((hf.comp (contDiff_const.mul contDiff_id)).const_smul _).contDiffAt

/-- All normal derivatives below order `k` agree at the boundary. -/
theorem iteratedDeriv_higherReflectionLower_zero {k i : ℕ} (hi : i < k) {f : ℝ → F}
    (hf : ContDiff ℝ i f) :
    iteratedDeriv i (higherReflectionLower k f) 0 = iteratedDeriv i f 0 := by
  rw [iteratedDeriv_higherReflectionLower hf]
  simp only [mul_zero, ← sum_smul, sum_higherReflectionCoeff_mul_pow hi, one_smul]

end Lower

end TauCeti
