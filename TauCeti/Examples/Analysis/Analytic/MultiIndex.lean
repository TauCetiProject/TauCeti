/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import TauCeti.Analysis.Complex.RealDeriv

/-!
# Normalization examples and counterexamples for multi-index Taylor coefficients

Concrete computations and counterexamples illustrating the conventions of
`FormalMultilinearSeries.mvCoeff` and `TauCeti.mvTaylorCoeff`:

* **Ordering of basis tuples (`mvCoeff_bilinearSeries_zero_one`):** for the non-symmetric degree-`2`
  series on `Fin 2 → 𝕜` with `p 2 (u, v) = u 0 * v 1`, the tuple `(e 0, e 1)` contributes `1` while
  `(e 1, e 0)` contributes `0`, giving `p.mvCoeff ![1, 1] = 1`. Keeping a single arbitrary ordering
  of the basis vectors could instead give `0`.
* **No double-counting on repeated coordinates (`mvCoeff_bilinearSeries_zero_zero`):** for
  `p 2 (u, v) = u 0 * v 0`, the unique tuple with counts `![2, 0]` is `(e 0, e 0)`, so
  `p.mvCoeff ![2, 0] = 1` rather than `2! = 2`.
* **Constant term (`mvCoeff_bilinearSeries_zero`, `mvCoeff_constFormalMultilinearSeries_zero`):**
  `mvCoeff p 0` evaluates `p 0` at the empty tuple, giving `0` on homogeneous degree-`2` series and
  `c` on the constant series `c`.
* **Factorial normalization (`mvTaylorCoeff_sq_zero`, `iteratedDeriv_sq_zero`):** for `z ↦ z 0 ^ 2`
  on `Fin 1 → 𝕜` at `0`, the Taylor coefficient of order `2` is `1`, whereas `iteratedDeriv 2` of
  `w ↦ w ^ 2` at `0` is `2! • 1 = 2`.
* **Expansion center (`mvTaylorCoeff_sq_three`):** for `z ↦ z 0 ^ 2` on `Fin 1 → 𝕜` at `![3]`, the
  first-order Taylor coefficient is `6` (the coefficient of `w` in `(3 + w) ^ 2`), whereas at `0`
  it is `0`.
* **Non-analytic functions (`mvTaylorCoeff_conjPlusOne`):** `z ↦ 1 + conj (z 0)` on `Fin 1 → ℂ` is
  analytic nowhere, so all its `ℂ`-Taylor coefficients vanish; in particular its order-`0`
  coefficient at `0` is `0 ≠ 1`.
* **Coordinatewise degree bounds vs total degree (`mvTaylorCoeff_sqFirst_comp_shear`):** `z 0 ^ 2`
  on `Fin 2 → ℝ` has zero Taylor coefficients at `0` whenever every coordinate of `α` is `< 2`, yet
  composing with the linear map `(w 0, w 1) ↦ (w 0 + w 1, 0)` produces `(w 0 + w 1) ^ 2`, whose
  `![1, 1]` Taylor coefficient is `2 ≠ 0`. Only vanishing in a fixed total degree is preserved by
  general continuous linear maps (`ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`).
-/

public section

open Finset TauCeti

namespace TauCeti.MultiIndexExample

section FormalSeries

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Continuous bilinear map `(u, v) ↦ u i₀ * v i₁` on `Fin 2 → 𝕜`. -/
noncomputable def bilinearTerm (i₀ i₁ : Fin 2) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 ↦ Fin 2 → 𝕜) 𝕜 :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin 2) (1 : 𝕜)).compContinuousLinearMap
    ![ContinuousLinearMap.proj i₀, ContinuousLinearMap.proj i₁]

@[simp]
theorem bilinearTerm_apply (i₀ i₁ : Fin 2) (m : Fin 2 → Fin 2 → 𝕜) :
    bilinearTerm i₀ i₁ m = m 0 i₀ * m 1 i₁ := by
  simp [bilinearTerm, Fin.prod_univ_two]

/-- Formal multilinear series on `Fin 2 → 𝕜` concentrated in degree `2` with
`p 2 (u, v) = u i₀ * v i₁`. -/
noncomputable def bilinearSeries (i₀ i₁ : Fin 2) : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜
  | 2 => bilinearTerm i₀ i₁
  | _ => 0

/-- On a pair of standard basis vectors `(e (a 0), e (a 1))`, `bilinearTerm i₀ i₁` evaluates to
`1` at `a = ![i₀, i₁]` and `0` otherwise. -/
theorem bilinearTerm_basis (i₀ i₁ : Fin 2) (a : Fin 2 → Fin 2) :
    bilinearTerm (𝕜 := 𝕜) i₀ i₁ (fun j ↦ Pi.single (a j) 1) =
      if a = ![i₀, i₁] then 1 else 0 := by
  simp only [bilinearTerm_apply]
  split_ifs with ha
  · subst ha
    simp
  · by_cases h0 : a 0 = i₀
    · have h1 : a 1 ≠ i₁ := fun h1 ↦ ha (funext (Fin.forall_fin_two.2 ⟨h0, h1⟩))
      simp [Pi.single_eq_of_ne' h1]
    · simp [Pi.single_eq_of_ne' h0]

/-- On `p 2 (u, v) = u 0 * v 1`, the basis tuple `(e 0, e 1)` evaluates to `1` while `(e 1, e 0)`
evaluates to `0`. -/
theorem bilinearTerm_zero_one_basis :
    bilinearTerm (𝕜 := 𝕜) 0 1 (fun j ↦ Pi.single (![0, 1] j) 1) = 1 ∧
      bilinearTerm (𝕜 := 𝕜) 0 1 (fun j ↦ Pi.single (![1, 0] j) 1) = 0 := by
  simp

/-- Summing over all basis tuples with counts `![1, 1]` gives `mvCoeff p ![1, 1] = 1` for
`p 2 (u, v) = u 0 * v 1`. -/
theorem mvCoeff_bilinearSeries_zero_one :
    (bilinearSeries (𝕜 := 𝕜) 0 1).mvCoeff ![1, 1] = 1 := by
  have hdeg : ∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i = 2 := by decide
  rw [FormalMultilinearSeries.mvCoeff_eq_sum _ hdeg]
  simp only [bilinearSeries, bilinearTerm_basis, sum_ite_eq']
  exact ite_eq_left (by decide)

/-- For `p 2 (u, v) = u 0 * v 0`, the unique tuple of basis vectors with counts `![2, 0]` is
`(e 0, e 0)`, so `mvCoeff p ![2, 0] = 1` (no factor of `2!`). -/
theorem mvCoeff_bilinearSeries_zero_zero :
    (bilinearSeries (𝕜 := 𝕜) 0 0).mvCoeff ![2, 0] = 1 := by
  have hdeg : ∑ i : Fin 2, (![2, 0] : Fin 2 → ℕ) i = 2 := by decide
  rw [FormalMultilinearSeries.mvCoeff_eq_sum _ hdeg]
  simp only [bilinearSeries, bilinearTerm_basis, sum_ite_eq']
  exact ite_eq_left (by decide)

/-- Both degree-`2` series have constant term `mvCoeff p 0 = 0`. -/
theorem mvCoeff_bilinearSeries_zero :
    (bilinearSeries (𝕜 := 𝕜) 0 1).mvCoeff 0 = 0 ∧
      (bilinearSeries (𝕜 := 𝕜) 0 0).mvCoeff 0 = 0 := by
  simp [FormalMultilinearSeries.mvCoeff_zero_eq_apply (v := 0), bilinearSeries]

/-- On `constFormalMultilinearSeries`, `mvCoeff` at `0` recovers the constant `c`. -/
theorem mvCoeff_constFormalMultilinearSeries_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (c : 𝕜) :
    (constFormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) c).mvCoeff 0 = c := by
  simp

end FormalSeries

section OneVariable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- For `z ↦ z 0 ^ 2` on `Fin 1 → 𝕜`, the Taylor coefficient of order `2` at `0` is `1`. -/
theorem mvTaylorCoeff_sq_zero :
    mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) 0 ![2] = 1 := by
  have hfn : (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) = fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ (![2] : Fin 1 → ℕ) i :=
    funext fun z ↦ by simp
  rw [hfn, mvTaylorCoeff_prod_pow]
  simp

/-- By contrast with `mvTaylorCoeff_sq_zero`, the second iterated derivative of `w ↦ w ^ 2` at `0`
carries the factor `2! = 2`. -/
theorem iteratedDeriv_sq_zero [CompleteSpace 𝕜] :
    iteratedDeriv 2 (fun w : 𝕜 ↦ w ^ 2) 0 = 2 := by
  have han : AnalyticAt 𝕜 (fun w : 𝕜 ↦ w ^ 2) 0 := analyticAt_id.fun_pow 2
  have h := han.factorial_smul_mvTaylorCoeff_of_unique (ι := Fin 1) (x := (0 : 𝕜)) ![2]
  simp only [Fin.default_eq_zero, Matrix.cons_val_zero, ← Pi.zero_def, mvTaylorCoeff_sq_zero] at h
  simpa [Nat.factorial] using h.symm

/-- Expanding `z ↦ z 0 ^ 2` around `![3]` gives first-order Taylor coefficient `6` (the coefficient
of `w` in `(3 + w) ^ 2 = 9 + 6 w + w ^ 2`), whereas expanding around `0` gives `0`. -/
theorem mvTaylorCoeff_sq_three :
    mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) ![3] ![1] = 6 ∧
      mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) 0 ![1] = 0 := by
  have hfn : (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) = fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ (![2] : Fin 1 → ℕ) i :=
    funext fun z ↦ by simp
  let p0 : (Fin 1 → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj 0
  refine ⟨?_, ?_⟩
  · rw [← zero_add (![3] : Fin 1 → 𝕜), ← mvTaylorCoeff_comp_add_right]
    have hexp : (fun z : Fin 1 → 𝕜 ↦ ((z + (![3] : Fin 1 → 𝕜)) 0) ^ 2) =
        (fun _ : Fin 1 → 𝕜 ↦ (9 : 𝕜)) +
          ((6 : 𝕜) • fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ (![1] : Fin 1 → ℕ) i) +
          fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ (![2] : Fin 1 → ℕ) i := by
      ext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_one,
        Matrix.cons_val_zero, pow_one]
      ring
    have h1 : AnalyticAt 𝕜 (fun _ : Fin 1 → 𝕜 ↦ (9 : 𝕜)) 0 := analyticAt_const
    have h2 : AnalyticAt 𝕜 ((6 : 𝕜) • fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ (![1] : Fin 1 → ℕ) i) 0 :=
      analyticAt_const.smul
        ((p0.analyticAt 0).congr (Filter.Eventually.of_forall fun _ ↦ by simp [p0]))
    have h3 : AnalyticAt 𝕜 (fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ (![2] : Fin 1 → ℕ) i) 0 := by
      simpa [p0, Fin.prod_univ_one] using (p0.analyticAt 0).fun_pow 2
    have h123 := ((h1.add h2).mvTaylorCoeff_add h3 ![1]).trans
      (congrArg (· + _) (h1.mvTaylorCoeff_add h2 ![1]))
    rw [hexp, h123, mvTaylorCoeff_const, mvTaylorCoeff_const_smul, mvTaylorCoeff_prod_pow,
      mvTaylorCoeff_prod_pow]
    have h10 : (![1] : Fin 1 → ℕ) ≠ 0 := fun h ↦ by simpa using congrFun h 0
    have h12 : (![1] : Fin 1 → ℕ) ≠ ![2] := fun h ↦ by simpa using congrFun h 0
    simp [h10, h12]
  · rw [hfn, mvTaylorCoeff_prod_pow]
    have h12 : (![1] : Fin 1 → ℕ) ≠ ![2] := fun h ↦ by simpa using congrFun h 0
    simp [h12]

end OneVariable

section NonAnalytic

/-- The real-smooth function `z ↦ 1 + conj (z 0)` on `Fin 1 → ℂ`. -/
def conjPlusOne (z : Fin 1 → ℂ) : ℂ := 1 + starRingEnd ℂ (z 0)

/-- `conjPlusOne` is `ℂ`-analytic nowhere on `Fin 1 → ℂ`. -/
theorem not_analyticAt_conjPlusOne (x : Fin 1 → ℂ) : ¬ AnalyticAt ℂ conjPlusOne x := by
  intro ha
  let s : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℂ ℂ
  have hsx : s (x 0) = x := by
    ext i
    rw [Subsingleton.elim i 0]
    simp [s]
  have hd : DifferentiableAt ℂ (fun w : ℂ ↦ conjPlusOne (s w) - 1) (x 0) :=
    (((hsx.symm ▸ ha).differentiableAt.comp (x 0) s.differentiableAt).sub_const 1)
  exact Complex.not_differentiableAt_conj (x 0)
    (by simpa [conjPlusOne, s] using hd)

/-- Because `conjPlusOne` is nowhere `ℂ`-analytic, every Taylor coefficient vanishes — in particular
`mvTaylorCoeff conjPlusOne 0 0 = 0`, whereas `conjPlusOne 0 = 1`. -/
theorem mvTaylorCoeff_conjPlusOne :
    (∀ x α, mvTaylorCoeff conjPlusOne x α = 0) ∧
      mvTaylorCoeff conjPlusOne 0 0 = 0 ∧ conjPlusOne 0 = 1 :=
  ⟨fun x α ↦ mvTaylorCoeff_of_not_analyticAt (not_analyticAt_conjPlusOne x) α,
    mvTaylorCoeff_of_not_analyticAt (not_analyticAt_conjPlusOne 0) 0, by simp [conjPlusOne]⟩

end NonAnalytic

section LinearChangeOfVariables

/-- The quadratic monomial `z ↦ z 0 ^ 2` on `Fin 2 → ℝ`. -/
def sqFirst (z : Fin 2 → ℝ) : ℝ := z 0 ^ 2

/-- Continuous linear map `(w 0, w 1) ↦ (w 0 + w 1, 0)` on `Fin 2 → ℝ`. -/
def shear : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  let p0 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let p1 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  ContinuousLinearMap.pi ![p0 + p1, 0]

/-- `sqFirst` has zero Taylor coefficients at `0` at every multi-index `α` with `∀ i, α i < 2`, yet
`sqFirst ∘ shear` (`w ↦ (w 0 + w 1) ^ 2`) has Taylor coefficient `2` at `![1, 1]`, showing that
coordinatewise degree bounds `< m` are not preserved by linear changes of variables; by contrast,
vanishing in each total degree `< 2` is preserved. -/
theorem mvTaylorCoeff_sqFirst_comp_shear :
    (∀ α : Fin 2 → ℕ, (∀ i, α i < 2) → mvTaylorCoeff sqFirst 0 α = 0) ∧
      (∀ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i < 2) ∧
      mvTaylorCoeff (sqFirst ∘ shear) 0 ![1, 1] = 2 ∧
      ∀ k < 2, ∀ β : Fin 2 → ℕ, ∑ j, β j = k → mvTaylorCoeff (sqFirst ∘ shear) 0 β = 0 := by
  let p0 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let p1 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hsq : sqFirst = fun z : Fin 2 → ℝ ↦ ∏ i, z i ^ (![2, 0] : Fin 2 → ℕ) i :=
    funext fun z ↦ by simp [sqFirst, Fin.prod_univ_two]
  have hsq_an : AnalyticAt ℝ sqFirst 0 := (p0.analyticAt 0).fun_pow 2
  refine ⟨fun α hα ↦ ?_, by decide, ?_, fun k hk β hβ ↦ ?_⟩
  · rw [hsq, mvTaylorCoeff_prod_pow]
    have hne : α ≠ ![2, 0] := fun h ↦ by
      have := hα 0
      rw [h] at this
      simp at this
    simp [hne]
  · have hexp : sqFirst ∘ shear =
        (fun w : Fin 2 → ℝ ↦ ∏ i, w i ^ (![2, 0] : Fin 2 → ℕ) i) +
          ((2 : ℝ) • fun w : Fin 2 → ℝ ↦ ∏ i, w i ^ (![1, 1] : Fin 2 → ℕ) i) +
          fun w : Fin 2 → ℝ ↦ ∏ i, w i ^ (![0, 2] : Fin 2 → ℕ) i := by
      ext w
      simp only [Function.comp_apply, sqFirst, shear, ContinuousLinearMap.pi_apply,
        Matrix.cons_val_zero, _root_.add_apply, ContinuousLinearMap.proj_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_two, Matrix.cons_val_one,
        pow_zero, pow_one, one_mul, mul_one]
      ring
    have h1 : AnalyticAt ℝ (fun w : Fin 2 → ℝ ↦ ∏ i, w i ^ (![2, 0] : Fin 2 → ℕ) i) 0 := by
      simpa [p0, Fin.prod_univ_two] using (p0.analyticAt 0).fun_pow 2
    have h2 : AnalyticAt ℝ
        ((2 : ℝ) • fun w : Fin 2 → ℝ ↦ ∏ i, w i ^ (![1, 1] : Fin 2 → ℕ) i) 0 :=
      analyticAt_const.smul
        (by simpa [p0, p1, Fin.prod_univ_two] using (p0.analyticAt 0).fun_mul (p1.analyticAt 0))
    have h3 : AnalyticAt ℝ (fun w : Fin 2 → ℝ ↦ ∏ i, w i ^ (![0, 2] : Fin 2 → ℕ) i) 0 := by
      simpa [p1, Fin.prod_univ_two] using (p1.analyticAt 0).fun_pow 2
    have h123 := ((h1.add h2).mvTaylorCoeff_add h3 ![1, 1]).trans
      (congrArg (· + _) (h1.mvTaylorCoeff_add h2 ![1, 1]))
    rw [hexp, h123, mvTaylorCoeff_prod_pow, mvTaylorCoeff_const_smul, mvTaylorCoeff_prod_pow,
      mvTaylorCoeff_prod_pow]
    have hne1 : (![1, 1] : Fin 2 → ℕ) ≠ ![2, 0] := fun h ↦ by simpa using congrFun h 0
    have hne3 : (![1, 1] : Fin 2 → ℕ) ≠ ![0, 2] := fun h ↦ by simpa using congrFun h 0
    simp [hne1, hne3]
  · refine shear.mvTaylorCoeff_comp_eq_zero (x := 0) (by simpa using hsq_an) (fun α hα ↦ ?_) β hβ
    rw [map_zero, hsq, mvTaylorCoeff_prod_pow]
    have hne : α ≠ ![2, 0] := fun h ↦ by
      rw [h] at hα
      simp [Fin.sum_univ_two] at hα
      omega
    simp [hne]

end LinearChangeOfVariables

end TauCeti.MultiIndexExample
