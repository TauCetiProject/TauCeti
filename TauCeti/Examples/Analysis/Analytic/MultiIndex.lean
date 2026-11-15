/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Data.Fin.VecNotation
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import Mathlib.Analysis.Analytic.Constructions

/-!
# Examples of multi-index power series and Taylor coefficients

These examples verify the normalization and conventions of `FormalMultilinearSeries.mvCoeff` and
`TauCeti.mvTaylorCoeff` on concrete low-dimensional functions and formal multilinear series.

* On `Fin 2 → 𝕜`, the asymmetric bilinear series with `p 2 (u, v) = u 0 * v 1` has
  `p.mvCoeff ![1, 1] = 1` (summing over both ordered pairs of basis vectors `(e 0, e 1)` and
  `(e 1, e 0)`, which contribute `1` and `0`) and `p.mvCoeff 0 = 0`.
* On `Fin 2 → 𝕜`, the symmetric monomial series with `p 2 (u, v) = u 0 * v 0` has
  `p.mvCoeff ![2, 0] = 1` rather than `2`, because `mvCoeff` sums over tuples of coordinates with
  prescribed counts rather than over permutations of positions.
* The constant formal multilinear series `constFormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) c` has
  `mvCoeff 0 = c` and `mvCoeff ![1, 0] = 0`.
* On `Fin 1 → 𝕜`, `z ↦ z 0 ^ 2` at `0` has multi-index Taylor coefficient `1` at `![2]`, while the
  second derivative `iteratedDeriv 2 (fun w : 𝕜 ↦ w ^ 2) 0` is `2`: the factorial `2!` multiplies
  `mvTaylorCoeff` rather than dividing `iteratedDeriv`.
* On `Fin 1 → 𝕜`, `z ↦ z 0 ^ 2` expanded about `![3]` has Taylor coefficient `6` at `![1]`, the
  linear coefficient of `(3 + w) ^ 2`.
* Over `ℂ`, `z ↦ 1 + conj (z 0)` on `Fin 1 → ℂ` is nowhere complex-analytic, so all its multi-index
  Taylor coefficients vanish; at `0` the order-`0` coefficient is `0`, not the value `1`.
* On `Fin 2 → 𝕜`, `G z = z 0 ^ 2` at `0` has vanishing Taylor coefficients whenever both coordinates
  of `α` are `< 2`, whereas after the linear change of variables `A z = ![z 0 + z 1, z 1]` its
  pullback `(z 0 + z 1) ^ 2` has coefficient `2` at `![1, 1]`; by contrast, vanishing in a fixed
  total degree (`k = 1`) is preserved by `ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`.
-/

public section

open ComplexConjugate Finset

namespace TauCeti

section FormalSeries

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- The series on `Fin 2 → 𝕜` whose only nonzero term is `p 2 (u, v) = u 0 * v 1` has
-- `mvCoeff ![1, 1] = 1` (from `(e 0, e 1)` giving `1` and `(e 1, e 0)` giving `0`) and
-- `mvCoeff 0 = 0`.
example :
    let B : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 ↦ Fin 2 → 𝕜) 𝕜 :=
      (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin 2) 𝕜).compContinuousLinearMap
        fun j ↦ ContinuousLinearMap.proj j
    let p : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 :=
      fun n ↦ if h : n = 2 then h ▸ B else 0
    p.mvCoeff ![1, 1] = 1 ∧ p.mvCoeff 0 = 0 := by
  intro B p
  have hp2 : p 2 = B := by simp [p]
  refine ⟨?_, ?_⟩
  · have hdeg : ∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i = 2 := by decide
    rw [p.mvCoeff_eq_sum hdeg]
    simp_rw [hp2]
    -- The only maps `Fin 2 → Fin 2` with coordinate counts `![1, 1]` are `![0, 1]` and `![1, 0]`.
    trans ∑ a ∈ ({![0, 1], ![1, 0]} : Finset (Fin 2 → Fin 2)), B fun j ↦ Pi.single (a j) 1
    · refine sum_congr ?_ fun _ _ ↦ rfl
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fintype.card_subtype]
      decide +revert
    · rw [sum_pair (by decide)]
      simp [B, Fin.prod_univ_two]
  · rw [p.mvCoeff_zero_eq_apply 0]
    simp [p]

-- The series on `Fin 2 → 𝕜` whose only nonzero term is `p 2 (u, v) = u 0 * v 0` has
-- `mvCoeff ![2, 0] = 1` (not `2`, since `![0, 0]` is the unique tuple with counts `![2, 0]`) and
-- `mvCoeff 0 = 0`.
example :
    let B : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 ↦ Fin 2 → 𝕜) 𝕜 :=
      (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin 2) 𝕜).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.proj (0 : Fin 2)
    let p : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 :=
      fun n ↦ if h : n = 2 then h ▸ B else 0
    p.mvCoeff ![2, 0] = 1 ∧ p.mvCoeff 0 = 0 := by
  intro B p
  have hp2 : p 2 = B := by simp [p]
  refine ⟨?_, ?_⟩
  · have hdeg : ∑ i : Fin 2, (![2, 0] : Fin 2 → ℕ) i = 2 := by decide
    rw [p.mvCoeff_eq_sum hdeg]
    simp_rw [hp2]
    -- The unique map `Fin 2 → Fin 2` with coordinate counts `![2, 0]` is `![0, 0]`.
    trans ∑ a ∈ ({![0, 0]} : Finset (Fin 2 → Fin 2)), B fun j ↦ Pi.single (a j) 1
    · refine sum_congr ?_ fun _ _ ↦ rfl
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Fintype.card_subtype]
      decide +revert
    · rw [sum_singleton]
      simp [B, Fin.prod_univ_two]
  · rw [p.mvCoeff_zero_eq_apply 0]
    simp [p]

-- The constant formal multilinear series has `mvCoeff 0 = c` and `mvCoeff ![1, 0] = 0`.
example (c : 𝕜) :
    (constFormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) c).mvCoeff 0 = c ∧
      (constFormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) c).mvCoeff ![1, 0] = 0 := by
  have hne : (![1, 0] : Fin 2 → ℕ) ≠ 0 := by decide
  simp [FormalMultilinearSeries.mvCoeff_constFormalMultilinearSeries, hne]

end FormalSeries

section TaylorCoeff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- At `0`, `z ↦ z 0 ^ 2` has Taylor coefficient `1` at `![2]`, while its second derivative is `2`.
example [CompleteSpace 𝕜] :
    mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) 0 ![2] = 1 ∧
      iteratedDeriv 2 (fun w : 𝕜 ↦ w ^ 2) 0 = 2 := by
  have hmon : (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) = fun z ↦ ∏ i : Fin 1, z i ^ (![2] : Fin 1 → ℕ) i := by
    ext z; simp
  have hc : mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) 0 ![2] = 1 := by
    rw [hmon, mvTaylorCoeff_prod_pow_zero]
    simp
  refine ⟨hc, ?_⟩
  have hsq : AnalyticAt 𝕜 (fun w : 𝕜 ↦ w ^ 2) 0 := by fun_prop
  have hderiv := hsq.factorial_smul_mvTaylorCoeff_of_unique (ι := Fin 1) (![2] : Fin 1 → ℕ)
  have h0 : (fun _ : Fin 1 ↦ (0 : 𝕜)) = 0 := rfl
  simp only [Fin.default_eq_zero, Matrix.cons_val_zero, h0, hc] at hderiv
  simpa [Nat.factorial] using hderiv.symm

-- Expanding `z ↦ z 0 ^ 2` about `![3]` gives Taylor coefficient `6` at `![1]`.
example : mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) ![3] ![1] = 6 := by
  rw [← zero_add (![3] : Fin 1 → 𝕜), ← mvTaylorCoeff_comp_add_right]
  have hexp : (fun z : Fin 1 → 𝕜 ↦ (z + (![3] : Fin 1 → 𝕜)) 0 ^ 2) =
      (fun z ↦ ∏ i : Fin 1, z i ^ (![2] : Fin 1 → ℕ) i) +
        ((6 : 𝕜) • fun z ↦ ∏ i : Fin 1, z i ^ (![1] : Fin 1 → ℕ) i) +
        fun _ ↦ (9 : 𝕜) := by
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_one, Matrix.cons_val_zero,
      pow_one]
    ring
  have hmon (τ : Fin 1 → ℕ) : AnalyticAt 𝕜 (fun z : Fin 1 → 𝕜 ↦ ∏ i, z i ^ τ i) 0 :=
    univ.analyticAt_fun_prod fun i _ ↦
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ ↦ 𝕜) i).analyticAt 0).fun_pow (τ i)
  rw [hexp, ((hmon ![2]).add ((hmon ![1]).const_smul (c := (6 : 𝕜)))).mvTaylorCoeff_add
    analyticAt_const, (hmon ![2]).mvTaylorCoeff_add ((hmon ![1]).const_smul (c := (6 : 𝕜))),
    mvTaylorCoeff_const_smul, mvTaylorCoeff_prod_pow_zero, mvTaylorCoeff_prod_pow_zero,
    mvTaylorCoeff_const]
  have h21 : (![1] : Fin 1 → ℕ) ≠ ![2] := by decide
  have h10 : (![1] : Fin 1 → ℕ) ≠ 0 := by decide
  simp [h21, h10]

-- Over `ℂ`, `f z = 1 + conj (z 0)` on `Fin 1 → ℂ` is nowhere analytic, so all its Taylor
-- coefficients vanish; at `0`, `mvTaylorCoeff f 0 0 = 0 ≠ f 0 = 1`.
example :
    let f : (Fin 1 → ℂ) → ℂ := fun z ↦ 1 + conj (z 0)
    (∀ x α, mvTaylorCoeff f x α = 0) ∧ mvTaylorCoeff f 0 0 ≠ f 0 := by
  intro f
  have hnot (x : Fin 1 → ℂ) : ¬AnalyticAt ℂ f x := by
    intro han
    let ι₁ : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℂ ℂ
    have hx : ι₁ (x 0) = x := by ext i; rw [Subsingleton.elim i 0]; rfl
    have hcomp : AnalyticAt ℂ (f ∘ ι₁) (x 0) :=
      (hx ▸ han).comp (ι₁.analyticAt (x 0))
    have hconj : DifferentiableAt ℂ (conj : ℂ → ℂ) (x 0) := by
      have hd : DifferentiableAt ℂ (fun w : ℂ ↦ (f (ι₁ w)) - 1) (x 0) :=
        hcomp.differentiableAt.sub (differentiableAt_const 1)
      simpa [f, ι₁] using hd
    have hR : fderiv ℝ (conj : ℂ → ℂ) (x 0) = Complex.conjCLE.toContinuousLinearMap :=
      Complex.conjCLE.hasFDerivAt.fderiv
    have hI := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L Complex.I) (hconj.fderiv_restrictScalars ℝ)
    have h1 := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L 1) (hconj.fderiv_restrictScalars ℝ)
    simp only [ContinuousLinearMap.coe_restrictScalars', hR, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, map_one, Complex.conj_I] at hI h1
    have hlin : fderiv ℂ (conj : ℂ → ℂ) (x 0) Complex.I =
        Complex.I * fderiv ℂ (conj : ℂ → ℂ) (x 0) 1 := by simp
    rw [← h1, mul_one, ← hI] at hlin
    exact Complex.I_ne_zero (by linear_combination -hlin / 2)
  refine ⟨fun x α ↦ mvTaylorCoeff_of_not_analyticAt (hnot x) α, ?_⟩
  rw [mvTaylorCoeff_of_not_analyticAt (hnot 0) 0]
  simp [f]

-- Coordinatewise vanishing (`∀ i, α i < 2`) is not preserved by a linear change of variables,
-- whereas vanishing in a fixed total degree (`∑ i, α i = 1`) is.
example :
    let G : (Fin 2 → 𝕜) → 𝕜 := fun z ↦ z 0 ^ 2
    let p₀ : (Fin 2 → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj 0
    let p₁ : (Fin 2 → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj 1
    let A : (Fin 2 → 𝕜) →L[𝕜] (Fin 2 → 𝕜) := ContinuousLinearMap.pi ![p₀ + p₁, p₁]
    (∀ α : Fin 2 → ℕ, (∀ i, α i < 2) → mvTaylorCoeff G 0 α = 0) ∧
      mvTaylorCoeff (G ∘ A) 0 ![1, 1] = 2 ∧
      (∀ β : Fin 2 → ℕ, ∑ j, β j = 1 → mvTaylorCoeff (G ∘ A) 0 β = 0) := by
  intro G p₀ p₁ A
  have hG_mon : G = fun z : Fin 2 → 𝕜 ↦ ∏ i : Fin 2, z i ^ (![2, 0] : Fin 2 → ℕ) i := by
    ext z; simp [G, Fin.prod_univ_two]
  have hG_coeff (α : Fin 2 → ℕ) :
      mvTaylorCoeff G 0 α = if α = ![2, 0] then 1 else 0 := by
    rw [hG_mon, mvTaylorCoeff_prod_pow_zero]
  refine ⟨fun α hα ↦ ?_, ?_, ?_⟩
  · have hne : α ≠ ![2, 0] := fun h ↦ by
      have := hα 0
      simp [h] at this
    simp [hG_coeff, hne]
  · have hexp : G ∘ A =
        (fun z : Fin 2 → 𝕜 ↦ ∏ i, z i ^ (![2, 0] : Fin 2 → ℕ) i) +
          ((2 : 𝕜) • fun z : Fin 2 → 𝕜 ↦ ∏ i, z i ^ (![1, 1] : Fin 2 → ℕ) i) +
          fun z : Fin 2 → 𝕜 ↦ ∏ i, z i ^ (![0, 2] : Fin 2 → ℕ) i := by
      ext z
      simp only [Function.comp_apply, G, A, p₀, p₁, ContinuousLinearMap.pi_apply,
        Matrix.cons_val_zero, add_apply, ContinuousLinearMap.proj_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_two, Matrix.cons_val_one,
        pow_zero, pow_one, mul_one, one_mul]
      ring
    have hmon (τ : Fin 2 → ℕ) : AnalyticAt 𝕜 (fun z : Fin 2 → 𝕜 ↦ ∏ i, z i ^ τ i) 0 :=
      univ.analyticAt_fun_prod fun i _ ↦
        ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ ↦ 𝕜) i).analyticAt 0).fun_pow (τ i)
    rw [hexp, ((hmon ![2, 0]).add ((hmon ![1, 1]).const_smul (c := (2 : 𝕜)))).mvTaylorCoeff_add
      (hmon ![0, 2]), (hmon ![2, 0]).mvTaylorCoeff_add ((hmon ![1, 1]).const_smul (c := (2 : 𝕜))),
      mvTaylorCoeff_const_smul, mvTaylorCoeff_prod_pow_zero, mvTaylorCoeff_prod_pow_zero,
      mvTaylorCoeff_prod_pow_zero]
    have h20 : (![1, 1] : Fin 2 → ℕ) ≠ ![2, 0] := by decide
    have h02 : (![1, 1] : Fin 2 → ℕ) ≠ ![0, 2] := by decide
    simp [h20, h02]
  · have hG_an : AnalyticAt 𝕜 G (A 0) := (p₀.analyticAt (A 0)).fun_pow 2
    refine A.mvTaylorCoeff_comp_eq_zero hG_an ?_
    rw [map_zero]
    intro α hα
    have hne : α ≠ ![2, 0] := by
      rintro rfl
      simp [Fin.sum_univ_two] at hα
    simp [hG_coeff, hne]

end TaylorCoeff

end TauCeti
