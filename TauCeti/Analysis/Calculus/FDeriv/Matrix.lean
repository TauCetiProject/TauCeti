/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A product rule for matrix-field fluxes

For a matrix field `A`, a vector field `v`, and specified coordinate directions `e i`,
the sum of the directional derivatives of the components of `A *ᵥ v` is the trace contraction
of `A` with the directional Jacobian of `v`, plus the column-divergence term of `A` applied to
`v`. In particular, the latter term vanishes when every column has zero directional divergence.

The field and the directions may be defined on any normed vector space over a nontrivially
normed field. Neither completeness nor independence of the directions is required.
-/

public section

namespace Matrix

variable {ι E 𝕜 : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The componentwise divergence product rule for a matrix field times a vector field. -/
theorem sum_fderiv_mulVec_eq_trace_add
    (A : E → Matrix ι ι 𝕜) (v : E → ι → 𝕜) (e : ι → E) (x : E)
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y ↦ A y i j) x)
    (hv : ∀ j, DifferentiableAt 𝕜 (fun y ↦ v y j) x) :
    ∑ i, fderiv 𝕜 (fun y ↦ (A y *ᵥ v y) i) x (e i) =
      (A x * Matrix.of (fun j i ↦ fderiv 𝕜 (fun y ↦ v y j) x (e i))).trace +
        ∑ j, v x j * (∑ i, fderiv 𝕜 (fun y ↦ A y i j) x (e i)) := by
  have hdc (i : ι) : fderiv 𝕜 (fun y ↦ (A y *ᵥ v y) i) x (e i) =
      ∑ j, (A x i j * fderiv 𝕜 (fun y ↦ v y j) x (e i) +
        v x j * fderiv 𝕜 (fun y ↦ A y i j) x (e i)) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y ↦ A y i j * v y j)
      (fun j _ ↦ (hA i j).mul (hv j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hv j)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [hdc, Finset.sum_add_distrib]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- If every column of a matrix field has zero directional divergence, the divergence of its
flux is the trace contraction with the directional Jacobian of the vector field. -/
theorem sum_fderiv_mulVec_eq_trace_of_sum_fderiv_eq_zero
    (A : E → Matrix ι ι 𝕜) (v : E → ι → 𝕜) (e : ι → E) (x : E)
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y ↦ A y i j) x)
    (hv : ∀ j, DifferentiableAt 𝕜 (fun y ↦ v y j) x)
    (hdiv : ∀ j, ∑ i, fderiv 𝕜 (fun y ↦ A y i j) x (e i) = 0) :
    ∑ i, fderiv 𝕜 (fun y ↦ (A y *ᵥ v y) i) x (e i) =
      (A x * Matrix.of (fun j i ↦ fderiv 𝕜 (fun y ↦ v y j) x (e i))).trace := by
  rw [sum_fderiv_mulVec_eq_trace_add A v e x hA hv]
  simp only [hdiv, mul_zero, Finset.sum_const_zero, add_zero]

end Matrix
