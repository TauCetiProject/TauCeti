/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Convex.SpectralFunction
public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction
public import TauCeti.Analysis.Matrix.MinkowskiDeterminant
public import TauCeti.Data.Fin.Basic

/-!
# Values and concavity of spectral functions on `2 × 2` matrices

The spectral function of `f : ℝⁿ → ℝ` sends a Hermitian matrix `A` to `f(λ(A))`, for `λ(A)` the
decreasingly sorted eigenvalue vector `Matrix.IsHermitian.eigenvalues₀`. These examples evaluate
spectral functions on diagonal `2 × 2` matrices and test the hypotheses of the concavity theorem
`Matrix.concaveOn_spectralFunction`.

* The geometric mean `σ₂^{1/2}` gives `det^{1/2}`. At `diag(4, 1)` and `diag(1, 4)` it is `2`,
  and at their midpoint `diag(5/2, 5/2)` it is `5/2 ≥ 2`. For real matrices of any size, the
  concavity of `A ↦ (∏ λ(A))^{1/n}` on the positive semidefinite matrices is
  `Matrix.concaveOn_det_rpow`.
* A symmetric but non-convex open cone `Γ ⊆ ℝ²` whose spectral domain is not convex: it contains
  `diag(1, -2/5)` and `diag(1, 1/10)` but not their midpoint.
* `min` is symmetric and concave, so its spectral function `λ₂` is concave. The convex `max` is the
  negative control: `λ₁` is `1` at `diag(1, 0)` and `diag(0, 1)` and `1/2` at their midpoint.
* On `{T | T > -1}`, a domain that is not a cone, `μ ↦ ∑ log(1 + μᵢ)` has spectral function
  `log det(1 + T)`. At `diag(-1/2, 1)` and `diag(1, -1/2)` it is `0`, and at their midpoint it is
  `2 log(5/4) > 0`, consistent with concavity.
* Ellipticity is needed for monotonicity: the spectral function of `f = -σ₁` decreases along
  `diag(1, 0) ≤ diag(2, 0)`.
-/

public section

open Matrix
open scoped ComplexOrder

namespace TauCeti.SpectralFunctionExamples

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The geometric mean and `det^{1/n}` -/

/-- The geometric mean `σ₂^{1/2}` on `ℝ²`. -/
noncomputable def geomMean (μ : Fin 2 → ℝ) : ℝ := (μ 0 * μ 1) ^ (2⁻¹ : ℝ)

/-- The spectral function of the geometric mean is `det^{1/2}`. -/
theorem geomMean_eigenvalues₀ {A : Matrix (Fin 2) (Fin 2) 𝕜} (hA : A.IsHermitian) :
    geomMean hA.eigenvalues₀ = RCLike.re A.det ^ (2⁻¹ : ℝ) := by
  rw [hA.det_eq_prod_eigenvalues₀]
  unfold geomMean
  -- `Fintype.card (Fin 2)` reduces to `2`, exposing the product to `Fin.prod_univ_two`.
  change _ = RCLike.re (∏ k : Fin 2, _) ^ _
  rw [Fin.prod_univ_two, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- `det^{1/2}` is `2` at `diag(4, 1)` and at `diag(1, 4)`, and `5/2` at their midpoint
`diag(5/2, 5/2)`. -/
theorem geomMean_diagonal_four_one (hA : (diagonal ![((4 : ℝ) : 𝕜), (1 : ℝ)]).IsHermitian)
    (hB : (diagonal ![((1 : ℝ) : 𝕜), (4 : ℝ)]).IsHermitian)
    (hM : (diagonal ![((5 / 2 : ℝ) : 𝕜), (5 / 2 : ℝ)]).IsHermitian) :
    geomMean hA.eigenvalues₀ = 2 ∧ geomMean hB.eigenvalues₀ = 2 ∧
      geomMean hM.eigenvalues₀ = 5 / 2 := by
  have h4 : (4 : ℝ) ^ (2⁻¹ : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simpa using Real.pow_rpow_inv_natCast (x := 2) (n := 2) (by norm_num) two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [hA.eigenvalues₀_diagonal_two (by norm_num), geomMean]
    simpa using h4
  · rw [hB.eigenvalues₀_diagonal_two_swap (by norm_num), geomMean]
    simpa using h4
  · rw [hM.eigenvalues₀_diagonal_two le_rfl, geomMean]
    simpa [← sq] using Real.pow_rpow_inv_natCast (x := 5 / 2) (n := 2) (by norm_num) two_ne_zero

/-- The midpoint of `diag(4, 1)` and `diag(1, 4)` is `diag(5/2, 5/2)`. -/
theorem midpoint_diagonal_four_one :
    (2⁻¹ : ℝ) • (diagonal ![(4 : ℝ), 1] + diagonal ![1, 4]) = diagonal ![5 / 2, 5 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- **Agreement with the Minkowski determinant theorem.** For real `n × n` matrices, the spectral
function `A ↦ (∏ λ(A))^{1/n}` of the geometric mean is `det^{1/n}`, and it is concave on the
positive semidefinite matrices by `Matrix.concaveOn_det_rpow`. -/
theorem concaveOn_prod_eigenvalues₀_rpow {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ConcaveOn ℝ {A : selfAdjoint.submodule ℝ (Matrix ι ι ℝ) | (A : Matrix ι ι ℝ).PosSemidef}
      fun A ↦ (∏ k, A.property.isHermitian.eigenvalues₀ k) ^ (Fintype.card ι : ℝ)⁻¹ := by
  have h := (Matrix.concaveOn_det_rpow (n := ι)).comp_linearMap
    (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)).subtype
  convert h using 1
  · ext A
    simp
  funext A
  simp [A.property.isHermitian.det_eq_prod_eigenvalues₀]

/-- At `diag(1, 0)` and `diag(0, 1)` the geometric mean of the sorted eigenvalues is `0`, and at
their midpoint `diag(1/2, 1/2)` it is `1/2`. -/
theorem geomMean_diagonal_one_zero (hA : (diagonal ![((1 : ℝ) : 𝕜), (0 : ℝ)]).IsHermitian)
    (hB : (diagonal ![((0 : ℝ) : 𝕜), (1 : ℝ)]).IsHermitian)
    (hM : (diagonal ![((1 / 2 : ℝ) : 𝕜), (1 / 2 : ℝ)]).IsHermitian) :
    geomMean hA.eigenvalues₀ = 0 ∧ geomMean hB.eigenvalues₀ = 0 ∧
      geomMean hM.eigenvalues₀ = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hA.eigenvalues₀_diagonal_two (by norm_num), geomMean]
    simp
  · rw [hB.eigenvalues₀_diagonal_two_swap (by norm_num), geomMean]
    simp
  · rw [hM.eigenvalues₀_diagonal_two le_rfl, geomMean]
    simpa [← sq] using Real.pow_rpow_inv_natCast (x := 1 / 2) (n := 2) (by norm_num) two_ne_zero

/-! ### A symmetric cone that is not convex -/

/-- Membership in a symmetric open cone in `ℝ²` that is not convex: the union of the positive
quadrant `Γ₂`, the wedge `{μ₁ > 0, -μ₁/2 < μ₂ < -μ₁/3}` and its mirror image. -/
def InNonconvexCone (μ : Fin 2 → ℝ) : Prop :=
  (0 < μ 0 ∧ 0 < μ 1) ∨ (0 < μ 0 ∧ -(μ 0 / 2) < μ 1 ∧ μ 1 < -(μ 0 / 3)) ∨
    (0 < μ 1 ∧ -(μ 1 / 2) < μ 0 ∧ μ 0 < -(μ 1 / 3))

/-- The cone `InNonconvexCone` is invariant under permutations of the coordinates. -/
theorem inNonconvexCone_comp_perm (σ : Equiv.Perm (Fin 2)) (μ : Fin 2 → ℝ) :
    InNonconvexCone (μ ∘ σ) = InNonconvexCone μ :=
  σ.apply_comp_fin_two (fun a b ↦ by
    simp only [InNonconvexCone, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact propext (by tauto)) μ

/-- **Convexity of `Γ` is necessary for the convexity of the spectral domain.** The real symmetric
`2 × 2` matrices with eigenvalue vector in the symmetric cone `InNonconvexCone` do not form a
convex set: the set contains `diag(1, -2/5)` and `diag(1, 1/10)` but not their midpoint
`diag(1, -3/20)`. -/
theorem not_convex_setOf_inNonconvexCone_eigenvalues₀ :
    ¬ Convex ℝ {A : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) |
      InNonconvexCone A.property.isHermitian.eigenvalues₀} := by
  intro hconv
  let A : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨diagonal ![1, -(2 / 5)], isHermitian_diagonal _⟩
  let B : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨diagonal ![1, 1 / 10], isHermitian_diagonal _⟩
  have hA : InNonconvexCone A.property.isHermitian.eigenvalues₀ := by
    rw [IsHermitian.eigenvalues₀_diagonal_two (𝕜 := ℝ) (a := 1) (b := -(2 / 5)) (by norm_num)]
    norm_num [InNonconvexCone]
  have hB : InNonconvexCone B.property.isHermitian.eigenvalues₀ := by
    rw [IsHermitian.eigenvalues₀_diagonal_two (𝕜 := ℝ) (a := 1) (b := 1 / 10) (by norm_num)]
    norm_num [InNonconvexCone]
  have hM : InNonconvexCone ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).property.isHermitian.eigenvalues₀ :=
    hconv hA hB (by norm_num) (by norm_num) (by norm_num)
  have hmid : ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B : Matrix (Fin 2) (Fin 2) ℝ) =
      diagonal ![1, -(3 / 20)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B] <;> norm_num
  rw [IsHermitian.eigenvalues₀_congr hmid _ (isHermitian_diagonal _),
    IsHermitian.eigenvalues₀_diagonal_two (𝕜 := ℝ) (a := 1) (b := -(3 / 20)) (by norm_num)] at hM
  norm_num [InNonconvexCone] at hM

/-! ### `min` and `max` -/

/-- The smaller coordinate of a vector in `ℝ²`. -/
def minPair (μ : Fin 2 → ℝ) : ℝ := min (μ 0) (μ 1)

/-- The larger coordinate of a vector in `ℝ²`. -/
def maxPair (μ : Fin 2 → ℝ) : ℝ := max (μ 0) (μ 1)

/-- **The smallest eigenvalue is concave**: `min` is symmetric and concave on `ℝ²`, so its
spectral function `λ₂` is concave on the Hermitian `2 × 2` matrices. -/
theorem concaveOn_minPair_eigenvalues₀ :
    ConcaveOn ℝ (Set.univ : Set (selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) 𝕜)))
      fun A ↦ minPair A.property.isHermitian.eigenvalues₀ := by
  simpa using Matrix.concaveOn_spectralFunction (𝕜 := 𝕜) (ι := Fin 2) (Γ := Set.univ)
    (fun _ _ _ ↦ Set.mem_univ _) (f := minPair)
    (fun σ μ _ ↦ σ.apply_comp_fin_two (fun a b ↦ by simp [minPair, min_comm]) μ)
    ((((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).concaveOn convex_univ).inf
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).concaveOn convex_univ)).congr
        fun μ _ ↦ by simp [minPair])

/-- **Concavity of `f` is used.** The convex symmetric function `max` has spectral function `λ₁`,
which is `1` at `diag(1, 0)` and `diag(0, 1)` but `1/2` at their midpoint `diag(1/2, 1/2)`, while
`min` gives `0`, `0` and `1/2`. -/
theorem maxPair_minPair_diagonal_one_zero
    (hA : (diagonal ![((1 : ℝ) : 𝕜), (0 : ℝ)]).IsHermitian)
    (hB : (diagonal ![((0 : ℝ) : 𝕜), (1 : ℝ)]).IsHermitian)
    (hM : (diagonal ![((1 / 2 : ℝ) : 𝕜), (1 / 2 : ℝ)]).IsHermitian) :
    (maxPair hA.eigenvalues₀ = 1 ∧ maxPair hB.eigenvalues₀ = 1 ∧ maxPair hM.eigenvalues₀ = 1 / 2) ∧
      (minPair hA.eigenvalues₀ = 0 ∧ minPair hB.eigenvalues₀ = 0 ∧
        minPair hM.eigenvalues₀ = 1 / 2) := by
  rw [hA.eigenvalues₀_diagonal_two (by norm_num), hB.eigenvalues₀_diagonal_two_swap (by norm_num),
    hM.eigenvalues₀_diagonal_two le_rfl]
  norm_num [maxPair, minPair]

/-! ### `log det(1 + T)` -/

/-- **`log det(1 + T)` as a spectral function.** On Hermitian matrices whose eigenvalues exceed
`-1`, the spectral function of `μ ↦ ∑ log(1 + μᵢ)` is `log det(1 + T)`. The domain
`{μ | ∀ i, -1 < μᵢ}` is open, convex and symmetric but not a cone. -/
theorem sum_log_one_add_eigenvalues₀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hA1 : ∀ k, -1 < hA.eigenvalues₀ k) :
    ∑ k, Real.log (1 + hA.eigenvalues₀ k) = Real.log (RCLike.re (A + 1).det) := by
  have h1 : (A + (1 : ℝ) • (1 : Matrix ι ι 𝕜)).IsHermitian := by
    rw [one_smul]
    exact hA.add isHermitian_one
  have hdet := h1.det_eq_prod_eigenvalues₀
  rw [hA.eigenvalues₀_add_smul_one 1 h1, one_smul] at hdet
  rw [hdet, ← RCLike.ofReal_prod, RCLike.ofReal_re, Real.log_prod fun k _ ↦ by
    simp only [Pi.add_apply]
    linarith [hA1 k]]
  simp [add_comm]

/-- The function `μ ↦ log(1 + μ₁) + log(1 + μ₂)` on `ℝ²`. -/
noncomputable def logOneAdd (μ : Fin 2 → ℝ) : ℝ := Real.log (1 + μ 0) + Real.log (1 + μ 1)

/-- `log det(1 + T)` is `0` at `diag(-1/2, 1)` and at `diag(1, -1/2)`, and `2 log(5/4) > 0` at
their midpoint `diag(1/4, 1/4)`, as concavity requires. -/
theorem logOneAdd_diagonal (hA : (diagonal ![((-(1 / 2) : ℝ) : 𝕜), (1 : ℝ)]).IsHermitian)
    (hB : (diagonal ![((1 : ℝ) : 𝕜), (-(1 / 2) : ℝ)]).IsHermitian)
    (hM : (diagonal ![((1 / 4 : ℝ) : 𝕜), (1 / 4 : ℝ)]).IsHermitian) :
    logOneAdd hA.eigenvalues₀ = 0 ∧ logOneAdd hB.eigenvalues₀ = 0 ∧
      logOneAdd hM.eigenvalues₀ = 2 * Real.log (5 / 4) ∧ 0 < 2 * Real.log (5 / 4) := by
  have h0 : Real.log 2 + Real.log (1 / 2) = 0 := by
    rw [one_div, Real.log_inv, add_neg_cancel]
  rw [hA.eigenvalues₀_diagonal_two_swap (by norm_num), hB.eigenvalues₀_diagonal_two (by norm_num),
    hM.eigenvalues₀_diagonal_two le_rfl]
  refine ⟨?_, ?_, ?_, mul_pos two_pos (Real.log_pos (by norm_num))⟩ <;>
    norm_num [logOneAdd] <;> linarith [h0]

/-! ### Ellipticity -/

/-- **Ellipticity is needed for monotonicity.** For the symmetric, concave, non-elliptic
`f = -σ₁`, the spectral function `T ↦ -tr T` decreases from `-1` to `-2` along
`diag(1, 0) ≤ diag(2, 0)`. -/
theorem neg_sum_eigenvalues₀_diagonal (hS : (diagonal ![(1 : 𝕜), 0]).IsHermitian)
    (hT : (diagonal ![(2 : 𝕜), 0]).IsHermitian) :
    (diagonal ![(2 : 𝕜), 0] - diagonal ![1, 0]).PosSemidef ∧
      -∑ k, hS.eigenvalues₀ k = -1 ∧ -∑ k, hT.eigenvalues₀ k = -2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [diagonal_sub]
    refine PosSemidef.diagonal fun i ↦ ?_
    fin_cases i <;> norm_num
  · rw [hS.sum_eigenvalues₀_eq_re_trace, trace_diagonal, Fin.sum_univ_two]
    simp
  · rw [hT.sum_eigenvalues₀_eq_re_trace, trace_diagonal, Fin.sum_univ_two]
    simp

end TauCeti.SpectralFunctionExamples
