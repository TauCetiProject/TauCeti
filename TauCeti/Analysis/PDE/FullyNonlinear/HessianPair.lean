/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FullyNonlinear.HessianCone
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.MvPolynomial.ElementarySymmetric
import TauCeti.Analysis.PDE.FullyNonlinear.HessianCone.Concave
import TauCeti.Analysis.PDE.FullyNonlinear.HessianCone.Derivative

/-!
# The Hessian pair `(σ_k^{1/k}, Γ_k)`

For `1 ≤ k ≤ n`, the function `σ_k^{1/k}` on the Hessian cone `Γ_k ⊆ ℝⁿ` is a concave admissible
pair (`TauCeti.isAdmissiblePair_esymm_rpow`, `TauCeti.concaveOn_esymm_rpow`) with structural
constant `γ = (binom(n, k)^{1/k} / n)ⁿ` (`TauCeti.hasStructuralConstant_esymm_rpow`).

* Smoothness: `σ_k` is a polynomial, positive on `Γ_k`, so its `k`-th root is smooth there.
* Symmetry and homogeneity: `σ_k` is symmetric and homogeneous of degree `k`.
* Ellipticity: `∂_j σ_k^{1/k} = (1/k) σ_k^{1/k - 1} σ_{k-1;j}`
  (`TauCeti.fderiv_esymm_rpow_single`), and `σ_{k-1;j} > 0` on `Γ_k`
  (`TauCeti.eval_update_zero_esymm_pos_of_mem_hessianCone`).
* Structural constant: by Maclaurin's inequality `S_n^{1/n} ≤ S_k^{1/k}` on the positive orthant
  (`TauCeti.normalizedEsymm_rpow_le`), where `S_j = σ_j / binom(n, j)` and `S_n = ∏_i μ_i`,
  `σ_k(μ)^{1/k} ≥ binom(n, k)^{1/k} (∏_i μ_i)^{1/n}`; Lemma 4 of Guo–Phong–Tong
  (`TauCeti.IsAdmissiblePair.hasStructuralConstant_pow_of_concaveOn`) turns this lower bound
  into the structural constant.

The constant is sharp: at `e = (1, …, 1)` every partial derivative of `σ_k^{1/k}` equals
`binom(n, k)^{1/k} / n` (`TauCeti.fderiv_esymm_rpow_one_single`), so
`∏_j ∂_j σ_k^{1/k}(e) = γ` (`TauCeti.prod_fderiv_esymm_rpow_one_single`). This follows from
Euler's identity and the symmetry of the partial derivatives at the symmetric point `e`
(`TauCeti.IsAdmissiblePair.fderiv_one_single`), valid for every admissible pair.

## References

* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), §1 and Lemma 4.
* B. Guo and D. H. Phong, *On L∞ estimates for fully nonlinear partial differential equations*,
  Ann. of Math. 200 (2024), arXiv:2204.12549, the examples after (1.2).
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {n k : ℕ}

/-- `σ_n(μ) = ∏_i μ_i` on `ℝⁿ`. -/
theorem eval_esymm_card (μ : Fin n → ℝ) : eval μ (esymm (Fin n) ℝ n) = ∏ i, μ i := by
  have h : powersetCard n (univ : Finset (Fin n)) = {univ} := by
    simpa using powersetCard_self (univ : Finset (Fin n))
  simp [esymm, h]

/-- `σ_k > 0` on `Γ_k` for `k ≥ 1`. -/
theorem eval_esymm_pos_of_mem_hessianCone {μ : Fin n → ℝ} (hμ : μ ∈ hessianCone n k)
    (hk : 1 ≤ k) : 0 < eval μ (esymm (Fin n) ℝ k) :=
  mem_hessianCone.1 hμ k (mem_Icc.2 ⟨hk, le_rfl⟩)

/-- `σ_k` is symmetric: `σ_k(μ ∘ σ) = σ_k(μ)`. -/
theorem eval_comp_perm_esymm (σ : Equiv.Perm (Fin n)) (μ : Fin n → ℝ) (k : ℕ) :
    eval (μ ∘ σ) (esymm (Fin n) ℝ k) = eval μ (esymm (Fin n) ℝ k) := by
  rw [← eval_rename, esymm_isSymmetric (Fin n) ℝ k σ]

/-- `σ_k(t μ) = t^k σ_k(μ)`. -/
theorem eval_smul_esymm (t : ℝ) (μ : Fin n → ℝ) (k : ℕ) :
    eval (t • μ) (esymm (Fin n) ℝ k) = t ^ k * eval μ (esymm (Fin n) ℝ k) :=
  (isHomogeneous_esymm (σ := Fin n) (R := ℝ) k).eval_smul t μ

/-- **The partial derivatives of `σ_{k+1}^{1/(k+1)}`** at a point where `σ_{k+1} > 0`:
`∂_j σ_{k+1}^{1/(k+1)} = (1/(k+1)) σ_{k+1}^{1/(k+1) - 1} σ_{k;j}`. -/
theorem fderiv_esymm_rpow_single {μ : Fin n → ℝ} (hμ : 0 < eval μ (esymm (Fin n) ℝ (k + 1)))
    (j : Fin n) :
    fderiv ℝ (fun ν ↦ eval ν (esymm (Fin n) ℝ (k + 1)) ^ ((k + 1 : ℕ) : ℝ)⁻¹) μ (Pi.single j 1) =
      ((k + 1 : ℕ) : ℝ)⁻¹ * eval μ (esymm (Fin n) ℝ (k + 1)) ^ (((k + 1 : ℕ) : ℝ)⁻¹ - 1) *
        eval (Function.update μ j 0) (esymm (Fin n) ℝ k) := by
  rw [((hasFDerivAt_eval_esymm_succ μ k).rpow_const (Or.inl hμ.ne')).fderiv]
  simp [Pi.single_apply, mul_assoc]

/-- `σ_k^{1/k}` is smooth on `Γ_k`. -/
theorem contDiffOn_esymm_rpow (n k : ℕ) {m : WithTop ℕ∞} :
    ContDiffOn ℝ m (fun μ ↦ eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹) (hessianCone n k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using contDiffOn_const
  intro μ hμ
  have hpos := eval_esymm_pos_of_mem_hessianCone hμ hk
  have hp : ContDiff ℝ m fun ν : Fin n → ℝ ↦ eval ν (esymm (Fin n) ℝ k) := by
    simpa using (AnalyticOnNhd.eval_continuousLinearMap'
      (fun i ↦ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i)
      (esymm (Fin n) ℝ k)).contDiff (n := m)
  exact (hp.contDiffAt.rpow_const_of_ne hpos.ne').contDiffWithinAt

/-- **The Hessian pair** `(σ_k^{1/k}, Γ_k)` is an admissible pair for `1 ≤ k ≤ n`. -/
theorem isAdmissiblePair_esymm_rpow (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsAdmissiblePair (hessianCone n k) fun μ ↦ eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹ where
  isAdmissibleCone := isAdmissibleCone_hessianCone hk hkn
  contDiffOn := contDiffOn_esymm_rpow n k
  apply_comp_perm σ μ _ := by simp only [eval_comp_perm_esymm]
  apply_smul {t} ht μ hμ := by
    rw [eval_smul_esymm, Real.mul_rpow (by positivity)
      (eval_esymm_pos_of_mem_hessianCone hμ hk).le, ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le, mul_inv_cancel₀ (by positivity), Real.rpow_one]
  fderiv_single_pos {μ} hμ j := by
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hpos := eval_esymm_pos_of_mem_hessianCone hμ hk
    rw [fderiv_esymm_rpow_single hpos]
    exact mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hpos _))
      (eval_update_zero_esymm_pos_of_mem_hessianCone hμ j)

/-- **The structural constant of the Hessian pair**: for `1 ≤ k ≤ n`, `(σ_k^{1/k}, Γ_k)`
satisfies the structural condition with constant `γ = (binom(n, k)^{1/k} / n)ⁿ`. -/
theorem hasStructuralConstant_esymm_rpow (hk : 1 ≤ k) (hkn : k ≤ n) :
    HasStructuralConstant (hessianCone n k)
      (fun μ ↦ eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹)
      (((n.choose k : ℝ) ^ (k : ℝ)⁻¹ / n) ^ n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hC : (0 : ℝ) < n.choose k := Nat.cast_pos.2 (Nat.choose_pos hkn)
  simpa using (isAdmissiblePair_esymm_rpow hk hkn).hasStructuralConstant_pow_of_concaveOn
    (concaveOn_esymm_rpow n k) (by positivity) fun μ hμ ↦ by
      -- Maclaurin: `S_n^{1/n} ≤ S_k^{1/k}`, with `S_n = ∏_i μ_i`.
      have hΓ : μ ∈ hessianCone n n := mem_hessianCone_of_pos hμ le_rfl
      have hM := normalizedEsymm_rpow_le hΓ hk hkn
      have hSk : 0 ≤ normalizedEsymm k μ :=
        (normalizedEsymm_pos_of_mem_hessianCone hΓ hkn).le
      rw [normalizedEsymm_def, normalizedEsymm_def, Fintype.card_fin, Nat.choose_self,
        Nat.cast_one, div_one, eval_esymm_card, one_div, one_div] at hM
      have hσ : eval μ (esymm (Fin n) ℝ k) = n.choose k * normalizedEsymm k μ := by
        rw [normalizedEsymm_def, Fintype.card_fin]
        field_simp
      rw [Fintype.card_fin, mul_div_cancel₀ _ hn.ne', hσ, Real.mul_rpow hC.le hSk]
      rw [normalizedEsymm_def, Fintype.card_fin] at hSk ⊢
      exact mul_le_mul_of_nonneg_left hM (by positivity)

/-- `σ_k(e) = binom(n, k)` at `e = (1, …, 1)`. -/
theorem eval_one_esymm (n k : ℕ) : eval 1 (esymm (Fin n) ℝ k) = n.choose k := by
  simp [esymm, card_powersetCard]

/-- **The Hessian constant is attained at `e`**: every partial derivative of `σ_k^{1/k}` at
`e = (1, …, 1)` is `binom(n, k)^{1/k} / n`, for `1 ≤ k ≤ n`. -/
theorem fderiv_esymm_rpow_one_single (hk : 1 ≤ k) (hkn : k ≤ n) (j : Fin n) :
    fderiv ℝ (fun μ ↦ eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹) 1 (Pi.single j 1) =
      (n.choose k : ℝ) ^ (k : ℝ)⁻¹ / n := by
  rw [(isAdmissiblePair_esymm_rpow hk hkn).fderiv_one_single, eval_one_esymm, Fintype.card_fin]

/-- **The structural constant of the Hessian pair is sharp**: `∏_j ∂_j σ_k^{1/k}(e)` is
`(binom(n, k)^{1/k} / n)ⁿ`, for `1 ≤ k ≤ n`. -/
theorem prod_fderiv_esymm_rpow_one_single (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∏ j, fderiv ℝ (fun μ ↦ eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹) 1 (Pi.single j 1) =
      ((n.choose k : ℝ) ^ (k : ℝ)⁻¹ / n) ^ n := by
  simp only [fderiv_esymm_rpow_one_single hk hkn, prod_const, card_univ, Fintype.card_fin]

end TauCeti
