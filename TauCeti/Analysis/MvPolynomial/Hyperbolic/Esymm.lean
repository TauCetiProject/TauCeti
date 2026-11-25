/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PDeriv

/-!
# Hyperbolicity of the elementary symmetric polynomials and their Gårding cones

Let `σ` be a finite type with `n` elements and `e = (1, …, 1)`. For `k ≤ n`, the elementary
symmetric polynomial `σ_k` is hyperbolic of degree `k` in the direction `e`
(`MvPolynomial.isHyperbolic_esymm`), and its Gårding cone is

`Γ(σ_k, e) = Γ_k = {λ | σ_1(λ) > 0, …, σ_k(λ) > 0}`

(`MvPolynomial.gardingCone_esymm`). For `k = 0` both sides are the whole space: `σ_0 = 1` is a
positive constant and the conditions are vacuous.

The proof starts from `σ_n = X₁ ⋯ X_n`, which is hyperbolic in the direction `e` with the open
positive orthant as Gårding cone (`MvPolynomial.isHyperbolic_esymm_card`,
`MvPolynomial.gardingCone_esymm_card`), and differentiates in the direction `e`:
`D_e σ_{k+1} = Σᵢ ∂ᵢ σ_{k+1} = (n − k)·σ_k` (`TauCeti.sum_pderiv_esymm_succ`), so Rolle's
theorem in the form
`MvPolynomial.IsHyperbolic.sum_smul_pderiv` passes hyperbolicity from `σ_{k+1}` to `σ_k`, and the
Gårding cones are nested, `Γ(σ_{k+1}, e) ⊆ Γ(σ_k, e)`
(`MvPolynomial.gardingCone_esymm_subset`). Every `σ_j` is positive on its own cone, which
gives `Γ(σ_k, e) ⊆ Γ_k`. Conversely, for `λ ∈ Γ_k` and `t ≥ 0` every term of the shift expansion
`σ_k(λ + t e) = Σ_{j ≤ k} binom(n − j, k − j) σ_j(λ) t^{k − j}` is nonnegative and the term
`j = k` is `σ_k(λ) > 0`.

## Main results

* `MvPolynomial.isHyperbolic_esymm_card`, `MvPolynomial.gardingCone_esymm_card`: `σ_n` is
  hyperbolic in the direction `e`, with the open positive orthant as Gårding cone.
* `MvPolynomial.isHyperbolic_esymm`: `σ_k` is hyperbolic of degree `k` in the direction `e`, for
  `k ≤ n`.
* `MvPolynomial.gardingCone_esymm_subset`: `Γ(σ_k, e) ⊆ Γ(σ_j, e)` for `j ≤ k`.
* `MvPolynomial.gardingCone_esymm`: `Γ(σ_k, e) = {σ_1 > 0, …, σ_k > 0}`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Finset

namespace MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- The elementary symmetric polynomial `σ_n = X₁ ⋯ X_n` in all `n` variables is hyperbolic of
degree `n` in the direction `e = (1, …, 1)`: `σ_n(x + t • e) = ∏ᵢ (xᵢ + t)`. -/
theorem isHyperbolic_esymm_card :
    IsHyperbolic (esymm σ ℝ (Fintype.card σ)) (Fintype.card σ) 1 where
  isHomogeneous := isHomogeneous_esymm _
  eval_pos := by simp [esymm_card]
  splits x := by
    rw [esymm_card, map_prod]
    exact Polynomial.Splits.prod fun i _ ↦ Polynomial.Splits.of_natDegree_le_one <| by
      simp [add_comm]

/-- The Gårding cone of `σ_n = X₁ ⋯ X_n` in the direction `e = (1, …, 1)` is the open positive
orthant. -/
theorem gardingCone_esymm_card :
    gardingCone (esymm σ ℝ (Fintype.card σ)) 1 = {x | ∀ i, 0 < x i} := by
  ext x
  simp only [mem_gardingCone, esymm_card, map_prod, eval_X, Pi.add_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one, Set.mem_ofPred_eq]
  refine ⟨fun h i ↦ ?_, fun h t ht ↦ Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_⟩
  · by_contra! hi
    exact h (-x i) (by linarith) (Finset.prod_eq_zero (Finset.mem_univ i) (by ring))
  · linarith [h i]

/-- **`σ_k` is hyperbolic in the direction `e`.** For `k ≤ n`, the elementary symmetric
polynomial `σ_k` in `n` variables is hyperbolic of degree `k` in the direction
`e = (1, …, 1)`. -/
theorem isHyperbolic_esymm {k : ℕ} (hk : k ≤ Fintype.card σ) :
    IsHyperbolic (esymm σ ℝ k) k 1 := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' hk
  induction j generalizing k with
  | zero =>
    rw [zero_add] at hj
    rw [← hj]
    exact isHyperbolic_esymm_card
  | succ j ih =>
    have h := (ih (k := k + 1) (by omega) (by omega)).sum_smul_pderiv (Nat.le_add_left 1 k)
    simp only [Pi.one_apply, one_smul, TauCeti.sum_pderiv_esymm_succ, Nat.add_sub_cancel] at h
    exact (isHyperbolic_smul_left_iff (Nat.cast_pos.2 (by omega))).1 h

/-- `Γ(σ_{k+1}, e) ⊆ Γ(σ_k, e)` for `k < n`, by Rolle's theorem. -/
private theorem gardingCone_esymm_succ_subset_of_lt {k : ℕ} (hk : k < Fintype.card σ) :
    gardingCone (esymm σ ℝ (k + 1)) 1 ⊆ gardingCone (esymm σ ℝ k) 1 := by
  have h := (isHyperbolic_esymm (σ := σ) hk).gardingCone_subset_sum_smul_pderiv
    (Nat.le_add_left 1 k)
  simp only [Pi.one_apply, one_smul, TauCeti.sum_pderiv_esymm_succ] at h
  rwa [gardingCone_smul_left (Nat.cast_ne_zero.2 (Nat.sub_ne_zero_of_lt hk))] at h

/-- `Γ(σ_k, e) ⊆ Γ(σ_j, e)` for `j ≤ k ≤ n`. -/
private theorem gardingCone_esymm_subset_of_le {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ Fintype.card σ) :
    gardingCone (esymm σ ℝ k) 1 ⊆ gardingCone (esymm σ ℝ j) 1 := by
  induction k, hjk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih => exact (gardingCone_esymm_succ_subset_of_lt hk).trans (ih (by omega))

/-- **The Gårding cone of `σ_k` is `Γ_k`.** `Γ(σ_k, e)` is the set of points where
`σ_1, …, σ_k` are positive. For `k > n` both sides are empty, since `σ_k = 0`. -/
theorem gardingCone_esymm (k : ℕ) :
    gardingCone (esymm σ ℝ k) 1 = {x | ∀ j, 1 ≤ j → j ≤ k → 0 < eval x (esymm σ ℝ j)} := by
  by_cases hk : k ≤ Fintype.card σ
  swap
  · -- Above the number of variables `σ_k` vanishes, and both sides are empty.
    have hz : esymm σ ℝ k = 0 := by
      rw [esymm_eq_multiset_esymm]
      exact Multiset.esymm_of_card_lt (by simpa using not_le.1 hk)
    have h0 (y : σ → ℝ) : eval y (esymm σ ℝ k) = 0 := by rw [hz, map_zero]
    ext x
    simp only [mem_gardingCone, Set.mem_ofPred_eq]
    refine ⟨fun h ↦ (h 0 le_rfl (by simpa using h0 _)).elim, fun h ↦ ?_⟩
    exact ((h k (by omega) le_rfl).ne' (h0 x)).elim
  ext x
  refine ⟨fun hx j _ hjk ↦ ?_, fun hx ↦ mem_gardingCone.2 fun t ht ↦ ?_⟩
  · have hj := isHyperbolic_esymm (σ := σ) (hjk.trans hk)
    exact eval_pos_of_mem_gardingCone hj.isHomogeneous hj.eval_pos
      (gardingCone_esymm_subset_of_le hjk hk hx)
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [esymm_zero]
    -- Every term of the shift expansion is nonnegative, and the last one is positive.
    rw [TauCeti.eval_add_smul_one_esymm]
    refine ne_of_gt (lt_of_lt_of_le ?_ (single_le_sum (fun j hj ↦ ?_) (self_mem_range_succ k)))
    · simpa using hx k hk0 le_rfl
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [esymm_zero, map_one, mul_one]
        positivity
      · have := hx j hj0 (Nat.lt_succ_iff.1 (mem_range.1 hj))
        positivity

/-- **The Gårding cones of the `σ_k` are nested**: `Γ(σ_k, e) ⊆ Γ(σ_j, e)` for `j ≤ k`. -/
theorem gardingCone_esymm_subset {j k : ℕ} (hjk : j ≤ k) :
    gardingCone (esymm σ ℝ k) 1 ⊆ gardingCone (esymm σ ℝ j) 1 := by
  rw [gardingCone_esymm, gardingCone_esymm]
  exact fun x hx i hi1 hij ↦ hx i hi1 (hij.trans hjk)

end MvPolynomial
