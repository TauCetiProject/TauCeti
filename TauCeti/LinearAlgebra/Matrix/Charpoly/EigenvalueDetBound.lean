/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Eigenvalue-based determinant norm bounds and diagonal operator combinations

Over an algebraically closed field `K` equipped with a ring homomorphism `ι : K →+* E` into a
normed field `E`, this file proves a lower bound on the norm of `c ^ finrank K Z * ι Λ.det` from
a uniform lower bound on `‖c * ι μ‖₊` over all eigenvalues `μ` of `Λ`, lifts linear combinations
of diagonal operators in a basis to a single diagonal operator, and expresses `(1 - y • A).det`
as the product `∏ (1 - y * μ)` over the roots of `A.charpoly`.

## Main results

* `TauCeti.pow_finrank_le_nnnorm_det`: if `ε ≤ ‖c * ι μ‖₊` for every eigenvalue `μ` of
  `Λ : Module.End K Z`, then `ε ^ Module.finrank K Z ≤ ‖c ^ Module.finrank K Z * ι Λ.det‖₊`.
* `TauCeti.toLin_diagonal_sum_eq`: `∑ p, d p • Matrix.toLin b b (diagonal (l p))` equals
  `Matrix.toLin b b (diagonal (fun k ↦ ∑ p, d p * l p k))`.
* `TauCeti.det_one_sub_smul_eq_prod_roots`: for a square matrix `A` over an algebraically closed
  field `K` and `y : K`, `(1 - y • A).det = (A.charpoly.roots.map fun μ ↦ 1 - y * μ).prod`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/HeckeStrings.lean`
(`New.Selmer.pow_finrank_le_nnnorm_det`, `New.Selmer.exists_diagonal_mem_norm_ge`,
`New.Selmer.exists_eventually_one_le_norm_eval_charpoly`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Module Matrix Polynomial

/-- Let `K` be an algebraically closed field, `E` a normed field, `ι : K →+* E` a ring
homomorphism, and `Λ : Module.End K Z` an endomorphism of a finite-dimensional `K`-vector space
`Z`. If `ε ≤ ‖c * ι μ‖₊` for every eigenvalue `μ` of `Λ`, then
`ε ^ finrank K Z ≤ ‖c ^ finrank K Z * ι (LinearMap.det Λ)‖₊`. -/
theorem pow_finrank_le_nnnorm_det {K E Z : Type*} [Field K] [IsAlgClosed K] [NormedField E]
    [AddCommGroup Z] [Module K Z] [Module.Finite K Z] (ι : K →+* E) (Λ : Module.End K Z) (c : E)
    {ε : NNReal} (h_eig : ∀ μ : K, Λ.HasEigenvalue μ → ε ≤ ‖c * ι μ‖₊) :
    ε ^ finrank K Z ≤ ‖c ^ finrank K Z * ι (LinearMap.det Λ)‖₊ := by
  have h_card : Multiset.card Λ.charpoly.roots = finrank K Z := by
    rw [IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree]
  have h_det : c ^ finrank K Z * ι (LinearMap.det Λ) =
      (Λ.charpoly.roots.map fun μ ↦ c * ι μ).prod := by
    rw [Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _), map_multiset_prod,
      Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, h_card]
  have h_norm : ‖(Λ.charpoly.roots.map fun μ ↦ c * ι μ).prod‖₊ =
      (Λ.charpoly.roots.map fun μ ↦ ‖c * ι μ‖₊).prod := by
    simp
  rw [h_det, h_norm, ← h_card, ← Multiset.card_map fun μ ↦ ‖c * ι μ‖₊]
  refine Multiset.pow_card_le_prod (Multiset.forall_mem_map_iff.mpr fun μ hμ ↦ h_eig μ ?_)
  exact (Module.End.hasEigenvalue_iff_isRoot_charpoly Λ μ).mpr (Polynomial.isRoot_of_mem_roots hμ)

/-- A linear combination of operators that are diagonal in a basis `b` is again diagonal in `b`,
with eigenvalues given by the corresponding linear combination of the diagonal entries. -/
theorem toLin_diagonal_sum_eq {R Z ι κ : Type*} [CommRing R] [AddCommGroup Z] [Module R Z]
    [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Basis ι R Z) (d : κ → R) (l : κ → ι → R) :
    ∑ p : κ, d p • Matrix.toLin b b (diagonal (l p)) =
      Matrix.toLin b b (diagonal fun k ↦ ∑ p : κ, d p * l p k) := by
  refine b.ext fun k ↦ ?_
  simp [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.toLin_self, diagonal_apply,
    Finset.sum_smul, smul_smul]

/-- For a square matrix `A` over an algebraically closed field `K` and `y : K`, the determinant of
`1 - y • A` equals the product of `1 - y * μ` over the multiset of roots of `A.charpoly`. -/
theorem det_one_sub_smul_eq_prod_roots {K n : Type*} [Field K] [IsAlgClosed K] [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (y : K) :
    (1 - y • A).det = (A.charpoly.roots.map fun μ ↦ 1 - y * μ).prod := by
  have h_split : A.charpoly.Splits := IsAlgClosed.splits _
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have h_card : A.charpoly.roots.card = Fintype.card n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]
  have h_eval : (1 - y • A).det = y ^ Fintype.card n * A.charpoly.eval y⁻¹ := by
    have h_char : A.charpoly.eval y⁻¹ = (y⁻¹ • (1 : Matrix n n K) - A).det := by
      rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i j
      simp [Matrix.charmatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.diagonal_apply, apply_ite]
    have h_mat : (1 - y • A) = y • (y⁻¹ • (1 : Matrix n n K) - A) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hy, one_smul]
    rw [h_char, h_mat, det_smul]
  rw [h_eval]
  nth_rw 1 [h_split.eq_prod_roots]
  rw [Polynomial.eval_mul, Polynomial.eval_C, A.charpoly_monic.leadingCoeff, one_mul,
    Polynomial.eval_multiset_prod, Multiset.map_map, ← h_card, ← Multiset.prod_replicate,
    ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun μ _ ↦ ?_
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    mul_sub, mul_inv_cancel₀ hy]

end TauCeti
