/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.BlockDehomogenize
public import TauCeti.RingTheory.MvPolynomial.FormIndex.Basic
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Dehomogenization of two-coordinate blocks and the weighted index

Over a field `K`, along the affine-chart linear forms `M h = ![-α h, 1]`
(`X (h, 1) - α h X (h, 0)`), the inverse substitution `substFormInv M (fun _ ↦ 1)` sends `X (h, 1)`
to `X (h, 1) + α h X (h, 0)`, so dehomogenizing via `MvPolynomial.blockDehomogenize`
(`TauCeti.RingTheory.MvPolynomial.BlockDehomogenize`) after `substFormInv` computes the Taylor
shift `taylor α (blockDehomogenize P)` (`MvPolynomial.blockDehomogenize_substFormInv`).
Consequently:

* For arbitrary `P`, `formIndex d (fun h ↦ ![-α h, 1]) P ≤ weightedIndex d α (blockDehomogenize P)`
  (`MvPolynomial.formIndex_le_weightedIndex_blockDehomogenize`), because dehomogenization can only
  cancel terms.
* When `P` is multihomogeneous of any multidegree `e`, `substFormInv` preserves multihomogeneity,
  so applying `blockDehomogenize` to `substFormInv (fun h ↦ ![-α h, 1]) (fun _ ↦ 1) P` causes no
  cancellation between distinct monomials, giving the exact equality
  `formIndex d (fun h ↦ ![-α h, 1]) P = weightedIndex d α (blockDehomogenize P)`
  (`MvPolynomial.IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Lemma 7.5.19.
* Ralf Stephan, `DiophantineApproximation/GeneralizedRothLemma.lean` in `rwst/Subspace-Theorems`,
  commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

namespace MvPolynomial

open Finset
open scoped ENNReal

variable {K κ : Type*} [Field K]

/-- Dehomogenizing after `substFormInv` along the affine-chart forms `M h = ![-α h, 1]` computes
the Taylor shift at `α` of `blockDehomogenize P`. -/
theorem blockDehomogenize_substFormInv (α : κ → K) (P : MvPolynomial (κ × Fin 2) K) :
    blockDehomogenize (substFormInv (fun h ↦ ![-α h, 1]) (fun _ ↦ 1) P) =
      taylor α (blockDehomogenize P) := by
  suffices blockDehomogenize.comp (substFormInv (fun h ↦ ![-α h, 1]) (fun _ ↦ 1)) =
      (taylor α).comp blockDehomogenize from AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases i
  · simp
  · have herase : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
    simp only [AlgHom.comp_apply, Fin.mk_one]
    rw [substFormInv_X_self (M := fun h ↦ ![-α h, 1]) (i₀ := fun _ ↦ 1) h]
    simp [herase, taylor_apply]

variable [Fintype κ]

/-- For any polynomial `P`, the index along the forms `X (h, 1) - α h X (h, 0)` is at most the
weighted index at `α` of `blockDehomogenize P`. -/
theorem formIndex_le_weightedIndex_blockDehomogenize (d : κ → ℕ) (α : κ → K)
    (P : MvPolynomial (κ × Fin 2) K) :
    formIndex d (fun h ↦ ![-α h, 1]) P ≤ weightedIndex d α (blockDehomogenize P) := by
  classical
  have hM : ∀ h : κ, (![-α h, 1] : Fin 2 → K) 1 ≠ 0 := fun _ ↦ one_ne_zero
  rw [formIndex_eq_iInf hM, weightedIndex_eq_iInf_support, ← blockDehomogenize_substFormInv]
  set Q := substFormInv (fun h ↦ ![-α h, 1]) (fun _ ↦ 1) P
  refine le_iInf₂ fun m hm ↦ ?_
  obtain ⟨n, hn, hmn⟩ := exists_mem_support_of_mem_support_blockDehomogenize hm
  refine (iInf₂_le n hn).trans_eq ?_
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_congr rfl fun h _ ↦ by simp [hmn h, div_eq_mul_inv]

/-- **Reduction of `formIndex` to `weightedIndex` by dehomogenization.** When `P` is
multihomogeneous of any multidegree `e : κ → ℕ`, its index along `X (h, 1) - α h X (h, 0)` equals
the weighted index of `blockDehomogenize P` at `α`. -/
theorem IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize [DecidableEq κ]
    {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) (d : κ → ℕ)
    (α : κ → K) :
    formIndex d (fun h ↦ ![-α h, 1]) P = weightedIndex d α (blockDehomogenize P) := by
  refine le_antisymm (formIndex_le_weightedIndex_blockDehomogenize d α P) ?_
  have hM : ∀ h : κ, (![-α h, 1] : Fin 2 → K) 1 ≠ 0 := fun _ ↦ one_ne_zero
  rw [formIndex_eq_iInf hM, weightedIndex_eq_iInf_support, ← blockDehomogenize_substFormInv]
  set Q := MvPolynomial.substFormInv (fun h ↦ ![-α h, 1]) (fun _ ↦ 1) P
  have hQ : IsMultiHomogeneous e Q := IsMultiHomogeneous.substFormInv hP _ _
  refine le_iInf₂ fun n hn ↦ ?_
  obtain ⟨m, hm, hmn, -⟩ :=
    IsMultiHomogeneous.exists_coeff_blockDehomogenize_eq_of_mem_support hQ hn
  refine (iInf₂_le m hm).trans_eq ?_
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_congr rfl fun h _ ↦ by simp [hmn h, div_eq_mul_inv]

/-- Multihomogeneity is necessary for equality in
`IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize`: the inhomogeneous polynomial
`X (0, 1) + X (0, 0) ^ 2 - X (0, 0)` dehomogenizes to `X 0` (weighted index `1` at `0`), whereas
its index along `X (0, 1)` is `0`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 2) ℚ := X (0, 1) + X (0, 0) ^ 2 - X (0, 0)
    formIndex ![1] (fun _ ↦ ![-0, 1]) P < weightedIndex ![1] ![0] (blockDehomogenize P) := by
  intro P
  have hdehom : blockDehomogenize P = X 0 := by simp [P]
  have hw : weightedIndex ![1] ![0] (X 0 : MvPolynomial (Fin 1) ℚ) = 1 := by
    rw [weightedIndex_eq_iInf_support, taylor_X, Matrix.cons_val_zero, map_zero, add_zero,
      support_X]
    simp [Finsupp.weight_apply]
  have hf : formIndex ![1] (fun _ : Fin 1 ↦ ![(-0 : ℚ), 1]) P = 0 := by
    have hM : Fin 1 → (![(-0 : ℚ), 1] : Fin 2 → ℚ) 1 ≠ 0 := fun _ ↦ one_ne_zero
    have hsub : substFormInv (fun _ : Fin 1 ↦ ![(-0 : ℚ), 1]) (fun _ ↦ 1) P = P := by simp [P]
    have hsupp : Finsupp.single ((0 : Fin 1), (0 : Fin 2)) 1 ∈ P.support := by
      rw [mem_support_iff]
      simp [P, X_pow_eq_monomial, coeff_X, coeff_monomial, Finsupp.single_eq_single_iff]
    rw [formIndex_eq_iInf hM, hsub]
    exact nonpos_iff_eq_zero.mp ((iInf₂_le _ hsupp).trans_eq (by simp))
  rw [hdehom, hw, hf]
  exact zero_lt_one

end MvPolynomial
