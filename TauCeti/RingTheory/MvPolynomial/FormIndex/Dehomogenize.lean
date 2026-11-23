/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Block.Dehomogenize
public import TauCeti.RingTheory.MvPolynomial.FormIndex.Basic
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Dehomogenization of two-coordinate blocks and the weighted index

Over any commutative ring `R`, along the affine-chart linear forms `M h = ![-α h, 1]`
(`X (h, 1) - α h X (h, 0)`), the division-free shift `X (h, 1) ↦ X (h, 1) + α h X (h, 0)` is inverse
to `substForm M (fun _ ↦ 1)` and after dehomogenizing via `MvPolynomial.blockDehomogenize`
(`TauCeti.RingTheory.MvPolynomial.Block.Dehomogenize`) computes the Taylor shift
`taylor α (blockDehomogenize P)`. Over a field `K`, this shift coincides with
`substFormInv M (fun _ ↦ 1)` (`MvPolynomial.blockDehomogenize_substFormInv`).
Consequently, over any commutative ring `R`:

* For arbitrary `P`, `formIndex d (fun h ↦ ![-α h, 1]) P ≤ weightedIndex d α (blockDehomogenize P)`
  (`MvPolynomial.formIndex_le_weightedIndex_blockDehomogenize`), because dehomogenization can only
  cancel terms.
* When `P` is multihomogeneous of any multidegree `e`, the shift preserves multihomogeneity,
  so applying `blockDehomogenize` after the shift causes no cancellation between distinct monomials,
  giving the exact equality
  `formIndex d (fun h ↦ ![-α h, 1]) P = weightedIndex d α (blockDehomogenize P)`
  (`MvPolynomial.IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize`). Over a field,
  rescaling the forms extends this to any forms `M h` with `M h 1 ≠ 0`, at the point
  `fun h ↦ -M h 0 / M h 1`
  (`MvPolynomial.IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize_of_ne_zero`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Lemma 7.5.19.
* Ralf Stephan, `DiophantineApproximation/FormIndex.lean`,
  `DiophantineApproximation/FormSpecialization.lean`, and
  `DiophantineApproximation/GeneralizedRothLemma.lean` in `rwst/Subspace-Theorems`, commit
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

namespace MvPolynomial

open Finset
open scoped ENNReal

section CommRing

variable {R κ : Type*} [CommRing R]

/-- Division-free inverse to `substForm (fun h ↦ ![-α h, 1]) (fun _ ↦ 1)` over any commutative
ring: sends `X (h, 1)` to `X (h, 1) + α h X (h, 0)` and fixes `X (h, 0)`. -/
private noncomputable def affineShift (α : κ → R) :
    MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial (κ × Fin 2) R :=
  aeval fun p ↦ if p.2 = 1 then X p + C (α p.1) * X (p.1, 0) else X p

private theorem substForm_affineShift (α : κ → R) (P : MvPolynomial (κ × Fin 2) R) :
    substForm (fun h ↦ ![-α h, 1]) (fun _ ↦ 1) (affineShift α P) = P := by
  suffices (substForm (fun h ↦ ![-α h, 1]) (fun _ ↦ 1)).comp (affineShift α) = AlgHom.id R _ from
    AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases i
  · simp [affineShift]
  · simp [affineShift, Fin.sum_univ_two]

private theorem affineShift_substForm (α : κ → R) (P : MvPolynomial (κ × Fin 2) R) :
    affineShift α (substForm (fun h ↦ ![-α h, 1]) (fun _ ↦ 1) P) = P := by
  suffices (affineShift α).comp (substForm (fun h ↦ ![-α h, 1]) (fun _ ↦ 1)) = AlgHom.id R _ from
    AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases i
  · simp [affineShift]
  · simp [affineShift, Fin.sum_univ_two]

private theorem blockDehomogenize_affineShift (α : κ → R) (P : MvPolynomial (κ × Fin 2) R) :
    blockDehomogenize (affineShift α P) = taylor α (blockDehomogenize P) := by
  suffices blockDehomogenize.comp (affineShift α) = (taylor α).comp blockDehomogenize from
    AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases i <;> simp [affineShift, taylor_apply]

private theorem isMultiHomogeneous_affineShift [DecidableEq κ] {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) (α : κ → R) :
    IsMultiHomogeneous e (affineShift α P) := by
  rw [affineShift]
  refine hP.aeval fun h i ↦ ?_
  fin_cases i
  · simp
  · simpa using (isMultiHomogeneous_X h (1 : Fin 2)).add
      ((isMultiHomogeneous_X h (0 : Fin 2)).C_mul (α h))

variable [Fintype κ]

private theorem formIndex_affine_eq_iInf (d : κ → ℕ) (α : κ → R)
    (P : MvPolynomial (κ × Fin 2) R) :
    formIndex d (fun h ↦ ![-α h, 1]) P =
      ⨅ n ∈ (affineShift α P).support, ∑ h, (n (h, 1) : ℝ≥0∞) / d h := by
  have hmem (t : ℝ≥0∞) : P ∈ formIdeal t d (fun h ↦ ![-α h, 1]) ↔
      ∀ n ∈ (affineShift α P).support, t ≤ ∑ h, (n (h, 1) : ℝ≥0∞) / d h := by
    set J : Ideal (MvPolynomial (κ × Fin 2) R) :=
      Ideal.span ((fun n ↦ monomial n (1 : R)) '' {n | t ≤ ∑ h, (n (h, 1) : ℝ≥0∞) / d h})
    have hJ (Q : MvPolynomial (κ × Fin 2) R) :
        Q ∈ J ↔ ∀ n ∈ Q.support, t ≤ ∑ h, (n (h, 1) : ℝ≥0∞) / d h := by
      rw [mem_ideal_span_monomial_image]
      refine forall₂_congr fun n _ ↦ ⟨?_, fun hn ↦ ⟨n, hn, le_rfl⟩⟩
      rintro ⟨e, he, hen⟩
      exact he.trans (Finset.sum_le_sum fun h _ ↦
        ENNReal.div_le_div_right (by exact_mod_cast hen (h, 1)) _)
    rw [formIdeal_eq_map_substForm t d (fun h ↦ ![-α h, 1]) (fun _ ↦ 1),
      Ideal.mem_map_iff_of_surjective _
        (Function.RightInverse.surjective (substForm_affineShift α)), ← hJ]
    exact ⟨fun ⟨Q, hQ, hQP⟩ ↦ by rwa [← hQP, affineShift_substForm],
      fun hQ ↦ ⟨affineShift α P, hQ, substForm_affineShift α P⟩⟩
  refine le_antisymm ?_ (le_formIndex_of_mem ((hmem _).mpr fun n hn ↦ iInf₂_le n hn))
  rw [formIndex_def]
  exact iSup₂_le fun _ ht ↦ le_iInf₂ ((hmem _).mp ht)

/-- For any polynomial `P` over a commutative ring, the index along the forms
`X (h, 1) - α h X (h, 0)` is at most the weighted index at `α` of `blockDehomogenize P`. -/
theorem formIndex_le_weightedIndex_blockDehomogenize (d : κ → ℕ) (α : κ → R)
    (P : MvPolynomial (κ × Fin 2) R) :
    formIndex d (fun h ↦ ![-α h, 1]) P ≤ weightedIndex d α (blockDehomogenize P) := by
  classical
  rw [formIndex_affine_eq_iInf, weightedIndex_eq_iInf_support, ← blockDehomogenize_affineShift]
  set Q := affineShift α P
  refine le_iInf₂ fun m hm ↦ ?_
  obtain ⟨n, hn, hmn⟩ := exists_mem_support_of_mem_support_blockDehomogenize hm
  refine (iInf₂_le n hn).trans_eq ?_
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_congr rfl fun h _ ↦ by simp [hmn h, div_eq_mul_inv]

/-- **Reduction of `formIndex` to `weightedIndex` by dehomogenization.** When `P` is
multihomogeneous of any multidegree `e : κ → ℕ` over a commutative ring, its index along
`X (h, 1) - α h X (h, 0)` equals the weighted index of `blockDehomogenize P` at `α`. -/
theorem IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize [DecidableEq κ]
    {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) (d : κ → ℕ)
    (α : κ → R) :
    formIndex d (fun h ↦ ![-α h, 1]) P = weightedIndex d α (blockDehomogenize P) := by
  refine le_antisymm (formIndex_le_weightedIndex_blockDehomogenize d α P) ?_
  rw [formIndex_affine_eq_iInf, weightedIndex_eq_iInf_support, ← blockDehomogenize_affineShift]
  set Q := affineShift α P
  have hQ : IsMultiHomogeneous e Q := isMultiHomogeneous_affineShift hP α
  refine le_iInf₂ fun n hn ↦ ?_
  obtain ⟨m, hm, hmn, -⟩ :=
    IsMultiHomogeneous.exists_coeff_blockDehomogenize_eq_of_mem_support hQ hn
  refine (iInf₂_le m hm).trans_eq ?_
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_congr rfl fun h _ ↦ by simp [hmn h, div_eq_mul_inv]

end CommRing

section Field

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

/-- **Form index via dehomogenization for general forms.** For a multihomogeneous polynomial `P`
in two-variable blocks and linear forms `M h` with `M h 1 ≠ 0`, `formIndex d M P` equals the
weighted index of `blockDehomogenize P` at `fun h ↦ -M h 0 / M h 1`. -/
theorem IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize_of_ne_zero [Fintype κ]
    [DecidableEq κ] {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P)
    (d : κ → ℕ) {M : κ → Fin 2 → K} (hM : ∀ h, M h 1 ≠ 0) :
    formIndex d M P = weightedIndex d (fun h ↦ -M h 0 / M h 1) (blockDehomogenize P) := by
  calc formIndex d M P = formIndex d (fun h ↦ M h 1 • ![-(-M h 0 / M h 1), 1]) P := by
        congr 1
        ext h i
        fin_cases i <;> simp [mul_div_cancel₀ _ (hM h)]
    _ = formIndex d (fun h ↦ ![-(-M h 0 / M h 1), 1]) P :=
        formIndex_smul_form (fun h ↦ (hM h).isUnit) d _ P
    _ = _ := hP.formIndex_eq_weightedIndex_blockDehomogenize d _

end Field

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
