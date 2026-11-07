/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.BlockHomogenize
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.FormIndex.Basic
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Dehomogenization of two-coordinate blocks and the weighted index

When each block `h : κ` carries only two coordinates `(h, 0)` and `(h, 1)`, setting every
homogenizing coordinate `X (h, 0)` to `1` and keeping `X (h, 1)` as `X h` defines the algebra map
`MvPolynomial.blockDehomogenize : MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial κ R`. On a single
block it agrees with `TauCeti.dehomogenize 0`, and after identifying `κ ⊕ κ` with `κ × Fin 2` it is
the evaluation `X (.inl h) ↦ 1, X (.inr h) ↦ X h` inverse to `MvPolynomial.blockHomogenize id e` on
multihomogeneous polynomials of multidegree `e`.

For a multihomogeneous polynomial `P` of any multidegree `e : κ → ℕ`, the homogenizing exponent
`n (h, 0) = e h - n (h, 1)` is determined by the affine exponent `n (h, 1)`, so
`blockDehomogenize` maps `P.support` bijectively onto `(blockDehomogenize P).support` without
cancellation: it preserves nonvanishing and the set of nonzero coefficients, and bounds the partial
degrees by `e`.

Over a field `K`, along the affine-chart linear forms `M h = ![-α h, 1]`
(`X (h, 1) - α h X (h, 0)`), the inverse substitution `substFormInv M (fun _ ↦ 1)` sends `X (h, 1)`
to `X (h, 1) + α h X (h, 0)`, so dehomogenizing after `substFormInv` computes the Taylor shift
`taylor α (blockDehomogenize P)` (`MvPolynomial.blockDehomogenize_substFormInv`). Consequently:

* For arbitrary `P`, `formIndex d (fun h ↦ ![-α h, 1]) P ≤ weightedIndex d α (blockDehomogenize P)`
  (`MvPolynomial.formIndex_le_weightedIndex_blockDehomogenize`), because dehomogenization can only
  cancel terms.
* When `P` is multihomogeneous of any multidegree `e`, no cancellation occurs in `substFormInv P`,
  giving the exact equality
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

variable {R K κ : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Setting the homogenizing variable `X (h, 0)` of each two-variable block `h` to `1` and sending
the affine variable `X (h, 1)` to `X h`. -/
noncomputable def blockDehomogenize : MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial κ R :=
  aeval fun p ↦ ![1, X p.1] p.2

@[simp]
theorem blockDehomogenize_X_zero (h : κ) :
    blockDehomogenize (X (h, 0) : MvPolynomial (κ × Fin 2) R) = 1 := by
  simp [blockDehomogenize]

@[simp]
theorem blockDehomogenize_X_one (h : κ) :
    blockDehomogenize (X (h, 1) : MvPolynomial (κ × Fin 2) R) = X h := by
  simp [blockDehomogenize]

/-- On `κ ⊕ κ`, renaming `.inl h ↦ (h, 0)` and `.inr h ↦ (h, 1)` and applying `blockDehomogenize`
is the evaluation `Sum.elim (fun _ ↦ 1) X` used in `MvPolynomial.blockHomogenize`. -/
theorem blockDehomogenize_rename_sumElim (F : MvPolynomial (κ ⊕ κ) R) :
    blockDehomogenize (rename (Sum.elim (·, 0) (·, 1)) F) = aeval (Sum.elim (fun _ ↦ 1) X) F := by
  suffices blockDehomogenize.comp (rename (R := R) (Sum.elim (·, 0) (·, 1))) =
      aeval (Sum.elim (fun _ ↦ 1) X) from AlgHom.congr_fun this F
  ext (h | h) : 1 <;> simp

/-- On a single two-variable block `Fin 1 × Fin 2`, `blockDehomogenize` agrees with
`TauCeti.dehomogenize 0` after dropping the unique block index. -/
theorem blockDehomogenize_fin_one (P : MvPolynomial (Fin 1 × Fin 2) R) :
    blockDehomogenize P = TauCeti.dehomogenize 0 (rename Prod.snd P) := by
  suffices blockDehomogenize (R := R) (κ := Fin 1) =
      (TauCeti.dehomogenize 0).comp (rename Prod.snd) from AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases h
  fin_cases i <;> simp

/-- `blockDehomogenize` drops the coordinate-`0` exponents of a monomial and keeps its
coordinate-`1` exponents. -/
theorem blockDehomogenize_monomial [Finite κ] (n : κ × Fin 2 →₀ ℕ) (c : R) :
    blockDehomogenize (monomial n c) =
      monomial (n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn) c := by
  cases nonempty_fintype κ
  rw [monomial_eq, monomial_eq, map_mul, blockDehomogenize, algHom_C,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fintype.prod_prod_type, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun h _ ↦ ?_
  rw [Fin.prod_univ_two]
  simp

/-- The affine exponent vector `h ↦ n (h, 1)` extracted from an exponent `n : κ × Fin 2 →₀ ℕ`. -/
private noncomputable def affineExp (n : κ × Fin 2 →₀ ℕ) : κ →₀ ℕ :=
  n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn

@[simp]
private theorem affineExp_apply (n : κ × Fin 2 →₀ ℕ) (h : κ) :
    affineExp n h = n (h, 1) :=
  rfl

private theorem blockDehomogenize_monomial_affineExp [Finite κ] (n : κ × Fin 2 →₀ ℕ) (c : R) :
    blockDehomogenize (monomial n c) = monomial (affineExp n) c :=
  blockDehomogenize_monomial n c

section MultiHomogeneous

variable [Finite κ] [DecidableEq κ] {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) R}

/-- Reconstructs the unique multidegree-`e` exponent vector on `κ × Fin 2` with coordinate-`1`
exponents `m`. -/
private noncomputable def liftAffineExp (e : κ → ℕ) (m : κ →₀ ℕ) : κ × Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p ↦ ![e p.1 - m p.1, m p.1] p.2

private theorem liftAffineExp_eq_of_mem_support (hP : IsMultiHomogeneous e P)
    {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) :
    liftAffineExp e (affineExp n) = n ∧ ∀ h, affineExp n h ≤ e h := by
  have hsum (h : κ) : n (h, 0) + n (h, 1) = e h := by
    have := isMultiHomogeneous_iff.mp hP n (mem_support_iff.mp hn) h
    rwa [Fin.sum_univ_two] at this
  refine ⟨?_, fun h ↦ (hsum h) ▸ Nat.le_add_left _ _⟩
  ext ⟨h, i⟩
  have := hsum h
  fin_cases i
  · simp [liftAffineExp]
    omega
  · simp [liftAffineExp]

private theorem coeff_blockDehomogenize_of_le (hP : IsMultiHomogeneous e P) {m : κ →₀ ℕ}
    (hm : ∀ h, m h ≤ e h) :
    (blockDehomogenize P).coeff m = P.coeff (liftAffineExp e m) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum]
  simp_rw [blockDehomogenize_monomial_affineExp, coeff_monomial]
  rw [Finset.sum_eq_single (liftAffineExp e m)]
  · have hleft : affineExp (liftAffineExp e m) = m := by ext h; simp [liftAffineExp]
    exact ite_eq_left hleft
  · intro n hn hne
    rw [ite_eq_right]
    rintro rfl
    exact hne (liftAffineExp_eq_of_mem_support hP hn).1.symm
  · intro hnotMem
    simp [notMem_support_iff.mp hnotMem]

private theorem coeff_blockDehomogenize_eq_zero_of_not_le (hP : IsMultiHomogeneous e P)
    {m : κ →₀ ℕ} (hm : ¬ ∀ h, m h ≤ e h) :
    (blockDehomogenize P).coeff m = 0 := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [blockDehomogenize_monomial_affineExp, coeff_monomial, ite_eq_right]
  rintro rfl
  exact hm (liftAffineExp_eq_of_mem_support hP hn).2

/-- Every nonzero coefficient of `blockDehomogenize P` is a coefficient of `P`, when `P` is
multihomogeneous. -/
theorem IsMultiHomogeneous.exists_coeff_eq_of_mem_support_blockDehomogenize
    (hP : IsMultiHomogeneous e P) {m : κ →₀ ℕ} (hm : m ∈ (blockDehomogenize P).support) :
    ∃ n ∈ P.support, (blockDehomogenize P).coeff m = P.coeff n := by
  have hne := mem_support_iff.mp hm
  by_cases hle : ∀ h, m h ≤ e h
  · have hc := coeff_blockDehomogenize_of_le hP hle
    exact ⟨liftAffineExp e m, mem_support_iff.mpr (hc ▸ hne), hc⟩
  · exact (hne (coeff_blockDehomogenize_eq_zero_of_not_le hP hle)).elim

/-- Every nonzero coefficient of a multihomogeneous polynomial `P` occurs as a nonzero coefficient
of `blockDehomogenize P` at the corresponding affine exponent. -/
theorem IsMultiHomogeneous.coeff_blockDehomogenize_eq_of_mem_support
    (hP : IsMultiHomogeneous e P) {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) :
    ∃ m ∈ (blockDehomogenize P).support,
      (∀ h, m h = n (h, 1)) ∧ (blockDehomogenize P).coeff m = P.coeff n := by
  obtain ⟨hlift, hle⟩ := liftAffineExp_eq_of_mem_support hP hn
  have hc : (blockDehomogenize P).coeff (affineExp n) = P.coeff n := by
    rw [coeff_blockDehomogenize_of_le hP hle, hlift]
  exact ⟨affineExp n, mem_support_iff.mpr (hc ▸ mem_support_iff.mp hn), fun _ ↦ rfl, hc⟩

/-- Dehomogenization of a multihomogeneous polynomial vanishes if and only if the polynomial itself
vanishes. -/
theorem IsMultiHomogeneous.blockDehomogenize_eq_zero (hP : IsMultiHomogeneous e P) :
    blockDehomogenize P = 0 ↔ P = 0 := by
  refine ⟨fun h0 ↦ by_contra fun hne ↦ ?_, fun h0 ↦ by simp [h0]⟩
  obtain ⟨n, hn⟩ := support_nonempty.mpr hne
  obtain ⟨m, hm, -, -⟩ := IsMultiHomogeneous.coeff_blockDehomogenize_eq_of_mem_support hP hn
  simp [h0] at hm

/-- Dehomogenizing a multihomogeneous polynomial of multidegree `e` gives a polynomial of degree at
most `e h` in each variable `h`. -/
theorem IsMultiHomogeneous.degreeOf_blockDehomogenize_le (hP : IsMultiHomogeneous e P) (h : κ) :
    (blockDehomogenize P).degreeOf h ≤ e h := by
  rw [degreeOf_le_iff]
  intro m hm
  by_contra hnot
  exact mem_support_iff.mp hm
    (coeff_blockDehomogenize_eq_zero_of_not_le hP fun hle ↦ hnot (hle h))

end MultiHomogeneous

end CommSemiring

section Field

variable [Field K]

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
  -- A nonzero monomial `m` of `blockDehomogenize Q` must come from at least one monomial `n` in
  -- `Q.support` with `affineExp n = m`.
  obtain ⟨n, hn, hnm⟩ : ∃ n ∈ Q.support, affineExp n = m := by
    by_contra! hnone
    refine mem_support_iff.mp hm ?_
    conv_lhs => rw [Q.as_sum]
    rw [map_sum, coeff_sum]
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    rw [blockDehomogenize_monomial_affineExp, coeff_monomial, ite_eq_right (hnone n hn)]
  subst hnm
  refine (iInf₂_le n hn).trans_eq ?_
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_congr rfl fun h _ ↦ by simp [div_eq_mul_inv]

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
  obtain ⟨m, hm, hmn, -⟩ := IsMultiHomogeneous.coeff_blockDehomogenize_eq_of_mem_support hQ hn
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
    have hM : ∀ h : Fin 1, (![(-0 : ℚ), 1] : Fin 2 → ℚ) 1 ≠ 0 := fun _ ↦ one_ne_zero
    have hsub : substFormInv (fun _ : Fin 1 ↦ ![(-0 : ℚ), 1]) (fun _ ↦ 1) P = P := by
      have herase : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
      have h1 := substFormInv_X_self (M := fun _ : Fin 1 ↦ ![(-0 : ℚ), 1])
        (i₀ := fun _ ↦ 1) 0
      simp only [herase, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, neg_zero, map_zero, zero_mul, sub_zero, inv_one, map_one,
        one_mul] at h1
      simp [P, h1]
    have hsupp : Finsupp.single ((0 : Fin 1), (0 : Fin 2)) 1 ∈ P.support := by
      rw [mem_support_iff]
      simp [P, X_pow_eq_monomial, coeff_X, coeff_monomial, Finsupp.single_eq_single_iff]
    rw [formIndex_eq_iInf hM, hsub]
    exact nonpos_iff_eq_zero.mp ((iInf₂_le _ hsupp).trans_eq (by simp))
  rw [hdehom, hw, hf]
  exact zero_lt_one

end Field

end MvPolynomial
