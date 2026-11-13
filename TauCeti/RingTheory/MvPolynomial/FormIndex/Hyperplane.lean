/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FormIndex.Basic
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.ChainRule
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Hyperplane derivative characterization of the index along linear forms

Over a field `K`, Bombieri and Gubler define `formIndex d M P` ideal-theoretically via powers of the
linear forms `M h (X h) = ∑ i, M h i • X (h, i)` (`TauCeti.RingTheory.MvPolynomial.FormIndex.Basic`)
and immediately note that it coincides with the smallest `(1 / d h)`-weighted order of a Hasse
derivative `hasseDeriv I P` that does not vanish identically on the common kernel
`⋂ h, ker (M h)`. This file proves both directions of that characterization in arbitrary
characteristic (using Hasse derivatives rather than naive partial derivatives) and connects
`substForm` and `substFormInv` with `MvPolynomial.blockLinearForm` and `MvPolynomial.linearSubst`:

* `MvPolynomial.taylor_map_mem_formIdeal` and
  `MvPolynomial.aeval_hasseDeriv_eq_zero_of_lt_formIndex`: over any commutative semiring `R`, for
  any `R`-algebra `A` and any tuple `y : κ × ι → A` satisfying `∑ i, M h i • y (h, i) = 0` in every
  block `h`, translating by `y` preserves `formIdeal`, so every Hasse derivative `hasseDeriv I P`
  of weighted order `∑ h, (∑ i, I (h, i)) / d h < formIndex d M P` vanishes at `y`.
* `MvPolynomial.exists_aeval_blockLinearForm_hasseDeriv_ne_zero_of_formIndex_ne_top`: conversely,
  over a field `K`, for nonzero linear forms `M` (`∀ h, M h ≠ 0`), whenever `formIndex d M P ≠ ⊤`
  and the columns of `B h : ι → τ → K` span `ker (M h)` in each block, there exists `I` of exact
  weighted order `∑ h, (∑ i, I (h, i)) / d h = formIndex d M P` such that
  `aeval (blockLinearForm B) (hasseDeriv I P) ≠ 0`.
* `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_formIndex_ne_top`,
  `MvPolynomial.exists_sum_div_eq_formIndex_and_eval_hasseDeriv_ne_zero`, and
  `MvPolynomial.le_formIndex_iff_forall_eval_hasseDeriv_eq_zero`: over an infinite field `K`, for
  nonzero linear forms `M` (`∀ h, M h ≠ 0`), `formIndex d M P ≠ ⊤` (in particular `P ≠ 0` with
  `∀ h, d h ≠ 0`) yields a point `x : κ × ι → K` in the common kernel at which `hasseDeriv I P` is
  nonzero, and characterizes `t ≤ formIndex d M P` by pointwise vanishing of low-order Hasse
  derivatives on the common kernel. Over a finite field, even a nonzero homogeneous polynomial of
  `formIndex` zero can vanish at every rational point of the kernel (see the `ZMod 2` example at
  the end of the file).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §7.5, Definition 7.5.17 and p. 221.
-/

public section

namespace MvPolynomial

open Finset
open scoped ENNReal

variable {R K κ ι τ : Type*}

section LinearSubst

variable [CommSemiring R] [Fintype ι] [DecidableEq ι]

/-- `substForm M i₀` is a block-linear substitution (`MvPolynomial.blockLinearForm`). -/
theorem substForm_eq_aeval_blockLinearForm (M : κ → ι → R) (i₀ : κ → ι) :
    substForm M i₀ =
      aeval (blockLinearForm fun h l a ↦ if l = i₀ h then M h a else if l = a then 1 else 0) := by
  ext ⟨h, l⟩ : 1
  by_cases hl : l = i₀ h
  · subst hl
    simp [blockLinearForm_apply]
  · simp [hl, blockLinearForm_apply]

/-- `substForm M i₀` is a linear substitution (`MvPolynomial.linearSubst`) by a block-diagonal
matrix. -/
theorem substForm_eq_linearSubst [Fintype κ] [DecidableEq κ] (M : κ → ι → R) (i₀ : κ → ι) :
    substForm M i₀ =
      linearSubst (Matrix.of fun p q : κ × ι ↦
        if p.1 = q.1 then (if p.2 = i₀ p.1 then M p.1 q.2 else if p.2 = q.2 then 1 else 0)
        else 0) := by
  ext ⟨h, l⟩ : 1
  rw [linearSubst_X, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single h (fun h' _ hh' ↦ by simp [hh'.symm]) (by simp)]
  by_cases hl : l = i₀ h
  · subst hl
    simp
  · simp [hl]

/-- `substFormInv M i₀` is a block-linear substitution (`MvPolynomial.blockLinearForm`). -/
theorem substFormInv_eq_aeval_blockLinearForm [Field K] (M : κ → ι → K) (i₀ : κ → ι) :
    substFormInv M i₀ =
      aeval (blockLinearForm fun h l a ↦
        if l = i₀ h then (if a = i₀ h then (M h (i₀ h))⁻¹ else - ((M h (i₀ h))⁻¹ * M h a))
        else if l = a then 1 else 0) := by
  ext ⟨h, l⟩ : 1
  by_cases hl : l = i₀ h
  · subst hl
    rw [substFormInv_X_self, aeval_X, blockLinearForm_apply,
      ← Finset.add_sum_erase _ _ (mem_univ (i₀ h))]
    simp only [↓reduceIte, mul_sub, mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    simp only [ne_of_mem_erase ha, ↓reduceIte, C_neg, C_mul, neg_mul, mul_assoc]
  · simp [hl, blockLinearForm_apply]

/-- `substFormInv M i₀` is a linear substitution (`MvPolynomial.linearSubst`) by a block-diagonal
matrix. -/
theorem substFormInv_eq_linearSubst [Field K] [Fintype κ] [DecidableEq κ] (M : κ → ι → K)
    (i₀ : κ → ι) :
    substFormInv M i₀ =
      linearSubst (Matrix.of fun p q : κ × ι ↦
        if p.1 = q.1 then
          (if p.2 = i₀ p.1 then
            (if q.2 = i₀ p.1 then (M p.1 (i₀ p.1))⁻¹ else - ((M p.1 (i₀ p.1))⁻¹ * M p.1 q.2))
          else if p.2 = q.2 then 1 else 0)
        else 0) := by
  rw [substFormInv_eq_aeval_blockLinearForm]
  ext ⟨h, l⟩ : 1
  rw [aeval_X, blockLinearForm_apply, linearSubst_X, Fintype.sum_prod_type,
    Finset.sum_eq_single h (fun h' _ hh' ↦ by simp [hh'.symm]) (by simp)]
  simp

end LinearSubst

section Vanishing

variable [CommSemiring R] [Fintype κ] [Fintype ι]

/-- Translating by any tuple `y : κ × ι → A` annihilated by every linear form `M h` maps
`formIdeal t d M` into `formIdeal t d (fun h i ↦ algebraMap R A (M h i))`. -/
theorem taylor_map_mem_formIdeal {A : Type*} [CommSemiring A] [Algebra R A]
    {t : ℝ≥0∞} {d : κ → ℕ} {M : κ → ι → R} {P : MvPolynomial (κ × ι) R}
    (hP : P ∈ formIdeal t d M) {y : κ × ι → A} (hy : ∀ h, ∑ i, M h i • y (h, i) = 0) :
    taylor y (map (algebraMap R A) P) ∈
      formIdeal t d (fun h i ↦ algebraMap R A (M h i)) := by
  set Ψ : MvPolynomial (κ × ι) R →+* MvPolynomial (κ × ι) A :=
    (taylor y).toRingHom.comp (map (algebraMap R A))
  -- On each block's linear form, the constant shift vanishes because `y` lies in `ker (M h)`.
  have hΨ_form (h : κ) :
      Ψ (∑ i, C (M h i) * X (h, i)) = ∑ i, C (algebraMap R A (M h i)) * X (h, i) := by
    have hy' : ∑ i, algebraMap R A (M h i) * y (h, i) = 0 := by
      simpa only [Algebra.smul_def] using hy h
    change taylor y (map (algebraMap R A) (∑ i, C (M h i) * X (h, i))) = _
    simp only [map_sum, map_mul, map_C, map_X, algHom_C, algebraMap_eq, taylor_X, mul_add,
      Finset.sum_add_distrib]
    simp only [← C_mul, ← map_sum, hy', C_0, add_zero]
  have hmap : Ideal.map Ψ (formIdeal t d M) ≤
      formIdeal t d (fun h i ↦ algebraMap R A (M h i)) := by
    rw [formIdeal_def, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    dsimp only
    rw [SetLike.mem_coe, map_prod]
    simp only [map_pow, hΨ_form]
    exact prod_pow_mem_formIdeal hj
  exact hmap (Ideal.mem_map_of_mem Ψ hP)

/-- **Vanishing of low-order Hasse derivatives on the common kernel.** For any `R`-algebra `A` and
any tuple `y : κ × ι → A` annihilated by every linear form `M h`, every Hasse derivative
`hasseDeriv I P` of `(1 / d h)`-weighted order strictly below `formIndex d M P` vanishes at `y`. -/
theorem aeval_hasseDeriv_eq_zero_of_lt_formIndex {A : Type*} [CommSemiring A] [Algebra R A]
    {d : κ → ℕ} {M : κ → ι → R} {P : MvPolynomial (κ × ι) R}
    {I : κ × ι →₀ ℕ} (hI : ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h < formIndex d M P)
    {y : κ × ι → A} (hy : ∀ h, ∑ i, M h i • y (h, i) = 0) :
    aeval y (hasseDeriv I P) = 0 := by
  rw [formIndex_def] at hI
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hI
  obtain ⟨hPs, hIs⟩ := lt_iSup_iff.mp hs
  rw [aeval_def, eval₂_eq_eval_map, ← hasseDeriv_map, ← coeff_taylor]
  exact coeff_eq_zero_of_mem_formIdeal (taylor_map_mem_formIdeal hPs hy) hIs

/-- Pointwise vanishing on the common kernel of Hasse derivatives of weighted order strictly below
`formIndex d M P`. -/
theorem eval_hasseDeriv_eq_zero_of_lt_formIndex {d : κ → ℕ} {M : κ → ι → R}
    {P : MvPolynomial (κ × ι) R} {I : κ × ι →₀ ℕ}
    (hI : ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h < formIndex d M P)
    {x : κ × ι → R} (hx : ∀ h, ∑ i, M h i * x (h, i) = 0) :
    eval x (hasseDeriv I P) = 0 := by
  simpa only [aeval_eq_eval] using
    aeval_hasseDeriv_eq_zero_of_lt_formIndex hI (y := x) (by simpa [smul_eq_mul] using hx)

/-- Any block-linear parameterization `B` of subspaces contained in `ker (M h)` annihilates every
Hasse derivative of weighted order strictly below `formIndex d M P`. -/
theorem aeval_blockLinearForm_hasseDeriv_eq_zero_of_lt_formIndex [Fintype τ] {d : κ → ℕ}
    {M : κ → ι → R} {P : MvPolynomial (κ × ι) R} {I : κ × ι →₀ ℕ}
    (hI : ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h < formIndex d M P)
    {B : κ → ι → τ → R} (hB : ∀ h a, ∑ i, M h i * B h i a = 0) :
    aeval (blockLinearForm B) (hasseDeriv I P) = 0 := by
  refine aeval_hasseDeriv_eq_zero_of_lt_formIndex hI fun h ↦ ?_
  simp only [blockLinearForm_apply, Algebra.smul_def, algebraMap_eq, Finset.mul_sum, ← mul_assoc,
    ← C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [← Finset.sum_mul, ← map_sum, hB h a, map_zero, zero_mul]

end Vanishing

section Hyperplane

variable [Field K] [Fintype κ] [Fintype ι]

section PivotHelpers

variable [DecidableEq ι]

/-- Setting every pivot variable `X (h, i₀ h)` to `0` while keeping complementary variables, via
`MvPolynomial.killCompl` on `{p : κ × ι // p.2 ≠ i₀ p.1}`. -/
private noncomputable def killPivot (i₀ : κ → ι) :
    MvPolynomial (κ × ι) K →ₐ[K] MvPolynomial (κ × ι) K :=
  (rename (Subtype.val : {p : κ × ι // p.2 ≠ i₀ p.1} → κ × ι)).comp
    (killCompl Subtype.val_injective)

/-- Projecting each block onto `ker (M h)` along the pivot coordinate `i₀ h`. -/
private noncomputable def kerForm (M : κ → ι → K) (i₀ : κ → ι) (p : κ × ι) :
    MvPolynomial (κ × ι) K :=
  if p.2 = i₀ p.1 then
    - ∑ j ∈ univ.erase (i₀ p.1), C (M p.1 j / M p.1 (i₀ p.1)) * X (p.1, j)
  else X p

omit [Fintype κ] in
private theorem sum_C_mul_kerForm_eq_zero {M : κ → ι → K} {i₀ : κ → ι}
    (hi₀ : ∀ h, M h (i₀ h) ≠ 0) (h : κ) :
    ∑ i, C (M h i) * kerForm M i₀ (h, i) = 0 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ (i₀ h))]
  have hpiv : C (M h (i₀ h)) * kerForm M i₀ (h, i₀ h) =
      - ∑ j ∈ univ.erase (i₀ h), C (M h j) * X (h, j) := by
    simp only [kerForm, ↓reduceIte, mul_neg, mul_sum, ← mul_assoc, ← C_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_div_cancel₀ _ (hi₀ h)]
  have hrest : ∑ i ∈ univ.erase (i₀ h), C (M h i) * kerForm M i₀ (h, i) =
      ∑ j ∈ univ.erase (i₀ h), C (M h j) * X (h, j) :=
    Finset.sum_congr rfl fun i hi ↦ by simp [kerForm, ne_of_mem_erase hi]
  rw [hpiv, hrest, neg_add_cancel]

omit [Fintype κ] in
private theorem aeval_kerForm_comp_substForm {M : κ → ι → K} {i₀ : κ → ι}
    (hi₀ : ∀ h, M h (i₀ h) ≠ 0) :
    (aeval (kerForm M i₀)).comp (substForm M i₀) = killPivot i₀ := by
  ext ⟨h, i⟩ : 1
  by_cases hi : i = i₀ h
  · subst hi
    simp [killPivot, killCompl, sum_C_mul_kerForm_eq_zero hi₀]
  · simp only [AlgHom.comp_apply, substForm_X_of_ne hi, aeval_X, kerForm, hi, ↓reduceIte,
      killPivot]
    rw [← rename_X (R := K) (f := (Subtype.val : {p : κ × ι // p.2 ≠ i₀ p.1} → κ × ι))
      ⟨(h, i), hi⟩, killCompl_rename_app, rename_X]

omit [Fintype κ] in
private theorem killPivot_comp_substFormInv {M : κ → ι → K} {i₀ : κ → ι}
    (hi₀ : ∀ h, M h (i₀ h) ≠ 0) :
    (killPivot i₀).comp (substFormInv M i₀) = aeval (kerForm M i₀) := by
  ext1 P
  rw [AlgHom.comp_apply, ← aeval_kerForm_comp_substForm hi₀, AlgHom.comp_apply,
    substForm_substFormInv hi₀]

omit [Fintype κ] [Fintype ι] [DecidableEq ι] in
private theorem coeff_killPivot_of_eq_zero {i₀ : κ → ι}
    (H : MvPolynomial (κ × ι) K) {r : κ × ι →₀ ℕ} (hr : ∀ h, r (h, i₀ h) = 0) :
    (killPivot i₀ H).coeff r = H.coeff r := by
  let f : {p : κ × ι // p.2 ≠ i₀ p.1} → κ × ι := Subtype.val
  have hsub : (r.support : Set (κ × ι)) ⊆ Set.range f := fun ⟨h, i⟩ hp ↦
    ⟨⟨(h, i), fun (hi : i = i₀ h) ↦ Finsupp.mem_support_iff.mp hp (hi ▸ hr h)⟩, rfl⟩
  have hmap := Finsupp.mapDomain_comapDomain f Subtype.val_injective r hsub
  rw [killPivot, AlgHom.comp_apply, ← hmap, coeff_rename_mapDomain f Subtype.val_injective,
    coeff_killCompl]

end PivotHelpers

/-- Core existence of a multi-index `I` of exact weighted order `formIndex d M P` whose Hasse
derivative does not vanish after projecting onto `∏ h, ker (M h)`. -/
private theorem exists_aeval_kerForm_hasseDeriv_ne_zero [DecidableEq ι]
    {d : κ → ℕ} {M : κ → ι → K} {i₀ : κ → ι} (hi₀ : ∀ h, M h (i₀ h) ≠ 0)
    {P : MvPolynomial (κ × ι) K} (htop : formIndex d M P ≠ ⊤) :
    ∃ I : κ × ι →₀ ℕ,
      ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h = formIndex d M P ∧
      aeval (kerForm M i₀) (hasseDeriv I P) ≠ 0 := by
  classical
  set Q := substFormInv M i₀ P
  have hQne : Q ≠ 0 := fun h0 ↦ htop (by simp [formIndex_eq_iInf hi₀, Q, h0])
  obtain ⟨n₀, hn₀, hmin⟩ := Finset.exists_min_image Q.support
    (fun n ↦ ∑ h, (n (h, i₀ h) : ℝ≥0∞) / d h) (support_nonempty.mpr hQne)
  have hidx : ∑ h, (n₀ (h, i₀ h) : ℝ≥0∞) / d h = formIndex d M P := by
    rw [formIndex_eq_iInf hi₀]
    exact le_antisymm (le_iInf₂ hmin) (iInf₂_le n₀ hn₀)
  set k : κ × ι →₀ ℕ := n₀.filter (fun p ↦ p.2 = i₀ p.1)
  set r : κ × ι →₀ ℕ := n₀.filter (fun p ↦ ¬ p.2 = i₀ p.1)
  have hrk : r + k = n₀ := by
    rw [add_comm]
    exact n₀.filter_add_filter_not _
  have hr0 (h : κ) : r (h, i₀ h) = 0 := by simp [r]
  have hkchoose : (k.prod fun p c ↦ (r p + c).choose c) = 1 := by
    refine Finset.prod_eq_one fun ⟨h, i⟩ hp ↦ ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at hp
    obtain ⟨-, rfl⟩ : _ ∧ i = i₀ h := hp
    simp [hr0 h]
  have hkillne : killPivot i₀ (hasseDeriv k Q) ≠ 0 := by
    intro h0
    have hc : (killPivot i₀ (hasseDeriv k Q)).coeff r = Q.coeff n₀ := by
      rw [coeff_killPivot_of_eq_zero _ hr0, hasseDeriv_coeff, hkchoose, hrk]
      simp
    exact mem_support_iff.mp hn₀ (hc ▸ by simp [h0])
  have h0P : P = hasseDeriv 0 P := by simp
  have hQP : Q = substFormInv M i₀ (hasseDeriv 0 P) := congrArg _ h0P
  rw [hQP, substFormInv_eq_aeval_blockLinearForm,
    hasseDeriv_aeval_blockLinearForm_hasseDeriv, map_sum] at hkillne
  obtain ⟨I, hI, hIne⟩ := exists_ne_zero_of_sum_ne_zero hkillne
  rw [map_smul, map_nsmul, ← substFormInv_eq_aeval_blockLinearForm, ← AlgHom.comp_apply,
    killPivot_comp_substFormInv hi₀, zero_add] at hIne
  refine ⟨I, ?_, fun h0 ↦ hIne (by rw [h0, nsmul_zero, smul_zero])⟩
  rw [← hidx]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  have hdeg := (mem_filter.mp hI).2 h
  have hksum : ∑ a, k (h, a) = n₀ (h, i₀ h) := by
    rw [Finset.sum_eq_single (i₀ h) (fun a _ ha ↦ by simp [k, ha]) (by simp)]
    simp [k]
  rw [← Nat.cast_sum, hdeg, hksum]

/-- **Nonvanishing Hasse derivative on a parameterized common kernel.** Over a field `K`, if every
linear form `M h` is nonzero (`∀ h, M h ≠ 0`), `formIndex d M P ≠ ⊤`, and the columns of
`B h : ι → τ → K` span `ker (M h)` in each block `h`, then there exists a multi-index `I` of exact
weighted order `formIndex d M P` such that `hasseDeriv I P` does not vanish under
`aeval (blockLinearForm B)`. -/
theorem exists_aeval_blockLinearForm_hasseDeriv_ne_zero_of_formIndex_ne_top [Fintype τ]
    {d : κ → ℕ} {M : κ → ι → K} (hM : ∀ h, M h ≠ 0) {P : MvPolynomial (κ × ι) K}
    (htop : formIndex d M P ≠ ⊤) {B : κ → ι → τ → K}
    (hBspan : ∀ h (v : ι → K), ∑ i, M h i * v i = 0 → ∃ c : τ → K, ∀ i, v i = ∑ a, B h i a * c a) :
    ∃ I : κ × ι →₀ ℕ,
      ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h = formIndex d M P ∧
      aeval (blockLinearForm B) (hasseDeriv I P) ≠ 0 := by
  classical
  choose i₀ hi₀ using fun h ↦ Function.ne_iff.mp (hM h)
  obtain ⟨I, hI, hIne⟩ := exists_aeval_kerForm_hasseDeriv_ne_zero hi₀ htop
  refine ⟨I, hI, fun h0 ↦ hIne ?_⟩
  -- Express each basis vector of `kerForm M i₀` as a combination of the columns of `B h`.
  have hker (h : κ) (j : ι) (hj : j ≠ i₀ h) :
      ∑ i, M h i * (if i = i₀ h then - (M h j / M h (i₀ h)) else if i = j then 1 else 0) = 0 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (i₀ h)),
      Finset.sum_eq_single j
        (fun i hi hij ↦ by simp [ne_of_mem_erase hi, hij])
        (fun hnot ↦ (hnot (mem_erase.mpr ⟨hj, mem_univ j⟩)).elim)]
    simp [hj, mul_div_cancel₀ _ (hi₀ h)]
  choose c hc using fun h (j : {j : ι // j ≠ i₀ h}) ↦ hBspan h _ (hker h j.1 j.2)
  set ψ : MvPolynomial (κ × τ) K →ₐ[K] MvPolynomial (κ × ι) K :=
    aeval (Function.uncurry fun h a ↦ ∑ j : {j : ι // j ≠ i₀ h}, C (c h j a) * X (h, j.1))
  suffices ψ.comp (aeval (blockLinearForm B)) = aeval (kerForm M i₀) by
    rw [← this, AlgHom.comp_apply, h0, map_zero]
  ext ⟨h, i⟩ : 1
  simp only [AlgHom.comp_apply, aeval_X, blockLinearForm_apply, map_sum, map_mul, algHom_C,
    algebraMap_eq, ψ, Function.uncurry_apply_pair]
  have hstep :
      (∑ a, C (B h i a) * ∑ j : {j : ι // j ≠ i₀ h}, C (c h j a) * X (h, j.1)) =
        ∑ j : {j : ι // j ≠ i₀ h},
          C (if i = i₀ h then - (M h j.1 / M h (i₀ h)) else if i = j.1 then 1 else 0) *
            X (h, j.1) := by
    trans ∑ a, ∑ j : {j : ι // j ≠ i₀ h}, C (B h i a * c h j a) * X (h, j.1)
    · refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [← mul_assoc, ← C_mul]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Finset.sum_mul, ← map_sum, ← hc h j i]
  rw [hstep]
  by_cases hi : i = i₀ h
  · subst hi
    simp only [↓reduceIte, kerForm, C_neg, neg_mul, Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_coe_sort (univ.erase (i₀ h))
      (fun j ↦ C (M h j / M h (i₀ h)) * X (h, j))]
    exact Finset.sum_equiv
      (Equiv.subtypeEquivRight fun j ↦ mem_erase.trans (and_iff_left (mem_univ j))).symm
      (by simp) (by simp)
  · rw [Fintype.sum_eq_single ⟨i, hi⟩ fun j hj ↦ by
      have hj' : i ≠ j.1 := fun h' ↦ hj (Subtype.ext h'.symm)
      simp [hi, hj']]
    simp [kerForm, hi]

/-- **Pointwise nonvanishing Hasse derivative on the common kernel.** Over an infinite field `K`,
if every linear form `M h` is nonzero (`∀ h, M h ≠ 0`) and `formIndex d M P ≠ ⊤`, then there exist
a multi-index `I` of exact weighted order `formIndex d M P` and a point `x : κ × ι → K` in the
common kernel `⋂ h, ker (M h)` such that `eval x (hasseDeriv I P) ≠ 0`. -/
theorem exists_eval_hasseDeriv_ne_zero_of_formIndex_ne_top [Infinite K]
    {d : κ → ℕ} {M : κ → ι → K} (hM : ∀ h, M h ≠ 0) {P : MvPolynomial (κ × ι) K}
    (htop : formIndex d M P ≠ ⊤) :
    ∃ (I : κ × ι →₀ ℕ) (x : κ × ι → K),
      ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h = formIndex d M P ∧
      (∀ h, ∑ i, M h i * x (h, i) = 0) ∧
      eval x (hasseDeriv I P) ≠ 0 := by
  classical
  choose i₀ hi₀ using fun h ↦ Function.ne_iff.mp (hM h)
  obtain ⟨I, hI, hIne⟩ := exists_aeval_kerForm_hasseDeriv_ne_zero hi₀ htop
  obtain ⟨z, hz⟩ : ∃ z : κ × ι → K, eval z (aeval (kerForm M i₀) (hasseDeriv I P)) ≠ 0 := by
    by_contra! hall
    exact hIne (MvPolynomial.funext fun z ↦ by simp [hall z])
  refine ⟨I, fun p ↦ eval z (kerForm M i₀ p), hI, fun h ↦ ?_, ?_⟩
  · simpa using congrArg (eval z) (sum_C_mul_kerForm_eq_zero hi₀ h)
  · have hcomp := comp_aeval_apply (kerForm M i₀) (aeval z) (hasseDeriv I P)
    simpa only [aeval_eq_eval] using hcomp.symm.trans_ne hz

/-- Over an infinite field `K`, for nonzero linear forms `M` (`∀ h, M h ≠ 0`), positive degree
weights `d` (`∀ h, d h ≠ 0`), and a nonzero polynomial `P`, there exist a multi-index `I` of exact
weighted order `formIndex d M P` and a point `x : κ × ι → K` in the common kernel at which
`hasseDeriv I P` does not vanish. -/
theorem exists_sum_div_eq_formIndex_and_eval_hasseDeriv_ne_zero [Infinite K] {d : κ → ℕ}
    {M : κ → ι → K} (hM : ∀ h, M h ≠ 0) (hd : ∀ h, d h ≠ 0) {P : MvPolynomial (κ × ι) K}
    (hP : P ≠ 0) :
    ∃ (I : κ × ι →₀ ℕ) (x : κ × ι → K),
      ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h = formIndex d M P ∧
      (∀ h, ∑ i, M h i * x (h, i) = 0) ∧
      eval x (hasseDeriv I P) ≠ 0 :=
  exists_eval_hasseDeriv_ne_zero_of_formIndex_ne_top hM
    ((formIndex_eq_top_iff hM hd).not.mpr hP)

/-- **Pointwise Hasse-derivative characterization of `formIndex`.** Over an infinite field `K`, for
nonzero linear forms `M` (`∀ h, M h ≠ 0`), `t ≤ formIndex d M P` if and only if every Hasse
derivative of `(1 / d h)`-weighted order strictly below `t` vanishes at every `K`-rational point of
the common kernel `⋂ h, ker (M h)`. -/
theorem le_formIndex_iff_forall_eval_hasseDeriv_eq_zero [Infinite K] {t : ℝ≥0∞} {d : κ → ℕ}
    {M : κ → ι → K} (hM : ∀ h, M h ≠ 0) {P : MvPolynomial (κ × ι) K} :
    t ≤ formIndex d M P ↔
      ∀ I : κ × ι →₀ ℕ, ∑ h, (∑ i, I (h, i) : ℝ≥0∞) / d h < t →
        ∀ x : κ × ι → K, (∀ h, ∑ i, M h i * x (h, i) = 0) → eval x (hasseDeriv I P) = 0 := by
  refine ⟨fun hle I hIt x hx ↦ eval_hasseDeriv_eq_zero_of_lt_formIndex (hIt.trans_le hle) hx,
    fun hall ↦ by_contra fun hnot ↦ ?_⟩
  have hlt : formIndex d M P < t := lt_of_not_ge hnot
  obtain ⟨I, x, hIeq, hx, hne⟩ :=
    exists_eval_hasseDeriv_ne_zero_of_formIndex_ne_top hM hlt.ne_top
  exact hne (hall I (hIeq.trans_lt hlt) x hx)

end Hyperplane

end MvPolynomial

end

namespace MvPolynomial

/-- Over a finite field (`ZMod 2`), `[Infinite K]` cannot be dropped from
`exists_eval_hasseDeriv_ne_zero_of_formIndex_ne_top` or
`le_formIndex_iff_forall_eval_hasseDeriv_eq_zero`, even for homogeneous polynomials: the cubic form
`P = X (0, 1) ^ 2 * X (0, 2) + X (0, 1) * X (0, 2) ^ 2` has `formIndex = 0` along `X (0, 0)`, yet
`hasseDeriv 0 P = P` vanishes at every `ZMod 2`-point. -/
example :
    let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
    let P : MvPolynomial (Fin 1 × Fin 3) (ZMod 2) :=
      X (0, 1) ^ 2 * X (0, 2) + X (0, 1) * X (0, 2) ^ 2
    formIndex ![1] (fun _ ↦ ![1, 0, 0]) P = 0 ∧
      ∀ x : Fin 1 × Fin 3 → ZMod 2, eval x (hasseDeriv 0 P) = 0 := by
  intro _ P
  refine ⟨?_, fun x ↦ ?_⟩
  · have hM : Fin 1 → (![1, 0, 0] : Fin 3 → ZMod 2) 0 ≠ 0 := fun _ ↦ one_ne_zero
    have hsub :
        substFormInv (fun _ : Fin 1 ↦ (![1, 0, 0] : Fin 3 → ZMod 2)) (fun _ ↦ 0) P = P := by
      simp [P]
    set m : Fin 1 × Fin 3 →₀ ℕ := Finsupp.single (0, 1) 2 + Finsupp.single (0, 2) 1
    set m' : Fin 1 × Fin 3 →₀ ℕ := Finsupp.single (0, 1) 1 + Finsupp.single (0, 2) 2
    have hP : P = monomial m 1 + monomial m' 1 := by simp [P, m, m', X, monomial_pow]
    have hne : m' ≠ m := fun h ↦ by
      have := congrArg (· (0, 1)) h
      simp [m, m'] at this
    have hsupp : m ∈ P.support := by
      rw [mem_support_iff, hP]
      simp [hne]
    rw [formIndex_eq_iInf hM, hsub]
    exact nonpos_iff_eq_zero.mp ((iInf₂_le m hsupp).trans_eq (by simp [m]))
  · rw [hasseDeriv_zero, LinearMap.id_apply]
    simp only [P, map_add, map_mul, map_pow, eval_X]
    generalize x (0, 1) = a, x (0, 2) = b
    fin_cases a <;> fin_cases b <;> decide

end MvPolynomial
