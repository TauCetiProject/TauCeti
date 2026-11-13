/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.FormIndex

import TauCeti.NumberTheory.DiophantineApproximation.Roth.IndexEstimate
import TauCeti.NumberTheory.Height.Basic

/-!
# Generalized Roth lemma for the index along linear forms

This file bounds the form index `MvPolynomial.formIndex d M P` of a nonzero multihomogeneous
polynomial `P` along a tuple of nonzero linear forms `M : Fin m → ι → K` over a number field
`K` when the block degree bounds `d h` decay geometrically (`d (h + 1) ≤ σ * d h` for
`0 < σ ≤ 1 / 2`) and the heights of the forms are large compared to `h(P)` and `m * d 0 * [K : ℚ]`
(Bombieri–Gubler, Lemma 7.5.19).

The proof reduces the multivariable linear-form statement to Roth's lemma
(`TauCeti.weightedIndex_le_of_logHeight_le`):
1. In each block `h`, `Height.exists_logHeight_le_mul_logHeight₁_div` finds distinct coordinates
   `i₀ h ≠ i₁ h` with `M h (i₁ h) ≠ 0` such that
   `h(M h) ≤ (card ι - 1) * h(-M h (i₀ h) / M h (i₁ h))`.
2. Iterated elimination (`MvPolynomial.exists_elimination`) specializes every other coordinate to
   `0` without vanishing, without increasing the multidegrees or the coefficient height, and
   without lowering `formIndex`.
3. Renaming the surviving two coordinates per block (`MvPolynomial.formIndex_rename_pair`) and
   dehomogenizing (`MvPolynomial.formIndex_eq_weightedIndex_dehomogenize_of_ne_zero`) preserves
   both the index and the coefficient height
   (`MvPolynomial.logHeight_blockDehomogenize_of_isMultiHomogeneous`), yielding a polynomial in `m`
   variables to which Roth's lemma applies.

## Main results

* `MvPolynomial.mulHeight_blockDehomogenize_of_isMultiHomogeneous`,
  `MvPolynomial.logHeight_blockDehomogenize_of_isMultiHomogeneous`: dehomogenizing a
  multihomogeneous polynomial preserves its coefficient height.
* `MvPolynomial.formIndex_le_of_degree_ratio`: the generalized Roth lemma for
  `MvPolynomial.formIndex`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Definitions 7.5.17–7.5.18 and Lemma 7.5.19.
-/

public section

open Module

namespace MvPolynomial

section Height

variable {K κ : Type*} [Field K] [Height.AdmissibleAbsValues K] [Finite κ] [DecidableEq κ]

/-- Dehomogenizing a multihomogeneous polynomial in two-variable blocks preserves its
multiplicative coefficient height, since `blockDehomogenize` bijects `P.support` onto the
support of the dehomogenized polynomial while preserving coefficients. -/
theorem mulHeight_blockDehomogenize_of_isMultiHomogeneous {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) :
    (blockDehomogenize P).mulHeight = P.mulHeight := by
  classical
  have hinj : Function.Injective (fun h : κ ↦ (h, (1 : Fin 2))) :=
    fun _ _ h ↦ (Prod.ext_iff.mp h).1
  let proj (n : κ × Fin 2 →₀ ℕ) : κ →₀ ℕ :=
    n.comapDomain (fun h ↦ (h, (1 : Fin 2))) hinj.injOn
  let lift (m : κ →₀ ℕ) : κ × Fin 2 →₀ ℕ :=
    m.mapDomain (fun h ↦ (h, (1 : Fin 2))) +
      Finsupp.equivFunOnFinite.symm (fun p : κ × Fin 2 ↦ if p.2 = 0 then e p.1 - m p.1 else 0)
  have hle_of_sup {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) (h : κ) :
      n (h, 1) ≤ e h := by
    have hsum : n (h, 0) + n (h, 1) = e h := by
      simpa [Fin.sum_univ_two] using isMultiHomogeneous_iff.mp hP n (mem_support_iff.mp hn) h
    omega
  have hlift_proj {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) : lift (proj n) = n := by
    have hsum (h : κ) : n (h, 0) + n (h, 1) = e h := by
      simpa [Fin.sum_univ_two] using isMultiHomogeneous_iff.mp hP n (mem_support_iff.mp hn) h
    ext ⟨h, i⟩
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · have := hsum h
      have hnot : (h, (0 : Fin 2)) ∉ Set.range (fun h : κ ↦ (h, (1 : Fin 2))) := by
        rintro ⟨_, he⟩
        simp at he
      simp only [lift, proj, Finsupp.coe_add, Pi.add_apply,
        Finsupp.mapDomain_of_notMem_range _ _ hnot, zero_add,
        Finsupp.coe_equivFunOnFinite_symm, ↓reduceIte, Finsupp.comapDomain_apply]
      omega
    · simp [lift, proj, Finsupp.comapDomain_apply, Finsupp.mapDomain_apply_of_injective hinj,
        Finsupp.coe_equivFunOnFinite_symm]
  have hcoeff {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) :
      (blockDehomogenize P).coeff (proj n) = P.coeff n := by
    rw [coeff_blockDehomogenize_of_isMultiHomogeneous hP (proj n)
        (fun h ↦ by simpa [proj, Finsupp.comapDomain_apply] using hle_of_sup hn h)]
    exact congrArg P.coeff (hlift_proj hn)
  let f : P.support → (blockDehomogenize P).support := fun ⟨n, hn⟩ ↦
    ⟨proj n, mem_support_iff.mpr (by rw [hcoeff hn]; exact mem_support_iff.mp hn)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ heq ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
    · have hproj : proj n₁ = proj n₂ := congrArg Subtype.val heq
      have hsub : n₁ = n₂ := by rw [← hlift_proj hn₁, hproj, hlift_proj hn₂]
      exact Subtype.ext hsub
    · obtain ⟨n, hn, hnm⟩ := (mem_support_blockDehomogenize_iff_of_isMultiHomogeneous hP).mp hm
      refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
      ext h
      simp [f, proj, Finsupp.comapDomain_apply, hnm h]
  rw [mulHeight_eq_support, mulHeight_eq_support,
    ← Height.mulHeight_comp_equiv (Equiv.ofBijective f hbij)]
  exact congrArg Height.mulHeight (funext fun ⟨n, hn⟩ ↦ hcoeff hn)

/-- Dehomogenizing a multihomogeneous polynomial in two-variable blocks preserves its logarithmic
coefficient height. -/
theorem logHeight_blockDehomogenize_of_isMultiHomogeneous {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) :
    (blockDehomogenize P).logHeight = P.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_blockDehomogenize_of_isMultiHomogeneous hP,
    logHeight_eq_log_mulHeight]

end Height

section GeneralizedRoth

/-- **Generalized Roth lemma for the index along linear forms** (Bombieri–Gubler, Lemma 7.5.19).
Let `P ≠ 0` be a multihomogeneous polynomial in `m ≥ 1` blocks of `card ι ≥ 2` variables over
a number field `K`, with multidegree `e h ≤ d h` for positive weights `d h` satisfying
`d (h + 1) ≤ σ * d h` where `0 < σ ≤ 1 / 2`. If
`(card ι - 1) * σ⁻¹ * (h(P) + 4 * m * d 0 * [K : ℚ]) ≤ d h * h(M h)` for every block `h`,
then `formIndex d M P ≤ 2 * m * σ ^ (1 / 2 ^ (m - 1))`. -/
theorem formIndex_le_of_degree_ratio {K : Type*} [Field K] [NumberField K]
    {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι] [Nontrivial ι]
    {P : MvPolynomial (Fin m × ι) K} (hP : P ≠ 0) {e d : Fin m → ℕ}
    (hPe : P.IsMultiHomogeneous e) (hed : ∀ h, e h ≤ d h) (hd : ∀ h, 0 < d h)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1 / 2)
    (hratio : ∀ h j : Fin m, (j : ℕ) = h + 1 → (d j : ℝ) ≤ σ * d h)
    {M : Fin m → ι → K} (hM : ∀ h, M h ≠ 0)
    (hMh : ∀ h, ((Fintype.card ι - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K)) ≤ d h * Height.logHeight (M h)) :
    formIndex d M P ≤ ENNReal.ofReal (2 * m * σ ^ ((1 : ℝ) / 2 ^ (m - 1))) := by
  classical
  -- Step 1: in each block, choose distinct coordinates `i₀ h ≠ i₁ h` capturing `h(M h)`.
  have hchoice : ∀ h : Fin m, ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ M h i₁ ≠ 0 ∧
      Height.logHeight (M h) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) * Height.logHeight₁ (-M h i₀ / M h i₁) := by
    intro h
    obtain ⟨i₀, i₁, hne, hne0, hlog⟩ :=
      Height.exists_logHeight_le_mul_logHeight₁_div (hM h)
    refine ⟨i₀, i₁, hne, hne0, ?_⟩
    rw [Nat.card_eq_fintype_card] at hlog
    rwa [neg_div, Height.logHeight₁_neg]
  choose i₀ i₁ hdiff hM₁ hlog_M using hchoice
  -- Step 2: eliminate every variable outside `{(h, i₀ h), (h, i₁ h)}`.
  let s : Finset (Fin m × ι) := Finset.univ.filter fun p ↦ p.2 ≠ i₀ p.1 ∧ p.2 ≠ i₁ p.1
  have hs : ∀ p ∈ s, p.2 ≠ i₁ p.1 := fun p hp ↦ (Finset.mem_filter.mp hp).2.2
  obtain ⟨Q, e', sh, hQ0, hQe, he', hvars, hcoeff, hind_elim⟩ :=
    exists_elimination (d := d) hM₁ hP hPe s hs
  have hQ_log : Q.logHeight ≤ P.logHeight := by
    let u : Finset (Fin m × ι →₀ ℕ) := Q.support.image (· + sh) ∪ P.support
    let idx : Q.support → u := fun ⟨n, hn⟩ ↦
      ⟨n + sh, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hn)⟩
    have hQ_mul : Q.mulHeight ≤ P.mulHeight := by
      rw [mulHeight_eq_support, mulHeight_eq_coeff P u Finset.subset_union_right]
      have hcomp : (fun n : Q.support ↦ Q.coeff n.1) = (fun n : u ↦ P.coeff n.1) ∘ idx :=
        funext fun ⟨n, hn⟩ ↦ hcoeff n hn
      rw [hcomp]
      exact Height.mulHeight_comp_le idx _
    rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight]
    exact Real.log_le_log (mulHeight_pos Q) hQ_mul
  -- Step 3: rename to `Fin m × Fin 2` and dehomogenize.
  let f : Fin m × Fin 2 → Fin m × ι := fun p ↦ (p.1, if p.2 = 0 then i₀ p.1 else i₁ p.1)
  have hf : Function.Injective f := by
    rintro ⟨h₁, j₁⟩ ⟨h₂, j₂⟩ h
    obtain ⟨rfl, hj⟩ : h₁ = h₂ ∧ _ := by simpa [f] using h
    rcases Fin.exists_fin_two.mp ⟨j₁, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨j₂, rfl⟩ with rfl | rfl
    · rfl
    · exact absurd hj (hdiff h₁)
    · exact absurd hj.symm (hdiff h₁)
    · rfl
  have hQ_range : ↑Q.vars ⊆ Set.range f := by
    rintro ⟨h, k⟩ hk
    have hmem_s : (h, k) ∉ s := fun hc ↦ hvars (h, k) hc hk
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hmem_s
    by_cases hk₀ : k = i₀ h
    · exact ⟨(h, 0), by simp [f, hk₀]⟩
    · exact ⟨(h, 1), by simp [f, hmem_s hk₀]⟩
  obtain ⟨Q₂, hQ₂⟩ := exists_rename_eq_of_vars_subset_range' Q f hQ_range
  have hQ₂0 : Q₂ ≠ 0 := fun h ↦ hQ0 (by rw [← hQ₂, h, map_zero])
  have hQ₂e : Q₂.IsMultiHomogeneous e' :=
    isMultiHomogeneous_iff_forall_isWeightedHomogeneous.mpr fun h n hn ↦ by
      have hn' : Q.coeff (n.mapDomain f) ≠ 0 := by
        rwa [← hQ₂, coeff_rename_mapDomain f hf]
      have hw := hQe.isWeightedHomogeneous h hn'
      rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index] at hw
      · simpa [Finsupp.weight_apply, f] using hw
      · intro; simp
      · intro _ _ _; split_ifs <;> simp
  let M' : Fin m → ι → K := fun h k ↦ if (h, k) ∈ s then 0 else M h k
  have hM'₁ : ∀ h, M' h (i₁ h) ≠ 0 := fun h ↦ by
    have hnot : (h, i₁ h) ∉ s := fun hc ↦ by simp [s] at hc
    simpa [M', hnot] using hM₁ h
  have hM'_zero : ∀ h k, k ≠ i₀ h → k ≠ i₁ h → M' h k = 0 := by
    intro h k hk₀ hk₁
    have hmem : (h, k) ∈ s := by simp [s, hk₀, hk₁]
    simp [M', hmem]
  let M₂ : Fin m → Fin 2 → K := fun h j ↦ if j = 0 then M h (i₀ h) else M h (i₁ h)
  have hM'_pair : (fun h j ↦ if j = 0 then M' h (i₀ h) else M' h (i₁ h)) = M₂ := by
    ext h j
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with rfl | rfl
    · have hnot : (h, i₀ h) ∉ s := fun hc ↦ by simp [s] at hc
      simp [M', M₂, hnot]
    · have hnot : (h, i₁ h) ∉ s := fun hc ↦ by simp [s] at hc
      simp [M', M₂, hnot]
  have hM₂₁ : ∀ h, M₂ h 1 ≠ 0 := fun h ↦ by simpa [M₂] using hM₁ h
  let R : MvPolynomial (Fin m) K := blockDehomogenize Q₂
  have hR0 : R ≠ 0 := blockDehomogenize_ne_zero_of_isMultiHomogeneous hQ₂e hQ₂0
  have hRdeg : ∀ h, R.degreeOf h ≤ d h := fun h ↦
    (degreeOf_blockDehomogenize_le hQ₂e h).trans ((he' h).trans (hed h))
  have hRlog : R.logHeight ≤ P.logHeight := by
    dsimp only [R]
    rw [logHeight_blockDehomogenize_of_isMultiHomogeneous hQ₂e, ← logHeight_rename Q₂ hf,
      hQ₂]
    exact hQ_log
  let α : Fin m → K := fun h ↦ -M₂ h 0 / M₂ h 1
  have hindex_eq : formIndex d M' Q = weightedIndex d α R := by
    rw [← hQ₂, formIndex_rename_pair hdiff hM'₁ hM'_zero Q₂, hM'_pair,
      formIndex_eq_weightedIndex_dehomogenize_of_ne_zero hQ₂e hM₂₁]
  -- Step 4: verify the height hypothesis of Roth's lemma and conclude.
  have hcard_pos : (0 : ℝ) < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
    have hlt : 1 < Fintype.card ι := Fintype.one_lt_card
    exact_mod_cast Nat.sub_pos_of_lt hlt
  have hα : ∀ h : Fin m,
      σ⁻¹ * (R.logHeight + 4 * m * d 0 * finrank ℚ K) ≤
        d h * Height.logHeight₁ (α h) := by
    intro h
    have h1 : ((Fintype.card ι - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (R.logHeight + 4 * m * d 0 * finrank ℚ K)) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) *
          (σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K)) := by
      gcongr
    have h2 : d h * Height.logHeight (M h) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) * (d h * Height.logHeight₁ (α h)) := by
      have hlog' : Height.logHeight (M h) ≤
          ((Fintype.card ι - 1 : ℕ) : ℝ) * Height.logHeight₁ (α h) := by
        simpa [α, M₂] using hlog_M h
      calc (d h : ℝ) * Height.logHeight (M h)
          ≤ d h * (((Fintype.card ι - 1 : ℕ) : ℝ) * Height.logHeight₁ (α h)) := by gcongr
        _ = ((Fintype.card ι - 1 : ℕ) : ℝ) * (d h * Height.logHeight₁ (α h)) := by ring
    exact le_of_mul_le_mul_left (h1.trans ((hMh h).trans h2)) hcard_pos
  exact (hind_elim.trans_eq hindex_eq).trans
    (TauCeti.weightedIndex_le_of_logHeight_le hR0 hd hRdeg hσ₀ hσ hratio α hα)

/-- Acceptance check: over `ℚ` with two variables per block and one block (`m = 1`),
`P = X (0, 1) - X (0, 0)` and `M 0 = ![1, 3 ^ 10]` satisfy the hypotheses of
`MvPolynomial.formIndex_le_of_degree_ratio` at `σ = 1 / 2`, giving `formIndex d M P ≤ 1`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 2) ℚ := X (0, 1) - X (0, 0)
    let d : Fin 1 → ℕ := fun _ ↦ 1
    let M : Fin 1 → Fin 2 → ℚ := fun _ ↦ ![1, 3 ^ 10]
    formIndex d M P ≤
      ENNReal.ofReal (2 * (1 : ℕ) * (1 / 2 : ℝ) ^ ((1 : ℝ) / 2 ^ (1 - 1))) := by
  intro P d M
  have hneq01 : (Finsupp.single (0, (0 : Fin 2)) 1 : Fin 1 × Fin 2 →₀ ℕ) ≠
      Finsupp.single (0, 1) 1 := fun h ↦ by
    have := DFunLike.congr_fun h (0, 0)
    simp at this
  have hP0 : P ≠ 0 := fun h ↦ by
    have := congrArg
      (fun p : MvPolynomial (Fin 1 × Fin 2) ℚ ↦ p.coeff (Finsupp.single (0, 1) 1)) h
    simp [P, coeff_X, hneq01] at this
  have hPe : P.IsMultiHomogeneous d := by
    have hpi : (Pi.single 0 1 : Fin 1 → ℕ) = d := by
      ext h
      fin_cases h
      simp [d]
    rw [← hpi]
    exact (isMultiHomogeneous_X (R := ℚ) 0 1).sub (isMultiHomogeneous_X 0 0)
  have hM0 : ∀ h, M h ≠ 0 := fun _ hc ↦ by
    have := congrFun hc 0
    norm_num [M] at this
  have hlogP : P.logHeight ≤ 0 := by
    have hcoeff_bound (v : AbsoluteValue ℚ ℝ) (n : P.support) : v (P.coeff n.1) ≤ 1 := by
      rcases eq_or_ne n.1 (Finsupp.single (0, 1) 1) with hn | hn1
      · simp [P, hn, coeff_X, hneq01]
      · rcases eq_or_ne n.1 (Finsupp.single (0, 0) 1) with hn | hn0
        · simp [P, hn, coeff_X, hneq01.symm]
        · simp [P, coeff_X, hn1.symm, hn0.symm]
    have hm : P.mulHeight ≤ 1 := by
      rw [mulHeight_eq_support]
      have harch : ∀ v ∈ Height.AdmissibleAbsValues.archAbsVal (K := ℚ),
          ⨆ i : P.support, v (P.coeff i.1) ≤ 1 := fun v _ ↦
        Real.iSup_le (fun i ↦ hcoeff_bound v i) zero_le_one
      have hnon : ∀ v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ),
          ⨆ i : P.support, v (P.coeff i.1) ≤ 1 := fun v _ ↦
        Real.iSup_le (fun i ↦ hcoeff_bound v i) zero_le_one
      simpa using Height.mulHeight_le_pow_totalWeight (K := ℚ)
        (x := fun i : P.support ↦ P.coeff i.1) le_rfl harch hnon
    rw [logHeight_eq_log_mulHeight]
    exact Real.log_nonpos (mulHeight_pos P).le hm
  have hlogM : (10 : ℝ) * Real.log 3 ≤ Height.logHeight (M 0) := by
    have hm : ((3 : ℝ) ^ 10 : ℝ) ≤ Height.mulHeight (M 0) := by
      have hratio_le : Height.mulHeight₁ (M 0 1 / M 0 0) ≤ Height.mulHeight (M 0) :=
        Height.mulHeight₁_div_le_mulHeight (M 0) 1 0
      have hm1 : Height.mulHeight₁ (M 0 1 / M 0 0) = 3 ^ 10 := by
        have hval : M 0 1 / M 0 0 = (3 : ℚ) ^ 10 := by simp [M]
        rw [hval, Rat.mulHeight₁_eq_max]
        norm_num
      exact hm1.symm.trans_le hratio_le
    rw [Height.logHeight_eq_log_mulHeight]
    have h10 : (10 : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ 10) := by
      rw [Real.log_pow]
      norm_num
    exact h10.trans_le (Real.log_le_log (by positivity) hm)
  have hlog3 : 1 < Real.log 3 := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hexp
  refine formIndex_le_of_degree_ratio hP0 hPe (fun _ ↦ le_rfl) (fun _ ↦ Nat.zero_lt_one)
    (by norm_num) (by norm_num) (fun h j hhj ↦ by omega) hM0 fun h ↦ ?_
  fin_cases h
  have hfin : (finrank ℚ ℚ : ℝ) = 1 := by simp
  rw [hfin]
  norm_num
  linarith

/-- Rejection check for `[Nontrivial ι]`: with `ι = Fin 1` (single variable per block),
`card ι - 1 = 0`, so the height hypothesis holds vacuously for `P = X (0, 0)`, `d = 1`, `M = 1`,
`σ = 1 / 4`, yet `formIndex d M P = 1 > 2 * 1 * (1 / 4)`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 1) ℚ := X (0, 0)
    let d : Fin 1 → ℕ := fun _ ↦ 1
    let M : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 1
    let σ : ℝ := 1 / 4
    (∀ h, ((Fintype.card (Fin 1) - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (P.logHeight + 4 * (1 : ℕ) * d 0 * finrank ℚ ℚ)) ≤
          d h * Height.logHeight (M h)) ∧
      ENNReal.ofReal (2 * (1 : ℕ) * σ ^ ((1 : ℝ) / 2 ^ (1 - 1))) < formIndex d M P := by
  intro P d M σ
  constructor
  · intro h
    simp
  · have hP : formIndex d M P = 1 := by
      have hM : ∀ h, M h 0 ≠ 0 := fun _ ↦ one_ne_zero
      rw [formIndex_eq_iInf hM]
      have hsub : substFormInv M (fun _ ↦ 0) P = X (0, 0) := by
        simp [P, substFormInv_X_self, M]
      rw [hsub, support_X, Finset.iInf_singleton]
      simp [d]
    rw [hP]
    norm_num [σ]

end GeneralizedRoth

end MvPolynomial
