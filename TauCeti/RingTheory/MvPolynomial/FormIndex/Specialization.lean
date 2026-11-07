/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Division
public import TauCeti.RingTheory.MvPolynomial.FormIndex.Basic

/-!
# Variable elimination for the index along linear forms

To reduce the generalized Roth lemma for `formIndex` on arbitrary variable blocks `κ × ι` to the
affine Roth index theorem, one eliminates in each block `h : κ` every coordinate outside two chosen
coordinates `i₀ h ≠ i₁ h` with `M h (i₀ h) ≠ 0`, without decreasing `formIndex` or enlarging the set
of nonzero coefficients.

Setting a non-pivot coordinate `X (h₁, j)` (`j ≠ i₀ h₁`) to `0` commutes with `substFormInv` once
the `(h₁, j)`-coefficient of `M` is zeroed out (`MvPolynomial.aeval_update_X_zero_substFormInv`), so
reducing modulo `X (h₁, j)` can only drop monomials of `substFormInv M i₀ P` and therefore cannot
decrease `formIndex` (`MvPolynomial.formIndex_le_formIndex_modMonomial_single`). Naive
specialization `X (h₁, j) ↦ 0` can annihilate `P` when every monomial of `P` is divisible by
`X (h₁, j)`; instead, one first divides `P` by the maximal power `X (h₁, j) ^ k` dividing `P`
(which has `formIndex` zero because `j ≠ i₀ h₁`, leaving `formIndex` unchanged by `formIndex_mul`)
and then reduces modulo `X (h₁, j)`.

Because the minimal exponent of a later variable can strictly increase after an earlier variable is
sliced (for instance, `X (0, 1) + X (0, 2)` has minimal exponent `0` in both `(0, 1)` and `(0, 2)`,
so simultaneous specialization vanishes while sequential slicing yields `1`), variables outside
`{i₀ h, i₁ h}` must be eliminated one at a time. Pulling the resulting polynomial back along the
two-coordinate embedding `(h, 0) ↦ (h, i₁ h), (h, 1) ↦ (h, i₀ h)` and normalizing each two-variable
form by `(M h (i₀ h))⁻¹` yields `MvPolynomial.exists_elimination`.

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

variable {K κ ι : Type*} [Field K]

section SingleVariable

variable [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- Setting a non-pivot variable `X (h₁, j)` (`j ≠ i₀ h₁`) to `0` after `substFormInv M i₀` is the
same as zeroing out `M h₁ j` and applying `substFormInv` after setting `X (h₁, j)` to `0`. -/
theorem aeval_update_X_zero_substFormInv {M : κ → ι → K} {i₀ : κ → ι} {h₁ : κ} {j : ι}
    (hj : j ≠ i₀ h₁) (P : MvPolynomial (κ × ι) K) :
    aeval (Function.update X (h₁, j) (0 : MvPolynomial (κ × ι) K)) (substFormInv M i₀ P) =
      substFormInv (Function.update M h₁ (Function.update (M h₁) j 0)) i₀
        (aeval (Function.update X (h₁, j) 0) P) := by
  set M' := Function.update M h₁ (Function.update (M h₁) j 0)
  set ev : MvPolynomial (κ × ι) K →ₐ[K] MvPolynomial (κ × ι) K :=
    aeval (Function.update X (h₁, j) 0)
  suffices ev.comp (substFormInv M i₀) = (substFormInv M' i₀).comp ev from AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  rcases eq_or_ne (h, i) (h₁, j) with heq | hne
  · cases heq
    simp [ev, hj]
  by_cases hi : i = i₀ h
  · subst hi
    simp only [AlgHom.comp_apply, ev, aeval_X, Function.update_of_ne hne, substFormInv_X_self,
      map_mul, algHom_C, map_sub, map_sum]
    rcases eq_or_ne h h₁ with rfl | hh
    · have hj' : i₀ h ≠ j := hj.symm
      simp only [M', Function.update_self, Function.update_of_ne hj']
      congr 2
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rcases eq_or_ne l j with rfl | hl
      · simp
      · have hnel : (h, l) ≠ (h, j) := fun hc ↦ hl (Prod.mk.inj hc).2
        simp [Function.update_of_ne hl, Function.update_of_ne hnel]
    · simp only [M', Function.update_of_ne hh]
      congr 2
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have hnel : (h, l) ≠ (h₁, j) := fun hc ↦ hh (Prod.mk.inj hc).1
      simp [Function.update_of_ne hnel]
  · simp [ev, Function.update_of_ne hne, hi]

variable [Fintype κ]

/-- Reducing modulo `X (h₁, j)` for `j ≠ i₀ h₁` and zeroing out `M h₁ j` does not decrease
`formIndex`. -/
theorem formIndex_le_formIndex_modMonomial_single {d : κ → ℕ} {M : κ → ι → K} {i₀ : κ → ι}
    (hM : ∀ h, M h (i₀ h) ≠ 0) {h₁ : κ} {j : ι} (hj : j ≠ i₀ h₁) (P : MvPolynomial (κ × ι) K) :
    formIndex d M P ≤
      formIndex d (Function.update M h₁ (Function.update (M h₁) j 0))
        (P.modMonomial (Finsupp.single (h₁, j) 1)) := by
  set M' := Function.update M h₁ (Function.update (M h₁) j 0)
  have hM' (h : κ) : M' h (i₀ h) ≠ 0 := by
    rcases eq_or_ne h h₁ with rfl | hh
    · simpa [M', hj.symm] using hM h
    · simpa [M', hh] using hM h
  have hcomm : substFormInv M' i₀ (P.modMonomial (Finsupp.single (h₁, j) 1)) =
      (substFormInv M i₀ P).modMonomial (Finsupp.single (h₁, j) 1) := by
    rw [← aeval_update_X_zero_eq_modMonomial, ← aeval_update_X_zero_substFormInv hj,
      aeval_update_X_zero_eq_modMonomial]
  rw [formIndex_eq_iInf hM, formIndex_eq_iInf hM', hcomm]
  refine le_iInf₂ fun n hn ↦ iInf₂_le n ?_
  have hns : ¬ Finsupp.single (h₁, j) 1 ≤ n :=
    fun hle ↦ mem_support_iff.mp hn (coeff_modMonomial_of_le _ hle)
  rw [mem_support_iff, coeff_modMonomial_of_not_le _ hns, ← mem_support_iff] at hn
  exact hn

omit [DecidableEq κ] [DecidableEq ι] in
/-- A power of a non-pivot variable `X (h₁, j)` (`j ≠ i₀ h₁`) has `formIndex` zero. -/
private theorem formIndex_X_pow_eq_zero {d : κ → ℕ} {M : κ → ι → K} {i₀ : κ → ι}
    (hM : ∀ h, M h (i₀ h) ≠ 0) {h₁ : κ} {j : ι} (hj : j ≠ i₀ h₁) (k : ℕ) :
    formIndex d M (X (h₁, j) ^ k : MvPolynomial (κ × ι) K) = 0 := by
  classical
  have hMne : ∀ h, M h ≠ 0 := fun h ↦ Function.ne_iff.mpr ⟨i₀ h, hM h⟩
  rw [formIndex_pow hMne, formIndex_eq_iInf hM, substFormInv_X_of_ne hj, support_X]
  suffices (⨅ n ∈ ({Finsupp.single (h₁, j) 1} : Finset (κ × ι →₀ ℕ)),
      ∑ h, (n (h, i₀ h) : ℝ≥0∞) / d h) = 0 by rw [this, smul_zero]
  refine nonpos_iff_eq_zero.mp
    ((iInf₂_le (Finsupp.single (h₁, j) 1) (mem_singleton_self _)).trans_eq
      (Finset.sum_eq_zero fun h _ ↦ ?_))
  have hne : (h₁, j) ≠ (h, i₀ h) := fun hc ↦ hj ((Prod.mk.inj hc).1 ▸ (Prod.mk.inj hc).2)
  simp [hne]

/-- Eliminating a single non-pivot variable `(h₁, j)` (`j ≠ i₀ h₁`) by dividing out its minimal
exponent in `P` and reducing modulo `X (h₁, j)`. -/
private theorem exists_eliminate_single {d e : κ → ℕ} {M : κ → ι → K} {i₀ : κ → ι}
    (hM : ∀ h, M h (i₀ h) ≠ 0) {P : MvPolynomial (κ × ι) K} (hP : P ≠ 0)
    (hPhom : IsMultiHomogeneous e P) {h₁ : κ} {j : ι} (hj : j ≠ i₀ h₁) :
    ∃ (P' : MvPolynomial (κ × ι) K) (e' : κ → ℕ),
      P' ≠ 0 ∧ (∀ h, e' h ≤ e h) ∧ IsMultiHomogeneous e' P' ∧
      P'.vars ⊆ P.vars.erase (h₁, j) ∧
      (∀ n' ∈ P'.support, ∃ n ∈ P.support, P'.coeff n' = P.coeff n) ∧
      formIndex d M P ≤
        formIndex d (Function.update M h₁ (Function.update (M h₁) j 0)) P' := by
  obtain ⟨n₀, hn₀, hmin⟩ :=
    Finset.exists_min_image P.support (fun n ↦ n (h₁, j)) (support_nonempty.mpr hP)
  set k := n₀ (h₁, j)
  set s := Finsupp.single (h₁, j) k
  set Q := P.divMonomial s
  set P' := Q.modMonomial (Finsupp.single (h₁, j) 1)
  have hmod0 : P.modMonomial s = 0 := by
    ext n
    by_cases hle : s ≤ n
    · simp [coeff_modMonomial_of_le P hle]
    · rw [coeff_modMonomial_of_not_le P hle]
      exact notMem_support_iff.mp fun hn ↦ hle (Finsupp.single_le_iff.mpr (hmin n hn))
  have hPeq : X (h₁, j) ^ k * Q = P := by
    have := divMonomial_add_modMonomial P s
    rwa [hmod0, add_zero, ← X_pow_eq_monomial] at this
  have hP'ne : P' ≠ 0 := by
    intro h0
    have hsle : s ≤ n₀ := Finsupp.single_le_iff.mpr le_rfl
    have hm0 : ¬ Finsupp.single (h₁, j) 1 ≤ n₀ - s := by
      rw [Finsupp.single_le_iff]
      simp [s, k]
    have hc : P'.coeff (n₀ - s) = P.coeff n₀ := by
      rw [coeff_modMonomial_of_not_le Q hm0, coeff_divMonomial, add_tsub_cancel_of_le hsle]
    exact mem_support_iff.mp hn₀ (hc ▸ by simp [h0])
  have hvars : P'.vars ⊆ P.vars.erase (h₁, j) := fun p hp ↦
    mem_erase.mpr ⟨ne_of_mem_of_not_mem hp (notMem_vars_modMonomial_single Q (h₁, j)),
      vars_divMonomial_subset P s (vars_modMonomial_subset Q _ hp)⟩
  have hcoeff : ∀ n' ∈ P'.support, ∃ n ∈ P.support, P'.coeff n' = P.coeff n := by
    intro n' hn'
    have hns : ¬ Finsupp.single (h₁, j) 1 ≤ n' :=
      fun hle ↦ mem_support_iff.mp hn' (coeff_modMonomial_of_le Q hle)
    have hc : P'.coeff n' = P.coeff (s + n') := by
      rw [coeff_modMonomial_of_not_le Q hns, coeff_divMonomial]
    exact ⟨s + n', mem_support_iff.mpr (hc ▸ mem_support_iff.mp hn'), hc⟩
  have hMne : ∀ h, M h ≠ 0 := fun h ↦ Function.ne_iff.mpr ⟨i₀ h, hM h⟩
  have hidx : formIndex d M P ≤
      formIndex d (Function.update M h₁ (Function.update (M h₁) j 0)) P' := by
    rw [← hPeq, formIndex_mul hMne, formIndex_X_pow_eq_zero hM hj, zero_add]
    exact formIndex_le_formIndex_modMonomial_single hM hj Q
  exact ⟨P', fun h ↦ e h - ∑ i, s (h, i), hP'ne, fun h ↦ Nat.sub_le _ _,
    (hPhom.divMonomial s).modMonomial _, hvars, hcoeff, hidx⟩

end SingleVariable

section FinsetElimination

variable [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- Iteratively eliminating every variable in a finite set `S` of non-pivot coordinates. -/
private theorem exists_eliminate_finset {d : κ → ℕ} {i₀ : κ → ι} (S : Finset (κ × ι))
    (hS : ∀ p ∈ S, p.2 ≠ i₀ p.1) :
    ∀ {e : κ → ℕ} {M : κ → ι → K} (_ : ∀ h, M h (i₀ h) ≠ 0)
      {P : MvPolynomial (κ × ι) K} (_ : P ≠ 0) (_ : IsMultiHomogeneous e P),
      ∃ (P' : MvPolynomial (κ × ι) K) (e' : κ → ℕ) (M' : κ → ι → K),
        P' ≠ 0 ∧ (∀ h, e' h ≤ e h) ∧ IsMultiHomogeneous e' P' ∧
        Disjoint P'.vars S ∧ P'.vars ⊆ P.vars ∧
        (∀ p ∉ S, M' p.1 p.2 = M p.1 p.2) ∧ (∀ p ∈ S, M' p.1 p.2 = 0) ∧
        (∀ n' ∈ P'.support, ∃ n ∈ P.support, P'.coeff n' = P.coeff n) ∧
        formIndex d M P ≤ formIndex d M' P' := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro e M _ P hP hPhom
    exact ⟨P, e, M, hP, fun _ ↦ le_rfl, hPhom, Finset.disjoint_empty_right _, Subset.rfl,
      fun _ _ ↦ rfl, fun _ hp ↦ (notMem_empty _ hp).elim, fun n hn ↦ ⟨n, hn, rfl⟩, le_rfl⟩
  | @insert p₀ S hp₀ ih =>
    intro e M hM P hP hPhom
    obtain ⟨h₁, j⟩ := p₀
    have hj : j ≠ i₀ h₁ := hS (h₁, j) (mem_insert_self _ _)
    obtain ⟨P₁, e₁, hP₁, he₁, hP₁hom, hP₁vars, hP₁coeff, hP₁idx⟩ :=
      exists_eliminate_single (d := d) hM hP hPhom hj
    set M₁ := Function.update M h₁ (Function.update (M h₁) j 0)
    have hM₁ (h : κ) : M₁ h (i₀ h) ≠ 0 := by
      rcases eq_or_ne h h₁ with rfl | hh
      · simpa [M₁, hj.symm] using hM h
      · simpa [M₁, hh] using hM h
    obtain ⟨P', e', M', hP', he', hP'hom, hdisj, hsub, hM'out, hM'in, hcoeff', hidx'⟩ :=
      ih (fun p hp ↦ hS p (mem_insert_of_mem hp)) hM₁ hP₁ hP₁hom
    have hp₀not : (h₁, j) ∉ P'.vars := fun hmem ↦
      (mem_erase.mp (hP₁vars (hsub hmem))).1 rfl
    refine ⟨P', e', M', hP', fun h ↦ (he' h).trans (he₁ h), hP'hom,
      disjoint_insert_right.mpr ⟨hp₀not, hdisj⟩,
      hsub.trans (hP₁vars.trans (erase_subset _ _)), ?_, ?_, ?_, hP₁idx.trans hidx'⟩
    · intro p hp
      rw [hM'out p (fun hs ↦ hp (mem_insert_of_mem hs))]
      have hpne : p ≠ (h₁, j) := fun hc ↦ hp (hc ▸ mem_insert_self _ _)
      rcases eq_or_ne p.1 h₁ with hh | hh
      · have hjne : p.2 ≠ j := fun h2 ↦ hpne (Prod.ext hh h2)
        simp [M₁, hh, Function.update_of_ne hjne]
      · simp [M₁, Function.update_of_ne hh]
    · intro p hp
      rcases mem_insert.mp hp with rfl | hpS
      · rw [hM'out (h₁, j) hp₀]
        simp [M₁]
      · exact hM'in p hpS
    · intro n' hn'
      obtain ⟨n₁, hn₁, hc₁⟩ := hcoeff' n' hn'
      obtain ⟨n, hn, hc⟩ := hP₁coeff n₁ hn₁
      exact ⟨n, hn, hc₁.trans hc⟩

omit [Field K] [Fintype κ] [DecidableEq κ] [Fintype ι] in
private theorem twoCoordEmb_injective {i₀ i₁ : κ → ι} (hne : ∀ h, i₀ h ≠ i₁ h) :
    Function.Injective (fun p : κ × Fin 2 ↦ (p.1, ![i₁ p.1, i₀ p.1] p.2)) := by
  rintro ⟨h, c⟩ ⟨h', c'⟩ hc
  obtain ⟨rfl, hc2⟩ := Prod.mk.inj hc
  fin_cases c <;> fin_cases c' <;> simp_all [(hne h).symm]

omit [DecidableEq κ] in
/-- Pulling `formIndex` back along the injective two-coordinate embedding
`emb (h, 0) = (h, i₁ h), emb (h, 1) = (h, i₀ h)` when all outside coefficients of `M'` vanish. -/
private theorem formIndex_rename_twoCoord {d : κ → ℕ} {i₀ i₁ : κ → ι} (hne : ∀ h, i₀ h ≠ i₁ h)
    {M' : κ → ι → K} (hM' : ∀ h, M' h (i₀ h) ≠ 0)
    (hzero : ∀ h i, i ≠ i₀ h → i ≠ i₁ h → M' h i = 0) (Q : MvPolynomial (κ × Fin 2) K) :
    formIndex d M' (rename (fun p : κ × Fin 2 ↦ (p.1, ![i₁ p.1, i₀ p.1] p.2)) Q) =
      formIndex d (fun h ↦ ![M' h (i₁ h), M' h (i₀ h)]) Q := by
  classical
  set emb : κ × Fin 2 → κ × ι := fun p ↦ (p.1, ![i₁ p.1, i₀ p.1] p.2)
  set N : κ → Fin 2 → K := fun h ↦ ![M' h (i₁ h), M' h (i₀ h)]
  have hemb : Function.Injective emb := twoCoordEmb_injective hne
  have hsub : substFormInv M' i₀ (rename emb Q) = rename emb (substFormInv N (fun _ ↦ 1) Q) := by
    suffices (substFormInv M' i₀).comp (rename emb) =
        (rename emb).comp (substFormInv N (fun _ ↦ 1)) from AlgHom.congr_fun this Q
    ext ⟨h, c⟩ : 1
    fin_cases c
    · simp [emb, (hne h).symm]
    · have herase2 : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
      simp only [AlgHom.comp_apply, Fin.mk_one, rename_X, emb, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [substFormInv_X_self, substFormInv_X_self]
      simp only [map_mul, algHom_C, map_sub, rename_X, N, herase2,
        Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      congr 2
      rw [Finset.sum_eq_single (i₁ h)]
      · rfl
      · intro i hi hii₁
        rw [hzero h i (ne_of_mem_erase hi) hii₁, map_zero, zero_mul]
      · intro hnot
        exact (hnot (mem_erase.mpr ⟨(hne h).symm, mem_univ _⟩)).elim
  have hN : ∀ h, N h 1 ≠ 0 := fun h ↦ hM' h
  rw [formIndex_eq_iInf hM', formIndex_eq_iInf hN, hsub, support_rename_of_injective hemb]
  refine le_antisymm (le_iInf₂ fun u hu ↦ ?_) (le_iInf₂ fun m hm ↦ ?_)
  · refine (iInf₂_le (u.mapDomain emb) (mem_image_of_mem _ hu)).trans_eq ?_
    exact Finset.sum_congr rfl fun h _ ↦ by
      have h1 : emb (h, 1) = (h, i₀ h) := rfl
      rw [← h1, Finsupp.mapDomain_apply_of_injective hemb]
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp hm
    refine (iInf₂_le u hu).trans_eq ?_
    exact Finset.sum_congr rfl fun h _ ↦ by
      have h1 : emb (h, 1) = (h, i₀ h) := rfl
      rw [← h1, Finsupp.mapDomain_apply_of_injective hemb]

omit [Fintype κ] [Fintype ι] in
private theorem isMultiHomogeneous_of_rename_twoCoord [Finite ι] {e' : κ → ℕ} {i₀ i₁ : κ → ι}
    (hne : ∀ h, i₀ h ≠ i₁ h) {Q : MvPolynomial (κ × Fin 2) K}
    (hhom : IsMultiHomogeneous e' (rename (fun p : κ × Fin 2 ↦ (p.1, ![i₁ p.1, i₀ p.1] p.2)) Q)) :
    IsMultiHomogeneous e' Q := by
  classical
  cases nonempty_fintype ι
  set emb : κ × Fin 2 → κ × ι := fun p ↦ (p.1, ![i₁ p.1, i₀ p.1] p.2)
  have hemb : Function.Injective emb := twoCoordEmb_injective hne
  rw [isMultiHomogeneous_iff]
  intro u hu h
  have hc : (rename emb Q).coeff (u.mapDomain emb) ≠ 0 := by
    rwa [coeff_rename_mapDomain emb hemb]
  have hsum := isMultiHomogeneous_iff.mp hhom (u.mapDomain emb) hc h
  have hpair : ∑ i : ι, (u.mapDomain emb) (h, i) = u (h, 0) + u (h, 1) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (i₁ h)),
      ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨hne h, mem_univ (i₀ h)⟩)]
    have hrest : ∑ i ∈ (univ.erase (i₁ h)).erase (i₀ h), (u.mapDomain emb) (h, i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ Finsupp.mapDomain_of_notMem_range u _ fun ⟨⟨h', c⟩, hc⟩ ↦ by
        obtain ⟨rfl, hc2⟩ := Prod.mk.inj hc
        fin_cases c
        · exact (mem_erase.mp (mem_erase.mp hi).2).1 hc2.symm
        · exact (mem_erase.mp hi).1 hc2.symm
    have h0 : emb (h, 0) = (h, i₁ h) := rfl
    have h1 : emb (h, 1) = (h, i₀ h) := rfl
    rw [hrest, add_zero, ← h0, ← h1, Finsupp.mapDomain_apply_of_injective hemb,
      Finsupp.mapDomain_apply_of_injective hemb]
  rw [Fin.sum_univ_two, ← hpair, hsum]

/-- **Variable elimination to two coordinates per block.** Given a nonzero multihomogeneous
polynomial `P` of multidegree `e` and two distinct coordinates `i₀ h ≠ i₁ h` per block with
`M h (i₀ h) ≠ 0`, sequential minimal-exponent slicing produces a nonzero multihomogeneous polynomial
`Q` on `κ × Fin 2` of multidegree `e' ≤ e` whose nonzero coefficients all occur in `P` and whose
index along the affine-chart forms `![- (- (M h (i₁ h) / M h (i₀ h))), 1]` is at least
`formIndex d M P`. -/
theorem exists_elimination {d e : κ → ℕ} {M : κ → ι → K} {i₀ i₁ : κ → ι}
    (hne : ∀ h, i₀ h ≠ i₁ h) (hM : ∀ h, M h (i₀ h) ≠ 0) {P : MvPolynomial (κ × ι) K}
    (hP : P ≠ 0) (hPhom : IsMultiHomogeneous e P) :
    ∃ (Q : MvPolynomial (κ × Fin 2) K) (e' : κ → ℕ),
      Q ≠ 0 ∧ (∀ h, e' h ≤ e h) ∧ IsMultiHomogeneous e' Q ∧
      (∀ u ∈ Q.support, ∃ n ∈ P.support, Q.coeff u = P.coeff n) ∧
      formIndex d M P ≤
        formIndex d (fun h ↦ ![- (- (M h (i₁ h) / M h (i₀ h))), 1]) Q := by
  classical
  set S : Finset (κ × ι) := univ.filter fun p ↦ p.2 ≠ i₀ p.1 ∧ p.2 ≠ i₁ p.1
  obtain ⟨P₁, e', M', hP₁, he', hP₁hom, hdisj, -, hM'out, hM'in, hP₁coeff, hidx⟩ :=
    exists_eliminate_finset (d := d) S (fun p hp ↦ (mem_filter.mp hp).2.1) hM hP hPhom
  set emb : κ × Fin 2 → κ × ι := fun p ↦ (p.1, ![i₁ p.1, i₀ p.1] p.2)
  have hemb : Function.Injective emb := twoCoordEmb_injective hne
  have hrange : (P₁.vars : Set (κ × ι)) ⊆ Set.range emb := by
    rintro ⟨h, i⟩ hp
    have hnotS : (h, i) ∉ S := Finset.disjoint_left.mp hdisj hp
    simp only [S, mem_filter, mem_univ, true_and, not_and_or, not_ne_iff] at hnotS
    rcases hnotS with rfl | rfl
    · exact ⟨(h, 1), rfl⟩
    · exact ⟨(h, 0), rfl⟩
  obtain ⟨Q, hQeq⟩ := exists_rename_eq_of_vars_subset_range P₁ emb hemb hrange
  have hQne : Q ≠ 0 := fun h0 ↦ hP₁ (by rw [← hQeq, h0, map_zero])
  have hQcoeff : ∀ u ∈ Q.support, ∃ n ∈ P.support, Q.coeff u = P.coeff n := by
    intro u hu
    have hc : Q.coeff u = P₁.coeff (u.mapDomain emb) := by
      rw [← hQeq, coeff_rename_mapDomain emb hemb]
    exact Exists.imp (fun n hn ↦ ⟨hn.1, hc.trans hn.2⟩)
      (hP₁coeff _ (mem_support_iff.mpr (hc ▸ mem_support_iff.mp hu)))
  have hM'0 (h : κ) : M' h (i₀ h) = M h (i₀ h) := hM'out (h, i₀ h) (by simp [S])
  have hM'1 (h : κ) : M' h (i₁ h) = M h (i₁ h) := hM'out (h, i₁ h) (by simp [S])
  have hM'z (h : κ) (i : ι) (hi0 : i ≠ i₀ h) (hi1 : i ≠ i₁ h) : M' h i = 0 :=
    hM'in (h, i) (mem_filter.mpr ⟨mem_univ _, hi0, hi1⟩)
  have hscale : (fun h ↦ (M h (i₀ h))⁻¹ • ![M' h (i₁ h), M' h (i₀ h)]) =
      (fun h ↦ ![- (- (M h (i₁ h) / M h (i₀ h))), 1]) := by
    ext h c
    fin_cases c <;> simp [hM'0, hM'1, div_eq_inv_mul, hM h]
  refine ⟨Q, e', hQne, he', isMultiHomogeneous_of_rename_twoCoord hne (hQeq.symm ▸ hP₁hom),
    hQcoeff, hidx.trans_eq ?_⟩
  rw [← hQeq, formIndex_rename_twoCoord hne (fun h ↦ (hM'0 h).symm ▸ hM h) hM'z,
    ← formIndex_smul_form (c := fun h ↦ (M h (i₀ h))⁻¹)
      (fun h ↦ isUnit_iff_ne_zero.mpr (inv_ne_zero (hM h))), hscale]

/-- Simultaneous specialization at componentwise-minimum exponents can annihilate a nonzero
multihomogeneous polynomial, whereas `exists_elimination` (which slices sequentially) preserves
nonvanishing: `P = X (0, 1) + X (0, 2)` has minimal exponent `0` in both `(0, 1)` and `(0, 2)`, so
setting both to `0` at once yields `0`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 3) ℚ := X (0, 1) + X (0, 2)
    P ≠ 0 ∧ IsMultiHomogeneous (Pi.single 0 1) P ∧
      aeval (fun p : Fin 1 × Fin 3 ↦ if p.2 = 0 then X p else (0 : MvPolynomial (Fin 1 × Fin 3) ℚ))
        P = 0 := by
  intro P
  refine ⟨?_, ?_, by simp [P]⟩
  · intro h0
    have := congrArg (eval (Pi.single ((0 : Fin 1), (1 : Fin 3)) (1 : ℚ))) h0
    simp [P, Pi.single_eq_of_ne] at this
  · exact (isMultiHomogeneous_X (0 : Fin 1) (1 : Fin 3)).add (isMultiHomogeneous_X 0 2)

end FinsetElimination

end MvPolynomial
