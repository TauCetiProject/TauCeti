/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.HomogeneousUnits
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Primality and graded localization of the generic depressed discriminant

Over an integral domain `R` in which `2 ≠ 0` and `m` is invertible, `TauCeti.depressedDiscr_prime`
(in `TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed`) proves primality of
`depressedDiscr R m` for all `m ≥ 2`. This file removes the unit assumption on `m` for `m ≥ 3`
by localizing at `m` and descending via the fact that `depressedDiscr R m` has unit leading
coefficient (up to sign) in the coefficient of `X` modulo `m`. This yields
`TauCeti.prime_depressedDiscr` whenever `(2 : R) ≠ 0` and `(m : R) ≠ 0` (for instance over `ℤ`).

In degrees `2` and `3`, `depressedDiscr R 2 = -4 * X 0` and
`depressedDiscr R 3 = -4 * X 0 ^ 3 - 27 * X 1 ^ 2`. Over any integral domain `R` with `2 ≠ 0` and
`m ≠ 0` in `R`, localizing `MvPolynomial (Fin (m - 1)) R` away from `depressedDiscr R m` has
homogeneous unit degrees `m * (m - 1) ℤ` and shift class group `ZMod (m * (m - 1))` for all
`m ≥ 2` (including `m = 2`, where `-4 * X 0` is a nonzero scalar multiple of the prime `X 0`).
In particular, when `2 ≠ 0` and `3 ≠ 0` in an integral domain `R` (such as `ℤ`), the negated cubic
discriminant `4 * X 0 ^ 3 + 27 * X 1 ^ 2` is prime of weight `12` for the weights `![4, 6]`, giving
shift class group `ZMod 12`.

## Main definitions

* `TauCeti.shiftClassGroupAwayDepressedDiscrEquiv`: the shift class group `ZMod (m * (m - 1))`
  after inverting `depressedDiscr R m` over an integral domain `R` with `m ≥ 2`, `(2 : R) ≠ 0`,
  and `(m : R) ≠ 0`.
* `TauCeti.shiftClassGroupAwayWeierstrassEquiv`: the shift class group `ZMod 12` after inverting
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` with weights `![4, 6]` over an integral domain `R` with
  `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.

## Main results

* `TauCeti.prime_depressedDiscr` and `TauCeti.prime_depressedDiscr_of_charZero`: primality of
  `depressedDiscr R m` for `m ≥ 3` over any integral domain with `(2 : R) ≠ 0` and `(m : R) ≠ 0`,
  and over characteristic-zero domains (`m ≥ 2` when `IsUnit (2 : R)` for `m = 2`).
* `TauCeti.homogeneousUnitDegrees_away_depressedDiscr`: the homogeneous unit degrees after
  inverting `depressedDiscr R m` are `AddSubgroup.zmultiples (m * (m - 1))` for all `m ≥ 2` with
  `(2 : R) ≠ 0` and `(m : R) ≠ 0`.
* `TauCeti.prime_four_mul_pow_three_add_twentyseven_mul_sq`: primality of
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` over any integral domain with `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.
-/

public section

namespace TauCeti

open Finset MvPolynomial TauCeti.GradedAlgebra

attribute [local instance] MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

private theorem discr_X_pow_add_X (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    (Polynomial.X ^ m + Polynomial.X : Polynomial R).discr =
      (-1 : R) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : R) ^ (m - 1) := by
  nontriviality R
  have hm1 : m - 1 ≠ 0 := by omega
  have hfac : (Polynomial.X ^ m + Polynomial.X : Polynomial R) =
      Polynomial.X * (Polynomial.X ^ (m - 1) - Polynomial.C (-1)) := by
    rw [map_neg, map_one, sub_neg_eq_add, mul_add, mul_one, ← pow_succ',
      Nat.sub_add_cancel (by omega)]
  have hmonX : (Polynomial.X : Polynomial R).Monic := Polynomial.monic_X
  have hmonQ : (Polynomial.X ^ (m - 1) - Polynomial.C (-1 : R)).Monic :=
    Polynomial.monic_X_pow_sub_C (-1) hm1
  have hdiscrX : (Polynomial.X : Polynomial R).discr = 1 := by
    simpa using Polynomial.discr_X_pow_sub_C (0 : R) 1
  have hres : (Polynomial.X : Polynomial R).resultant
      (Polynomial.X ^ (m - 1) - Polynomial.C (-1)) = 1 := by
    rw [Polynomial.natDegree_X, ← sub_zero (Polynomial.X : Polynomial R), ← Polynomial.C_0,
      Polynomial.resultant_X_sub_C_left _ _ 0 le_rfl]
    simp [zero_pow hm1]
  have hm2 : m - 1 - 1 = m - 2 := by omega
  rw [hfac, hmonX.discr_mul hmonQ, hdiscrX, hres, one_pow, one_mul, mul_one,
    Polynomial.discr_X_pow_sub_C, hm2]
  simp only [neg_neg, one_pow, mul_one]

private theorem depressedDiscr_coeff_single_eq (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    (depressedDiscr R m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m) =
      (-1 : R) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : R) ^ (m - 1) := by
  classical
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let v : Fin (m - 1) → R := Pi.single i₀ 1
  have heval_sum : eval v (depressedDiscr R m) =
      (depressedDiscr R m).coeff (Finsupp.single i₀ m) := by
    rw [eval_eq, Finset.sum_eq_single (Finsupp.single i₀ m)]
    · rw [Finset.prod_eq_single i₀]
      · simp [v]
      · intro j _ hj
        simp [Finsupp.single_eq_of_ne hj]
      · intro hi0
        exact (hi0 (Finsupp.mem_support_iff.mpr (by simp; omega))).elim
    · intro d hd hne
      have hex : ∃ j : Fin (m - 1), j ≠ i₀ ∧ d j ≠ 0 := by
        by_contra hno
        push Not at hno
        have hmem := depressedDiscr_mem R m
        rw [mem_weightedHomogeneousSubmodule] at hmem
        have hwt : Finsupp.weight (depressedWeight m) d = (m : ℤ) * (m - 1) :=
          hmem (mem_support_iff.mp hd)
        have hsum : Finsupp.weight (depressedWeight m) d = (d i₀ : ℤ) * ((m : ℤ) - 1) := by
          rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single i₀]
          · simp only [depressedWeight_apply, i₀, nsmul_eq_mul]
            have hwti0 : ((m - 3 : ℕ) : ℤ) + 2 = (m : ℤ) - 1 := by omega
            rw [hwti0]
          · intro j _ hj
            rw [hno j hj, zero_smul]
          · intro hi0
            rw [Finsupp.notMem_support_iff.mp hi0, zero_smul]
        rw [hsum] at hwt
        have hm1_ne : ((m : ℤ) - 1) ≠ 0 := by omega
        have hdi0 : d i₀ = m := by
          have : (d i₀ : ℤ) = (m : ℤ) := mul_right_cancel₀ hm1_ne hwt
          omega
        apply hne
        ext j
        by_cases hj : j = i₀
        · subst hj; simp [hdi0]
        · simp [hno j hj, hj]
      obtain ⟨j, hj, hdj⟩ := hex
      have hprod : ∏ i ∈ d.support, v i ^ d i = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdj)
          (by simp [v, Pi.single_eq_of_ne hj, hdj])
      rw [hprod, mul_zero]
    · intro hnot
      rw [notMem_support_iff.mp hnot, zero_mul]
  have heval_discr : eval v (depressedDiscr R m) =
      (Polynomial.X ^ m + Polynomial.X : Polynomial R).discr := by
    nontriviality R
    let p : Polynomial R := Polynomial.X ^ m + Polynomial.X
    have hp_mon : p.Monic :=
      (Polynomial.monic_X_pow m).add_of_left (by
        rw [Polynomial.degree_X_pow, Polynomial.degree_X]
        exact_mod_cast (by omega : 1 < m))
    have hp_deg : p.natDegree = m := by
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by
        rw [Polynomial.degree_X_pow, Polynomial.degree_X]
        exact_mod_cast (by omega : 1 < m)), Polynomial.natDegree_X_pow]
    have hp_next : p.nextCoeff = 0 := by
      rw [Polynomial.nextCoeff, hp_deg, ite_eq_right (by omega)]
      simp [p, Polynomial.coeff_X, show m - 1 ≠ m by omega, show 1 ≠ m - 1 by omega]
    have hv_eq : (fun j : Fin (m - 1) ↦ p.coeff (m - 2 - (j : ℕ))) = v := by
      ext j
      by_cases hj : j = i₀
      · subst hj
        simp [p, v, i₀, Polynomial.coeff_X, show m - 2 - (m - 3) = 1 by omega,
          show 1 ≠ m by omega]
      · have hne1 : 1 ≠ m - 2 - (j : ℕ) := by
          intro h1
          apply hj
          ext
          dsimp [i₀]
          omega
        have hnem : m - 2 - (j : ℕ) ≠ m := by omega
        simp [p, v, Polynomial.coeff_X, Pi.single_eq_of_ne hj, hne1, hnem]
    rw [discr_eq_eval_depressedDiscr hp_mon hp_deg hp_next, hv_eq]
  rw [← heval_sum, heval_discr, discr_X_pow_add_X R hm]

private theorem depressedDiscr_dvd_of_C_pow_mul_dvd {R : Type*} [CommRing R] [IsDomain R]
    {m : ℕ} (hm : 3 ≤ m) (hmR : (m : R) ≠ 0) {f : MvPolynomial (Fin (m - 1)) R}
    {k : ℕ} {q : MvPolynomial (Fin (m - 1)) R}
    (h : C ((m : R) ^ k) * f = depressedDiscr R m * q) : depressedDiscr R m ∣ f := by
  induction k generalizing q with
  | zero =>
    rw [pow_zero, map_one, one_mul] at h
    exact ⟨q, h⟩
  | succ k ih =>
    let I : Ideal R := Ideal.span {(m : R)}
    let A := R ⧸ I
    let π : R →+* A := Ideal.Quotient.mk I
    have hπm : π (m : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have hq0 : depressedDiscr A m * MvPolynomial.map π q = 0 := by
      have hmap := congrArg (MvPolynomial.map π) h
      have hpow : π ((m : R) ^ (k + 1)) = 0 := by
        rw [map_pow, hπm, zero_pow (Nat.succ_ne_zero k)]
      rw [map_mul, map_C, hpow, map_zero, zero_mul, map_mul, map_depressedDiscr] at hmap
      exact hmap.symm
    let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
    let σ := (Equiv.optionSubtypeNe i₀).symm
    let e : MvPolynomial (Fin (m - 1)) A ≃ₐ[A]
        Polynomial (MvPolynomial {b : Fin (m - 1) // b ≠ i₀} A) :=
      (renameEquiv A σ).trans (optionEquivLeft A {b : Fin (m - 1) // b ≠ i₀})
    have hcoeff_eq : ∀ (p : MvPolynomial (Fin (m - 1)) A) (n : ℕ)
        (d : {b : Fin (m - 1) // b ≠ i₀} →₀ ℕ),
        ((e p).coeff n).coeff d =
          p.coeff ((Finsupp.optionElim n d).mapDomain (Equiv.optionSubtypeNe i₀)) := by
      intro p n d
      dsimp only [e, AlgEquiv.trans_apply]
      rw [optionEquivLeft_coeff_coeff]
      let u := (Finsupp.optionElim n d).mapDomain (Equiv.optionSubtypeNe i₀)
      have hu : u.mapDomain σ = Finsupp.optionElim n d := by
        dsimp only [u]
        rw [← Finsupp.mapDomain_comp]
        have hcomp : σ ∘ Equiv.optionSubtypeNe i₀ = id :=
          funext (Equiv.symm_apply_apply (Equiv.optionSubtypeNe i₀))
        rw [hcomp, Finsupp.mapDomain_id]
      have hren := coeff_rename_mapDomain σ σ.injective p u
      rw [hu, ← renameEquiv_apply (R := A)] at hren
      exact hren
    have hσ_none : σ i₀ = none := (Equiv.symm_apply_eq (Equiv.optionSubtypeNe i₀)).mpr rfl
    have hσ_some : ∀ j : {b : Fin (m - 1) // b ≠ i₀}, σ j.val = some j := fun j ↦
      (Equiv.symm_apply_eq (Equiv.optionSubtypeNe i₀)).mpr rfl
    have hgt : ∀ n > m, (e (depressedDiscr A m)).coeff n = 0 := by
      intro n hn
      refine MvPolynomial.ext _ _ fun d ↦ ?_
      rw [AddMonoidAlgebra.coeff_zero, hcoeff_eq]
      by_contra hne
      have hmem := depressedDiscr_mem A m
      rw [mem_weightedHomogeneousSubmodule] at hmem
      let u := (Finsupp.optionElim n d).mapDomain (Equiv.optionSubtypeNe i₀)
      have hwt : Finsupp.weight (depressedWeight m) u = (m : ℤ) * (m - 1) := hmem hne
      have hui₀ : u i₀ = n := by
        dsimp only [u]
        rw [Finsupp.mapDomain_equiv_apply, hσ_none, Finsupp.optionElim_apply_none]
      have hle : (u i₀ : ℤ) * depressedWeight m i₀ ≤
          Finsupp.weight (depressedWeight m) u := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        by_cases hiu : i₀ ∈ u.support
        · exact Finset.single_le_sum
            (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _)
              (by rw [depressedWeight_apply]; omega)) hiu
        · rw [Finsupp.notMem_support_iff.mp hiu, Nat.cast_zero, zero_mul]
          exact Finset.sum_nonneg fun j _ ↦
            mul_nonneg (Nat.cast_nonneg _) (by rw [depressedWeight_apply]; omega)
      rw [hwt, hui₀] at hle
      have hwti₀ : depressedWeight m i₀ = (m : ℤ) - 1 := by
        rw [depressedWeight_apply]
        dsimp [i₀]
        omega
      rw [hwti₀] at hle
      have : (n : ℤ) ≤ m := by nlinarith
      omega
    have hcm : (e (depressedDiscr A m)).coeff m =
        C ((depressedDiscr A m).coeff (Finsupp.single i₀ m)) := by
      refine MvPolynomial.ext _ _ fun d ↦ ?_
      rw [hcoeff_eq]
      by_cases hd : d = 0
      · subst hd
        rw [coeff_C, ite_eq_left rfl]
        congr 1
        ext j
        by_cases hj : j = i₀
        · subst hj
          rw [Finsupp.mapDomain_equiv_apply, hσ_none, Finsupp.optionElim_apply_none,
            Finsupp.single_eq_same]
        · rw [Finsupp.mapDomain_equiv_apply, hσ_some ⟨j, hj⟩, Finsupp.optionElim_apply_some,
            Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hj)]
      · rw [coeff_C, ite_eq_right (Ne.symm hd)]
        by_contra hne
        have hmem := depressedDiscr_mem A m
        rw [mem_weightedHomogeneousSubmodule] at hmem
        let u := (Finsupp.optionElim m d).mapDomain (Equiv.optionSubtypeNe i₀)
        have hwt : Finsupp.weight (depressedWeight m) u = (m : ℤ) * (m - 1) := hmem hne
        obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hd
        have huj : u j.val ≠ 0 := by
          dsimp only [u]
          rw [Finsupp.mapDomain_equiv_apply, hσ_some j, Finsupp.optionElim_apply_some]
          exact hj
        have hui₀ : u i₀ = m := by
          dsimp only [u]
          rw [Finsupp.mapDomain_equiv_apply, hσ_none, Finsupp.optionElim_apply_none]
        have hi0_mem : i₀ ∈ u.support := Finsupp.mem_support_iff.mpr (by rw [hui₀]; omega)
        have hj_mem : j.val ∈ u.support := Finsupp.mem_support_iff.mpr huj
        have hsub : ({i₀, j.val} : Finset _) ⊆ u.support := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hi0_mem
          · rw [Finset.mem_singleton.mp hx]; exact hj_mem
        have hsum_le : ∑ x ∈ ({i₀, j.val} : Finset _), (u x : ℤ) * depressedWeight m x ≤
            Finsupp.weight (depressedWeight m) u := by
          rw [Finsupp.weight_apply, Finsupp.sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ ↦
            mul_nonneg (Nat.cast_nonneg _) (by rw [depressedWeight_apply]; omega)
        rw [Finset.sum_pair j.property.symm, hui₀] at hsum_le
        have hwti₀ : depressedWeight m i₀ = (m : ℤ) - 1 := by
          rw [depressedWeight_apply]
          dsimp [i₀]
          omega
        have hwtj : 2 ≤ depressedWeight m j.val := by
          rw [depressedWeight_apply]
          omega
        have huj_pos : (1 : ℤ) ≤ u j.val := by exact_mod_cast Nat.pos_of_ne_zero huj
        rw [hwt, hwti₀] at hsum_le
        nlinarith
    have hunit : IsUnit ((e (depressedDiscr A m)).coeff m) := by
      rw [hcm, depressedDiscr_coeff_single_eq A hm]
      have hmA : (m : A) = 0 := by
        simpa [π] using hπm
      have hm1A : ((m - 1 : ℕ) : A) = -1 := by
        have h1 : ((m - 1 : ℕ) : A) + ((1 : ℕ) : A) = (m : A) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
        rw [Nat.cast_one, hmA] at h1
        exact eq_neg_of_add_eq_zero_left h1
      rw [hm1A, ← pow_add]
      exact (isUnit_one.neg.pow _).map C
    have heq0 : e (depressedDiscr A m) * e (MvPolynomial.map π q) = 0 := by
      rw [← map_mul, hq0, map_zero]
    have hmapq : MvPolynomial.map π q = 0 := by
      by_cases hnt : Nontrivial A
      · have hdeg : (e (depressedDiscr A m)).natDegree = m :=
          Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
            (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hgt) hunit.ne_zero
        have hlc_unit : IsUnit (e (depressedDiscr A m)).leadingCoeff := by
          rw [Polynomial.leadingCoeff, hdeg]
          exact hunit
        exact e.injective
          ((Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hlc_unit).mp heq0)
      · rw [not_nontrivial_iff_subsingleton] at hnt
        exact Subsingleton.elim _ _
    have hr : ∀ r' : R, π r' = 0 ↔ (m : R) ∣ r' := fun r' ↦
      (Ideal.Quotient.eq_zero_iff_mem (I := I)).trans Ideal.mem_span_singleton
    obtain ⟨q', hq_eq⟩ := (MvPolynomial.C_dvd_iff_map_hom_eq_zero π (m : R) hr q).mpr hmapq
    have hnext : C ((m : R) ^ k) * f = depressedDiscr R m * q' := by
      have hC_ne : (C (m : R) : MvPolynomial (Fin (m - 1)) R) ≠ 0 :=
        fun h0 ↦ hmR (C_eq_zero.mp h0)
      apply mul_left_cancel₀ hC_ne
      calc C (m : R) * (C ((m : R) ^ k) * f)
          = C ((m : R) ^ (k + 1)) * f := by rw [pow_succ', map_mul, mul_assoc]
        _ = depressedDiscr R m * q := h
        _ = C (m : R) * (depressedDiscr R m * q') := by rw [hq_eq]; ring
    exact ih hnext

/-- **Primality of the generic depressed discriminant without inverting `m`.** Over any integral
domain `R` in which `(2 : R) ≠ 0` and `(m : R) ≠ 0`, `depressedDiscr R m` is prime for every
`m ≥ 3`. -/
theorem prime_depressedDiscr {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 3 ≤ m) :
    Prime (depressedDiscr R m) := by
  let Rm := Localization.Away (m : R)
  have : IsDomain Rm := IsLocalization.Away.isDomain (S := Rm) hmR
  have hinj : Function.Injective (algebraMap R Rm) :=
    IsLocalization.injective Rm (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hmR))
  have h2m : (2 : Rm) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff (algebraMap R Rm) hinj).mpr h2
  have hum : IsUnit (m : Rm) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (m : R)
  have hprime_Rm : Prime (depressedDiscr Rm m) :=
    depressedDiscr_prime h2m hum (by omega)
  have hmap_eq : MvPolynomial.map (algebraMap R Rm) (depressedDiscr R m) = depressedDiscr Rm m :=
    map_depressedDiscr (algebraMap R Rm)
  refine ⟨fun h0 ↦ hprime_Rm.ne_zero (by rw [← hmap_eq, h0, map_zero]),
    fun hu ↦ hprime_Rm.not_isUnit (hmap_eq ▸ hu.map _), ?_⟩
  intro f g hfg
  have hfg_Rm : depressedDiscr Rm m ∣
      MvPolynomial.map (algebraMap R Rm) f * MvPolynomial.map (algebraMap R Rm) g := by
    have h1 := map_dvd (MvPolynomial.map (σ := Fin (m - 1)) (algebraMap R Rm)) hfg
    rwa [map_mul, hmap_eq] at h1
  have descend : ∀ x : MvPolynomial (Fin (m - 1)) R,
      depressedDiscr Rm m ∣ MvPolynomial.map (algebraMap R Rm) x → depressedDiscr R m ∣ x := by
    let := MvPolynomial.algebraMvPolynomial (σ := Fin (m - 1)) (R := R) (S := Rm)
    rintro x ⟨qRm, hqRm⟩
    obtain ⟨⟨q₀, _, b, ⟨kb, rfl⟩, rfl⟩, hq₀⟩ :=
      IsLocalization.surj ((Submonoid.powers (m : R)).map (C (σ := Fin (m - 1)))) qRm
    simp only [MvPolynomial.algebraMap_def, map_C] at hq₀
    have hcx : C ((m : R) ^ kb) * x = depressedDiscr R m * q₀ := by
      apply MvPolynomial.map_injective _ hinj
      rw [map_mul, map_C, map_mul, hmap_eq, hqRm, mul_left_comm, mul_comm _ qRm, hq₀]
    exact depressedDiscr_dvd_of_C_pow_mul_dvd hm hmR hcx
  rcases hprime_Rm.dvd_or_dvd hfg_Rm with hf | hg
  · exact Or.inl (descend f hf)
  · exact Or.inr (descend g hg)

/-- Over a characteristic-zero integral domain `R`, the generic depressed discriminant
`depressedDiscr R m` is prime for `m ≥ 3`, and also for `m = 2` when `IsUnit (2 : R)`. -/
theorem prime_depressedDiscr_of_charZero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {m : ℕ} (hm : 2 ≤ m) (h2 : m = 2 → IsUnit (2 : R)) : Prime (depressedDiscr R m) := by
  rcases eq_or_lt_of_le hm with rfl | hm3
  · exact depressedDiscr_prime two_ne_zero (h2 rfl) le_rfl
  · exact prime_depressedDiscr two_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hm3

/-! ### Graded localization and the short Weierstrass cubic factor -/

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields homogeneous unit degrees `m * (m - 1) ℤ` over any integral domain `R` with `m ≥ 2`,
`(2 : R) ≠ 0`, and `(m : R) ≠ 0`. -/
theorem homogeneousUnitDegrees_away_depressedDiscr {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      = AddSubgroup.zmultiples ((m : ℤ) * (m - 1)) := by
  rcases eq_or_lt_of_le hm with rfl | hm3
  · have h4 : (-4 : R) ≠ 0 := by
      intro h0
      exact mul_ne_zero h2 h2 (by linear_combination -h0)
    have hx : (X 0 : MvPolynomial (Fin 1) R) ∈
        weightedHomogeneousSubmodule R (depressedWeight 2) ((2 : ℤ) * (2 - 1)) := by
      rw [mem_weightedHomogeneousSubmodule]
      convert isWeightedHomogeneous_X R (depressedWeight 2) 0
      simp [depressedWeight_apply]
    exact homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_C_mul_prime
      (depressedWeight 2) (depressedDiscr_mem R 2) h4 hx prime_X
      (by rw [depressedDiscr_two, map_neg, map_ofNat])
  · exact homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_prime
      (depressedWeight m) (depressedDiscr_mem R m) (prime_depressedDiscr h2 hmR hm3)

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields shift class group `ZMod (m * (m - 1))` over any integral domain `R` with `m ≥ 2`,
`(2 : R) ≠ 0`, and `(m : R) ≠ 0`. -/
noncomputable def shiftClassGroupAwayDepressedDiscrEquiv {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      ≃+ ZMod (m * (m - 1)) :=
  (ShiftClassGroup.equivZMod (homogeneousUnitDegrees_away_depressedDiscr h2 hmR hm)).trans
    (ZMod.ringEquivCongr (by
      have h : ((m : ℤ) * (m - 1)) = ((m * (m - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [h, Int.natAbs_natCast])).toAddEquiv

/-- The identification of the shift class group after inverting `depressedDiscr R m` with
`ZMod (m * (m - 1))` sends the class of `d` to `d mod m * (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayDepressedDiscrEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) (d : ℤ) :
    shiftClassGroupAwayDepressedDiscrEquiv h2 hmR hm d = d := by
  rw [shiftClassGroupAwayDepressedDiscrEquiv, AddEquiv.trans_apply, ShiftClassGroup.equivZMod_mk,
    RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, map_intCast]

/-- The negative of the cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short
Weierstrass discriminant factor), has weight `12` when the variables have weights `4` and `6`. -/
theorem mem_weightedHomogeneousSubmodule_weierstrass (R : Type*) [CommRing R] :
    (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  have h3 : (depressedDiscr R 3).IsWeightedHomogeneous (depressedWeight 3) 6 :=
    (mem_weightedHomogeneousSubmodule R _ _ _).mp (depressedDiscr_mem R 3)
  have hscaled := h3.comp_weight (AddMonoidHom.mulLeft (2 : ℤ))
  have hw : (AddMonoidHom.mulLeft (2 : ℤ)) ∘ depressedWeight 3 = (![4, 6] : Fin 2 → ℤ) := by
    ext i
    fin_cases i <;> simp [depressedWeight_apply]
  rw [hw] at hscaled
  have hneg : -(depressedDiscr R 3) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 :=
    neg_mem ((mem_weightedHomogeneousSubmodule R _ _ _).mpr hscaled)
  rwa [depressedDiscr_three, show -(-4 * X 0 ^ 3 - 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) =
    4 * X 0 ^ 3 + 27 * X 1 ^ 2 by ring] at hneg

/-- Over any integral domain `R` in which `(2 : R) ≠ 0` and `(3 : R) ≠ 0`, the negative of the
cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short Weierstrass discriminant
factor), is prime. -/
theorem prime_four_mul_pow_three_add_twentyseven_mul_sq {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hassoc : Associated (depressedDiscr R 3)
      (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) :=
    ⟨-1, by simp [depressedDiscr_three]; ring⟩
  exact hassoc.prime_iff.mp
    (prime_depressedDiscr h2 (m := 3) (by norm_num; exact h3) (by norm_num))

/-- Inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` in `R[a, b]` with weights `4, 6` over an integral
domain `R` with `(2 : R) ≠ 0` and `(3 : R) ≠ 0` yields shift class group `ZMod 12`. -/
noncomputable def shiftClassGroupAwayWeierstrassEquiv {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
          (mem_weightedHomogeneousSubmodule_weierstrass R)) ≃+ ZMod 12 :=
  shiftClassGroupAwayGradingWeightedEquiv (![4, 6] : Fin 2 → ℤ)
    (mem_weightedHomogeneousSubmodule_weierstrass R)
    (prime_four_mul_pow_three_add_twentyseven_mul_sq h2 h3)

/-- The identification of the shift class group after inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2`
with `ZMod 12` sends the class of `d` to `d mod 12`. -/
@[simp]
theorem shiftClassGroupAwayWeierstrassEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (d : ℤ) :
    shiftClassGroupAwayWeierstrassEquiv h2 h3 d = d :=
  shiftClassGroupAwayGradingWeightedEquiv_mk _ _ _ d

end TauCeti
