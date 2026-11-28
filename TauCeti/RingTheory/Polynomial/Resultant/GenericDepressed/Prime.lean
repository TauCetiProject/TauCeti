/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic
import TauCeti.Algebra.MvPolynomial.Equiv
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.MvPolynomial.Localization
import TauCeti.RingTheory.Polynomial.Resultant.FreeMonic
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Primality of the generic depressed discriminant

Over a domain `R` in which `2 ≠ 0` and `(m : R) ≠ 0`, with `2` invertible when `m = 2`, the generic
depressed discriminant `depressedDiscr R m` of `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is prime
(`TauCeti.depressedDiscr_prime`, covering for instance `ℤ` for every `m ≥ 3`).

When `m` is invertible, translating the variable by `cₘ₋₁ / m` turns the free monic polynomial
`Xᵐ + cₘ₋₁ Xᵐ⁻¹ + ⋯ + c₀` into a depressed polynomial with the same discriminant, yielding a ring
map from `R[a₂, …, aₘ]` to `R[c₀, …, cₘ₋₁]` carrying the depressed discriminant to the
discriminant of the free monic polynomial, which is prime (`Polynomial.prime_discr_freeMonic`), with
retraction `cₘ₋₁ = 0`. For `m ≥ 3` with `(m : R) ≠ 0`, primality follows by localizing at `m` and
descending via `MvPolynomial.dvd_of_map_localization_away` using the fact that `depressedDiscr R m`
has unit leading coefficient (up to sign) in the variable `aₘ₋₁` modulo `m`.

The hypotheses are needed: in characteristic `3` the discriminant for `m = 3` is `-a₂³`, in
characteristic `2` the discriminant for `m = 2` is `0`, and over `ℤ` the discriminant for `m = 2`
is `-4 a₂`.

## Main results

* `TauCeti.depressedDiscr_prime`: over a domain with `2 ≠ 0`, `(m : R) ≠ 0`, `2 ≤ m`, and
  `IsUnit (2 : R)` when `m = 2`, `depressedDiscr R m` is prime.
* `TauCeti.prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq`: primality of
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` over any integral domain with `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.
-/

public section

open Polynomial

namespace TauCeti

section Ring

variable {R : Type*} [CommRing R] {m : ℕ}

private theorem two_le_depressedWeight (j : Fin (m - 1)) : 2 ≤ depressedWeight m j := by
  rw [depressedWeight_apply]
  omega

private theorem depressedWeight_nonneg (j : Fin (m - 1)) : 0 ≤ depressedWeight m j :=
  le_trans (by omega) (two_le_depressedWeight j)

private theorem depressedWeight_last (hm : 3 ≤ m) :
    depressedWeight m ⟨m - 3, by omega⟩ = (m : ℤ) - 1 := by
  rw [depressedWeight_apply]
  dsimp
  omega

private theorem weight_eq_of_mem_support_depressedDiscr {d : Fin (m - 1) →₀ ℕ}
    (hd : d ∈ (depressedDiscr R m).support) :
    Finsupp.weight (depressedWeight m) d = (m : ℤ) * (m - 1) :=
  (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (depressedDiscr_mem R m)
    (MvPolynomial.mem_support_iff.mp hd)

private theorem sum_le_weight_depressedWeight (d : Fin (m - 1) →₀ ℕ)
    {s : Finset (Fin (m - 1))} (hs : s ⊆ d.support) :
    ∑ x ∈ s, (d x : ℤ) * depressedWeight m x ≤ Finsupp.weight (depressedWeight m) d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    fun x _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (depressedWeight_nonneg x)

/-- Any monomial in the support of `depressedDiscr R m` has degree at most `m` in the variable
`aₘ₋₁` (corresponding to the linear term `X`). -/
private theorem depressedDiscr_support_le (hm : 3 ≤ m) {d : Fin (m - 1) →₀ ℕ}
    (hd : d ∈ (depressedDiscr R m).support) : d ⟨m - 3, by omega⟩ ≤ m := by
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  have hwt := weight_eq_of_mem_support_depressedDiscr hd
  have hle : (d i₀ : ℤ) * depressedWeight m i₀ ≤ Finsupp.weight (depressedWeight m) d := by
    by_cases hiu : i₀ ∈ d.support
    · simpa using sum_le_weight_depressedWeight d (Finset.singleton_subset_iff.mpr hiu)
    · rw [Finsupp.notMem_support_iff.mp hiu, Nat.cast_zero, zero_mul]
      simpa using sum_le_weight_depressedWeight d (Finset.empty_subset _)
  rw [hwt, depressedWeight_last hm] at hle
  have : (d i₀ : ℤ) ≤ m := by nlinarith
  dsimp only [i₀] at this
  omega

/-- Any monomial in the support of `depressedDiscr R m` with degree at least `m` in `aₘ₋₁` must be
`aₘ₋₁ ^ m`. -/
private theorem depressedDiscr_eq_single_of_le (hm : 3 ≤ m) {d : Fin (m - 1) →₀ ℕ}
    (hd : d ∈ (depressedDiscr R m).support) (hge : m ≤ d ⟨m - 3, by omega⟩) :
    d = Finsupp.single ⟨m - 3, by omega⟩ m := by
  set i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  have hdi₀ : d i₀ = m := le_antisymm (depressedDiscr_support_le hm hd) hge
  have hwt := weight_eq_of_mem_support_depressedDiscr hd
  have hzero : ∀ j, j ≠ i₀ → d j = 0 := by
    intro j hj
    by_contra hdj
    have hsub : ({i₀, j} : Finset _) ⊆ d.support := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finsupp.mem_support_iff.mpr (by rw [hdi₀]; omega)
      · rw [Finset.mem_singleton.mp hx]; exact Finsupp.mem_support_iff.mpr hdj
    have hsum_le := sum_le_weight_depressedWeight d hsub
    rw [Finset.sum_pair hj.symm, hdi₀, depressedWeight_last hm, hwt] at hsum_le
    have hwtj : 2 ≤ depressedWeight m j := two_le_depressedWeight j
    have hdj_pos : (1 : ℤ) ≤ d j := by exact_mod_cast Nat.pos_of_ne_zero hdj
    nlinarith
  ext j
  by_cases hj : j = i₀
  · subst hj; simp [hdi₀]
  · simp [hzero j hj, hj]

/-- A monomial in the support of `depressedDiscr R m` supported solely on `aₘ₋₁` must be
`aₘ₋₁ ^ m`. -/
private theorem depressedDiscr_eq_single_of_support_subset (hm : 3 ≤ m)
    {d : Fin (m - 1) →₀ ℕ} (hd : d ∈ (depressedDiscr R m).support)
    (hsupp : ∀ j ≠ ⟨m - 3, by omega⟩, d j = 0) :
    d = Finsupp.single ⟨m - 3, by omega⟩ m := by
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  have hwt := weight_eq_of_mem_support_depressedDiscr hd
  have hsum : Finsupp.weight (depressedWeight m) d = (d i₀ : ℤ) * ((m : ℤ) - 1) := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single i₀]
    · rw [depressedWeight_last hm, nsmul_eq_mul]
    · intro j _ hj
      rw [hsupp j hj, zero_smul]
    · intro hi0
      rw [Finsupp.notMem_support_iff.mp hi0, zero_smul]
  rw [hsum] at hwt
  have hdi₀ : d i₀ = m := by
    have : (d i₀ : ℤ) = (m : ℤ) := mul_right_cancel₀ (by omega) hwt
    omega
  exact depressedDiscr_eq_single_of_le hm hd hdi₀.ge

/-- Evaluating `depressedDiscr R m` at `Pi.single i₀ 1` extracts the coefficient of `aₘ₋₁ ^ m`:
every other monomial in the support involves some `j ≠ i₀`. -/
private theorem eval_single_one_depressedDiscr (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    MvPolynomial.eval (Pi.single (⟨m - 3, by omega⟩ : Fin (m - 1)) 1) (depressedDiscr R m) =
      (depressedDiscr R m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m) := by
  classical
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let v : Fin (m - 1) → R := Pi.single i₀ 1
  rw [MvPolynomial.eval_eq, Finset.sum_eq_single (Finsupp.single i₀ m)]
  · rw [Finset.prod_eq_single i₀]
    · simp [i₀]
    · intro j _ hj
      simp [Finsupp.single_eq_of_ne hj]
    · intro hi0
      exact (hi0 (Finsupp.mem_support_iff.mpr (by simp; omega))).elim
  · intro d hd hne
    have hex : ∃ j : Fin (m - 1), j ≠ i₀ ∧ d j ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hne (depressedDiscr_eq_single_of_support_subset hm hd hno)
    obtain ⟨j, hj, hdj⟩ := hex
    have hprod : ∏ i ∈ d.support, v i ^ d i = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdj)
        (by simp [v, Pi.single_eq_of_ne hj, hdj])
    rw [hprod, mul_zero]
  · intro hnot
    rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]

/-- Evaluating `depressedDiscr R m` at `Pi.single i₀ 1` gives the discriminant of `X ^ m + X`. -/
private theorem eval_single_one_depressedDiscr_eq_discr (R : Type*) [CommRing R] {m : ℕ}
    (hm : 3 ≤ m) :
    MvPolynomial.eval (Pi.single (⟨m - 3, by omega⟩ : Fin (m - 1)) 1) (depressedDiscr R m) =
      (X ^ m + X : R[X]).discr := by
  nontriviality R
  have hlt : (X : R[X]).degree < (X ^ m : R[X]).degree := by
    rw [degree_X_pow, degree_X]
    exact_mod_cast (by omega : 1 < m)
  have hmon : (X ^ m + X : R[X]).Monic := (monic_X_pow m).add_of_left hlt
  have hdeg : (X ^ m + X : R[X]).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]
  have hnext : (X ^ m + X : R[X]).nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; omega), hdeg, coeff_add, coeff_X_pow, coeff_X,
      ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  rw [discr_eq_eval_depressedDiscr hmon hdeg hnext]
  refine congrArg (fun v ↦ MvPolynomial.eval v (depressedDiscr R m)) ?_
  ext j
  rw [coeff_add, coeff_X_pow, coeff_X]
  by_cases hj : j = ⟨m - 3, by omega⟩
  · subst hj
    simp [show m - 2 - (m - 3) = 1 by omega, show 1 ≠ m by omega]
  · have hj' : (j : ℕ) ≠ m - 3 := fun h ↦ hj (Fin.ext h)
    simp [hj, show m - 2 - (j : ℕ) ≠ m by omega, show 1 ≠ m - 2 - (j : ℕ) by omega]

/-- Extract the coefficient of `aₘ₋₁ ^ m` in `depressedDiscr R m` by evaluating at
`Pi.single i₀ 1` (corresponding to `X ^ m + X`). -/
private theorem depressedDiscr_coeff_single_eq (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    (depressedDiscr R m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m) =
      (-1 : R) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : R) ^ (m - 1) := by
  rw [← eval_single_one_depressedDiscr R hm, eval_single_one_depressedDiscr_eq_discr R hm,
    discr_X_pow_add_X (by omega)]

private theorem coeff_optionSubtypeNeEquiv_depressedDiscr_self (A : Type*) [CommRing A]
    {m : ℕ} (hm : 3 ≤ m) :
    (MvPolynomial.optionSubtypeNeEquiv A (⟨m - 3, by omega⟩ : Fin (m - 1))
      (depressedDiscr A m)).coeff m =
      MvPolynomial.C ((depressedDiscr A m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m)) := by
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  rw [MvPolynomial.coeff_coeff_optionSubtypeNeEquiv]
  by_cases hd : d = 0
  · subst hd
    rw [MvPolynomial.coeff_C, ite_eq_left rfl, Finsupp.optionElim_zero, Finsupp.mapDomain_single,
      Equiv.optionSubtypeNe_none]
  · rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hd)]
    by_contra hne
    let u := (Finsupp.optionElim m d).mapDomain (Equiv.optionSubtypeNe i₀)
    have hui₀ : u i₀ = m := by
      rw [Finsupp.mapDomain_equiv_apply, Equiv.optionSubtypeNe_symm_self,
        Finsupp.optionElim_apply_none]
    have hu_eq := depressedDiscr_eq_single_of_le hm (MvPolynomial.mem_support_iff.mpr hne) hui₀.ge
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hd
    have huj : u j.val = d j := by
      rw [Finsupp.mapDomain_equiv_apply, Equiv.optionSubtypeNe_symm_of_ne j.property,
        Finsupp.optionElim_apply_some]
    dsimp only [u, i₀] at huj
    rw [hu_eq, Finsupp.single_eq_of_ne j.property] at huj
    exact hj huj.symm

private theorem isUnit_leadingCoeff_optionSubtypeNeEquiv_depressedDiscr (A : Type*) [CommRing A]
    [Nontrivial A] {m : ℕ} (hm : 3 ≤ m) (hmA : (m : A) = 0) :
    IsUnit (MvPolynomial.optionSubtypeNeEquiv A (⟨m - 3, by omega⟩ : Fin (m - 1))
      (depressedDiscr A m)).leadingCoeff := by
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let e := MvPolynomial.optionSubtypeNeEquiv A i₀
  have hunit : IsUnit ((e (depressedDiscr A m)).coeff m) := by
    rw [coeff_optionSubtypeNeEquiv_depressedDiscr_self A hm, depressedDiscr_coeff_single_eq A hm,
      Nat.cast_sub (by omega), hmA, Nat.cast_one, zero_sub, ← pow_add]
    exact (isUnit_one.neg.pow _).map MvPolynomial.C
  have hle : (e (depressedDiscr A m)).natDegree ≤ m := by
    rw [MvPolynomial.natDegree_optionSubtypeNeEquiv, MvPolynomial.degreeOf_eq_sup,
      Finset.sup_le_iff]
    exact fun d hd ↦ depressedDiscr_support_le hm hd
  have hdeg : (e (depressedDiscr A m)).natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hle hunit.ne_zero
  rwa [leadingCoeff, hdeg]

/-- For `m ≥ 3`, whenever `(m : A) = 0`, `depressedDiscr A m` is regular because it has unit
leading coefficient (up to sign) in the variable `aₘ₋₁`. -/
private theorem isLeftRegular_depressedDiscr_of_natCast_eq_zero {A : Type*} [CommRing A] {m : ℕ}
    (hm : 3 ≤ m) (hmA : (m : A) = 0) : IsLeftRegular (depressedDiscr A m) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · intro x y _
    exact Subsingleton.elim x y
  · let e := MvPolynomial.optionSubtypeNeEquiv A (⟨m - 3, by omega⟩ : Fin (m - 1))
    have hlc := isUnit_leadingCoeff_optionSubtypeNeEquiv_depressedDiscr A hm hmA
    intro x y hxy
    have h0 : e (depressedDiscr A m) * e (x - y) = 0 := by
      rw [← map_mul, mul_sub, sub_eq_zero.mpr hxy, map_zero]
    exact sub_eq_zero.mp (e.injective
      (((isUnit_leadingCoeff_mul_right_eq_zero_iff hlc).mp h0).trans (map_zero e).symm))

/-- Primality of `depressedDiscr R m` when `m` is a unit in `R`, via the Tschirnhaus shift from
`freeMonic R m`. -/
private theorem depressedDiscr_prime_of_isUnit [IsDomain R] (h2 : (2 : R) ≠ 0) (hm : IsUnit (m : R))
    (hm2 : 2 ≤ m) : Prime (depressedDiscr R m) := by
  -- Translating the root coordinate by `c / m`, with `c` the subleading coefficient, turns the
  -- free monic polynomial `F` into a depressed polynomial `T` with the same discriminant.
  let F := freeMonic R m
  let c : MvPolynomial (Fin m) R :=
    MvPolynomial.C (↑hm.unit⁻¹ : R) * MvPolynomial.X ⟨m - 1, by omega⟩
  let T := taylor (-c) F
  have hFdeg : F.natDegree = m := natDegree_freeMonic R m
  have hTmonic : T.Monic := by
    rw [Monic, leadingCoeff_taylor]
    exact monic_freeMonic R m
  have hTdeg : T.natDegree = m := by rw [natDegree_taylor, hFdeg]
  have hTnext : T.nextCoeff = 0 := by
    have hu : (m : MvPolynomial (Fin m) R) * MvPolynomial.C (↑hm.unit⁻¹ : R) = 1 := by
      rw [← map_natCast MvPolynomial.C, ← map_mul, hm.mul_val_inv, map_one]
    rw [nextCoeff_taylor, (monic_freeMonic R m).leadingCoeff, hFdeg,
      nextCoeff_of_natDegree_pos (by omega), hFdeg, coeff_freeMonic, dite_eq_left (by omega)]
    linear_combination (-MvPolynomial.X ⟨m - 1, by omega⟩) * hu
  -- `ψ` substitutes the coefficients of `T`, and `ε` sets `c` to zero.
  let ψ : MvPolynomial (Fin (m - 1)) R →ₐ[R] MvPolynomial (Fin m) R :=
    MvPolynomial.aeval fun j ↦ T.coeff (m - 2 - j)
  let ε : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin (m - 1)) R :=
    MvPolynomial.aeval fun i : Fin m ↦ (genericDepressed R m).coeff i
  have hψ : ψ (depressedDiscr R m) = F.discr := by
    rw [← discr_comp_X_add_C F (-c), ← taylor_apply,
      discr_eq_eval_depressedDiscr hTmonic hTdeg hTnext,
      ← map_depressedDiscr (algebraMap R (MvPolynomial (Fin m) R)), MvPolynomial.eval_map,
      ← MvPolynomial.aeval_def]
  have hεF : F.map ε.toRingHom = genericDepressed R m :=
    map_aeval_coeff_freeMonic monic_genericDepressed natDegree_genericDepressed
  have hεψ : ε.comp ψ = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    have hc : ε c = 0 := by
      simp only [c, ε, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, coeff_genericDepressed,
        ite_eq_right (show m - 1 ≠ m by omega), dite_eq_right (show ¬m - 1 + 2 ≤ m by omega),
        mul_zero]
    have hTε : T.map ε.toRingHom = genericDepressed R m := by
      rw [map_taylor, hεF, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_neg, hc, neg_zero,
        taylor_zero]
    have := coeff_map ε.toRingHom (p := T) (m - 2 - j)
    rw [hTε, coeff_genericDepressed_sub_two_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    simpa [ψ] using this.symm
  refine comap_prime ψ ε (fun a ↦ congr($hεψ a)) ?_
  rw [hψ]
  exact prime_discr_freeMonic h2 hm2

/-- **The generic depressed discriminant is prime.** Over a domain in which `2 ≠ 0` and
`(m : R) ≠ 0`, with `IsUnit (2 : R)` when `m = 2`, the discriminant of `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ`
is a prime element of `R[a₂, …, aₘ]` for every `m ≥ 2`. -/
theorem depressedDiscr_prime [IsDomain R] (h2 : (2 : R) ≠ 0) (hmR : (m : R) ≠ 0) (hm2 : 2 ≤ m)
    (h2u : m = 2 → IsUnit (2 : R)) : Prime (depressedDiscr R m) := by
  rcases eq_or_lt_of_le hm2 with rfl | hm3
  · exact depressedDiscr_prime_of_isUnit h2 (h2u rfl) le_rfl
  · let Rm := Localization.Away (m : R)
    have : IsDomain Rm := IsLocalization.Away.isDomain (S := Rm) hmR
    have hinj : Function.Injective (algebraMap R Rm) :=
      IsLocalization.injective Rm (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hmR))
    have h2m : (2 : Rm) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero_iff (algebraMap R Rm) hinj).mpr h2
    have hum : IsUnit (m : Rm) := by
      simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (m : R)
    have hprime_Rm : Prime (depressedDiscr Rm m) :=
      depressedDiscr_prime_of_isUnit h2m hum (by omega)
    have hmap_eq :
        MvPolynomial.map (algebraMap R Rm) (depressedDiscr R m) = depressedDiscr Rm m :=
      map_depressedDiscr (algebraMap R Rm)
    have hreg_mod : IsLeftRegular
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(m : R)})) (depressedDiscr R m)) := by
      have hm_mod : ((m : ℕ) : R ⧸ Ideal.span {(m : R)}) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(m : R)}))]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      rw [map_depressedDiscr]
      exact isLeftRegular_depressedDiscr_of_natCast_eq_zero hm3 hm_mod
    have hm_reg : IsLeftRegular (m : R) := (IsRegular.of_ne_zero hmR).left
    refine ⟨fun h0 ↦ hprime_Rm.ne_zero (by rw [← hmap_eq, h0, map_zero]),
      fun hu ↦ hprime_Rm.not_isUnit (hmap_eq ▸ hu.map _), ?_⟩
    intro f g hfg
    have hfg_Rm : depressedDiscr Rm m ∣
        MvPolynomial.map (algebraMap R Rm) f * MvPolynomial.map (algebraMap R Rm) g := by
      have h1 := map_dvd (MvPolynomial.map (σ := Fin (m - 1)) (algebraMap R Rm)) hfg
      rwa [map_mul, hmap_eq] at h1
    rcases hprime_Rm.dvd_or_dvd hfg_Rm with hf | hg
    · exact Or.inl (MvPolynomial.dvd_of_map_localization_away (m : R) hm_reg hreg_mod
        (hmap_eq ▸ hf))
    · exact Or.inr (MvPolynomial.dvd_of_map_localization_away (m : R) hm_reg hreg_mod
        (hmap_eq ▸ hg))

/-- Over any integral domain `R` in which `(2 : R) ≠ 0` and `(3 : R) ≠ 0`, the negative of the
cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short Weierstrass discriminant
factor), is prime. -/
theorem prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hassoc : Associated (depressedDiscr R 3)
      (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) :=
    ⟨-1, by rw [depressedDiscr_three]; simp only [Units.val_neg, Units.val_one]; ring⟩
  exact hassoc.prime_iff.mp
    (depressedDiscr_prime h2 (m := 3) (by exact_mod_cast h3) (by norm_num)
      (fun h ↦ absurd h (by omega)))

end Ring

end TauCeti
