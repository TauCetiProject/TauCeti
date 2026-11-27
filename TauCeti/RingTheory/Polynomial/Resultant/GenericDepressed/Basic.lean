/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.WeightedHomogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import TauCeti.Algebra.MvPolynomial.Equiv
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.Polynomial.Resultant.FreeMonic
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# The generic depressed polynomial and its discriminant

The generic depressed polynomial of degree `m` is
`Xᵐ + a₂ Xᵐ⁻² + a₃ Xᵐ⁻³ + ⋯ + aₘ` over the polynomial ring `R[a₂, …, aₘ]`: the generic monic
polynomial of degree `m` whose coefficient of `Xᵐ⁻¹` vanishes. The variable `aⱼ` is
`MvPolynomial.X (j - 2)`, indexed by `Fin (m - 1)`, and carries the weight `j`. These weights
come from the action `x ↦ t x` of the multiplicative group on the roots, under which `aⱼ` is
multiplied by `tʲ`.

The discriminant of the generic depressed polynomial is weighted homogeneous of weight
`m (m - 1)`, over every commutative ring. For `m = 2` it is `-4 a₂`, and for `m = 3` it is
`-4 a₂³ - 27 a₃²`.

Over a domain in which `2 ≠ 0` and `(m : R) ≠ 0`, with `2` invertible when `m = 2`, the
discriminant is moreover prime (`TauCeti.depressedDiscr_prime`, covering for instance `ℤ` for
every `m ≥ 3`). When `m` is invertible, translating the variable by `cₘ₋₁ / m` turns the free
monic polynomial `Xᵐ + cₘ₋₁ Xᵐ⁻¹ + ⋯ + c₀` into a depressed polynomial with the same discriminant,
yielding a ring map from `R[a₂, …, aₘ]` to `R[c₀, …, cₘ₋₁]` carrying the depressed discriminant to
the discriminant of the free monic polynomial, which is prime (`Polynomial.prime_discr_freeMonic`),
with retraction `cₘ₋₁ = 0`. For `m ≥ 3` with `(m : R) ≠ 0`, primality follows by localizing at `m`
and descending via the fact that `depressedDiscr R m` has unit leading coefficient (up to sign) in
the variable `aₘ₋₁` modulo `m`. The hypotheses are needed: in characteristic `3` the discriminant
for `m = 3` is `-a₂³`, in characteristic `2` the discriminant for `m = 2` is `0`, and over `ℤ`
the discriminant for `m = 2` is `-4 a₂`.

## Main definitions

* `TauCeti.genericDepressed R m`: the generic depressed polynomial of degree `m` over
  `R[a₂, …, aₘ]`.
* `TauCeti.depressedWeight m`: the integer weights of the variables, `aⱼ` having weight `j`.
* `TauCeti.depressedDiscr R m`: the discriminant of `genericDepressed R m`.

## Main results

* `TauCeti.monic_genericDepressed`, `TauCeti.natDegree_genericDepressed`,
  `TauCeti.degree_genericDepressed`, `TauCeti.nextCoeff_genericDepressed`: the generic depressed
  polynomial is monic of degree `m` with vanishing subleading coefficient.
* `TauCeti.map_eval_genericDepressed`: every monic depressed polynomial of degree `m` is a
  specialization of the generic one.
* `TauCeti.discr_genericDepressed`: `depressedDiscr R m` is the discriminant of
  `genericDepressed R m`.
* `TauCeti.depressedDiscr_mem`: the discriminant is weighted homogeneous of weight `m (m - 1)`.
* `TauCeti.depressedDiscr_three_mem_four_six`: for `m = 3` and the doubled weights `4, 6` of the
  short Weierstrass equation, the discriminant `-4 a³ - 27 b²` has weight `12`.
* `TauCeti.map_depressedDiscr`: the discriminant commutes with changing the coefficients.
* `TauCeti.depressedDiscr_prime`: over a domain with `2 ≠ 0`, `(m : R) ≠ 0`, `2 ≤ m`, and
  `IsUnit (2 : R)` when `m = 2`, the discriminant is prime.
* `TauCeti.depressedDiscr_two`, `TauCeti.depressedDiscr_three`: the discriminants in degrees `2`
  and `3`.
* `TauCeti.mem_weightedHomogeneousSubmodule_weierstrass`: `4 * X 0 ^ 3 + 27 * X 1 ^ 2` has weight
  `12` for the weights `![4, 6]`.
* `TauCeti.prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq`: primality of
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` over any integral domain with `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.
-/

public section

open Polynomial

namespace TauCeti

section Semiring

variable (R : Type*) [CommSemiring R] (m : ℕ)

/-- The generic depressed polynomial `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` of degree `m`, over the polynomial
ring in the variables `aⱼ = MvPolynomial.X (j - 2)`, `j = 2, …, m`. -/
noncomputable def genericDepressed : (MvPolynomial (Fin (m - 1)) R)[X] :=
  X ^ m + ∑ j : Fin (m - 1), C (MvPolynomial.X j) * X ^ (m - 2 - j)

/-- The weights of the variables of `genericDepressed R m`: the variable `j` is `aⱼ₊₂`, of weight
`j + 2`. -/
def depressedWeight : Fin (m - 1) → ℤ := fun j ↦ j + 2

@[simp]
theorem depressedWeight_apply (j : Fin (m - 1)) : depressedWeight m j = j + 2 := (rfl)

variable {R m}

/-- The coefficients of the generic depressed polynomial: `1` in degree `m`, the variable
`aₘ₋ₖ = MvPolynomial.X (m - 2 - k)` in degree `k ≤ m - 2`, and `0` otherwise. -/
theorem coeff_genericDepressed (k : ℕ) :
    (genericDepressed R m).coeff k =
      if k = m then 1 else if h : k + 2 ≤ m then MvPolynomial.X ⟨m - 2 - k, by omega⟩ else 0 := by
  simp only [genericDepressed, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with hm hk
  · rw [Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by have := j.isLt; omega), add_zero]
  · rw [zero_add, Finset.sum_eq_single ⟨m - 2 - k, by omega⟩
      (fun j _ hj ↦ ite_eq_right fun h ↦ hj (Fin.ext (by simp only; omega))) (by simp)]
    exact ite_eq_left (by simp only; omega)
  · exact (zero_add _).trans
      (Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by have := j.isLt; omega))

/-- The variable `aⱼ₊₂` is the coefficient of `Xᵐ⁻²⁻ʲ` in the generic depressed polynomial. -/
@[simp]
theorem coeff_genericDepressed_sub_two_sub (j : Fin (m - 1)) :
    (genericDepressed R m).coeff (m - 2 - j) = MvPolynomial.X j := by
  have hj := j.isLt
  rw [coeff_genericDepressed, ite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  ext
  simp only
  omega

/-- The coefficients of the generic depressed polynomial are weighted homogeneous: the coefficient
of `Xⁱ` has weight `m - i` for the natural weights `j ↦ j + 2` of `depressedWeight`. -/
theorem isWeightedHomogeneous_coeff_genericDepressed (i : ℕ) :
    ((genericDepressed R m).coeff i).IsWeightedHomogeneous (fun j : Fin (m - 1) ↦ (j : ℕ) + 2)
      (m - i) := by
  rw [coeff_genericDepressed]
  split_ifs with hm hi
  · rw [hm, Nat.sub_self]
    exact MvPolynomial.isWeightedHomogeneous_one R _
  · convert MvPolynomial.isWeightedHomogeneous_X R _ _ using 1
    simp only
    omega
  · exact MvPolynomial.isWeightedHomogeneous_zero R _ _

/-- The lower terms of the generic depressed polynomial have degree less than `m`. -/
private theorem degree_sum_lt :
    (∑ j : Fin (m - 1), C (MvPolynomial.X j : MvPolynomial (Fin (m - 1)) R) *
      X ^ (m - 2 - j)).degree < (m : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe m)).2 fun j _ ↦ ?_)
  have hj := j.isLt
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  rw [Nat.cast_withBot]
  exact WithBot.coe_lt_coe.2 (by omega)

/-- The generic depressed polynomial is monic. -/
@[simp]
theorem monic_genericDepressed : (genericDepressed R m).Monic := by
  nontriviality R
  exact (monic_X_pow m).add_of_left (by rw [degree_X_pow]; exact degree_sum_lt)

/-- The generic depressed polynomial has degree `m`. -/
@[simp]
theorem natDegree_genericDepressed [Nontrivial R] : (genericDepressed R m).natDegree = m := by
  rw [genericDepressed, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact
    degree_sum_lt), natDegree_X_pow]

/-- The generic depressed polynomial has degree `m`. -/
@[simp]
theorem degree_genericDepressed [Nontrivial R] : (genericDepressed R m).degree = m := by
  rw [degree_eq_natDegree monic_genericDepressed.ne_zero, natDegree_genericDepressed]

/-- The generic depressed polynomial is depressed: its subleading coefficient vanishes. -/
@[simp]
theorem nextCoeff_genericDepressed : (genericDepressed R m).nextCoeff = 0 := by
  nontriviality R
  rw [nextCoeff, natDegree_genericDepressed]
  split_ifs with hm
  · rfl
  rw [coeff_genericDepressed, ite_eq_right (by omega), dite_eq_right (by omega)]

/-- **Universal property of the generic depressed polynomial.** A monic polynomial `p` of degree
`m` with vanishing subleading coefficient is the specialization of `genericDepressed R m` at
`aⱼ₊₂ = p.coeff (m - 2 - j)`. -/
theorem map_eval_genericDepressed {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = m)
    (hnext : p.nextCoeff = 0) :
    (genericDepressed R m).map (MvPolynomial.eval fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j)) =
      p := by
  ext k : 2
  rw [coeff_map, coeff_genericDepressed]
  split_ifs with hm hk
  · rw [map_one, hm, ← hdeg, hp.coeff_natDegree]
  · rw [MvPolynomial.eval_X]
    congr 1
    simp only
    omega
  · rw [map_zero, eq_comm]
    rcases lt_or_ge m k with hlt | hle
    · exact coeff_eq_zero_of_natDegree_lt (hdeg ▸ hlt)
    · rw [nextCoeff, hdeg, ite_eq_right (by omega)] at hnext
      rwa [show k = m - 1 by omega]

/-- Changing the coefficients of the generic depressed polynomial along `φ : R →+* S` gives the
generic depressed polynomial over `S`. -/
@[simp]
theorem map_genericDepressed {S : Type*} [CommSemiring S] (φ : R →+* S) :
    (genericDepressed R m).map (MvPolynomial.map φ) = genericDepressed S m := by
  simp [genericDepressed, Polynomial.map_sum]

end Semiring

section Ring

variable (R : Type*) [CommRing R] (m : ℕ)

/-- The discriminant of the generic depressed polynomial `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ`, a polynomial in
`a₂, …, aₘ`. -/
noncomputable def depressedDiscr : MvPolynomial (Fin (m - 1)) R :=
  (genericDepressed R m).discr

variable {R m}

/-- `depressedDiscr R m` is the discriminant of the generic depressed polynomial. -/
theorem discr_genericDepressed : (genericDepressed R m).discr = depressedDiscr R m := (rfl)

/-- The discriminant of a monic polynomial `p` of degree `m` with vanishing subleading coefficient
is `depressedDiscr R m` evaluated at `aⱼ₊₂ = p.coeff (m - 2 - j)`. -/
theorem discr_eq_eval_depressedDiscr {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = m)
    (hnext : p.nextCoeff = 0) :
    p.discr =
      MvPolynomial.eval (fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j)) (depressedDiscr R m) := by
  rw [← discr_genericDepressed, ← monic_genericDepressed.discr_map,
    map_eval_genericDepressed hp hdeg hnext]

/-- Changing the coefficients of the generic depressed discriminant along `φ : R →+* S` gives the
generic depressed discriminant over `S`. -/
@[simp]
theorem map_depressedDiscr {S : Type*} [CommRing S] (φ : R →+* S) :
    MvPolynomial.map φ (depressedDiscr R m) = depressedDiscr S m := by
  rw [← discr_genericDepressed, ← monic_genericDepressed.discr_map, map_genericDepressed,
    discr_genericDepressed]

variable (R m)

/-- **The generic depressed discriminant is isobaric.** The discriminant of
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is weighted homogeneous of weight `m (m - 1)`, for the weights
`aⱼ ↦ j`. -/
theorem depressedDiscr_mem :
    depressedDiscr R m ∈
      MvPolynomial.weightedHomogeneousSubmodule R (depressedWeight m) (m * (m - 1)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R m) 0]
    exact zero_mem _
  have h := isWeightedHomogeneous_discr (p := genericDepressed R m) fun i ↦ by
    rw [natDegree_genericDepressed]
    exact isWeightedHomogeneous_coeff_genericDepressed i
  rw [natDegree_genericDepressed] at h
  have hw : (Nat.castAddMonoidHom ℤ) ∘ (fun j : Fin (m - 1) ↦ (j : ℕ) + 2) = depressedWeight m := by
    ext j
    simp
  have hm : Nat.castAddMonoidHom ℤ (m * (m - 1)) = (m * (m - 1) : ℤ) := by
    rcases m with _ | m <;> simp
  rw [← discr_genericDepressed, MvPolynomial.mem_weightedHomogeneousSubmodule, ← hw, ← hm]
  exact h.comp_weight _

variable {R m}

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

private theorem weight_eq_of_mem_support_depressedDiscr {m : ℕ} {d : Fin (m - 1) →₀ ℕ}
    (hd : d ∈ (depressedDiscr R m).support) :
    Finsupp.weight (depressedWeight m) d = (m : ℤ) * (m - 1) :=
  (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (depressedDiscr_mem R m)
    (MvPolynomial.mem_support_iff.mp hd)

private theorem sum_le_weight_depressedWeight {m : ℕ} (d : Fin (m - 1) →₀ ℕ)
    {s : Finset (Fin (m - 1))} (hs : s ⊆ d.support) :
    ∑ x ∈ s, (d x : ℤ) * depressedWeight m x ≤ Finsupp.weight (depressedWeight m) d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    fun x _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (depressedWeight_nonneg x)

/-- Any monomial in the support of `depressedDiscr R m` has degree at most `m` in the variable
`aₘ₋₁` (corresponding to the linear term `X`). -/
private theorem depressedDiscr_support_le {m : ℕ} (hm : 3 ≤ m) {d : Fin (m - 1) →₀ ℕ}
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
private theorem depressedDiscr_eq_single_of_le {m : ℕ} (hm : 3 ≤ m) {d : Fin (m - 1) →₀ ℕ}
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
private theorem depressedDiscr_eq_single_of_support_subset {m : ℕ} (hm : 3 ≤ m)
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

/-- Evaluate `depressedDiscr R m` at `Pi.single i₀ 1` (corresponding to `X ^ m + X`) to extract
the coefficient of `aₘ₋₁ ^ m`. -/
private theorem depressedDiscr_coeff_single_eq (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    (depressedDiscr R m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m) =
      (-1 : R) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : R) ^ (m - 1) := by
  classical
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let v : Fin (m - 1) → R := Pi.single i₀ 1
  -- Only the monomial `aₘ₋₁ ^ m` survives when evaluating at `Pi.single i₀ 1`: every other
  -- monomial in the support involves some `j ≠ i₀` (`depressedDiscr_eq_single_of_support_subset`).
  have heval_sum : MvPolynomial.eval v (depressedDiscr R m) =
      (depressedDiscr R m).coeff (Finsupp.single i₀ m) := by
    rw [MvPolynomial.eval_eq, Finset.sum_eq_single (Finsupp.single i₀ m)]
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
        exact hne (depressedDiscr_eq_single_of_support_subset hm hd hno)
      obtain ⟨j, hj, hdj⟩ := hex
      have hprod : ∏ i ∈ d.support, v i ^ d i = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdj)
          (by simp [v, Pi.single_eq_of_ne hj, hdj])
      rw [hprod, mul_zero]
    · intro hnot
      rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
  -- On the other hand, specializing `genericDepressed R m` at `Pi.single i₀ 1` gives `X ^ m + X`.
  have heval_discr : MvPolynomial.eval v (depressedDiscr R m) =
      (X ^ m + X : R[X]).discr := by
    nontriviality R
    let p : R[X] := X ^ m + X
    have hp_mon : p.Monic := (monic_X_pow m).add_of_left
      (by rw [degree_X_pow, degree_X]; exact_mod_cast (by omega : 1 < m))
    have hp_deg : p.natDegree = m := by
      rw [natDegree_add_eq_left_of_degree_lt
        (by rw [degree_X_pow, degree_X]; exact_mod_cast (by omega : 1 < m)), natDegree_X_pow]
    have hp_next : p.nextCoeff = 0 := by
      rw [nextCoeff, hp_deg, ite_eq_right (by omega)]
      have hm1 : m - 1 ≠ m := by omega
      have h1m : 1 ≠ m - 1 := by omega
      simp [p, coeff_X, hm1, h1m]
    have hv_eq : (fun j : Fin (m - 1) ↦ p.coeff (m - 2 - (j : ℕ))) = v := by
      ext j
      by_cases hj : j = i₀
      · subst hj
        have hidx : m - 2 - (m - 3) = 1 := by omega
        have h1m : 1 ≠ m := by omega
        simp [p, v, i₀, coeff_X, hidx, h1m]
      · have hne1 : 1 ≠ m - 2 - (j : ℕ) := by
          intro h1
          apply hj
          ext
          dsimp [i₀]
          omega
        have hnem : m - 2 - (j : ℕ) ≠ m := by omega
        simp [p, v, coeff_X, Pi.single_eq_of_ne hj, hne1, hnem]
    rw [discr_eq_eval_depressedDiscr hp_mon hp_deg hp_next, hv_eq]
  rw [← heval_sum, heval_discr, discr_X_pow_add_X (by omega)]

private theorem coeff_optionSubtypeNeEquiv_depressedDiscr_of_lt (A : Type*) [CommRing A]
    {m : ℕ} (hm : 3 ≤ m) {n : ℕ} (hn : m < n) :
    (MvPolynomial.optionSubtypeNeEquiv A (⟨m - 3, by omega⟩ : Fin (m - 1))
      (depressedDiscr A m)).coeff n = 0 := by
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  rw [AddMonoidAlgebra.coeff_zero, MvPolynomial.coeff_coeff_optionSubtypeNeEquiv]
  by_contra hne
  let u := (Finsupp.optionElim n d).mapDomain (Equiv.optionSubtypeNe i₀)
  have hui₀ : u i₀ = n := by
    dsimp only [u]
    rw [Finsupp.mapDomain_equiv_apply]
    simp
  have hle := depressedDiscr_support_le hm (MvPolynomial.mem_support_iff.mpr hne)
  dsimp only [u, i₀] at hui₀
  omega

private theorem coeff_optionSubtypeNeEquiv_depressedDiscr_self (A : Type*) [CommRing A]
    {m : ℕ} (hm : 3 ≤ m) :
    (MvPolynomial.optionSubtypeNeEquiv A (⟨m - 3, by omega⟩ : Fin (m - 1))
      (depressedDiscr A m)).coeff m =
      MvPolynomial.C ((depressedDiscr A m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m)) := by
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  have hσ_none : (Equiv.optionSubtypeNe i₀).symm i₀ = none :=
    Equiv.optionSubtypeNe_symm_self i₀
  have hσ_some : ∀ j : {b : Fin (m - 1) // b ≠ i₀},
      (Equiv.optionSubtypeNe i₀).symm j.val = some j :=
    fun j ↦ Equiv.optionSubtypeNe_symm_of_ne j.property
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  rw [MvPolynomial.coeff_coeff_optionSubtypeNeEquiv]
  by_cases hd : d = 0
  · subst hd
    rw [MvPolynomial.coeff_C, ite_eq_left rfl]
    congr 1
    ext j
    by_cases hj : j = i₀
    · subst hj
      rw [Finsupp.mapDomain_equiv_apply, hσ_none, Finsupp.optionElim_apply_none,
        Finsupp.single_eq_same]
    · rw [Finsupp.mapDomain_equiv_apply, hσ_some ⟨j, hj⟩, Finsupp.optionElim_apply_some,
        Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hj)]
  · rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hd)]
    by_contra hne
    let u := (Finsupp.optionElim m d).mapDomain (Equiv.optionSubtypeNe i₀)
    have hui₀ : u i₀ = m := by
      dsimp only [u]
      rw [Finsupp.mapDomain_equiv_apply, hσ_none, Finsupp.optionElim_apply_none]
    have hu_eq := depressedDiscr_eq_single_of_le hm (MvPolynomial.mem_support_iff.mpr hne) hui₀.ge
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hd
    have huj : u j.val = d j := by
      dsimp only [u]
      rw [Finsupp.mapDomain_equiv_apply, hσ_some j, Finsupp.optionElim_apply_some]
    dsimp only [u, i₀] at huj
    rw [hu_eq, Finsupp.single_eq_of_ne j.property] at huj
    exact hj huj.symm

/-- Descent step for primality of `depressedDiscr R m`: if `C (m ^ k) * f` is divisible by
`depressedDiscr R m`, then `f` itself is divisible by `depressedDiscr R m`.

The proof descends one power of `m` at a time: modulo `(m)`, the coefficient of `aₘ₋₁ ^ m` in
`depressedDiscr` is the unit `±1` while higher degrees vanish, so the quotient `q` vanishes
modulo `(m)`, letting us cancel `C m` from both sides. -/
private theorem depressedDiscr_dvd_of_C_pow_mul_dvd [IsDomain R] {m : ℕ} (hm : 3 ≤ m)
    (hmR : (m : R) ≠ 0) {f : MvPolynomial (Fin (m - 1)) R} {k : ℕ}
    {q : MvPolynomial (Fin (m - 1)) R}
    (h : MvPolynomial.C ((m : R) ^ k) * f = depressedDiscr R m * q) :
    depressedDiscr R m ∣ f := by
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
      rw [map_mul, MvPolynomial.map_C, hpow, map_zero, zero_mul, map_mul,
        map_depressedDiscr] at hmap
      exact hmap.symm
    let e := MvPolynomial.optionSubtypeNeEquiv A (⟨m - 3, by omega⟩ : Fin (m - 1))
    have hunit : IsUnit ((e (depressedDiscr A m)).coeff m) := by
      rw [coeff_optionSubtypeNeEquiv_depressedDiscr_self A hm, depressedDiscr_coeff_single_eq A hm]
      have hmA : (m : A) = 0 := by simpa [π] using hπm
      have hm1A : ((m - 1 : ℕ) : A) = -1 := by
        have h1 : ((m - 1 : ℕ) : A) + ((1 : ℕ) : A) = (m : A) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
        rw [Nat.cast_one, hmA] at h1
        exact eq_neg_of_add_eq_zero_left h1
      rw [hm1A, ← pow_add]
      exact (isUnit_one.neg.pow _).map MvPolynomial.C
    have hmapq : MvPolynomial.map π q = 0 := by
      by_cases hnt : Nontrivial A
      · have hdeg : (e (depressedDiscr A m)).natDegree = m :=
          natDegree_eq_of_le_of_coeff_ne_zero
            (natDegree_le_iff_coeff_eq_zero.mpr
              fun n hn ↦ coeff_optionSubtypeNeEquiv_depressedDiscr_of_lt A hm hn)
            hunit.ne_zero
        have hlc_unit : IsUnit (e (depressedDiscr A m)).leadingCoeff := by
          rwa [leadingCoeff, hdeg]
        have heq0 : e (depressedDiscr A m) * e (MvPolynomial.map π q) = 0 := by
          rw [← map_mul, hq0, map_zero]
        exact e.injective (((isUnit_leadingCoeff_mul_right_eq_zero_iff hlc_unit).mp heq0).trans
          (map_zero e).symm)
      · rw [not_nontrivial_iff_subsingleton] at hnt
        exact Subsingleton.elim _ _
    have hr : ∀ r' : R, π r' = 0 ↔ (m : R) ∣ r' := fun r' ↦
      (Ideal.Quotient.eq_zero_iff_mem (I := I)).trans Ideal.mem_span_singleton
    obtain ⟨q', hq_eq⟩ := (MvPolynomial.C_dvd_iff_map_hom_eq_zero π (m : R) hr q).mpr hmapq
    have hnext : MvPolynomial.C ((m : R) ^ k) * f = depressedDiscr R m * q' := by
      have hC_ne : (MvPolynomial.C (m : R) : MvPolynomial (Fin (m - 1)) R) ≠ 0 :=
        fun h0 ↦ hmR (MvPolynomial.C_eq_zero.mp h0)
      apply mul_left_cancel₀ hC_ne
      calc MvPolynomial.C (m : R) * (MvPolynomial.C ((m : R) ^ k) * f)
          = MvPolynomial.C ((m : R) ^ (k + 1)) * f := by rw [pow_succ', map_mul, mul_assoc]
        _ = depressedDiscr R m * q := h
        _ = MvPolynomial.C (m : R) * (depressedDiscr R m * q') := by rw [hq_eq]; ring
    exact ih hnext

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
        IsLocalization.surj ((Submonoid.powers (m : R)).map (MvPolynomial.C (σ := Fin (m - 1))))
          qRm
      simp only [MvPolynomial.algebraMap_def, MvPolynomial.map_C] at hq₀
      have hcx : MvPolynomial.C ((m : R) ^ kb) * x = depressedDiscr R m * q₀ := by
        apply MvPolynomial.map_injective _ hinj
        rw [map_mul, MvPolynomial.map_C, map_mul, hmap_eq, hqRm, mul_left_comm, mul_comm _ qRm, hq₀]
      exact depressedDiscr_dvd_of_C_pow_mul_dvd hm3 hmR hcx
    rcases hprime_Rm.dvd_or_dvd hfg_Rm with hf | hg
    · exact Or.inl (descend f hf)
    · exact Or.inr (descend g hg)

variable (R m)

/-- The discriminant `-4 a³ - 27 b²` of `X³ + a X + b` is weighted homogeneous of weight `12` for
the weights `4, 6` of `a, b`, those of the short Weierstrass equation `y² = x³ + a x + b`. -/
theorem depressedDiscr_three_mem_four_six :
    depressedDiscr R 3 ∈
      MvPolynomial.weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  -- Doubling the weights `2, 3` of `depressedWeight 3` doubles the weight `6` of the discriminant.
  have h := ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (depressedDiscr_mem R 3)).comp_weight (AddMonoidHom.mulLeft (2 : ℤ))
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  convert h using 1
  · ext j
    fin_cases j <;> simp
  · simp

/-- For `m = 2`, the discriminant of `X² + a₂` is `-4 a₂`. -/
theorem depressedDiscr_two : depressedDiscr R 2 = -4 * MvPolynomial.X 0 := by
  nontriviality R
  rw [← discr_genericDepressed, discr_of_degree_eq_two (by rw [degree_genericDepressed,
    Nat.cast_ofNat])]
  simp [genericDepressed]

/-- For `m = 3`, the discriminant of `X³ + a₂ X + a₃` is `-4 a₂³ - 27 a₃²`. -/
theorem depressedDiscr_three :
    depressedDiscr R 3 = -4 * MvPolynomial.X 0 ^ 3 - 27 * MvPolynomial.X 1 ^ 2 := by
  nontriviality R
  rw [← discr_genericDepressed, discr_of_degree_eq_three (by rw [degree_genericDepressed,
    Nat.cast_ofNat])]
  simp [genericDepressed, Fin.sum_univ_two, coeff_X]

/-- The negative of the cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short
Weierstrass discriminant factor), has weight `12` when the variables have weights `4` and `6`. -/
theorem mem_weightedHomogeneousSubmodule_weierstrass :
    (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      MvPolynomial.weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  have hneg_eq : -(depressedDiscr R 3) =
      (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
    rw [depressedDiscr_three]
    ring
  rw [← hneg_eq]
  exact neg_mem (depressedDiscr_three_mem_four_six R)

variable {R}

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
