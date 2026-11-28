/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.WeightedHomogeneous
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

Over a domain in which `2` is nonzero and `m ≥ 2` is invertible, for instance over a field of
characteristic `0`, the discriminant is moreover prime. Translating the variable by `cₘ₋₁ / m`
turns the free monic polynomial `Xᵐ + cₘ₋₁ Xᵐ⁻¹ + ⋯ + c₀` into a depressed polynomial with the
same discriminant. This gives a ring map from `R[a₂, …, aₘ]` to `R[c₀, …, cₘ₋₁]` carrying the
depressed discriminant to the discriminant of the free monic polynomial, which is prime
(`Polynomial.prime_discr_freeMonic`); setting `cₘ₋₁ = 0` is a retraction of that map. The
hypotheses are needed: in characteristic `3` the discriminant for `m = 3` is `-a₂³`, and in
characteristic `2` the discriminant for `m = 2` is `0`.

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
* `TauCeti.depressedDiscr_prime`: over a domain in which `2 ≠ 0` and `m` is invertible, the
  discriminant is prime.
* `TauCeti.depressedDiscr_two`, `TauCeti.depressedDiscr_three`: the discriminants in degrees `2`
  and `3`.
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

/-- **The generic depressed discriminant is prime.** Over a domain in which `2 ≠ 0` and `m ≥ 2` is
invertible, in particular over a field of characteristic `0`, the discriminant of
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is a prime element of `R[a₂, …, aₘ]`. -/
theorem depressedDiscr_prime [IsDomain R] (h2 : (2 : R) ≠ 0) (hm : IsUnit (m : R))
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

end Ring

end TauCeti
