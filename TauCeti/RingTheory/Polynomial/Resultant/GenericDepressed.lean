/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.WeightedHomogeneous

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

## Main definitions

* `TauCeti.genericDepressed R m`: the generic depressed polynomial of degree `m` over
  `R[a₂, …, aₘ]`.
* `TauCeti.depressedWeight m`: the integer weights of the variables, `aⱼ` having weight `j`.
* `TauCeti.depressedDiscr R m`: the discriminant of `genericDepressed R m`.

## Main results

* `TauCeti.coeff_genericDepressed`, `TauCeti.coeff_genericDepressed_self`,
  `TauCeti.coeff_genericDepressed_sub_two_sub`: coefficient formulas for `genericDepressed R m`.
* `TauCeti.monic_genericDepressed`, `TauCeti.natDegree_genericDepressed`,
  `TauCeti.degree_genericDepressed`, `TauCeti.nextCoeff_genericDepressed`: the generic depressed
  polynomial is monic of degree `m` with vanishing subleading coefficient.
* `TauCeti.map_map_genericDepressed`, `TauCeti.map_genericDepressed_eq_iff`,
  `TauCeti.map_algHom_genericDepressed_eq_iff`, `TauCeti.map_eval_genericDepressed`: base change
  and universal specialization property for monic depressed polynomials of degree `m`.
* `TauCeti.genericDepressed_zero`, `TauCeti.genericDepressed_one`,
  `TauCeti.genericDepressed_two`, `TauCeti.genericDepressed_three`,
  `TauCeti.genericDepressed_four`: explicit formulas in degrees `0` through `4`.
* `TauCeti.discr_genericDepressed`, `TauCeti.map_depressedDiscr`, `TauCeti.aeval_depressedDiscr`,
  `TauCeti.discr_eq_eval_depressedDiscr`: base change and evaluation of `depressedDiscr R m`.
* `TauCeti.depressedDiscr_mem_smul`, `TauCeti.depressedDiscr_mem`: the discriminant is weighted
  homogeneous of weight `(m * (m - 1)) • u` (and `m * (m - 1)` for `depressedWeight m`).
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

/-- The coefficient of `X ^ m` in `TauCeti.genericDepressed R m` is `1`. -/
@[simp]
theorem coeff_genericDepressed_self (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).coeff m = 1 := by
  rw [coeff_genericDepressed, ite_eq_left rfl]

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

/-- Mapping the base ring commutes with forming `TauCeti.genericDepressed`. -/
@[simp]
theorem map_map_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (m : ℕ) :
    (genericDepressed R m).map (MvPolynomial.map φ) = genericDepressed S m := by
  ext k : 2
  rw [Polynomial.coeff_map, coeff_genericDepressed, coeff_genericDepressed]
  split_ifs <;> simp

/-- **Characteristic specialization property of `TauCeti.genericDepressed`.** For any monic
depressed polynomial `f : S[X]` of `natDegree` `m`, a ring homomorphism
`φ : MvPolynomial (Fin (m - 1)) R →+* S` realizes `f` from `genericDepressed R m` if and only
if it sends each variable `X i` to the coefficient `f.coeff (m - 2 - i)`. -/
theorem map_genericDepressed_eq_iff {R S : Type*} [CommSemiring R] [CommSemiring S]
    {f : S[X]} {m : ℕ} (hf : f.Monic) (hdeg : f.natDegree = m) (hnext : f.nextCoeff = 0)
    (φ : MvPolynomial (Fin (m - 1)) R →+* S) :
    (genericDepressed R m).map φ = f ↔
      ∀ i : Fin (m - 1), φ (MvPolynomial.X i) = f.coeff (m - 2 - (i : ℕ)) := by
  constructor
  · intro h i
    have hc := congrArg (fun p : S[X] ↦ p.coeff (m - 2 - (i : ℕ))) h
    simpa [Polynomial.coeff_map, coeff_genericDepressed_sub_two_sub] using hc
  · intro hφ
    refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
    rw [Polynomial.coeff_map, coeff_genericDepressed]
    split_ifs with hkm hk
    · rw [hkm, map_one, ← hdeg]
      exact hf.leadingCoeff.symm
    · have hk_eq : m - 2 - (m - 2 - k) = k := by omega
      simpa [hk_eq] using hφ ⟨m - 2 - k, by omega⟩
    · simp only [map_zero]
      rcases eq_or_ne k (m - 1) with rfl | hkne
      · have hm1 : 1 ≤ m := by omega
        have hpos : 0 < f.natDegree := by omega
        have hsub : m - 1 = f.natDegree - 1 := by omega
        rw [hsub, ← nextCoeff_of_natDegree_pos hpos, hnext]
      · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- **Unique `R`-algebra specialization of `TauCeti.genericDepressed`.** For any monic depressed
polynomial `f : S[X]` of `natDegree` `m` over an `R`-algebra `S`, an `R`-algebra homomorphism
`φ : MvPolynomial (Fin (m - 1)) R →ₐ[R] S` maps `genericDepressed R m` to `f` if and only if
`φ = MvPolynomial.aeval fun i : Fin (m - 1) ↦ f.coeff (m - 2 - i)`. -/
theorem map_algHom_genericDepressed_eq_iff (R : Type*) [CommSemiring R] {S : Type*}
    [CommSemiring S] [Algebra R S] {f : S[X]} {m : ℕ} (hf : f.Monic) (hdeg : f.natDegree = m)
    (hnext : f.nextCoeff = 0) (φ : MvPolynomial (Fin (m - 1)) R →ₐ[R] S) :
    (genericDepressed R m).map φ.toRingHom = f ↔
      φ = MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦ f.coeff (m - 2 - (i : ℕ)) := by
  rw [map_genericDepressed_eq_iff hf hdeg hnext]
  exact ⟨fun h ↦ MvPolynomial.algHom_ext fun i ↦ by simpa using h i,
    fun h i ↦ by simp [h]⟩

/-- **Universal property of the generic depressed polynomial.** A monic polynomial `p` of degree
`m` with vanishing subleading coefficient over an `R`-algebra `S` is the specialization of
`genericDepressed R m` at `aⱼ₊₂ = p.coeff (m - 2 - j)`. -/
theorem map_eval_genericDepressed {S : Type*} [CommSemiring S] [Algebra R S]
    {p : S[X]} (hp : p.Monic) (hdeg : p.natDegree = m) (hnext : p.nextCoeff = 0) :
    (genericDepressed R m).map
        (MvPolynomial.aeval (R := R) fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j)).toRingHom =
      p :=
  (map_genericDepressed_eq_iff hp hdeg hnext _).mpr fun j ↦ by simp

/-- For `m = 0`, `TauCeti.genericDepressed R 0` is the constant polynomial `1`. -/
@[simp]
theorem genericDepressed_zero (R : Type*) [CommSemiring R] :
    genericDepressed R 0 = 1 := by
  ext k : 2
  rw [coeff_genericDepressed, Polynomial.coeff_one]
  split_ifs
  · simp
  · omega
  · simp

/-- For `m = 1`, `TauCeti.genericDepressed R 1` is `X`. -/
@[simp]
theorem genericDepressed_one (R : Type*) [CommSemiring R] :
    genericDepressed R 1 = Polynomial.X := by
  ext k : 2
  rw [coeff_genericDepressed, Polynomial.coeff_X]
  split_ifs <;> first | omega | rfl

/-- For `m = 2`, `TauCeti.genericDepressed R 2` is `X ^ 2 + C (X 0)`. -/
theorem genericDepressed_two (R : Type*) [CommSemiring R] :
    genericDepressed R 2 = Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0) := by
  ext k : 2
  rw [coeff_genericDepressed]
  rcases k with _ | _ | _ | k <;> simp [Fin.eq_zero]

/-- For `m = 3`, `TauCeti.genericDepressed R 3` is `X ^ 3 + C (X 0) * X + C (X 1)`. -/
theorem genericDepressed_three (R : Type*) [CommSemiring R] :
    genericDepressed R 3 =
      Polynomial.X ^ 3 + Polynomial.C (MvPolynomial.X 0) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 1) := by
  ext k : 2
  rw [coeff_genericDepressed]
  rcases k with _ | _ | _ | _ | k <;> simp [Polynomial.coeff_X]

/-- For `m = 4`, `TauCeti.genericDepressed R 4` is
`X ^ 4 + C (X 0) * X ^ 2 + C (X 1) * X + C (X 2)`. -/
theorem genericDepressed_four (R : Type*) [CommSemiring R] :
    genericDepressed R 4 =
      Polynomial.X ^ 4 + Polynomial.C (MvPolynomial.X 0) * Polynomial.X ^ 2 +
        Polynomial.C (MvPolynomial.X 1) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 2) := by
  ext k : 2
  rw [coeff_genericDepressed]
  rcases k with _ | _ | _ | _ | _ | k <;> simp [Polynomial.coeff_X]

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

/-- Mapping the base ring commutes with forming `TauCeti.depressedDiscr`. -/
@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (depressedDiscr R m) = depressedDiscr S m := by
  rw [← discr_genericDepressed, ← (monic_genericDepressed (R := R) (m := m)).discr_map
    (MvPolynomial.map φ), map_map_genericDepressed, discr_genericDepressed]

/-- Evaluating `TauCeti.depressedDiscr R m` at `a : Fin (m - 1) → S` computes the discriminant of
the specialized depressed polynomial `(genericDepressed R m).map (aeval a)`. -/
theorem aeval_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {m : ℕ}
    (a : Fin (m - 1) → S) :
    MvPolynomial.aeval a (depressedDiscr R m) =
      ((genericDepressed R m).map (MvPolynomial.aeval a).toRingHom).discr := by
  rw [← discr_genericDepressed, (monic_genericDepressed (R := R) (m := m)).discr_map]
  rfl

/-- The discriminant of a monic polynomial `p` of degree `m` with vanishing subleading coefficient
over an `R`-algebra `S` is `depressedDiscr R m` evaluated at `aⱼ₊₂ = p.coeff (m - 2 - j)`. -/
theorem discr_eq_eval_depressedDiscr {S : Type*} [CommRing S] [Algebra R S]
    {p : S[X]} (hp : p.Monic) (hdeg : p.natDegree = m) (hnext : p.nextCoeff = 0) :
    p.discr =
      MvPolynomial.aeval (R := R) (fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j))
        (depressedDiscr R m) := by
  have h := (monic_genericDepressed (R := R) (m := m)).discr_map
    (MvPolynomial.aeval (R := R) fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j)).toRingHom
  rw [map_eval_genericDepressed hp hdeg hnext] at h
  rw [← discr_genericDepressed]
  exact h

variable (R m)

/-- **The generic depressed discriminant is isobaric (general monoid weights).** For any element
`u` of an additive commutative monoid `M`, the discriminant of `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is
weighted homogeneous of weight `(m * (m - 1)) • u` when `aⱼ` is given weight `j • u`. -/
theorem depressedDiscr_mem_smul {M : Type*} [AddCommMonoid M] (u : M) :
    depressedDiscr R m ∈
      MvPolynomial.weightedHomogeneousSubmodule R (fun j : Fin (m - 1) ↦ ((j : ℕ) + 2) • u)
        ((m * (m - 1)) • u) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R m) 0]
    exact zero_mem _
  rw [← discr_genericDepressed, MvPolynomial.mem_weightedHomogeneousSubmodule]
  have h := isWeightedHomogeneous_discr u (p := genericDepressed R m) fun i ↦ by
    rw [natDegree_genericDepressed]
    have hi := (isWeightedHomogeneous_coeff_genericDepressed (R := R) (m := m) i).comp_weight
      (multiplesHom M u)
    simpa [Function.comp_def, multiplesHom_apply] using hi
  rwa [natDegree_genericDepressed] at h

/-- **The generic depressed discriminant is isobaric.** The discriminant of
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is weighted homogeneous of weight `m (m - 1)`, for the weights
`aⱼ ↦ j`. -/
theorem depressedDiscr_mem :
    depressedDiscr R m ∈
      MvPolynomial.weightedHomogeneousSubmodule R (depressedWeight m) (m * (m - 1)) := by
  have h := depressedDiscr_mem_smul R m (1 : ℤ)
  have hw : (fun j : Fin (m - 1) ↦ ((j : ℕ) + 2) • (1 : ℤ)) = depressedWeight m := by
    ext j
    simp
  have hm : ((m * (m - 1)) • (1 : ℤ)) = (m * (m - 1) : ℤ) := by
    rcases m with _ | m <;> simp
  rwa [hw, hm] at h

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
