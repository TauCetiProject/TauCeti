/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Graded

/-!
# The generic depressed polynomial and its discriminant

The *generic depressed monic polynomial* of degree `m` over `R` is
`Xᵐ + a₂ Xᵐ⁻² + a₃ Xᵐ⁻³ + ⋯ + aₘ` in `(R[a₂, …, aₘ])[X]`, where `aₖ` is represented by the
variable `MvPolynomial.X ⟨k - 2, _⟩` of `MvPolynomial (Fin (m - 1)) R`. Every monic polynomial of
degree `m` over an algebra in which `m` is invertible reduces to a specialization of this family
after translating `X` by `-a₁ / m` (`Polynomial.discr_comp_X_add_C` preserves the discriminant).

Giving `aₖ` weight `k` (`TauCeti.depressedWeight m`) makes `genericDepressed R m` quasi-homogeneous
of degree `m` when `X` has weight `1`. Its discriminant `TauCeti.depressedDiscr R m` therefore has
weighted degree `m * (m - 1)` (`TauCeti.isWeightedHomogeneous_depressedDiscr`,
`TauCeti.depressedDiscr_mem`).

Specializing all variables except one yields two binomial-type families whose discriminants are
explicit pure powers:
* Setting `aₘ = a` and all other `aₖ = 0` gives `Xᵐ + a`, with discriminant
  `(-1) ^ (m * (m - 1) / 2) * m ^ m * a ^ (m - 1)` (`TauCeti.aeval_single_sub_two_depressedDiscr`).
* For `m ≥ 3`, setting `aₘ₋₁ = a` and all other `aₖ = 0` gives `Xᵐ + a X = X (Xᵐ⁻¹ + a)`, with
  discriminant `(-1) ^ ((m - 1) * (m - 2) / 2) * (m - 1) ^ (m - 1) * a ^ m`
  (`TauCeti.aeval_single_sub_three_depressedDiscr`).

For `m ≥ 3` over a domain `R` in which `(m : R) ≠ 0` and `((m - 1 : ℕ) : R) ≠ 0`, these two
specializations force `depressedDiscr R m` to be irreducible and prime in `R[a₂, …, aₘ]`, without
any factoriality assumption on `R`:
* Any factorization splits the weight `m * (m - 1)` into two natural weights `a + b`. Nonvanishing
  on both coordinate axes forces both `m` and `m - 1` to divide `a`, hence `m * (m - 1) ∣ a` since
  `m` and `m - 1` are coprime, so one factor has weight `0` and is a constant dividing the coprime
  elements `m ^ m` and `(m - 1) ^ (m - 1)` in `R`, hence a unit
  (`TauCeti.irreducible_depressedDiscr_of_three_le`).
* Over `K = FractionRing R`, irreducibility in the factorial ring `K[a₂, …, aₘ]` implies primality.
  To descend divisibility `H * Δ = P` from `K[a₂, …, aₘ]` to `R[a₂, …, aₘ]`, note that
  `aₘ ^ (m - 1)` is the unique monomial of `Δ` of degree at least `m - 1` in `aₘ` (with coefficient
  `± m ^ m`), and `aₘ₋₁ ^ m` is the unique monomial of degree at least `m` in `aₘ₋₁` (with
  coefficient `± (m - 1) ^ (m - 1)`). Clearing denominators along each variable puts both a power of
  `m` times `H` and a power of `m - 1` times `H` into `R[a₂, …, aₘ]`, and coprimality of `m` and
  `m - 1` in `R` puts `H` itself into `R[a₂, …, aₘ]` (`TauCeti.prime_depressedDiscr_of_three_le`).

By contrast, at `m = 2` we have `depressedDiscr R 2 = -4 * X 0`, which over a domain `R` is prime
if and only if `2` is a unit in `R` (`TauCeti.prime_depressedDiscr_two_iff`); for instance `-4 a₂`
factors as `(-2) * (2 a₂)` in `ℤ[a₂]`, whereas `-4 a₂³ - 27 a₃²` is prime in `ℤ[a₂, a₃]`. Over a
field `K`, both cases unite: `depressedDiscr K m` is prime whenever `(m : K) ≠ 0` and
`((m - 1 : ℕ) : K) ≠ 0` (`TauCeti.prime_depressedDiscr_of_ne_zero`), and in particular for all
`m ≥ 2` in characteristic zero (`TauCeti.prime_depressedDiscr`).

## Main definitions

* `TauCeti.genericDepressed`: the generic depressed monic polynomial
  `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` over `MvPolynomial (Fin (m - 1)) R`.
* `TauCeti.depressedWeight`: the `ℤ`-weight `i ↦ i + 2` giving `aₖ` weight `k`.
* `TauCeti.depressedDiscr`: the discriminant of `genericDepressed R m`.

## Main results

* `TauCeti.isWeightedHomogeneous_depressedDiscr`, `TauCeti.depressedDiscr_mem`:
  `depressedDiscr R m` has weighted degree `m * (m - 1)`.
* `TauCeti.aeval_single_sub_two_depressedDiscr`, `TauCeti.aeval_single_sub_three_depressedDiscr`:
  explicit formulas on the `aₘ`-axis and `aₘ₋₁`-axis.
* `TauCeti.prime_depressedDiscr_two_iff`: over a domain `R`, `depressedDiscr R 2` is prime iff
  `IsUnit (2 : R)`.
* `TauCeti.irreducible_depressedDiscr_of_three_le`, `TauCeti.prime_depressedDiscr_of_three_le`:
  irreducibility and primality of `depressedDiscr R m` for `m ≥ 3` over any domain `R` in which
  `m` and `m - 1` are nonzero.
* `TauCeti.prime_depressedDiscr_of_ne_zero`, `TauCeti.prime_depressedDiscr`: primality over fields
  when `(m : K) ≠ 0` and `((m - 1 : ℕ) : K) ≠ 0`, and in characteristic zero for `m ≥ 2`.
-/

public section

namespace TauCeti

open Polynomial

section GenericDepressed

/-- The generic depressed monic polynomial of degree `m` over `R`,
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ`, where `aₖ` is the variable `⟨k - 2, _⟩` of
`MvPolynomial (Fin (m - 1)) R`. -/
noncomputable def genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    Polynomial (MvPolynomial (Fin (m - 1)) R) :=
  X ^ m + ∑ i : Fin (m - 1), C (MvPolynomial.X i) * X ^ (m - (i.val + 2))

theorem genericDepressed_def (R : Type*) [CommSemiring R] (m : ℕ) :
    genericDepressed R m =
      X ^ m + ∑ i : Fin (m - 1), C (MvPolynomial.X i) * X ^ (m - (i.val + 2)) :=
  (rfl)

/-- The `k`-th coefficient of `genericDepressed R m`: `1` at `k = m`, the variable
`MvPolynomial.X ⟨m - 2 - k, _⟩` for `k + 2 ≤ m`, and `0` otherwise (in particular at
`k = m - 1`). -/
theorem coeff_genericDepressed (R : Type*) [CommSemiring R] (m k : ℕ) :
    (genericDepressed R m).coeff k =
      if k = m then 1
      else if hk : k + 2 ≤ m then MvPolynomial.X ⟨m - 2 - k, by omega⟩
      else 0 := by
  rw [genericDepressed_def, coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with hkm hk
  · subst hkm
    rw [Finset.sum_eq_zero (fun i _ ↦ ite_eq_right (by omega)), add_zero]
  · rw [zero_add, Finset.sum_eq_single ⟨m - 2 - k, by omega⟩]
    · exact ite_eq_left (by simp; omega)
    · intro i _ hne
      exact ite_eq_right fun h ↦ hne (Fin.ext (by simp; omega))
    · simp
  · rw [zero_add]
    exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by omega)

/-- `genericDepressed R m` is monic for every commutative semiring `R` and every `m : ℕ`. -/
theorem monic_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).Monic := by
  refine monic_X_pow_add ?_
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [coeff_C_mul, coeff_X_pow, ite_eq_right (by omega), mul_zero]

@[simp]
theorem natDegree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).natDegree = m := by
  refine le_antisymm ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_genericDepressed, ite_eq_right (by omega), dite_eq_right_iff.mpr fun h ↦ by omega]
  · refine le_natDegree_of_ne_zero ?_
    rw [coeff_genericDepressed, ite_eq_left rfl]
    exact one_ne_zero

/-- The second-highest coefficient of `genericDepressed R m` vanishes for all `R` and `m`. -/
@[simp]
theorem nextCoeff_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).nextCoeff = 0 := by
  nontriviality R
  rw [nextCoeff, natDegree_genericDepressed]
  split_ifs with hm
  · rfl
  · rw [coeff_genericDepressed, ite_eq_right (by omega), dite_eq_right_iff.mpr fun h ↦ by omega]

/-- Base change of `genericDepressed` along a ring homomorphism on the coefficients. -/
theorem map_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (m : ℕ) :
    (genericDepressed R m).map (MvPolynomial.map φ) = genericDepressed S m := by
  simp [genericDepressed_def, Polynomial.map_sum]

/-- Evaluating the coefficient variables of `genericDepressed R m` at `a : Fin (m - 1) → A`
produces the concrete depressed monic polynomial `Xᵐ + ∑ i, C (a i) * X ^ (m - (i + 2))`. -/
theorem map_aeval_genericDepressed {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (m : ℕ) (a : Fin (m - 1) → A) :
    (genericDepressed R m).map (MvPolynomial.aeval a).toRingHom =
      X ^ m + ∑ i : Fin (m - 1), C (a i) * X ^ (m - (i.val + 2)) := by
  simp [genericDepressed_def, Polynomial.map_sum]

@[simp]
theorem genericDepressed_zero (R : Type*) [CommSemiring R] :
    genericDepressed R 0 = 1 := by
  simp [genericDepressed_def]

@[simp]
theorem genericDepressed_one (R : Type*) [CommSemiring R] :
    genericDepressed R 1 = X := by
  simp [genericDepressed_def]

theorem genericDepressed_two (R : Type*) [CommSemiring R] :
    genericDepressed R 2 = X ^ 2 + C (MvPolynomial.X 0) := by
  simp [genericDepressed_def]

theorem genericDepressed_three (R : Type*) [CommSemiring R] :
    genericDepressed R 3 =
      X ^ 3 + C (MvPolynomial.X 0) * X + C (MvPolynomial.X 1) := by
  rw [genericDepressed_def, Fin.sum_univ_two]
  simp [add_assoc]

theorem genericDepressed_four (R : Type*) [CommSemiring R] :
    genericDepressed R 4 =
      X ^ 4 + C (MvPolynomial.X 0) * X ^ 2 + C (MvPolynomial.X 1) * X +
        C (MvPolynomial.X 2) := by
  rw [genericDepressed_def, Fin.sum_univ_three]
  simp [add_assoc]

end GenericDepressed

section DepressedDiscr

/-- The weight assignment on `Fin (m - 1)` giving `aₖ` (variable `⟨k - 2, _⟩`) weight `k`. -/
def depressedWeight (m : ℕ) : Fin (m - 1) → ℤ := fun i ↦ (i.val : ℤ) + 2

@[simp]
theorem depressedWeight_apply {m : ℕ} (i : Fin (m - 1)) :
    depressedWeight m i = (i.val : ℤ) + 2 :=
  (rfl)

/-- The discriminant of `genericDepressed R m`, as an element of `MvPolynomial (Fin (m - 1)) R`. -/
noncomputable def depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin (m - 1)) R :=
  (genericDepressed R m).discr

theorem depressedDiscr_def (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m = (genericDepressed R m).discr :=
  (rfl)

@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (depressedDiscr R m) = depressedDiscr S m := by
  rw [depressedDiscr_def, ← (monic_genericDepressed R m).discr_map (MvPolynomial.map φ),
    map_genericDepressed, depressedDiscr_def]

/-- Evaluating `depressedDiscr R m` at `a : Fin (m - 1) → A` computes the discriminant of the
specialized depressed monic polynomial over `A`. -/
theorem aeval_depressedDiscr {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (m : ℕ)
    (a : Fin (m - 1) → A) :
    MvPolynomial.aeval a (depressedDiscr R m) =
      (X ^ m + ∑ i : Fin (m - 1), C (a i) * X ^ (m - (i.val + 2))).discr := by
  rw [depressedDiscr_def, ← map_aeval_genericDepressed (R := R),
    (monic_genericDepressed R m).discr_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

@[simp]
theorem depressedDiscr_zero (R : Type*) [CommRing R] :
    depressedDiscr R 0 = 1 := by
  simpa [depressedDiscr_def] using discr_C (1 : MvPolynomial (Fin 0) R)

@[simp]
theorem depressedDiscr_one (R : Type*) [CommRing R] :
    depressedDiscr R 1 = 1 := by
  have hX : (X : Polynomial (MvPolynomial (Fin 0) R)) = X ^ 1 - C 0 := by simp
  rw [depressedDiscr_def, genericDepressed_one, hX, discr_X_pow_sub_C]
  simp

/-- The discriminant of the generic depressed quadratic `X² + a₂` is `-4 a₂`. -/
theorem depressedDiscr_two (R : Type*) [CommRing R] :
    depressedDiscr R 2 = -4 * MvPolynomial.X 0 := by
  have h : (X ^ 2 + C (MvPolynomial.X 0) : Polynomial (MvPolynomial (Fin 1) R)) =
      X ^ 2 - C (-MvPolynomial.X 0) := by rw [map_neg, sub_neg_eq_add]
  rw [depressedDiscr_def, genericDepressed_two, h, discr_X_pow_sub_C]
  ring

/-- The discriminant of the generic depressed cubic `X³ + a₂ X + a₃` is `-4 a₂³ - 27 a₃²`. -/
theorem depressedDiscr_three (R : Type*) [CommRing R] :
    depressedDiscr R 3 = -4 * MvPolynomial.X 0 ^ 3 - 27 * MvPolynomial.X 1 ^ 2 := by
  nontriviality R
  have hdeg : (genericDepressed R 3).degree = 3 := by
    rw [degree_eq_natDegree (monic_genericDepressed R 3).ne_zero, natDegree_genericDepressed]
    rfl
  rw [depressedDiscr_def, discr_of_degree_eq_three hdeg, genericDepressed_three]
  simp

/-- The discriminant of the generic depressed quartic `X⁴ + a₂ X² + a₃ X + a₄`. -/
theorem depressedDiscr_four (R : Type*) [CommRing R] :
    depressedDiscr R 4 =
      256 * MvPolynomial.X 2 ^ 3 - 128 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2 +
        144 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
        27 * MvPolynomial.X 1 ^ 4 + 16 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 2 -
        4 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 := by
  rw [depressedDiscr_def, genericDepressed_four, discr_depressedQuartic]

/-- `depressedDiscr R m` is weighted homogeneous of `ℕ`-weight `m * (m - 1)` when variable `i` has
weight `i + 2`. -/
theorem isWeightedHomogeneous_depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    (depressedDiscr R m).IsWeightedHomogeneous (fun i : Fin (m - 1) ↦ i.val + 2)
      (m * (m - 1)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim (depressedDiscr R m) 0 ▸
      MvPolynomial.isWeightedHomogeneous_zero R _ _
  let w : Fin (m - 1) → ℕ := fun i ↦ i.val + 2
  have := MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid (R := R) (w := w)
  have hmem := (monic_genericDepressed R m).discr_mem_graded
    (𝒜 := MvPolynomial.weightedHomogeneousSubmodule R w) (w := (1 : ℕ)) fun k hk ↦ by
      rw [natDegree_genericDepressed] at hk ⊢
      rw [nsmul_one, coeff_genericDepressed, ite_eq_right (by omega)]
      split_ifs with hk2
      · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
        have hw : m - k = w ⟨m - 2 - k, by omega⟩ := by dsimp [w]; omega
        rw [hw]
        exact MvPolynomial.isWeightedHomogeneous_X R w _
      · exact zero_mem _
  simpa [depressedDiscr_def, natDegree_genericDepressed] using hmem

/-- `depressedDiscr R m` lies in the graded piece of `ℤ`-weight `m * (m - 1)` for
`depressedWeight m`. -/
theorem depressedDiscr_mem (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m ∈
      MvPolynomial.weightedHomogeneousSubmodule R (depressedWeight m) ((m : ℤ) * (m - 1)) := by
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  intro d hd
  have hnat := isWeightedHomogeneous_depressedDiscr R m hd
  have hcast : Finsupp.weight (depressedWeight m) d =
      ((Finsupp.weight (fun i : Fin (m - 1) ↦ i.val + 2) d : ℕ) : ℤ) := by
    simp [Finsupp.weight_apply, Finsupp.sum, depressedWeight]
  rw [hcast, hnat]
  rcases m with _ | m <;> simp

end DepressedDiscr

section Specializations

/-- Specializing `depressedDiscr R m` (`m ≥ 2`) to `Pi.single ⟨m - 2, _⟩ a` (setting `aₘ = a` and
all other `aₖ = 0`) computes the discriminant of `Xᵐ + a`. -/
theorem aeval_single_sub_two_depressedDiscr {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : ℕ} (hm : 2 ≤ m) (a : A) :
    MvPolynomial.aeval (Pi.single ⟨m - 2, by omega⟩ a) (depressedDiscr R m) =
      (-1) ^ (m * (m - 1) / 2) * (m : A) ^ m * a ^ (m - 1) := by
  rw [aeval_depressedDiscr, Finset.sum_eq_single ⟨m - 2, by omega⟩]
  · have hsub : m - (m - 2 + 2) = 0 := by omega
    have hpoly : X ^ m + C (Pi.single (M := fun _ : Fin (m - 1) ↦ A) ⟨m - 2, by omega⟩ a
        ⟨m - 2, by omega⟩) * X ^ (m - (m - 2 + 2)) = X ^ m - C (-a) := by
      rw [hsub, Pi.single_eq_same, pow_zero, mul_one, map_neg, sub_neg_eq_add]
    rw [hpoly, discr_X_pow_sub_C, neg_neg]
  · intro i _ hne
    rw [Pi.single_eq_of_ne hne, map_zero, zero_mul]
  · simp

/-- Specializing `depressedDiscr R m` (`m ≥ 3`) to `Pi.single ⟨m - 3, _⟩ a` (setting `aₘ₋₁ = a`
and all other `aₖ = 0`) computes the discriminant of `Xᵐ + a X = X (Xᵐ⁻¹ + a)`. -/
theorem aeval_single_sub_three_depressedDiscr {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : ℕ} (hm : 3 ≤ m) (a : A) :
    MvPolynomial.aeval (Pi.single ⟨m - 3, by omega⟩ a) (depressedDiscr R m) =
      (-1) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : A) ^ (m - 1) * a ^ m := by
  nontriviality A
  rw [aeval_depressedDiscr, Finset.sum_eq_single ⟨m - 3, by omega⟩]
  · have hsub : m - (m - 3 + 2) = 1 := by omega
    let g : A[X] := X ^ (m - 1) - C (-a)
    have hg : g.Monic := monic_X_pow_sub_C (-a) (by omega)
    have hpoly : X ^ m + C (Pi.single (M := fun _ : Fin (m - 1) ↦ A) ⟨m - 3, by omega⟩ a
        ⟨m - 3, by omega⟩) * X ^ (m - (m - 3 + 2)) = X * g := by
      rw [hsub, Pi.single_eq_same, pow_one]
      have hm' : (X : A[X]) ^ m = X * X ^ (m - 1) := by
        conv_lhs => rw [← Nat.add_sub_of_le (by omega : 1 ≤ m), pow_add, pow_one]
      rw [hm']
      dsimp [g]
      rw [map_neg, sub_neg_eq_add]
      ring
    have hX_discr : (X : A[X]).discr = 1 := by
      have hX : (X : A[X]) = X ^ 1 - C 0 := by simp
      rw [hX, discr_X_pow_sub_C]
      simp
    have hres : (X : A[X]).resultant g = a := by
      have hX1 : (X : A[X]).resultant g = (X ^ 1).resultant g 1 g.natDegree := by
        rw [pow_one, natDegree_X]
      rw [hX1, resultant_X_pow_left g 1 g.natDegree le_rfl, pow_one, coeff_sub, coeff_X_pow,
        ite_eq_right (by omega), zero_sub, coeff_C_zero, neg_neg]
    have hpow : a ^ (m - 2) * a ^ 2 = a ^ m := by
      rw [← pow_add, show m - 2 + 2 = m by omega]
    rw [hpoly, monic_X.discr_mul hg, hX_discr, hres, one_mul]
    dsimp [g]
    rw [discr_X_pow_sub_C, neg_neg, show m - 1 - 1 = m - 2 by omega, mul_assoc, hpow]
  · intro i _ hne
    rw [Pi.single_eq_of_ne hne, map_zero, zero_mul]
  · simp

private theorem eq_single_of_le_of_isWeightedHomogeneous {σ R : Type*} [CommSemiring R]
    {w : σ → ℕ} (hw : ∀ i, 0 < w i) {φ : MvPolynomial σ R} {j : σ} {k : ℕ}
    (hφ : φ.IsWeightedHomogeneous w (k * w j)) {s : σ →₀ ℕ} (hs : s ∈ φ.support)
    (hk : k ≤ s j) : s = Finsupp.single j k := by
  classical
  have hdeg : Finsupp.weight w s = k * w j := hφ (MvPolynomial.mem_support_iff.mp hs)
  have hsplit : s j * w j + Finsupp.weight w (s.erase j) = k * w j := by
    have := congrArg (Finsupp.weight w) (Finsupp.single_add_erase j s)
    simpa [map_add, Finsupp.weight_apply, zero_smul] using this.trans hdeg
  have hle : k * w j ≤ s j * w j := Nat.mul_le_mul_right (w j) hk
  have hsj : s j = k := Nat.eq_of_mul_eq_mul_right (hw j) (by omega)
  rw [hsj] at hsplit
  have hzero : s.erase j = 0 := by
    ext i
    by_contra hi
    have hle' := Finsupp.le_weight_of_ne_zero' w hi
    have hwi := hw i
    omega
  rw [← Finsupp.single_add_erase j s, hsj, hzero, add_zero]

/-- The coefficient of `aₘ ^ (m - 1)` in `depressedDiscr R m` (`m ≥ 2`). -/
theorem coeff_single_sub_two_depressedDiscr (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m) :
    (depressedDiscr R m).coeff (Finsupp.single ⟨m - 2, by omega⟩ (m - 1)) =
      (-1) ^ (m * (m - 1) / 2) * (m : R) ^ m := by
  let w : Fin (m - 1) → ℕ := fun i ↦ i.val + 2
  let j : Fin (m - 1) := ⟨m - 2, by omega⟩
  have hwj : (m - 1) • w j = m * (m - 1) := by
    dsimp [w, j]
    rw [show m - 2 + 2 = m by omega, mul_comm]
  have hhom : (depressedDiscr R m).IsWeightedHomogeneous w ((m - 1) • w j) :=
    hwj.symm ▸ isWeightedHomogeneous_depressedDiscr R m
  have hinj (n : ℕ) (hn : n • w j = (m - 1) • w j) : n = m - 1 := by
    dsimp [w, j] at hn
    exact Nat.eq_of_mul_eq_mul_right (by omega) hn
  rw [hhom.coeff_single_eq_eval hinj, ← MvPolynomial.aeval_eq_eval,
    aeval_single_sub_two_depressedDiscr (R := R) hm (1 : R), one_pow, mul_one]

/-- The coefficient of `aₘ₋₁ ^ m` in `depressedDiscr R m` (`m ≥ 3`). -/
theorem coeff_single_sub_three_depressedDiscr (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    (depressedDiscr R m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m) =
      (-1) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : R) ^ (m - 1) := by
  let w : Fin (m - 1) → ℕ := fun i ↦ i.val + 2
  let j : Fin (m - 1) := ⟨m - 3, by omega⟩
  have hwj : m • w j = m * (m - 1) := by
    dsimp [w, j]
    rw [show m - 3 + 2 = m - 1 by omega]
  have hhom : (depressedDiscr R m).IsWeightedHomogeneous w (m • w j) :=
    hwj.symm ▸ isWeightedHomogeneous_depressedDiscr R m
  have hinj (n : ℕ) (hn : n • w j = m • w j) : n = m := by
    dsimp [w, j] at hn
    exact Nat.eq_of_mul_eq_mul_right (by omega) hn
  rw [hhom.coeff_single_eq_eval hinj, ← MvPolynomial.aeval_eq_eval,
    aeval_single_sub_three_depressedDiscr (R := R) hm (1 : R), one_pow, mul_one]

end Specializations

section Primality

/-- Over an integral domain `R`, `depressedDiscr R 2 = -4 * X 0` is prime if and only if `2` is a
unit in `R`. -/
theorem prime_depressedDiscr_two_iff {R : Type*} [CommRing R] [IsDomain R] :
    Prime (depressedDiscr R 2) ↔ IsUnit (2 : R) := by
  rw [depressedDiscr_two]
  constructor
  · intro hp
    have hfac : (-4 : MvPolynomial (Fin 1) R) * MvPolynomial.X 0 =
        MvPolynomial.C (-2 : R) * (MvPolynomial.C (2 : R) * MvPolynomial.X 0) := by
      rw [← mul_assoc, ← map_mul]
      norm_num
      exact (map_ofNat MvPolynomial.C 4).symm
    rcases hp.irreducible.isUnit_or_isUnit hfac with hu | hu
    · have hu' : IsUnit (-2 : R) := by simpa using hu.map MvPolynomial.constantCoeff
      simpa using hu'.neg
    · exact False.elim ((MvPolynomial.prime_X (R := R) (i := (0 : Fin 1))).not_isUnit
        (isUnit_of_mul_isUnit_right hu))
  · intro hu
    have hc : (-4 : MvPolynomial (Fin 1) R) * MvPolynomial.X 0 =
        MvPolynomial.C (-(2 : R) ^ 2) * MvPolynomial.X 0 := by
      norm_num
      exact (map_ofNat MvPolynomial.C 4).symm
    rw [hc]
    exact (associated_unit_mul_left (MvPolynomial.X (0 : Fin 1)) _
      (((hu.pow 2).neg).map MvPolynomial.C)).prime_iff.mpr
      (MvPolynomial.prime_X (R := R) (i := (0 : Fin 1)))

private theorem isUnit_of_dvd_depressedDiscr_of_weight_zero {R : Type*} [CommRing R]
    {m : ℕ} (hm : 3 ≤ m) {P : MvPolynomial (Fin (m - 1)) R}
    (hP : P.IsWeightedHomogeneous (fun i : Fin (m - 1) ↦ i.val + 2) 0)
    (hdvd : P ∣ depressedDiscr R m) : IsUnit P := by
  have hC : P = MvPolynomial.C P.constantCoeff := by
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · rw [MvPolynomial.coeff_zero_C]
      rfl
    · rw [MvPolynomial.coeff_C, ite_eq_right hd.symm]
      by_contra hc
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd
      exact absurd (hP.apply_eq_zero_of_coeff_ne_zero hc hi) (by omega)
  rw [hC] at hdvd ⊢
  have h1 : P.constantCoeff ∣ (m : R) ^ m := by
    have hd := map_dvd (MvPolynomial.aeval (Pi.single ⟨m - 2, by omega⟩ (1 : R))) hdvd
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      aeval_single_sub_two_depressedDiscr (by omega), one_pow, mul_one] at hd
    exact (isUnit_one.neg.pow _).dvd_mul_left.mp hd
  have h2 : P.constantCoeff ∣ ((m - 1 : ℕ) : R) ^ (m - 1) := by
    have hd := map_dvd (MvPolynomial.aeval (Pi.single ⟨m - 3, by omega⟩ (1 : R))) hdvd
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      aeval_single_sub_three_depressedDiscr hm, one_pow, mul_one] at hd
    exact (isUnit_one.neg.pow _).dvd_mul_left.mp hd
  have hcop : IsCoprime (m : R) ((m - 1 : ℕ) : R) :=
    ⟨1, -1, by rw [Nat.cast_sub (by omega)]; ring⟩
  exact ((hcop.pow (m := m) (n := m - 1)).isUnit_of_dvd' h1 h2).map MvPolynomial.C

/-- For `m ≥ 3` over a commutative ring `R` without zero divisors in which `(m : R) ≠ 0` and
`((m - 1 : ℕ) : R) ≠ 0`, `depressedDiscr R m` is irreducible in `MvPolynomial (Fin (m - 1)) R`. -/
theorem irreducible_depressedDiscr_of_three_le {R : Type*} [CommRing R] [NoZeroDivisors R]
    {m : ℕ} (hm : 3 ≤ m) (hm0 : (m : R) ≠ 0) (hm1 : ((m - 1 : ℕ) : R) ≠ 0) :
    Irreducible (depressedDiscr R m) := by
  have : Nontrivial R := ⟨m, 0, hm0⟩
  let w : Fin (m - 1) → ℕ := fun i ↦ i.val + 2
  have hm_pos : 0 < m * (m - 1) := Nat.mul_pos (by omega) (by omega)
  have hval₁ :
      MvPolynomial.aeval (Pi.single ⟨m - 2, by omega⟩ (1 : R)) (depressedDiscr R m) ≠ 0 := by
    rw [aeval_single_sub_two_depressedDiscr (by omega), one_pow, mul_one]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hm0)
  have hval₂ :
      MvPolynomial.aeval (Pi.single ⟨m - 3, by omega⟩ (1 : R)) (depressedDiscr R m) ≠ 0 := by
    rw [aeval_single_sub_three_depressedDiscr hm, one_pow, mul_one]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hm1)
  refine ⟨fun hu ↦ ?_, fun F G hFG ↦ ?_⟩
  · have h0 : MvPolynomial.eval (0 : Fin (m - 1) → R) (depressedDiscr R m) = 0 :=
      (isWeightedHomogeneous_depressedDiscr R m).eval₂_eq_zero hm_pos.ne' (RingHom.id R)
        fun _ _ ↦ rfl
    exact not_isUnit_zero (h0 ▸ hu.map (MvPolynomial.eval 0))
  · have hFG0 : F * G ≠ 0 := fun h ↦ hval₁ (by rw [hFG, h, map_zero])
    obtain ⟨a, b, hF, hG, hab⟩ :=
      (hFG ▸ isWeightedHomogeneous_depressedDiscr R m).exists_of_mul hFG0
    have hF₁ : MvPolynomial.aeval (Pi.single ⟨m - 2, by omega⟩ (1 : R)) F ≠ 0 :=
      left_ne_zero_of_mul (by rwa [← map_mul, ← hFG])
    have hF₂ : MvPolynomial.aeval (Pi.single ⟨m - 3, by omega⟩ (1 : R)) F ≠ 0 :=
      left_ne_zero_of_mul (by rwa [← map_mul, ← hFG])
    obtain ⟨k₁, hk₁⟩ := hF.exists_nsmul_eq_of_aeval_single_ne_zero hF₁
    obtain ⟨k₂, hk₂⟩ := hF.exists_nsmul_eq_of_aeval_single_ne_zero hF₂
    have hdvd₁ : m ∣ a := by
      dsimp [w] at hk₁
      rw [show m - 2 + 2 = m by omega, mul_comm] at hk₁
      exact ⟨k₁, hk₁.symm⟩
    have hdvd₂ : m - 1 ∣ a := by
      dsimp [w] at hk₂
      rw [show m - 3 + 2 = m - 1 by omega, mul_comm] at hk₂
      exact ⟨k₂, hk₂.symm⟩
    have hcop_nat : Nat.Coprime m (m - 1) :=
      (Nat.coprime_self_sub_right (by omega : 1 ≤ m)).mpr (Nat.coprime_one_right m)
    obtain ⟨c, hca⟩ := hcop_nat.mul_dvd_of_dvd_of_dvd hdvd₁ hdvd₂
    rcases c with _ | _ | c
    · rw [mul_zero] at hca
      exact Or.inl (isUnit_of_dvd_depressedDiscr_of_weight_zero hm (hca ▸ hF) ⟨G, hFG⟩)
    · have hb : b = 0 := by simp at hca; omega
      exact Or.inr (isUnit_of_dvd_depressedDiscr_of_weight_zero hm (hb ▸ hG)
        ⟨F, by rw [hFG, mul_comm]⟩)
    · exfalso
      have hlt : m * (m - 1) < m * (m - 1) * (c + 1 + 1) :=
        lt_mul_of_one_lt_right hm_pos (by omega)
      omega

private theorem pow_mul_coeff_mem_range_of_mul_map_eq {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {Δ P : MvPolynomial σ R} {H : MvPolynomial σ S}
    (hmul : H * MvPolynomial.map φ Δ = MvPolynomial.map φ P) {j : σ} {k : ℕ} {u : R}
    (hu : Δ.coeff (Finsupp.single j k) = u)
    (huniq : ∀ s ∈ Δ.support, k ≤ s j → s = Finsupp.single j k) :
    ∀ r : ℕ, ∀ e : σ →₀ ℕ, H.degreeOf j - e j < r → φ u ^ r * H.coeff e ∈ φ.range := by
  classical
  intro r
  induction r with
  | zero => intro e he; omega
  | succ r ih =>
    intro e he
    by_cases he0 : H.coeff e = 0
    · simp [he0]
    have hc := congrArg (fun p ↦ p.coeff (e + Finsupp.single j k)) hmul
    rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_map] at hc
    have hx₀ : (e, Finsupp.single j k) ∈ Finset.antidiagonal (e + Finsupp.single j k) :=
      Finset.mem_antidiagonal.mpr rfl
    rw [← Finset.add_sum_erase _ _ hx₀, MvPolynomial.coeff_map, hu] at hc
    have hsum : φ u ^ r *
        ∑ x ∈ (Finset.antidiagonal (e + Finsupp.single j k)).erase (e, Finsupp.single j k),
          H.coeff x.1 * (MvPolynomial.map φ Δ).coeff x.2 ∈ φ.range := by
      rw [Finset.mul_sum]
      refine φ.range.sum_mem fun x hx ↦ ?_
      rw [MvPolynomial.coeff_map, ← mul_assoc]
      by_cases hx1 : H.coeff x.1 = 0
      · simp [hx1]
      by_cases hx2 : Δ.coeff x.2 = 0
      · simp [hx2]
      obtain ⟨hne, hadd⟩ := Finset.mem_erase.mp hx
      rw [Finset.mem_antidiagonal] at hadd
      have hlt : x.2 j < k := by
        by_contra! hge
        have hs := huniq x.2 (MvPolynomial.mem_support_iff.mpr hx2) hge
        exact hne (Prod.ext (add_right_cancel (hs ▸ hadd)) hs)
      have hxj : e j < x.1 j := by
        have := DFunLike.congr_fun hadd j
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        omega
      have hdeg := MvPolynomial.monomial_le_degreeOf j (MvPolynomial.mem_support_iff.mpr hx1)
      exact φ.range.mul_mem (ih x.1 (by omega)) ⟨Δ.coeff x.2, rfl⟩
    have hrhs : φ u ^ r * φ (P.coeff (e + Finsupp.single j k)) ∈ φ.range :=
      φ.range.mul_mem (φ.range.pow_mem ⟨u, rfl⟩ r) ⟨_, rfl⟩
    have heq : φ u ^ (r + 1) * H.coeff e =
        φ u ^ r * φ (P.coeff (e + Finsupp.single j k)) -
          φ u ^ r *
            ∑ x ∈ (Finset.antidiagonal (e + Finsupp.single j k)).erase (e, Finsupp.single j k),
              H.coeff x.1 * (MvPolynomial.map φ Δ).coeff x.2 := by
      rw [← hc]; ring
    rw [heq]
    exact φ.range.sub_mem hrhs hsum

private theorem dvd_of_mul_map_eq_of_isCoprime {σ R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {Δ P : MvPolynomial σ R} {H : MvPolynomial σ S}
    (hmul : H * MvPolynomial.map φ Δ = MvPolynomial.map φ P) {u₁ u₂ : R} {N₁ N₂ : ℕ}
    (h₁ : ∀ e, φ u₁ ^ N₁ * H.coeff e ∈ φ.range)
    (h₂ : ∀ e, φ u₂ ^ N₂ * H.coeff e ∈ φ.range)
    (hcop : IsCoprime u₁ u₂) : Δ ∣ P := by
  classical
  obtain ⟨a, b, hab⟩ := hcop.pow (m := N₁) (n := N₂)
  have hmem (e : σ →₀ ℕ) : H.coeff e ∈ φ.range := by
    have h1 : φ (a * u₁ ^ N₁ + b * u₂ ^ N₂) * H.coeff e =
        φ a * (φ u₁ ^ N₁ * H.coeff e) + φ b * (φ u₂ ^ N₂ * H.coeff e) := by
      simp only [map_add, map_mul, map_pow]; ring
    rw [hab, map_one, one_mul] at h1
    rw [h1]
    exact φ.range.add_mem (φ.range.mul_mem ⟨a, rfl⟩ (h₁ e)) (φ.range.mul_mem ⟨b, rfl⟩ (h₂ e))
  let H₀ : MvPolynomial σ R :=
    ∑ e ∈ H.support, MvPolynomial.monomial e (Classical.choose (hmem e))
  have hH₀ : MvPolynomial.map φ H₀ = H := by
    conv_rhs => rw [H.as_sum]
    simp only [H₀, map_sum, MvPolynomial.map_monomial]
    exact Finset.sum_congr rfl fun e _ ↦ by rw [Classical.choose_spec (hmem e)]
  have hprod : MvPolynomial.map φ (Δ * H₀) = MvPolynomial.map φ P := by
    rw [map_mul, hH₀, mul_comm, hmul]
  exact ⟨H₀, (MvPolynomial.map_injective φ hφ hprod).symm⟩

/-- For `m ≥ 3` over a commutative ring `R` without zero divisors in which `(m : R) ≠ 0` and
`((m - 1 : ℕ) : R) ≠ 0`, `depressedDiscr R m` is prime in `MvPolynomial (Fin (m - 1)) R`. -/
theorem prime_depressedDiscr_of_three_le {R : Type*} [CommRing R] [NoZeroDivisors R]
    {m : ℕ} (hm : 3 ≤ m) (hm0 : (m : R) ≠ 0) (hm1 : ((m - 1 : ℕ) : R) ≠ 0) :
    Prime (depressedDiscr R m) := by
  have : Nontrivial R := ⟨m, 0, hm0⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let K := FractionRing R
  let φ := algebraMap R K
  have hφ : Function.Injective φ := IsFractionRing.injective R K
  have hm0K : (m : K) ≠ 0 := by simpa using (map_ne_zero_iff φ hφ).mpr hm0
  have hm1K : ((m - 1 : ℕ) : K) ≠ 0 := by simpa using (map_ne_zero_iff φ hφ).mpr hm1
  have hprimeK : Prime (depressedDiscr K m) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_depressedDiscr_of_three_le hm hm0K hm1K)
  have hirrR := irreducible_depressedDiscr_of_three_le hm hm0 hm1
  let w : Fin (m - 1) → ℕ := fun i ↦ i.val + 2
  have hw : ∀ i, 0 < w i := fun i ↦ by dsimp [w]; omega
  have hw₁ : (m - 1) * w ⟨m - 2, by omega⟩ = m * (m - 1) := by
    dsimp [w]
    rw [show m - 2 + 2 = m by omega, mul_comm]
  have hw₂ : m * w ⟨m - 3, by omega⟩ = m * (m - 1) := by
    dsimp [w]
    rw [show m - 3 + 2 = m - 1 by omega]
  have hhom₁ : (depressedDiscr R m).IsWeightedHomogeneous w ((m - 1) * w ⟨m - 2, by omega⟩) :=
    hw₁.symm ▸ isWeightedHomogeneous_depressedDiscr R m
  have hhom₂ : (depressedDiscr R m).IsWeightedHomogeneous w (m * w ⟨m - 3, by omega⟩) :=
    hw₂.symm ▸ isWeightedHomogeneous_depressedDiscr R m
  have hdesc {P : MvPolynomial (Fin (m - 1)) R}
      (hdvd : depressedDiscr K m ∣ MvPolynomial.map φ P) : depressedDiscr R m ∣ P := by
    obtain ⟨H, hH⟩ := hdvd
    rw [← map_depressedDiscr φ m, mul_comm] at hH
    have h₁ := pow_mul_coeff_mem_range_of_mul_map_eq φ hH.symm
      (coeff_single_sub_two_depressedDiscr R (by omega)) fun s hs hle ↦
        eq_single_of_le_of_isWeightedHomogeneous hw hhom₁ hs hle
    have h₂ := pow_mul_coeff_mem_range_of_mul_map_eq φ hH.symm
      (coeff_single_sub_three_depressedDiscr R hm) fun s hs hle ↦
        eq_single_of_le_of_isWeightedHomogeneous hw hhom₂ hs hle
    have hcop₀ : IsCoprime (m : R) ((m - 1 : ℕ) : R) :=
      ⟨1, -1, by rw [Nat.cast_sub (by omega)]; ring⟩
    have hcop := (isCoprime_mul_units_left
      (isUnit_one.neg.pow (m * (m - 1) / 2))
      (isUnit_one.neg.pow ((m - 1) * (m - 2) / 2))
      ((m : R) ^ m) (((m - 1 : ℕ) : R) ^ (m - 1))).mpr (hcop₀.pow (m := m) (n := m - 1))
    exact dvd_of_mul_map_eq_of_isCoprime hφ hH.symm
      (fun e ↦ h₁ (H.degreeOf ⟨m - 2, by omega⟩ + 1) e (by omega))
      (fun e ↦ h₂ (H.degreeOf ⟨m - 3, by omega⟩ + 1) e (by omega)) hcop
  refine ⟨hirrR.ne_zero, hirrR.not_isUnit, fun A B hAB ↦ ?_⟩
  have hAB' : depressedDiscr K m ∣ MvPolynomial.map φ A * MvPolynomial.map φ B := by
    rw [← map_depressedDiscr φ m, ← map_mul]
    exact map_dvd (MvPolynomial.map φ) hAB
  exact (hprimeK.dvd_or_dvd hAB').imp hdesc hdesc

/-- Over a field `K`, `depressedDiscr K m` is prime whenever `(m : K) ≠ 0` and
`((m - 1 : ℕ) : K) ≠ 0`. -/
theorem prime_depressedDiscr_of_ne_zero {K : Type*} [Field K] {m : ℕ}
    (hm0 : (m : K) ≠ 0) (hm1 : ((m - 1 : ℕ) : K) ≠ 0) :
    Prime (depressedDiscr K m) := by
  rcases m with _ | _ | _ | m
  · exact absurd (by simp : ((0 : ℕ) : K) = 0) hm0
  · exact absurd (by simp : ((1 - 1 : ℕ) : K) = 0) hm1
  · exact prime_depressedDiscr_two_iff.mpr hm0.isUnit
  · exact prime_depressedDiscr_of_three_le (by omega) hm0 hm1

/-- Over a field `K` of characteristic zero, `depressedDiscr K m` is prime for every `m ≥ 2`. -/
theorem prime_depressedDiscr (K : Type*) [Field K] [CharZero K] {m : ℕ} (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega))

end Primality

end TauCeti
