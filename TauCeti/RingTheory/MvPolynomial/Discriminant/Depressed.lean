/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Discriminant.Generic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.MvPolynomial.Prime
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# The generic depressed discriminant and Weierstrass specialization

Setting the subleading coefficient to zero gives the generic depressed monic polynomial
`TauCeti.genericDepressed R m = X ^ m + ∑ i : Fin (m - 1), C (X i) * X ^ (m - (i + 2))`,
with weights `depressedWeight m i = i + 2`. Specializing `Polynomial.freeMonic` shows that its
discriminant `TauCeti.depressedDiscr R m` has weight `m * (m - 1)` over any commutative ring.
Whenever `m ≥ 2` is invertible in `R`, the Tschirnhaus shift `X ↦ X + a₁ / m` induces an
`R`-algebra automorphism `TauCeti.tschirnhausEquiv` of `MvPolynomial (Fin m) R` carrying
`(Polynomial.freeMonic R m).discr` to the variable-embedded `depressedDiscr R m`. Consequently,
`depressedDiscr R m` is prime whenever `m ≥ 2`, `2 ≠ 0`, and `IsUnit (m : R)` over an integral
domain (in particular over a field of characteristic zero), so localizing
`MvPolynomial (Fin (m - 1)) R` away from `depressedDiscr R m` has homogeneous unit degrees
`m * (m - 1) ℤ` and shift class group `ZMod (m * (m - 1))`.

In degrees `2` and `3` the depressed discriminant is `-4 * X 0` and `-4 * X 0 ^ 3 - 27 * X 1 ^ 2`.
In particular, when `2 ≠ 0` and `3 ≠ 0` in an integral domain `R` (such as `ℤ`),
`4 * X 0 ^ 3 + 27 * X 1 ^ 2` is prime of weight `12` for the weights `![4, 6]`, giving shift class
group `ZMod 12`.

## Main definitions

* `TauCeti.genericDepressed`: the generic depressed monic polynomial of degree `m`.
* `TauCeti.depressedWeight`: the weight `i ↦ i + 2` on the coefficients of `genericDepressed`.
* `TauCeti.depressedDiscr`: the discriminant of `genericDepressed`.
* `TauCeti.depressedEmb`: the variable embedding `j ↦ m - 2 - j` from depressed to monic
  coefficients.
* `TauCeti.tschirnhausEquiv`: the Tschirnhaus automorphism eliminating the subleading coefficient
  when `IsUnit (m : R)`.
* `TauCeti.shiftClassGroupAwayDepressedDiscrEquiv`: the shift class group `ZMod (m * (m - 1))`
  after inverting `depressedDiscr R m`.
* `TauCeti.shiftClassGroupAwayWeierstrassEquiv`: the shift class group `ZMod 12` after inverting
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` with weights `![4, 6]`.

## Main results

* `TauCeti.depressedDiscr_mem`: `depressedDiscr R m` has weight `m * (m - 1)` for `depressedWeight`.
* `TauCeti.depressedDiscr_prime` and `TauCeti.depressedDiscr_prime_of_charZero`: primality of
  `depressedDiscr R m` for `m ≥ 2` when `(2 : R) ≠ 0` and `IsUnit (m : R)` (in particular over a
  field of characteristic zero).
* `TauCeti.homogeneousUnitDegrees_away_depressedDiscr`: the homogeneous unit degrees after
  inverting `depressedDiscr R m` are `AddSubgroup.zmultiples (m * (m - 1))`.
* `TauCeti.depressedDiscr_two` and `TauCeti.depressedDiscr_three`: explicit formulas in degrees
  `2` and `3`.
* `TauCeti.prime_four_mul_pow_three_add_twentyseven_mul_sq`: primality of
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` over any integral domain with `2 ≠ 0` and `3 ≠ 0`.
-/

public section

namespace TauCeti

open Finset MvPolynomial TauCeti.GradedAlgebra

attribute [local instance] MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

section Depressed

/-- The generic depressed monic polynomial of degree `m`,
`X ^ m + a₂ * X ^ (m - 2) + ⋯ + aₘ`, where `X i` (`i : Fin (m - 1)`) represents `a_{i + 2}`. -/
noncomputable def genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    Polynomial (MvPolynomial (Fin (m - 1)) R) :=
  Polynomial.X ^ m +
    ∑ i : Fin (m - 1), Polynomial.C (X i) * Polynomial.X ^ (m - (i.val + 2))

/-- Explicit expansion of `genericDepressed R m` as a sum of monomials. -/
theorem genericDepressed_eq (R : Type*) [CommSemiring R] (m : ℕ) :
    genericDepressed R m =
      Polynomial.X ^ m +
        ∑ i : Fin (m - 1), Polynomial.C (X i) * Polynomial.X ^ (m - (i.val + 2)) :=
  (rfl)

/-- The weight of the variable `a_{i + 2}` (`X i`) in `genericDepressed R m` is `i + 2`. -/
def depressedWeight (m : ℕ) : Fin (m - 1) → ℤ := fun i ↦ (i.val : ℤ) + 2

/-- The weight assigned by `depressedWeight m` to `i : Fin (m - 1)` is `i + 2`. -/
@[simp]
theorem depressedWeight_apply (m : ℕ) (i : Fin (m - 1)) : depressedWeight m i = (i.val : ℤ) + 2 :=
  (rfl)

/-- The discriminant of the generic depressed monic polynomial of degree `m`. -/
noncomputable def depressedDiscr (R : Type*) [CommRing R] (m : ℕ) : MvPolynomial (Fin (m - 1)) R :=
  Polynomial.discr (genericDepressed R m)

/-- Unfolding lemma expressing `depressedDiscr R m` as the discriminant of
`genericDepressed R m`. -/
theorem depressedDiscr_eq (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m = Polynomial.discr (genericDepressed R m) :=
  (rfl)

/-- The `k`-th coefficient of `genericDepressed R m` is `X (m - 2 - k)` for `k + 2 ≤ m`, `1` for
`k = m`, and `0` otherwise. -/
theorem coeff_genericDepressed (R : Type*) [CommSemiring R] (m k : ℕ) :
    (genericDepressed R m).coeff k =
      if h : k + 2 ≤ m then X ⟨m - 2 - k, by omega⟩ else if k = m then 1 else 0 := by
  simp only [genericDepressed, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases hlt : k + 2 ≤ m
  · have hkm : k ≠ m := by omega
    rw [dite_eq_left hlt, ite_eq_right hkm, zero_add,
      Finset.sum_eq_single (⟨m - 2 - k, by omega⟩ : Fin (m - 1))]
    · rw [ite_eq_left (by dsimp; omega)]
    · intro i _ hne
      refine ite_eq_right fun heq' ↦ hne ?_
      ext
      dsimp
      omega
    · intro hmem
      exact (hmem (mem_univ _)).elim
  · rw [dite_eq_right hlt, Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by omega), add_zero]

/-- Over a nontrivial semiring, `genericDepressed R m` has degree `m`. -/
@[simp]
theorem degree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).degree = m :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun k hk ↦ by
      have hgt : m < k := WithBot.coe_lt_coe.mp hk
      have hlt : ¬ k + 2 ≤ m := by omega
      simp [coeff_genericDepressed, hlt, hgt.ne'])
    (by simp [coeff_genericDepressed])

/-- Over a nontrivial semiring, `genericDepressed R m` has `natDegree` equal to `m`. -/
@[simp]
theorem natDegree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).natDegree = m :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_genericDepressed R m)

/-- The generic depressed polynomial `genericDepressed R m` is monic over any commutative
semiring. -/
theorem monic_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).Monic := by
  nontriviality R
  rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_genericDepressed, coeff_genericDepressed]
  simp

/-- Forming `genericDepressed` commutes with base change along any ring homomorphism. -/
@[simp]
theorem map_map_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (m : ℕ) : (genericDepressed R m).map (MvPolynomial.map f) = genericDepressed S m := by
  simp [genericDepressed, Polynomial.map_sum]

/-- Forming `depressedDiscr` commutes with base change along any ring homomorphism. -/
@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    MvPolynomial.map f (depressedDiscr R m) = depressedDiscr S m := by
  rw [depressedDiscr, depressedDiscr, ← (monic_genericDepressed R m).discr_map,
    map_map_genericDepressed]

/-- **Weighted homogeneity of the generic depressed discriminant.** Over any commutative ring,
`depressedDiscr R m` has weight `m * (m - 1)` for `depressedWeight m`. -/
theorem depressedDiscr_mem (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m ∈
      weightedHomogeneousSubmodule R (depressedWeight m) ((m : ℤ) * (m - 1)) := by
  let g : Fin m → MvPolynomial (Fin (m - 1)) R :=
    fun i ↦ if h : (i : ℕ) + 2 ≤ m then X ⟨m - 2 - (i : ℕ), by omega⟩ else 0
  have hmap : (Polynomial.freeMonic R m).map (aeval g).toRingHom = genericDepressed R m := by
    refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
    rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, coeff_genericDepressed]
    by_cases hlt : k + 2 ≤ m
    · have hkm : k < m := by omega
      simp [g, hlt, hkm]
    · by_cases hlt' : k < m
      · have hne : k ≠ m := hlt'.ne
        simp [g, hlt, hlt', hne]
      · by_cases heq : k = m
        · subst heq
          simp
        · simp [hlt, hlt', heq]
  have hdiscr : aeval g (Polynomial.freeMonic R m).discr = depressedDiscr R m := by
    have h := (Polynomial.monic_freeMonic R m).discr_map (aeval g).toRingHom
    rw [hmap] at h
    exact h.symm
  have hg : ∀ i : Fin m, (g i).IsWeightedHomogeneous (depressedWeight m) (freeMonicWeight m i) := by
    intro i
    dsimp only [g]
    split_ifs with h
    · convert isWeightedHomogeneous_X R (depressedWeight m) ⟨m - 2 - (i : ℕ), by omega⟩
      simp only [depressedWeight, freeMonicWeight_apply]
      omega
    · exact isWeightedHomogeneous_zero R (depressedWeight m) _
  rw [mem_weightedHomogeneousSubmodule, ← hdiscr]
  exact ((mem_weightedHomogeneousSubmodule ..).mp
    (discr_freeMonic_mem_weightedHomogeneousSubmodule R m)).aeval hg

/-- The embedding sending variable `j` of `genericDepressed R m` to the coefficient index
`m - 2 - j` of `Polynomial.freeMonic R m`. -/
def depressedEmb (m : ℕ) (hm : 2 ≤ m) : Fin (m - 1) → Fin m :=
  fun j ↦ ⟨m - 2 - j.val, by omega⟩

/-- The image of `j : Fin (m - 1)` under `depressedEmb m hm` is `⟨m - 2 - j, _⟩`. -/
@[simp]
theorem depressedEmb_apply (m : ℕ) (hm : 2 ≤ m) (j : Fin (m - 1)) :
    depressedEmb m hm j = ⟨m - 2 - j.val, by omega⟩ :=
  (rfl)

/-- The variable embedding `depressedEmb m hm` is injective. -/
theorem depressedEmb_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (depressedEmb m hm) := fun j₁ j₂ h ↦ by
  ext
  have := congrArg Fin.val h
  dsimp [depressedEmb] at this
  omega

private theorem coeff_map_rename_genericDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (k : ℕ) :
    ((genericDepressed R m).map (rename (depressedEmb m hm)).toRingHom).coeff k =
      if h : k + 2 ≤ m then X ⟨k, by omega⟩ else if k = m then 1 else 0 := by
  rw [Polynomial.coeff_map, coeff_genericDepressed]
  split_ifs with h1 h2
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, depressedEmb]
    congr 1
    ext
    dsimp
    omega
  · simp
  · simp

/-- The depressed monic polynomial of degree `m` viewed inside `(MvPolynomial (Fin m) R)[X]`
via `depressedEmb`. -/
private noncomputable def embeddedDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m) :
    Polynomial (MvPolynomial (Fin m) R) :=
  (genericDepressed R m).map (rename (depressedEmb m hm)).toRingHom

/-- The Tschirnhaus shift `c * X (m - 1)` where `m * c = 1`. -/
private noncomputable def tschirnhausShift (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R :=
  C ((hmR.unit⁻¹ : Rˣ) : R) * X ⟨m - 1, by omega⟩

/-- The algebra endomorphism of `MvPolynomial (Fin m) R` taking the depressed coefficients to the
shifted coefficients of `Polynomial.freeMonic R m` while fixing `X (m - 1)`. -/
private noncomputable def tschirnhausToDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun i : Fin m ↦
    if (i : ℕ) + 2 ≤ m then
      ((Polynomial.freeMonic R m).comp
        (Polynomial.X - Polynomial.C (tschirnhausShift R hm hmR))).coeff i
    else X ⟨m - 1, by omega⟩

/-- The algebra endomorphism of `MvPolynomial (Fin m) R` taking the coefficients of
`Polynomial.freeMonic R m` to those of the shifted depressed polynomial while fixing `X (m - 1)`. -/
private noncomputable def tschirnhausFromDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun i : Fin m ↦
    if (i : ℕ) + 2 ≤ m then
      ((embeddedDepressed R hm).comp
        (Polynomial.X + Polynomial.C (tschirnhausShift R hm hmR))).coeff i
    else X ⟨m - 1, by omega⟩

private theorem natCast_mul_C_inv_eq_one {R : Type*} [CommRing R] {m : ℕ} (hmR : IsUnit (m : R)) :
    (m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R) = 1 := by
  rw [← map_natCast C, ← map_mul, hmR.mul_val_inv, map_one]

private theorem map_embeddedDepressed_tschirnhausToDepressed (R : Type*) [CommRing R] {m : ℕ}
    (hm : 2 ≤ m) (hmR : IsUnit (m : R)) :
    (embeddedDepressed R hm).map (tschirnhausToDepressed R hm hmR).toRingHom =
      (Polynomial.freeMonic R m).comp
        (Polynomial.X - Polynomial.C (tschirnhausShift R hm hmR)) := by
  nontriviality R
  let s := tschirnhausShift R hm hmR
  let F := Polynomial.freeMonic R m
  have hF_deg : F.natDegree = m := Polynomial.natDegree_freeMonic R m
  have hF_mon : F.Monic := Polynomial.monic_freeMonic R m
  have hshift : F.comp (Polynomial.X - Polynomial.C s) = Polynomial.taylor (-s) F := by
    rw [Polynomial.taylor_apply, map_neg, sub_eq_add_neg]
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [Polynomial.coeff_map, embeddedDepressed, coeff_map_rename_genericDepressed R hm]
  by_cases h1 : k + 2 ≤ m
  · simp [tschirnhausToDepressed, h1]
  · rw [dite_eq_right h1]
    by_cases h2 : k = m
    · have hlead : (Polynomial.taylor (-s) F).coeff m = 1 := by
        have h := Polynomial.leadingCoeff_taylor (-s) F
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_taylor, hF_deg, hF_mon.leadingCoeff] at h
        exact h
      rw [h2, ite_eq_left rfl, map_one, hshift, hlead]
    · rw [ite_eq_right h2, map_zero, hshift]
      by_cases hkm1 : k = m - 1
      · subst hkm1
        have hnext := Polynomial.nextCoeff_taylor F (-s)
        have hpos1 : 0 < (Polynomial.taylor (-s) F).natDegree := by
          rw [Polynomial.natDegree_taylor, hF_deg]
          omega
        rw [Polynomial.nextCoeff_of_natDegree_pos hpos1,
          Polynomial.nextCoeff_of_natDegree_pos (by rw [hF_deg]; omega),
          Polynomial.natDegree_taylor, hF_deg, hF_mon.leadingCoeff, mul_one,
          Polynomial.coeff_freeMonic, dite_eq_left (by omega)] at hnext
        rw [hnext]
        calc
          (0 : MvPolynomial (Fin m) R)
            = X ⟨m - 1, by omega⟩ - ((m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R)) *
                X ⟨m - 1, by omega⟩ := by rw [natCast_mul_C_inv_eq_one hmR, one_mul, sub_self]
          _ = X ⟨m - 1, by omega⟩ + (m : MvPolynomial (Fin m) R) * -s := by
                dsimp [s, tschirnhausShift]
                ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        rw [Polynomial.natDegree_taylor, hF_deg]
        omega

private theorem map_freeMonic_tschirnhausFromDepressed (R : Type*) [CommRing R] {m : ℕ}
    (hm : 2 ≤ m) (hmR : IsUnit (m : R)) :
    (Polynomial.freeMonic R m).map (tschirnhausFromDepressed R hm hmR).toRingHom =
      (embeddedDepressed R hm).comp (Polynomial.X + Polynomial.C (tschirnhausShift R hm hmR)) := by
  nontriviality R
  let s := tschirnhausShift R hm hmR
  let G := embeddedDepressed R hm
  have hG_mon : G.Monic := (monic_genericDepressed R m).map _
  have hG_deg : G.natDegree = m := by
    dsimp only [G, embeddedDepressed]
    rw [(monic_genericDepressed R m).natDegree_map]
    exact natDegree_genericDepressed R m
  have hshift : G.comp (Polynomial.X + Polynomial.C s) = Polynomial.taylor s G :=
    (Polynomial.taylor_apply s G).symm
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic]
  by_cases h1 : k < m
  · rw [dite_eq_left h1]
    by_cases hlt : k + 2 ≤ m
    · simp [tschirnhausFromDepressed, hlt]
    · have hk : k = m - 1 := by omega
      subst hk
      have hnext := Polynomial.nextCoeff_taylor G s
      have hpos1 : 0 < (Polynomial.taylor s G).natDegree := by
        rw [Polynomial.natDegree_taylor, hG_deg]
        omega
      rw [Polynomial.nextCoeff_of_natDegree_pos hpos1,
        Polynomial.nextCoeff_of_natDegree_pos (by rw [hG_deg]; omega),
        Polynomial.natDegree_taylor, hG_deg, hG_mon.leadingCoeff, mul_one] at hnext
      have hGcoeff : G.coeff (m - 1) = 0 := by
        dsimp only [G, embeddedDepressed]
        rw [coeff_map_rename_genericDepressed R hm, dite_eq_right (by omega),
          ite_eq_right (by omega)]
      rw [hGcoeff, zero_add] at hnext
      have hnot : ¬ m - 1 + 2 ≤ m := by omega
      have hX : (tschirnhausFromDepressed R hm hmR).toRingHom (X ⟨m - 1, h1⟩) =
          X ⟨m - 1, h1⟩ := by
        simp [tschirnhausFromDepressed, hnot]
      rw [hshift, hnext, hX]
      calc
        (X ⟨m - 1, h1⟩ : MvPolynomial (Fin m) R)
          = ((m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R)) *
              X ⟨m - 1, h1⟩ := by rw [natCast_mul_C_inv_eq_one hmR, one_mul]
        _ = (m : MvPolynomial (Fin m) R) * s := by
              dsimp [s, tschirnhausShift]
              ring
  · rw [dite_eq_right h1]
    by_cases h2 : k = m
    · have hlead : (Polynomial.taylor s G).coeff m = 1 := by
        have h := Polynomial.leadingCoeff_taylor s G
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_taylor, hG_deg, hG_mon.leadingCoeff] at h
        exact h
      rw [h2, ite_eq_left rfl, map_one, hshift, hlead]
    · rw [ite_eq_right h2, map_zero, hshift, Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [Polynomial.natDegree_taylor, hG_deg]
      omega

/-- **The Tschirnhaus automorphism.** Whenever `m ≥ 2` is invertible in `R`, shifting the root
coordinate by `a₁ / m` defines an `R`-algebra automorphism of `MvPolynomial (Fin m) R` taking the
generic monic polynomial `Polynomial.freeMonic R m` to the shifted depressed polynomial
`G(X + a₁ / m)` and keeping the subleading coefficient variable `X ⟨m - 1, _⟩` fixed. -/
noncomputable def tschirnhausEquiv (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R := by
  let φ := tschirnhausToDepressed R hm hmR
  let ψ := tschirnhausFromDepressed R hm hmR
  let s := tschirnhausShift R hm hmR
  have hnot : ¬ m - 1 + 2 ≤ m := by omega
  have hφs : φ s = s := by simp [φ, s, tschirnhausToDepressed, tschirnhausShift, hnot]
  have hψs : ψ s = s := by simp [ψ, s, tschirnhausFromDepressed, tschirnhausShift, hnot]
  have hφψ : φ.comp ψ = AlgHom.id R _ := by
    have hpoly :
        (Polynomial.freeMonic R m).map (φ.comp ψ).toRingHom = Polynomial.freeMonic R m := by
      have hring : (φ.comp ψ).toRingHom = φ.toRingHom.comp ψ.toRingHom := rfl
      rw [hring, ← Polynomial.map_map, map_freeMonic_tschirnhausFromDepressed R hm hmR,
        Polynomial.map_comp, map_embeddedDepressed_tschirnhausToDepressed R hm hmR,
        Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
      have hφs' : φ.toRingHom s = s := hφs
      rw [hφs', Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        add_sub_cancel_right, Polynomial.comp_X]
    refine algHom_ext fun i ↦ ?_
    have hi := congrArg (fun p ↦ p.coeff i) hpoly
    rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, dite_eq_left i.isLt] at hi
    exact hi
  have hψφ : ψ.comp φ = AlgHom.id R _ := by
    have hpoly : (embeddedDepressed R hm).map (ψ.comp φ).toRingHom = embeddedDepressed R hm := by
      have hring : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
      rw [hring, ← Polynomial.map_map, map_embeddedDepressed_tschirnhausToDepressed R hm hmR,
        Polynomial.map_comp, map_freeMonic_tschirnhausFromDepressed R hm hmR,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      have hψs' : ψ.toRingHom s = s := hψs
      rw [hψs', Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
        sub_add_cancel, Polynomial.comp_X]
    refine algHom_ext fun i ↦ ?_
    by_cases hlt : (i : ℕ) + 2 ≤ m
    · have hi := congrArg (fun p ↦ p.coeff i) hpoly
      rw [Polynomial.coeff_map, embeddedDepressed, coeff_map_rename_genericDepressed R hm,
        dite_eq_left hlt] at hi
      exact hi
    · have hi : i = ⟨m - 1, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hi]
      simp [φ, ψ, tschirnhausToDepressed, tschirnhausFromDepressed, hnot]
  exact AlgEquiv.ofAlgHom ψ φ hψφ hφψ

/-- The Tschirnhaus automorphism fixes the subleading coefficient variable `X ⟨m - 1, _⟩`. -/
@[simp]
theorem tschirnhausEquiv_X_subleading (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) :
    tschirnhausEquiv R hm hmR (X ⟨m - 1, by omega⟩) = X ⟨m - 1, by omega⟩ := by
  have hnot : ¬ m - 1 + 2 ≤ m := by omega
  simp [tschirnhausEquiv, tschirnhausFromDepressed, hnot]

/-- Applying `tschirnhausEquiv` coefficientwise carries `Polynomial.freeMonic R m` to the shifted
embedded depressed polynomial. -/
theorem map_freeMonic_tschirnhausEquiv (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) :
    (Polynomial.freeMonic R m).map (tschirnhausEquiv R hm hmR).toAlgHom.toRingHom =
      ((genericDepressed R m).map (rename (depressedEmb m hm)).toRingHom).comp
        (Polynomial.X + Polynomial.C (C ((hmR.unit⁻¹ : Rˣ) : R) * X ⟨m - 1, by omega⟩)) :=
  map_freeMonic_tschirnhausFromDepressed R hm hmR

/-- The Tschirnhaus automorphism maps `(Polynomial.freeMonic R m).discr` to the embedded
`depressedDiscr R m`. -/
theorem tschirnhausEquiv_discr_freeMonic (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) :
    tschirnhausEquiv R hm hmR (Polynomial.freeMonic R m).discr =
      rename (depressedEmb m hm) (depressedDiscr R m) := by
  have h1 := (Polynomial.monic_freeMonic R m).discr_map
    (tschirnhausEquiv R hm hmR).toAlgHom.toRingHom
  have h2 := (monic_genericDepressed R m).discr_map (rename (depressedEmb m hm)).toRingHom
  rw [map_freeMonic_tschirnhausEquiv, Polynomial.discr_comp_X_add_C] at h1
  exact h1.symm.trans h2

/-- **Primality of the generic depressed discriminant.** Over any integral domain in which
`2 ≠ 0` and `m` is invertible, `depressedDiscr R m` is prime for every `m ≥ 2`. -/
theorem depressedDiscr_prime {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R)) (hm : 2 ≤ m) :
    Prime (depressedDiscr R m) := by
  rw [← prime_rename_iff_of_injective (depressedEmb_injective m hm),
    ← tschirnhausEquiv_discr_freeMonic R hm hmR]
  exact (MulEquiv.prime_iff (tschirnhausEquiv R hm hmR).toMulEquiv).mpr
    (prime_discr_freeMonic h2 hm)

/-- Over a field of characteristic zero, the generic depressed discriminant is prime for every
`m ≥ 2`. -/
theorem depressedDiscr_prime_of_charZero (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  depressedDiscr_prime (two_ne_zero) (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hm

/-! ### Graded localization consequences and low-degree formulas -/

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields homogeneous unit degrees `m * (m - 1) ℤ`. -/
theorem homogeneousUnitDegrees_away_depressedDiscr {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R)) (hm : 2 ≤ m) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      = AddSubgroup.zmultiples ((m : ℤ) * (m - 1)) :=
  homogeneousUnitDegrees_away_prime (depressedWeight m) (depressedDiscr_mem R m)
    (depressedDiscr_prime h2 hmR hm)

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields shift class group `ZMod (m * (m - 1))`. -/
noncomputable def shiftClassGroupAwayDepressedDiscrEquiv {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R)) (hm : 2 ≤ m) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      ≃+ ZMod (m * (m - 1)) :=
  (shiftClassGroupAwayPrimeEquiv (depressedWeight m) (depressedDiscr_mem R m)
    (depressedDiscr_prime h2 hmR hm)).trans (ZMod.ringEquivCongr (by
      have h : ((m : ℤ) * (m - 1)) = ((m * (m - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [h, Int.natAbs_natCast])).toAddEquiv

/-- The identification of the shift class group after inverting `depressedDiscr R m` with
`ZMod (m * (m - 1))` sends the class of `d` to `d mod m * (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayDepressedDiscrEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R)) (hm : 2 ≤ m) (d : ℤ) :
    shiftClassGroupAwayDepressedDiscrEquiv h2 hmR hm d = d := by
  simp [shiftClassGroupAwayDepressedDiscrEquiv]

/-- In degree `2`, `depressedDiscr R 2 = -4 * X 0`. -/
theorem depressedDiscr_two (R : Type*) [CommRing R] : depressedDiscr R 2 = -4 * X 0 := by
  nontriviality R
  rw [depressedDiscr, Polynomial.discr_of_degree_eq_two (degree_genericDepressed R 2)]
  simp only [coeff_genericDepressed]
  norm_num

/-- In degree `3`, `depressedDiscr R 3 = -4 * X 0 ^ 3 - 27 * X 1 ^ 2`. -/
theorem depressedDiscr_three (R : Type*) [CommRing R] :
    depressedDiscr R 3 = -4 * X 0 ^ 3 - 27 * X 1 ^ 2 := by
  nontriviality R
  rw [depressedDiscr, Polynomial.discr_of_degree_eq_three (degree_genericDepressed R 3)]
  simp only [coeff_genericDepressed]
  norm_num

/-- The Weierstrass cubic discriminant `4 * X 0 ^ 3 + 27 * X 1 ^ 2` has weight `12` when the
variables have weights `4` and `6`. -/
theorem mem_weightedHomogeneousSubmodule_weierstrass (R : Type*) [CommRing R] :
    (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  have h0 : (4 * X 0 ^ 3 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
    have hx : (X 0 : MvPolynomial (Fin 2) R).IsWeightedHomogeneous (![4, 6] : Fin 2 → ℤ) 4 :=
      isWeightedHomogeneous_X R _ 0
    simpa [← map_ofNat (C (σ := Fin 2) (R := R))] using (hx.pow 3).C_mul (4 : R)
  have h1 : (27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
    have hx : (X 1 : MvPolynomial (Fin 2) R).IsWeightedHomogeneous (![4, 6] : Fin 2 → ℤ) 6 :=
      isWeightedHomogeneous_X R _ 1
    simpa [← map_ofNat (C (σ := Fin 2) (R := R))] using (hx.pow 2).C_mul (27 : R)
  exact add_mem h0 h1

private theorem exists_C_mul_eq_map_of_isLocalization {σ R : Type*} [CommRing R] (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] (q : MvPolynomial σ S) :
    ∃ (b : M) (q₀ : MvPolynomial σ R),
      C (algebraMap R S (b : R)) * q = MvPolynomial.map (algebraMap R S) q₀ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples M q.support q.coeff
  choose c hc using fun m (hm : m ∈ q.support) ↦ hb m hm
  refine ⟨b, ∑ m ∈ q.support.attach, monomial m.1 (c m.1 m.2), ?_⟩
  rw [map_sum]
  have hq : q = ∑ m ∈ q.support.attach, monomial m.1 (q.coeff m.1) := by
    conv_lhs => rw [q.as_sum]
    exact (Finset.sum_attach q.support (fun m ↦ monomial m (q.coeff m))).symm
  conv_lhs => rw [hq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [map_monomial, C_mul_monomial, ← Algebra.smul_def, ← hc m.1 m.2]

private theorem pow_mul_dvd_of_C_mul_dvd_away {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] {d : R} (hd : d ≠ 0) [IsLocalization.Away d S]
    {W' f q : MvPolynomial (Fin 2) R} {c u : R} (hc : c ≠ 0)
    (hu : IsUnit (algebraMap R S u))
    {P : Polynomial (MvPolynomial (Fin 1) S)} (hP_mon : P.Monic) (hP_deg : 0 < P.natDegree)
    (hW' : finSuccEquiv S 1 (MvPolynomial.map (algebraMap R _) W') =
      Polynomial.C (C (algebraMap R S u)) * P)
    (hcf : C c * f = W' * q) :
    ∃ (k : ℕ) (q' : MvPolynomial (Fin 2) R), C (d ^ k) * f = W' * q' := by
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hd))
  have hinj_mv : Function.Injective (MvPolynomial.map (σ := Fin 2) (algebraMap R S)) :=
    MvPolynomial.map_injective _ hinj
  let F : Polynomial (MvPolynomial (Fin 1) S) :=
    finSuccEquiv S 1 (MvPolynomial.map (algebraMap R S) f)
  let Q : Polynomial (MvPolynomial (Fin 1) S) :=
    finSuccEquiv S 1 (MvPolynomial.map (algebraMap R S) q)
  have hfinC : ∀ a : S, finSuccEquiv S 1 (C a) = Polynomial.C (C a) := fun a ↦ by
    simpa [Polynomial.algebraMap_apply, algebraMap_eq] using
      (finSuccEquiv S 1).commutes a
  have hCF : Polynomial.C (C (algebraMap R S c)) * F =
      Polynomial.C (C (algebraMap R S u)) * P * Q := by
    have h1 := congrArg (fun p ↦ finSuccEquiv S 1 (MvPolynomial.map (algebraMap R S) p)) hcf
    rw [map_mul, map_mul, map_C, map_mul, map_mul, hfinC, hW'] at h1
    exact h1
  have hP_dvd_cF : P ∣ Polynomial.C (C (algebraMap R S c)) * F :=
    ⟨Polynomial.C (C (algebraMap R S u)) * Q, by rw [hCF]; ring⟩
  have hF_split : F = F %ₘ P + P * (F /ₘ P) := (Polynomial.modByMonic_add_div F P).symm
  have hP_dvd_rem : P ∣ Polynomial.C (C (algebraMap R S c)) * (F %ₘ P) := by
    have h1 : P * (Polynomial.C (C (algebraMap R S c)) * (F /ₘ P)) +
        Polynomial.C (C (algebraMap R S c)) * (F %ₘ P) =
        Polynomial.C (C (algebraMap R S c)) * F := by
      rw [← mul_assoc, mul_comm P, mul_assoc, ← mul_add, add_comm, ← hF_split]
    rw [← h1] at hP_dvd_cF
    exact (dvd_add_right (dvd_mul_right P _)).mp hP_dvd_cF
  have hrem_zero : F %ₘ P = 0 := by
    by_contra hne
    have hc_ne : Polynomial.C (C (algebraMap R S c)) ≠
        (0 : Polynomial (MvPolynomial (Fin 1) S)) := by
      intro h0
      exact hc (hinj (by simpa using C_eq_zero.mp (Polynomial.C_eq_zero.mp h0)))
    have hprod_ne : Polynomial.C (C (algebraMap R S c)) * (F %ₘ P) ≠ 0 :=
      mul_ne_zero hc_ne hne
    have hdeg_le1 : P.natDegree ≤ (Polynomial.C (C (algebraMap R S c)) * (F %ₘ P)).natDegree :=
      Polynomial.natDegree_le_of_dvd hP_dvd_rem hprod_ne
    have hdeg_le2 : (Polynomial.C (C (algebraMap R S c)) * (F %ₘ P)).natDegree ≤
        (F %ₘ P).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    have hP_ne_one : P ≠ 1 := fun h1 ↦ by
      rw [h1, Polynomial.natDegree_one] at hP_deg
      exact lt_irrefl 0 hP_deg
    have hdeg_lt : (F %ₘ P).natDegree < P.natDegree :=
      Polynomial.natDegree_modByMonic_lt F hP_mon hP_ne_one
    omega
  have hP_dvd_F : P ∣ F := by
    rw [hrem_zero, zero_add] at hF_split
    exact ⟨F /ₘ P, hF_split⟩
  obtain ⟨H₀, hH₀⟩ := hP_dvd_F
  have hF_eq : F = finSuccEquiv S 1 (MvPolynomial.map (algebraMap R S) W') *
      (Polynomial.C (C ((hu.unit⁻¹ : Sˣ) : S)) * H₀) := by
    rw [hH₀, hW']
    calc P * H₀ = Polynomial.C (C (1 : S)) * (P * H₀) := by simp
    _ = Polynomial.C (C (algebraMap R S u * ((hu.unit⁻¹ : Sˣ) : S))) * (P * H₀) := by
          rw [hu.mul_val_inv]
    _ = Polynomial.C (C (algebraMap R S u)) * P *
          (Polynomial.C (C ((hu.unit⁻¹ : Sˣ) : S)) * H₀) := by
          simp only [map_mul]
          ring
  let h₂ : MvPolynomial (Fin 2) S :=
    (finSuccEquiv S 1).symm (Polynomial.C (C ((hu.unit⁻¹ : Sˣ) : S)) * H₀)
  have hf₂ : MvPolynomial.map (algebraMap R S) f =
      MvPolynomial.map (algebraMap R S) W' * h₂ := by
    apply (finSuccEquiv S 1).injective
    simpa [F, h₂] using hF_eq
  obtain ⟨⟨b, kb, hkb⟩, q', hq'⟩ :=
    exists_C_mul_eq_map_of_isLocalization (Submonoid.powers d) S h₂
  refine ⟨kb, q', hinj_mv ?_⟩
  have hbk : b = d ^ kb := hkb.symm
  rw [map_mul, map_C, map_mul, ← hbk, hf₂, ← mul_assoc, mul_comm (C (algebraMap R S b)),
    mul_assoc, hq', ← map_mul]

private theorem weierstrass_dvd_of_C_mul_dvd {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) {c : R} (hc : c ≠ 0)
    {f q : MvPolynomial (Fin 2) R}
    (hcf : C c * f = (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) * q) :
    (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∣ f := by
  let W : MvPolynomial (Fin 2) R := 4 * X 0 ^ 3 + 27 * X 1 ^ 2
  -- First descend divisibility after inverting 2, using monicity in `X 0`.
  have hdvd₂ : ∃ (k₂ : ℕ) (q₂ : MvPolynomial (Fin 2) R), C ((2 : R) ^ k₂) * f = W * q₂ := by
    let R₂ := Localization.Away (2 : R)
    have : IsDomain R₂ := IsLocalization.Away.isDomain (S := R₂) h2
    have hu₂ : IsUnit (algebraMap R R₂ 2) := IsLocalization.Away.algebraMap_isUnit (2 : R)
    have hu₄ : IsUnit (algebraMap R R₂ 4) := by
      have h4 : algebraMap R R₂ 4 = algebraMap R R₂ 2 ^ 2 := by
        rw [← map_pow]
        norm_num
      exact h4 ▸ hu₂.pow 2
    let P₂ : Polynomial (MvPolynomial (Fin 1) R₂) :=
      Polynomial.X ^ 3 + Polynomial.C (C ((hu₄.unit⁻¹ : R₂ˣ) : R₂) * (27 * X 0 ^ 2))
    have hP₂_mon : P₂.Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
    have hP₂_deg : 0 < P₂.natDegree := by
      dsimp [P₂]
      rw [Polynomial.natDegree_X_pow_add_C]
      decide
    have hW₂ : finSuccEquiv R₂ 1 (MvPolynomial.map (algebraMap R R₂) W) =
        Polynomial.C (C (algebraMap R R₂ 4)) * P₂ := by
      have h0 : finSuccEquiv R₂ 1 (X 0) = Polynomial.X := finSuccEquiv_X_zero
      have h1 : finSuccEquiv R₂ 1 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
      calc finSuccEquiv R₂ 1 (MvPolynomial.map (algebraMap R R₂) W)
          = Polynomial.C (C (algebraMap R R₂ 4)) * Polynomial.X ^ 3 +
              Polynomial.C (27 * X 0 ^ 2) := by
            simp [W, map_add, map_mul, map_pow, map_ofNat, h0, h1]
        _ = Polynomial.C (C (algebraMap R R₂ 4)) * P₂ := by
            dsimp [P₂]
            rw [mul_add, ← Polynomial.C_mul, ← mul_assoc, ← C_mul, hu₄.mul_val_inv, map_one,
              one_mul]
    exact pow_mul_dvd_of_C_mul_dvd_away h2 hc hu₄ hP₂_mon hP₂_deg hW₂ hcf
  -- Next descend divisibility after inverting 3, using monicity in `X 1`.
  have hdvd₃ : ∃ (k₃ : ℕ) (q₃ : MvPolynomial (Fin 2) R), C ((3 : R) ^ k₃) * f = W * q₃ := by
    let σswap : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    let W' : MvPolynomial (Fin 2) R := rename σswap W
    let f' : MvPolynomial (Fin 2) R := rename σswap f
    let q' : MvPolynomial (Fin 2) R := rename σswap q
    have hcf' : C c * f' = W' * q' := by
      have h1 := congrArg (rename (R := R) σswap) hcf
      rw [map_mul, rename_C, map_mul] at h1
      exact h1
    let R₃ := Localization.Away (3 : R)
    have : IsDomain R₃ := IsLocalization.Away.isDomain (S := R₃) h3
    have hu₃ : IsUnit (algebraMap R R₃ 3) := IsLocalization.Away.algebraMap_isUnit (3 : R)
    have hu₂₇ : IsUnit (algebraMap R R₃ 27) := by
      have h27 : algebraMap R R₃ 27 = algebraMap R R₃ 3 ^ 3 := by
        rw [← map_pow]
        norm_num
      exact h27 ▸ hu₃.pow 3
    let P₃ : Polynomial (MvPolynomial (Fin 1) R₃) :=
      Polynomial.X ^ 2 + Polynomial.C (C ((hu₂₇.unit⁻¹ : R₃ˣ) : R₃) * (4 * X 0 ^ 3))
    have hP₃_mon : P₃.Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
    have hP₃_deg : 0 < P₃.natDegree := by
      dsimp [P₃]
      rw [Polynomial.natDegree_X_pow_add_C]
      decide
    have hW'₃ : finSuccEquiv R₃ 1 (MvPolynomial.map (algebraMap R R₃) W') =
        Polynomial.C (C (algebraMap R R₃ 27)) * P₃ := by
      have h0 : finSuccEquiv R₃ 1 (X 0) = Polynomial.X := finSuccEquiv_X_zero
      have h1 : finSuccEquiv R₃ 1 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
      have hW'_eq : W' = 4 * X 1 ^ 3 + 27 * X 0 ^ 2 := by
        simp [W', W, σswap, map_add, map_mul, map_pow, map_ofNat]
      calc finSuccEquiv R₃ 1 (MvPolynomial.map (algebraMap R R₃) W')
          = Polynomial.C (C (algebraMap R R₃ 27)) * Polynomial.X ^ 2 +
              Polynomial.C (4 * X 0 ^ 3) := by
            rw [hW'_eq]
            simp [map_add, map_mul, map_pow, map_ofNat, h0, h1]
            ring
        _ = Polynomial.C (C (algebraMap R R₃ 27)) * P₃ := by
            dsimp [P₃]
            rw [mul_add, ← Polynomial.C_mul, ← mul_assoc, ← C_mul, hu₂₇.mul_val_inv, map_one,
              one_mul]
    obtain ⟨k₃, q₃', hq₃'⟩ := pow_mul_dvd_of_C_mul_dvd_away h3 hc hu₂₇ hP₃_mon hP₃_deg hW'₃ hcf'
    refine ⟨k₃, rename σswap q₃', ?_⟩
    have hback := congrArg (rename (R := R) σswap) hq₃'
    have hinv : (σswap : Fin 2 → Fin 2) ∘ σswap = id := by
      funext i
      fin_cases i <;> rfl
    dsimp only [W', f'] at hback
    rw [map_mul, rename_C, map_mul, rename_rename, rename_rename, hinv, rename_id] at hback
    exact hback
  obtain ⟨k₂, q₂, hq₂⟩ := hdvd₂
  obtain ⟨k₃, q₃, hq₃⟩ := hdvd₃
  have hcop : Nat.Coprime (2 ^ k₂) (3 ^ k₃) := (by decide : Nat.Coprime 2 3).pow k₂ k₃
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ k₂) (3 ^ k₃)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  let a : ℤ := Nat.gcdA (2 ^ k₂) (3 ^ k₃)
  let b : ℤ := Nat.gcdB (2 ^ k₂) (3 ^ k₃)
  have hbezR : ((2 : R) ^ k₂) * (a : R) + ((3 : R) ^ k₃) * (b : R) = 1 := by
    have h1 := congrArg (Int.cast : ℤ → R) hbez
    simpa [a, b, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using h1.symm
  refine ⟨C (a : R) * q₂ + C (b : R) * q₃, ?_⟩
  change f = W * (C (a : R) * q₂ + C (b : R) * q₃)
  calc f = C ((2 : R) ^ k₂ * (a : R) + (3 : R) ^ k₃ * (b : R)) * f := by
        rw [hbezR, map_one, one_mul]
  _ = C (a : R) * (C ((2 : R) ^ k₂) * f) + C (b : R) * (C ((3 : R) ^ k₃) * f) := by
        rw [map_add, map_mul, map_mul]
        ring
  _ = C (a : R) * (W * q₂) + C (b : R) * (W * q₃) := by rw [hq₂, hq₃]
  _ = W * (C (a : R) * q₂ + C (b : R) * q₃) := by ring

/-- Over any integral domain in which `2 ≠ 0` and `3 ≠ 0`, the Weierstrass discriminant
`4 * X 0 ^ 3 + 27 * X 1 ^ 2` is prime. -/
theorem prime_four_mul_pow_three_add_twentyseven_mul_sq {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  let W : MvPolynomial (Fin 2) R := 4 * X 0 ^ 3 + 27 * X 1 ^ 2
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hinj_mv : Function.Injective (MvPolynomial.map (σ := Fin 2) (algebraMap R K)) :=
    MvPolynomial.map_injective _ hinj
  have h2K : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff (algebraMap R K) hinj).mpr h2
  have h3K : (3 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff (algebraMap R K) hinj).mpr h3
  have hassocK : Associated (depressedDiscr K 3)
      (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) K) :=
    ⟨-1, by simp [depressedDiscr_three]; ring⟩
  have hWK : Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) K) :=
    hassocK.prime_iff.mp
      (depressedDiscr_prime h2K (m := 3) (by norm_num; exact h3K) (by norm_num))
  have hWK_eq : MvPolynomial.map (algebraMap R K) W =
      (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) K) := by
    dsimp [W]
    simp [map_add, map_mul, map_pow, map_ofNat]
  rw [← hWK_eq] at hWK
  refine ⟨fun h0 ↦ hWK.ne_zero (by rw [show W = 4 * X 0 ^ 3 + 27 * X 1 ^ 2 from rfl, h0, map_zero]),
    fun hu ↦ hWK.not_isUnit (hu.map _), ?_⟩
  intro f g hfg
  have hfgK : MvPolynomial.map (algebraMap R K) W ∣
      MvPolynomial.map (algebraMap R K) f * MvPolynomial.map (algebraMap R K) g := by
    have h1 := map_dvd (MvPolynomial.map (σ := Fin 2) (algebraMap R K)) hfg
    rwa [map_mul] at h1
  have descend : ∀ x : MvPolynomial (Fin 2) R,
      MvPolynomial.map (algebraMap R K) W ∣ MvPolynomial.map (algebraMap R K) x → W ∣ x := by
    rintro x ⟨qK, hqK⟩
    obtain ⟨⟨c, hc⟩, q₀, hq₀⟩ :=
      exists_C_mul_eq_map_of_isLocalization (nonZeroDivisors R) K qK
    have hcx : C c * x = W * q₀ := by
      apply hinj_mv
      rw [map_mul, map_C, map_mul, hqK, ← hq₀]
      ring
    exact weierstrass_dvd_of_C_mul_dvd h2 h3 (nonZeroDivisors.ne_zero hc) hcx
  rcases hWK.dvd_or_dvd hfgK with hfK | hgK
  · exact Or.inl (descend f hfK)
  · exact Or.inr (descend g hgK)

/-- Inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` in `R[a, b]` with weights `4, 6` (when `2 ≠ 0` and
`3 ≠ 0` in an integral domain `R`) yields shift class group `ZMod 12`. -/
noncomputable def shiftClassGroupAwayWeierstrassEquiv {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
          (mem_weightedHomogeneousSubmodule_weierstrass R)) ≃+ ZMod 12 :=
  shiftClassGroupAwayPrimeEquiv (![4, 6] : Fin 2 → ℤ)
    (mem_weightedHomogeneousSubmodule_weierstrass R)
    (prime_four_mul_pow_three_add_twentyseven_mul_sq h2 h3)

/-- The identification of the Weierstrass shift class group with `ZMod 12` sends the class of `d`
to `d mod 12`. -/
@[simp]
theorem shiftClassGroupAwayWeierstrassEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (d : ℤ) :
    shiftClassGroupAwayWeierstrassEquiv h2 h3 d = d :=
  shiftClassGroupAwayPrimeEquiv_mk _ _ _ d

end Depressed

end TauCeti
