/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Discriminant.Generic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
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
domain (in particular over a field of characteristic zero). For `m ≥ 3`, localizing at `m` and
descending via the fact that `depressedDiscr R m` is monic up to sign in the coefficient of `X`
modulo `m` removes the unit assumption, yielding primality whenever `2 ≠ 0` and `(m : R) ≠ 0`
(for example over `ℤ`).

In degrees `2` and `3` the depressed discriminant is `-4 * X 0` and `-4 * X 0 ^ 3 - 27 * X 1 ^ 2`.
Localizing `MvPolynomial (Fin (m - 1)) R` away from `depressedDiscr R m` has homogeneous unit
degrees `m * (m - 1) ℤ` and shift class group `ZMod (m * (m - 1))` whenever `m ≥ 2`, `(2 : R) ≠ 0`,
and `(m : R) ≠ 0` (including `m = 2`, since inverting `-4 * X 0` inverts both `2` and `X 0`).
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
* `TauCeti.depressedDiscr_prime_of_isUnit`, `TauCeti.depressedDiscr_prime`, and
  `TauCeti.depressedDiscr_prime_of_charZero`: primality of `depressedDiscr R m` for `m ≥ 2` when
  `IsUnit (m : R)`, and for `m ≥ 3` under the weaker assumption `(m : R) ≠ 0` (assuming
  `(2 : R) ≠ 0`).
* `TauCeti.homogeneousUnitDegrees_away_depressedDiscr`: the homogeneous unit degrees after
  inverting `depressedDiscr R m` are `AddSubgroup.zmultiples (m * (m - 1))` for all `m ≥ 2` with
  `(2 : R) ≠ 0` and `(m : R) ≠ 0`.
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

/-- The substitution mapping coefficient variables of `Polynomial.freeMonic R m` to those of
`genericDepressed R m` (sending the subleading coefficient to `0`). -/
private noncomputable def depressedSubst (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin (m - 1)) R :=
  aeval fun i : Fin m ↦
    if h : (i : ℕ) + 2 ≤ m then X ⟨m - 2 - (i : ℕ), by omega⟩ else 0

/-- The generic depressed monic polynomial of degree `m`,
`X ^ m + a₂ * X ^ (m - 2) + ⋯ + aₘ`, where `X i` (`i : Fin (m - 1)`) represents `a_{i + 2}`. -/
noncomputable def genericDepressed (R : Type*) [CommRing R] (m : ℕ) :
    Polynomial (MvPolynomial (Fin (m - 1)) R) :=
  (Polynomial.freeMonic R m).map (depressedSubst R m).toRingHom

/-- Explicit expansion of `genericDepressed R m` as a sum of monomials. -/
theorem genericDepressed_eq (R : Type*) [CommRing R] (m : ℕ) :
    genericDepressed R m =
      Polynomial.X ^ m +
        ∑ i : Fin (m - 1), Polynomial.C (X i) * Polynomial.X ^ (m - (i.val + 2)) := by
  rw [genericDepressed, Polynomial.freeMonic, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sum]
  congr 1
  rcases m with _ | _ | m
  · simp
  · simp [depressedSubst]
  · simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, depressedSubst, aeval_X]
    rw [Fin.sum_univ_castSucc]
    have hlast : ¬ (Fin.last (m + 1) : ℕ) + 2 ≤ m + 2 := by simp
    rw [dite_eq_right hlast, Polynomial.C_0, zero_mul, add_zero]
    refine Finset.sum_bij (fun j _ ↦ j.rev) (fun _ _ ↦ mem_univ _)
      (fun _ _ _ _ h ↦ Fin.rev_injective h)
      (fun j _ ↦ ⟨j.rev, mem_univ _, Fin.rev_rev j⟩) (fun j _ ↦ ?_)
    have hj : (j.castSucc : ℕ) + 2 ≤ m + 2 := by simp; omega
    rw [dite_eq_left hj]
    congr 1
    · refine congrArg Polynomial.C (congrArg X ?_)
      ext; simp [Fin.val_rev]
    · congr 1; simp [Fin.val_rev]; omega

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
theorem coeff_genericDepressed (R : Type*) [CommRing R] (m k : ℕ) :
    (genericDepressed R m).coeff k =
      if h : k + 2 ≤ m then X ⟨m - 2 - k, by omega⟩ else if k = m then 1 else 0 := by
  rw [genericDepressed, Polynomial.coeff_map, Polynomial.coeff_freeMonic]
  by_cases hlt : k < m
  · rw [dite_eq_left hlt]
    simp [depressedSubst, hlt.ne]
  · rw [dite_eq_right hlt]
    by_cases heq : k = m
    · subst heq; simp
    · have h2 : ¬ k + 2 ≤ m := by omega
      simp [h2, heq]

/-- Over a nontrivial ring, `genericDepressed R m` has degree `m`. -/
@[simp]
theorem degree_genericDepressed (R : Type*) [CommRing R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).degree = m :=
  ((Polynomial.monic_freeMonic R m).degree_map _).trans (Polynomial.degree_freeMonic R m)

/-- Over a nontrivial ring, `genericDepressed R m` has `natDegree` equal to `m`. -/
@[simp]
theorem natDegree_genericDepressed (R : Type*) [CommRing R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).natDegree = m :=
  ((Polynomial.monic_freeMonic R m).natDegree_map _).trans (Polynomial.natDegree_freeMonic R m)

/-- The generic depressed polynomial `genericDepressed R m` is monic over any commutative ring. -/
theorem monic_genericDepressed (R : Type*) [CommRing R] (m : ℕ) :
    (genericDepressed R m).Monic :=
  (Polynomial.monic_freeMonic R m).map _

/-- Forming `genericDepressed` commutes with base change along any ring homomorphism. -/
@[simp]
theorem map_map_genericDepressed {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (m : ℕ) : (genericDepressed R m).map (MvPolynomial.map f) = genericDepressed S m := by
  simp only [genericDepressed, Polynomial.map_map]
  rw [← Polynomial.map_map_freeMonic R S m f, Polynomial.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, depressedSubst,
      aeval_X, map_X]
    split_ifs <;> simp

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
  have hdiscr : depressedSubst R m (Polynomial.freeMonic R m).discr = depressedDiscr R m :=
    ((Polynomial.monic_freeMonic R m).discr_map (depressedSubst R m).toRingHom).symm
  have hg : ∀ i : Fin m,
      (if h : (i : ℕ) + 2 ≤ m then X ⟨m - 2 - (i : ℕ), by omega⟩
        else (0 : MvPolynomial (Fin (m - 1)) R)).IsWeightedHomogeneous
        (depressedWeight m) (freeMonicWeight m i) := by
    intro i
    split_ifs with h
    · convert isWeightedHomogeneous_X R (depressedWeight m) ⟨m - 2 - (i : ℕ), by omega⟩
      simp only [depressedWeight, freeMonicWeight_apply]
      omega
    · exact isWeightedHomogeneous_zero R (depressedWeight m) _
  rw [mem_weightedHomogeneousSubmodule, ← hdiscr]
  dsimp only [depressedSubst]
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
        simpa [hF_deg, hF_mon.leadingCoeff] using
          Polynomial.coeff_taylor_natDegree (r := -s) (f := F)
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
    rw [(monic_genericDepressed R m).natDegree_map, natDegree_genericDepressed R m]
  let Q := G.comp (Polynomial.X + Polynomial.C s)
  have hshift : Q = Polynomial.taylor s G := (Polynomial.taylor_apply s G).symm
  have hQ_mon : Q.Monic := hG_mon.comp (Polynomial.monic_X_add_C s) (by simp)
  have hQ_deg : Q.natDegree = m := by rw [hshift, Polynomial.natDegree_taylor, hG_deg]
  let q : Polynomial.MonicDegreeEq (MvPolynomial (Fin m) R) m :=
    Polynomial.MonicDegreeEq.mk Q hQ_mon hQ_deg
  have hsymm : (MvPolynomial.mapEquivMonic R (MvPolynomial (Fin m) R) m).symm q =
      tschirnhausFromDepressed R hm hmR := by
    refine algHom_ext fun i ↦ ?_
    simp only [MvPolynomial.mapEquivMonic, Equiv.coe_fn_symm_mk, aeval_X, q,
      Polynomial.MonicDegreeEq.mk_coe, tschirnhausFromDepressed]
    by_cases hlt : (i : ℕ) + 2 ≤ m
    · simp [Q, G, s, hlt]
    · have hi : (i : ℕ) = m - 1 := by omega
      have hfin : i = ⟨m - 1, by omega⟩ := Fin.ext hi
      rw [ite_eq_right hlt, hfin]
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
      rw [hshift, hnext]
      let i₁ : Fin m := ⟨m - 1, by omega⟩
      change (m : MvPolynomial (Fin m) R) * s = X i₁
      calc
        (m : MvPolynomial (Fin m) R) * s
          = ((m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R)) * X i₁ := by
                dsimp [s, tschirnhausShift, i₁]
                ring
        _ = X i₁ := by rw [natCast_mul_C_inv_eq_one hmR, one_mul]
  have h := congrArg (fun f ↦ (MvPolynomial.mapEquivMonic R (MvPolynomial (Fin m) R) m f).1) hsymm
  rw [(MvPolynomial.mapEquivMonic R (MvPolynomial (Fin m) R) m).apply_symm_apply q] at h
  exact h.symm

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

/-- **Primality of the generic depressed discriminant when the degree is invertible.** Over any
integral domain in which `2 ≠ 0` and `m` is invertible, `depressedDiscr R m` is prime for every
`m ≥ 2`. -/
theorem depressedDiscr_prime_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R)) (hm : 2 ≤ m) :
    Prime (depressedDiscr R m) := by
  rw [← prime_rename_iff_of_injective (depressedEmb_injective m hm),
    ← tschirnhausEquiv_discr_freeMonic R hm hmR]
  exact (MulEquiv.prime_iff (tschirnhausEquiv R hm hmR).toMulEquiv).mpr
    (prime_discr_freeMonic h2 hm)

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
  rw [hfac, hmonX.discr_mul hmonQ, hdiscrX, hres, one_pow, one_mul, mul_one,
    Polynomial.discr_X_pow_sub_C, show m - 1 - 1 = m - 2 by omega]
  simp only [neg_neg, one_pow, mul_one]

private theorem depressedDiscr_coeff_single_eq (R : Type*) [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    (depressedDiscr R m).coeff (Finsupp.single ⟨m - 3, by omega⟩ m) =
      (-1 : R) ^ ((m - 1) * (m - 2) / 2) * ((m - 1 : ℕ) : R) ^ (m - 1) := by
  classical
  let i₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let v : Fin (m - 1) → R := Pi.single i₀ 1
  have heval_sum : eval v (depressedDiscr R m) =
      (depressedDiscr R m).coeff (Finsupp.single i₀ m) := by
    rw [eval_eq]
    rw [Finset.sum_eq_single (Finsupp.single i₀ m)]
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
          rw [Finsupp.weight_apply, Finsupp.sum]
          rw [Finset.sum_eq_single i₀]
          · simp only [depressedWeight_apply, i₀, nsmul_eq_mul]
            have : ((m - 3 : ℕ) : ℤ) + 2 = (m : ℤ) - 1 := by omega
            rw [this]
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
    rw [depressedDiscr, ← (monic_genericDepressed R m).discr_map (eval v)]
    congr 1
    rw [genericDepressed_eq, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Finset.sum_eq_single i₀]
    · simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        eval_X, v, Pi.single_eq_same, map_one, one_mul, i₀]
      rw [show m - (m - 3 + 2) = 1 by omega, pow_one]
    · intro j _ hj
      simp [v, Pi.single_eq_of_ne hj]
    · intro hi0
      exact (hi0 (mem_univ i₀)).elim
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
        ext x
        dsimp only [u]
        rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
        exact congrArg (Finsupp.optionElim n d)
          (Equiv.symm_apply_apply (Equiv.optionSubtypeNe i₀) x)
      have hren := coeff_rename_mapDomain σ σ.injective p u
      rw [hu, ← renameEquiv_apply (R := A)] at hren
      exact hren
    have hσ_none : σ i₀ = none := (Equiv.symm_apply_eq (Equiv.optionSubtypeNe i₀)).mpr rfl
    have hσ_some : ∀ j : {b : Fin (m - 1) // b ≠ i₀}, σ j.1 = some j := fun j ↦
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
            (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (by simp [depressedWeight]; omega)) hiu
        · rw [Finsupp.notMem_support_iff.mp hiu, Nat.cast_zero, zero_mul]
          exact Finset.sum_nonneg fun j _ ↦
            mul_nonneg (Nat.cast_nonneg _) (by simp [depressedWeight]; omega)
      rw [hwt, hui₀] at hle
      have hwti₀ : depressedWeight m i₀ = (m : ℤ) - 1 := by
        simp only [depressedWeight, i₀]
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
        have huj : u j.1 ≠ 0 := by
          dsimp only [u]
          rw [Finsupp.mapDomain_equiv_apply, hσ_some j, Finsupp.optionElim_apply_some]
          exact hj
        have hui₀ : u i₀ = m := by
          dsimp only [u]
          rw [Finsupp.mapDomain_equiv_apply, hσ_none, Finsupp.optionElim_apply_none]
        have hi0_mem : i₀ ∈ u.support := Finsupp.mem_support_iff.mpr (by rw [hui₀]; omega)
        have hj_mem : j.1 ∈ u.support := Finsupp.mem_support_iff.mpr huj
        have hsub : ({i₀, j.1} : Finset _) ⊆ u.support := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hi0_mem
          · rw [Finset.mem_singleton.mp hx]; exact hj_mem
        have hsum_le : ∑ x ∈ ({i₀, j.1} : Finset _), (u x : ℤ) * depressedWeight m x ≤
            Finsupp.weight (depressedWeight m) u := by
          rw [Finsupp.weight_apply, Finsupp.sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ ↦
            mul_nonneg (Nat.cast_nonneg _) (by simp [depressedWeight]; omega)
        rw [Finset.sum_pair j.2.symm, hui₀] at hsum_le
        have hwti₀ : depressedWeight m i₀ = (m : ℤ) - 1 := by
          simp only [depressedWeight, i₀]
          omega
        have hwtj : 2 ≤ depressedWeight m j.1 := by
          simp only [depressedWeight]
          omega
        have huj_pos : (1 : ℤ) ≤ u j.1 := by exact_mod_cast Nat.pos_of_ne_zero huj
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

/-- **Primality of the generic depressed discriminant.** Over any integral domain in which
`2 ≠ 0` and `(m : R) ≠ 0`, `depressedDiscr R m` is prime for every `m ≥ 3`. -/
theorem depressedDiscr_prime {R : Type*} [CommRing R] [IsDomain R]
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
    depressedDiscr_prime_of_isUnit h2m hum (by omega)
  have hmap_eq : MvPolynomial.map (algebraMap R Rm) (depressedDiscr R m) = depressedDiscr Rm m :=
    map_depressedDiscr (algebraMap R Rm) m
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

/-- Over a field of characteristic zero, the generic depressed discriminant is prime for every
`m ≥ 2`. -/
theorem depressedDiscr_prime_of_charZero (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  depressedDiscr_prime_of_isUnit two_ne_zero
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hm

/-! ### Graded localization consequences and low-degree formulas -/

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

private theorem homogeneousUnitDegrees_away_depressedDiscr_two {R : Type*} [CommRing R]
    [IsDomain R] (h2 : (2 : R) ≠ 0) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight 2)) (depressedDiscr_mem R 2))
      = AddSubgroup.zmultiples ((2 : ℤ) * (2 - 1)) := by
  refine le_antisymm ?_ ?_
  · rw [homogeneousUnitDegrees_le_iff]
    intro u deg hu
    obtain ⟨n, a, ha, hua⟩ := mem_awayGrading_iff.mp hu
    have hdiscr_ne : depressedDiscr R 2 ≠ 0 := by
      rw [depressedDiscr_two]
      have h4 : (-4 : R) ≠ 0 := by
        intro h0
        have h22 : (2 : R) * 2 = 0 := by
          have : -(-4 : R) = 2 * 2 := by ring
          rw [h0, neg_zero] at this
          exact this.symm
        exact mul_ne_zero h2 h2 h22
      intro h0
      have hcoeff := congrArg (fun p : MvPolynomial (Fin 1) R ↦ p.coeff (Finsupp.single 0 1)) h0
      have h4eq : (-4 : MvPolynomial (Fin 1) R) = C (-4 : R) := by rw [map_neg, map_ofNat]
      rw [h4eq, coeff_C_mul, coeff_X] at hcoeff
      simp [h4] at hcoeff
    have : IsDomain (Localization.Away (depressedDiscr R 2)) :=
      IsLocalization.Away.isDomain (S := Localization.Away (depressedDiscr R 2)) hdiscr_ne
    have ha_ne : a ≠ 0 := by
      rintro rfl
      rw [Localization.mk_zero] at hua
      exact u.isUnit.ne_zero hua
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr ha_ne
    have hwt := (mem_weightedHomogeneousSubmodule ..).mp ha (mem_support_iff.mp hd)
    have hsum : Finsupp.weight (depressedWeight 2) d = (d 0 : ℤ) * ((2 : ℤ) * (2 - 1)) := by
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ ↦ by simp),
        Fin.sum_univ_one]
      simp [depressedWeight]
    rw [hsum] at hwt
    have hdeg_sol : deg = ((d 0 : ℤ) - n) * ((2 : ℤ) * (2 - 1)) := by
      rw [nsmul_eq_mul] at hwt
      push_cast at hwt
      linarith
    rw [hdeg_sol]
    exact ⟨(d 0 : ℤ) - n, by dsimp only; rw [zsmul_eq_mul, Int.cast_id]⟩
  · rw [AddSubgroup.zmultiples_le]
    exact mem_homogeneousUnitDegrees_awayGrading_self (depressedDiscr_mem R 2)

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields homogeneous unit degrees `m * (m - 1) ℤ`. -/
theorem homogeneousUnitDegrees_away_depressedDiscr {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      = AddSubgroup.zmultiples ((m : ℤ) * (m - 1)) := by
  rcases eq_or_lt_of_le hm with rfl | hm3
  · exact homogeneousUnitDegrees_away_depressedDiscr_two h2
  · exact homogeneousUnitDegrees_away_prime (depressedWeight m) (depressedDiscr_mem R m)
      (depressedDiscr_prime h2 hmR hm3)

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields shift class group `ZMod (m * (m - 1))`. -/
noncomputable def shiftClassGroupAwayDepressedDiscrEquiv {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      ≃+ ZMod (m * (m - 1)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_away_depressedDiscr h2 hmR hm)).trans
    ((Int.quotientZMultiplesEquivZMod ((m : ℤ) * (m - 1))).trans
      (ZMod.ringEquivCongr (by
        have h : ((m : ℤ) * (m - 1)) = ((m * (m - 1) : ℕ) : ℤ) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
        rw [h, Int.natAbs_natCast])).toAddEquiv)

/-- The identification of the shift class group after inverting `depressedDiscr R m` with
`ZMod (m * (m - 1))` sends the class of `d` to `d mod m * (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayDepressedDiscrEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) (d : ℤ) :
    shiftClassGroupAwayDepressedDiscrEquiv h2 hmR hm d = d := by
  dsimp [shiftClassGroupAwayDepressedDiscrEquiv]
  exact map_intCast _ d

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

/-- Over any integral domain in which `2 ≠ 0` and `3 ≠ 0`, the Weierstrass discriminant
`4 * X 0 ^ 3 + 27 * X 1 ^ 2` is prime. -/
theorem prime_four_mul_pow_three_add_twentyseven_mul_sq {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hassoc : Associated (depressedDiscr R 3)
      (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) :=
    ⟨-1, by simp [depressedDiscr_three]; ring⟩
  exact hassoc.prime_iff.mp
    (depressedDiscr_prime h2 (m := 3) (by norm_num; exact h3) (by norm_num))

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
