/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic

import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.Polynomial.Resultant.FreeMonic

/-!
# Universal specialization and Tschirnhaus equivalence for `TauCeti.genericDepressed`

This file complements `TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic` with the
characteristic universal specialization property of `TauCeti.genericDepressed R m` over arbitrary
`R`-algebras (`Polynomial.Monic.map_genericDepressed_eq_iff`,
`Polynomial.Monic.map_aeval_genericDepressed`, `TauCeti.map_algHom_genericDepressed_eq_iff`),
explicit formulas in degrees `0` through `4`, and the Tschirnhaus `R`-algebra equivalence
`TauCeti.tschirnhausAlgEquiv : MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`
when `(m : R)` is invertible.

## Main definitions

* `TauCeti.tschirnhausAlgEquiv`: for `IsUnit (m : R)`, the Tschirnhaus `R`-algebra equivalence
  `MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`.

## Main results

* `TauCeti.coeff_genericDepressed_self`: the degree-`m` coefficient of `genericDepressed R m` is
  `1`.
* `Polynomial.Monic.map_genericDepressed_eq_iff`, `TauCeti.map_algHom_genericDepressed_eq_iff`,
  `Polynomial.Monic.map_aeval_genericDepressed`: base change and universal specialization property
  for monic depressed polynomials of degree `m`.
* `TauCeti.genericDepressed_zero`, `TauCeti.genericDepressed_one`,
  `TauCeti.genericDepressed_two`, `TauCeti.genericDepressed_three`,
  `TauCeti.genericDepressed_four`: explicit formulas in degrees `0` through `4`.
* `TauCeti.map_tschirnhausAlgEquiv_freeMonic`, `TauCeti.tschirnhausAlgEquiv_X`,
  `TauCeti.tschirnhausAlgEquiv_X_mk_sub_one`, `TauCeti.tschirnhausAlgEquiv_symm_X`,
  `TauCeti.map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed`,
  `TauCeti.tschirnhausAlgEquiv_symm_C_X`: forward and inverse rules for
  `TauCeti.tschirnhausAlgEquiv`.
-/

public section

open Polynomial

namespace TauCeti

section Semiring

/-- The coefficient of `X ^ m` in `TauCeti.genericDepressed R m` is `1`. -/
@[simp]
theorem coeff_genericDepressed_self (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).coeff m = 1 := by
  rw [coeff_genericDepressed, ite_eq_left rfl]

end Semiring

end TauCeti

namespace Polynomial.Monic

/-- **Characteristic specialization property of `TauCeti.genericDepressed`.** For any monic
depressed polynomial `f : S[X]` of `natDegree` `m`, a ring homomorphism
`φ : MvPolynomial (Fin (m - 1)) R →+* S` realizes `f` from `TauCeti.genericDepressed R m` if and
only if it sends each variable `X i` to the coefficient `f.coeff (m - 2 - i)`. -/
theorem map_genericDepressed_eq_iff {R S : Type*} [CommSemiring R] [CommSemiring S]
    {f : S[X]} {m : ℕ} (hf : f.Monic) (hdeg : f.natDegree = m) (hnext : f.nextCoeff = 0)
    (φ : MvPolynomial (Fin (m - 1)) R →+* S) :
    (TauCeti.genericDepressed R m).map φ = f ↔
      ∀ i : Fin (m - 1), φ (MvPolynomial.X i) = f.coeff (m - 2 - (i : ℕ)) := by
  constructor
  · intro h i
    have hc := congrArg (fun p : S[X] ↦ p.coeff (m - 2 - (i : ℕ))) h
    simpa [Polynomial.coeff_map, TauCeti.coeff_genericDepressed_sub_two_sub] using hc
  · intro hφ
    ext k : 2
    rw [Polynomial.coeff_map, TauCeti.coeff_genericDepressed]
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

/-- **Universal property of the generic depressed polynomial.** A monic polynomial `p` of degree
`m` with vanishing subleading coefficient over an `R`-algebra `S` is the specialization of
`TauCeti.genericDepressed R m` at `aⱼ₊₂ = p.coeff (m - 2 - j)`. -/
theorem map_aeval_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {p : S[X]} {m : ℕ} (hp : p.Monic) (hdeg : p.natDegree = m) (hnext : p.nextCoeff = 0) :
    (TauCeti.genericDepressed R m).map
        (MvPolynomial.aeval (R := R) fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j)).toRingHom =
      p :=
  (hp.map_genericDepressed_eq_iff hdeg hnext _).mpr fun j ↦ by simp

end Polynomial.Monic

namespace TauCeti

section Semiring

/-- **Unique `R`-algebra specialization of `TauCeti.genericDepressed`.** For any monic depressed
polynomial `f : S[X]` of `natDegree` `m` over an `R`-algebra `S`, an `R`-algebra homomorphism
`φ : MvPolynomial (Fin (m - 1)) R →ₐ[R] S` maps `genericDepressed R m` to `f` if and only if
`φ = MvPolynomial.aeval fun i : Fin (m - 1) ↦ f.coeff (m - 2 - i)`. -/
theorem map_algHom_genericDepressed_eq_iff (R : Type*) [CommSemiring R] {S : Type*}
    [CommSemiring S] [Algebra R S] {f : S[X]} {m : ℕ} (hf : f.Monic) (hdeg : f.natDegree = m)
    (hnext : f.nextCoeff = 0) (φ : MvPolynomial (Fin (m - 1)) R →ₐ[R] S) :
    (genericDepressed R m).map φ.toRingHom = f ↔
      φ = MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦ f.coeff (m - 2 - (i : ℕ)) := by
  rw [hf.map_genericDepressed_eq_iff hdeg hnext]
  exact ⟨fun h ↦ MvPolynomial.algHom_ext fun i ↦ by simpa using h i,
    fun h i ↦ by simp [h]⟩

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

section Tschirnhaus

/-- If `(m : R)` is a unit in a nontrivial ring `R`, then `m ≠ 0`, so `m - 1 < m`. -/
private theorem sub_one_lt_of_isUnit {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    (hmu : IsUnit (m : R)) : m - 1 < m := by
  rcases m with _ | n
  · rw [Nat.cast_zero] at hmu
    exact absurd hmu not_isUnit_zero
  · omega

/-- The `R`-algebra map from the universal monic coefficient ring `MvPolynomial (Fin m) R` to
`(MvPolynomial (Fin (m - 1)) R)[X]`, classifying the shifted generic depressed polynomial
`((genericDepressed R m).map C).comp (X + C X)`. -/
private noncomputable def tschirnhausToDepressed (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] :=
  MvPolynomial.aeval fun k : Fin m ↦
    (((genericDepressed R m).map Polynomial.C).comp
      (Polynomial.X + Polynomial.C Polynomial.X)).coeff k

/-- Mapping `Polynomial.freeMonic R m` along `tschirnhausToDepressed` produces the generic
depressed polynomial translated by the indeterminate `Polynomial.X`. -/
private theorem map_tschirnhausToDepressed_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).map (tschirnhausToDepressed R m).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let Q : (MvPolynomial (Fin (m - 1)) R)[X][X] :=
    ((genericDepressed R m).map Polynomial.C).comp (Polynomial.X + Polynomial.C Polynomial.X)
  have hQ_eq : Q = taylor Polynomial.X ((genericDepressed R m).map Polynomial.C) := by
    rw [taylor_apply]
  have hQmon : Q.Monic := by
    rw [hQ_eq, Monic.def, leadingCoeff_taylor]
    exact ((monic_genericDepressed (R := R) (m := m)).map Polynomial.C).leadingCoeff
  have hQdeg : Q.natDegree = m := by
    rw [hQ_eq, natDegree_taylor, (monic_genericDepressed (R := R) (m := m)).natDegree_map,
      natDegree_genericDepressed]
  exact Polynomial.map_aeval_coeff_freeMonic hQmon hQdeg

/-- The normalized subleading coefficient `m⁻¹ • X ⟨m - 1, _⟩` (negated root barycenter) of
`Polynomial.freeMonic R m` when `IsUnit (m : R)` (and `0` in the subsingleton case `m = 0`). -/
private noncomputable def tschirnhausNegBarycenter {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) : MvPolynomial (Fin m) R :=
  if hm : m - 1 < m then (↑hmu.unit⁻¹ : R) • MvPolynomial.X ⟨m - 1, hm⟩ else 0

/-- Centering `Polynomial.freeMonic R m` by `- tschirnhausNegBarycenter hmu` to annihilate its
subleading coefficient. -/
private noncomputable def tschirnhausCentered {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) : (MvPolynomial (Fin m) R)[X] :=
  (freeMonic R m).comp (Polynomial.X - Polynomial.C (tschirnhausNegBarycenter hmu))

/-- The inverse `R`-algebra map `(MvPolynomial (Fin (m - 1)) R)[X] →ₐ[R] MvPolynomial (Fin m) R`
of `tschirnhausToDepressed`, sending `C (X i)` to the `(m - 2 - i)`-nd coefficient of
`tschirnhausCentered hmu` and `Polynomial.X` to `tschirnhausNegBarycenter hmu`. -/
private noncomputable def tschirnhausFromDepressed {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (MvPolynomial (Fin (m - 1)) R)[X] →ₐ[R] MvPolynomial (Fin m) R :=
  Polynomial.aevalTower
    (MvPolynomial.aeval fun i : Fin (m - 1) ↦
      (tschirnhausCentered hmu).coeff (m - 2 - (i : ℕ)))
    (tschirnhausNegBarycenter hmu)

private theorem tschirnhausToDepressed_X_mk_sub_one {R : Type*} [CommRing R] {m : ℕ}
    (hm : m - 1 < m) :
    tschirnhausToDepressed R m (MvPolynomial.X ⟨m - 1, hm⟩) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let G : (MvPolynomial (Fin (m - 1)) R)[X][X] := (genericDepressed R m).map Polynomial.C
  have hGmon : G.Monic := (monic_genericDepressed (R := R) (m := m)).map Polynomial.C
  have hGdeg : G.natDegree = m := by
    rw [(monic_genericDepressed (R := R) (m := m)).natDegree_map Polynomial.C,
      natDegree_genericDepressed]
  have hGnext : G.nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_map_eq_of_isUnit_leadingCoeff _ (by simp),
      nextCoeff_genericDepressed, map_zero]
  have htaylor : (taylor Polynomial.X G).coeff (m - 1) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
    have htdeg : (taylor Polynomial.X G).natDegree = m := by rw [natDegree_taylor, hGdeg]
    have htpos : 0 < (taylor Polynomial.X G).natDegree := by omega
    have htnext := nextCoeff_of_natDegree_pos htpos
    rw [htdeg] at htnext
    rw [← htnext, nextCoeff_taylor, hGnext, hGdeg, hGmon.leadingCoeff, zero_add, mul_one]
  simpa only [tschirnhausToDepressed, MvPolynomial.aeval_X, G, ← taylor_apply] using htaylor

private theorem tschirnhausToDepressed_tschirnhausNegBarycenter {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    tschirnhausToDepressed R m (tschirnhausNegBarycenter hmu) = Polynomial.X := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : m - 1 < m := sub_one_lt_of_isUnit hmu
  rw [tschirnhausNegBarycenter, dite_eq_left hm, map_smul, tschirnhausToDepressed_X_mk_sub_one hm,
    ← smul_mul_assoc]
  have hum : (↑hmu.unit⁻¹ : R) • (m : (MvPolynomial (Fin (m - 1)) R)[X]) = 1 := by
    have h1 := congrArg (algebraMap R (MvPolynomial (Fin (m - 1)) R)[X]) hmu.val_inv_mul
    rwa [map_mul, map_natCast, map_one, ← Algebra.smul_def] at h1
  rw [hum, one_mul]

private theorem map_tschirnhausFromDepressed_comp_C_genericDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (genericDepressed R m).map ((tschirnhausFromDepressed hmu).toRingHom.comp Polynomial.C) =
      tschirnhausCentered hmu := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : m - 1 < m := sub_one_lt_of_isUnit hmu
  have hP₀_eq : tschirnhausCentered hmu =
      taylor (-tschirnhausNegBarycenter hmu) (freeMonic R m) := by
    simp [tschirnhausCentered, taylor_apply, sub_eq_add_neg]
  have hP₀_mon : (tschirnhausCentered hmu).Monic := by
    rw [hP₀_eq, Monic.def, leadingCoeff_taylor, (monic_freeMonic R m).leadingCoeff]
  have hP₀_deg : (tschirnhausCentered hmu).natDegree = m := by
    rw [hP₀_eq, natDegree_taylor, natDegree_freeMonic]
  have hP₀_next : (tschirnhausCentered hmu).nextCoeff = 0 := by
    have hfpos : 0 < (freeMonic R m).natDegree := by rw [natDegree_freeMonic]; omega
    rw [hP₀_eq, nextCoeff_taylor, nextCoeff_of_natDegree_pos hfpos]
    simp only [natDegree_freeMonic, (monic_freeMonic R m).leadingCoeff, mul_one, coeff_freeMonic,
      dite_eq_left hm, tschirnhausNegBarycenter, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    have hmul : (m : MvPolynomial (Fin m) R) * MvPolynomial.C (↑hmu.unit⁻¹ : R) = 1 := by
      rw [← map_natCast MvPolynomial.C m, ← map_mul, hmu.mul_val_inv, map_one]
    linear_combination -MvPolynomial.X ⟨m - 1, hm⟩ * hmul
  have hbase : (tschirnhausFromDepressed hmu).toRingHom.comp Polynomial.C =
      (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
        (tschirnhausCentered hmu).coeff (m - 2 - (i : ℕ))).toRingHom :=
    RingHom.ext (Polynomial.aevalTower_C _ _)
  rw [hbase]
  exact hP₀_mon.map_aeval_genericDepressed hP₀_deg hP₀_next

private theorem tschirnhausToDepressed_comp_tschirnhausFromDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (tschirnhausToDepressed R m).comp (tschirnhausFromDepressed hmu) = AlgHom.id R _ := by
  apply Polynomial.algHom_ext'
  · refine MvPolynomial.algHom_ext fun i ↦ ?_
    have hcomp : (tschirnhausCentered hmu).map (tschirnhausToDepressed R m).toRingHom =
        (genericDepressed R m).map Polynomial.C := by
      rw [tschirnhausCentered, Polynomial.map_comp, map_tschirnhausToDepressed_freeMonic]
      have hX_map : (Polynomial.X - Polynomial.C (tschirnhausNegBarycenter hmu)).map
          (tschirnhausToDepressed R m).toRingHom = Polynomial.X - Polynomial.C Polynomial.X := by
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
          congrArg (fun q ↦ Polynomial.X - Polynomial.C q)
            (tschirnhausToDepressed_tschirnhausNegBarycenter hmu)
      rw [hX_map]
      have htay := Polynomial.taylor_neg_taylor (Polynomial.X : (MvPolynomial (Fin (m - 1)) R)[X])
        ((genericDepressed R m).map Polynomial.C)
      rw [Polynomial.taylor_apply, Polynomial.taylor_apply, map_neg, ← sub_eq_add_neg] at htay
      exact htay
    have hcoeff := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦
      p.coeff (m - 2 - (i : ℕ))) hcomp
    rw [Polynomial.coeff_map, Polynomial.coeff_map, coeff_genericDepressed_sub_two_sub] at hcoeff
    simpa [tschirnhausFromDepressed, Polynomial.aevalTower_C] using hcoeff
  · simpa [tschirnhausFromDepressed] using tschirnhausToDepressed_tschirnhausNegBarycenter hmu

private theorem tschirnhausFromDepressed_comp_tschirnhausToDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (tschirnhausFromDepressed hmu).comp (tschirnhausToDepressed R m) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun k ↦ ?_
  have hcomp : ((freeMonic R m).map (tschirnhausToDepressed R m).toRingHom).map
      (tschirnhausFromDepressed hmu).toRingHom = freeMonic R m := by
    rw [map_tschirnhausToDepressed_freeMonic, Polynomial.map_comp, Polynomial.map_map,
      map_tschirnhausFromDepressed_comp_C_genericDepressed]
    have hX_from :
        tschirnhausFromDepressed hmu Polynomial.X = tschirnhausNegBarycenter hmu := by
      rw [tschirnhausFromDepressed, Polynomial.aevalTower_X]
    have hX_inv : (Polynomial.X + Polynomial.C (Polynomial.X :
          (MvPolynomial (Fin (m - 1)) R)[X])).map
        (tschirnhausFromDepressed hmu).toRingHom =
        Polynomial.X + Polynomial.C (tschirnhausNegBarycenter hmu) := by
      simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
        congrArg (fun q ↦ Polynomial.X + Polynomial.C q) hX_from
    rw [hX_inv, tschirnhausCentered]
    have htay := Polynomial.taylor_neg_taylor (-tschirnhausNegBarycenter hmu) (freeMonic R m)
    rw [neg_neg, Polynomial.taylor_apply, Polynomial.taylor_apply, map_neg,
      ← sub_eq_add_neg] at htay
    exact htay
  have hcoeff := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff k) hcomp
  rw [Polynomial.map_map, Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.isLt] at hcoeff
  simpa using hcoeff

/-- When `(m : R)` is invertible, centering `Polynomial.freeMonic R m` by its root barycenter
`- m⁻¹ * X (m - 1)` and recording the negated root barycenter (normalized subleading coefficient)
`m⁻¹ * X (m - 1)` in `Polynomial.X` gives an `R`-algebra equivalence
`MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`. -/
noncomputable def tschirnhausAlgEquiv {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R)) :
    MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] :=
  AlgEquiv.ofAlgHom (tschirnhausToDepressed R m) (tschirnhausFromDepressed hmu)
    (tschirnhausToDepressed_comp_tschirnhausFromDepressed hmu)
    (tschirnhausFromDepressed_comp_tschirnhausToDepressed hmu)

private theorem tschirnhausAlgEquiv_toAlgHom {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (tschirnhausAlgEquiv hmu).toAlgHom = tschirnhausToDepressed R m :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

/-- Mapping `Polynomial.freeMonic R m` along `TauCeti.tschirnhausAlgEquiv` produces the generic
depressed polynomial translated by `Polynomial.X`. -/
theorem map_tschirnhausAlgEquiv_freeMonic {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (freeMonic R m).map (tschirnhausAlgEquiv hmu).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) := by
  have hhom : (tschirnhausAlgEquiv hmu).toRingHom =
      (tschirnhausToDepressed R m).toRingHom := by
    rw [RingEquiv.toRingHom_eq_coe, ← AlgEquiv.toRingHom_toAlgHom,
      tschirnhausAlgEquiv_toAlgHom, AlgHom.toRingHom_eq_coe]
  rw [hhom]
  exact map_tschirnhausToDepressed_freeMonic R m

/-- `TauCeti.tschirnhausAlgEquiv` maps `X k` to the `k`-th coefficient of the shifted generic
depressed polynomial `((genericDepressed R m).map C).comp (X + C X)`. -/
theorem tschirnhausAlgEquiv_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (k : Fin m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X k) =
      (((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X)).coeff k := by
  have h := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦ p.coeff k)
    (map_tschirnhausAlgEquiv_freeMonic hmu)
  rw [Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.isLt] at h
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv] using h

/-- `TauCeti.tschirnhausAlgEquiv` maps the subleading coefficient variable `X ⟨m - 1, hm⟩` to
`m * Polynomial.X`. -/
@[simp]
theorem tschirnhausAlgEquiv_X_mk_sub_one {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (hm : m - 1 < m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X ⟨m - 1, hm⟩) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
  rw [← AlgEquiv.coe_toAlgHom, tschirnhausAlgEquiv_toAlgHom]
  exact tschirnhausToDepressed_X_mk_sub_one hm

/-- The inverse of `TauCeti.tschirnhausAlgEquiv` maps `Polynomial.X` to the normalized subleading
coefficient `(↑hmu.unit⁻¹ : R) • X ⟨m - 1, hm⟩` (the negated root barycenter). -/
@[simp]
theorem tschirnhausAlgEquiv_symm_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (hm : m - 1 < m) :
    (tschirnhausAlgEquiv hmu).symm Polynomial.X =
      (↑hmu.unit⁻¹ : R) • MvPolynomial.X ⟨m - 1, hm⟩ := by
  rw [tschirnhausAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, tschirnhausFromDepressed,
    Polynomial.aevalTower_X, tschirnhausNegBarycenter, dite_eq_left hm]

/-- Mapping `TauCeti.genericDepressed R m` along `(tschirnhausAlgEquiv hmu).symm` composed with
`Polynomial.C` centers `Polynomial.freeMonic R m` at
`Polynomial.X - C ((tschirnhausAlgEquiv hmu).symm X)`. -/
theorem map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (genericDepressed R m).map ((tschirnhausAlgEquiv hmu).symm.toRingHom.comp Polynomial.C) =
      (freeMonic R m).comp
        (Polynomial.X - Polynomial.C ((tschirnhausAlgEquiv hmu).symm Polynomial.X)) := by
  have hX : (tschirnhausAlgEquiv hmu).symm Polynomial.X = tschirnhausNegBarycenter hmu := by
    rw [tschirnhausAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, tschirnhausFromDepressed,
      Polynomial.aevalTower_X]
  rw [hX]
  exact map_tschirnhausFromDepressed_comp_C_genericDepressed hmu

/-- The inverse of `TauCeti.tschirnhausAlgEquiv` maps `Polynomial.C (MvPolynomial.X i)` to the
`(m - 2 - i)`-nd coefficient of `Polynomial.freeMonic R m` centered at
`Polynomial.X - C ((tschirnhausAlgEquiv hmu).symm X)`. -/
theorem tschirnhausAlgEquiv_symm_C_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (i : Fin (m - 1)) :
    (tschirnhausAlgEquiv hmu).symm (Polynomial.C (MvPolynomial.X i)) =
      ((freeMonic R m).comp
        (Polynomial.X - Polynomial.C ((tschirnhausAlgEquiv hmu).symm Polynomial.X))).coeff
        (m - 2 - (i : ℕ)) := by
  have h := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff (m - 2 - (i : ℕ)))
    (map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed hmu)
  rw [Polynomial.coeff_map, RingHom.comp_apply, coeff_genericDepressed_sub_two_sub] at h
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv] using h

end Tschirnhaus

end TauCeti
