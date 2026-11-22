/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed

import TauCeti.Algebra.Polynomial.Taylor

/-!
# Tschirnhaus equivalence between generic monic and depressed coefficient rings

Over a commutative ring `R` in which the degree `m` is invertible, translating the indeterminate of
the universal monic polynomial `Polynomial.freeMonic R m` by its root barycenter
`- m⁻¹ * X (m - 1)` eliminates its subleading coefficient. This yields an `R`-algebra equivalence
`TauCeti.tschirnhausAlgEquiv : MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`
identifying the universal monic coefficient ring with polynomials in the negated root barycenter
over the universal depressed coefficient ring.

## Main definitions

* `TauCeti.tschirnhausAlgEquiv`: for `IsUnit (m : R)`, the Tschirnhaus `R`-algebra equivalence
  `MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`.

## Main results

* `TauCeti.map_tschirnhausAlgEquiv_freeMonic`, `TauCeti.tschirnhausAlgEquiv_X`,
  `TauCeti.tschirnhausAlgEquiv_X_sub_one`: forward polynomial and generator rules for
  `TauCeti.tschirnhausAlgEquiv`.
* `TauCeti.tschirnhausAlgEquiv_symm_X`,
  `TauCeti.map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed`,
  `TauCeti.tschirnhausAlgEquiv_symm_C_X`: inverse generator and specialization rules for
  `TauCeti.tschirnhausAlgEquiv`.
-/

public section

open MvPolynomial Polynomial

namespace TauCeti

section Tschirnhaus

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
  exact congrArg Subtype.val
    ((MvPolynomial.mapEquivMonic R _ m).apply_symm_apply (.mk Q hQmon hQdeg))

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

private theorem tschirnhausToDepressed_X_sub_one {R : Type*} [CommRing R] {m : ℕ}
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
  have hGpos : 0 < G.natDegree := by omega
  have hGnext : G.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos hGpos, hGdeg, Polynomial.coeff_map, coeff_genericDepressed,
      ite_eq_right (by omega), dite_eq_right (by omega), map_zero]
  have htaylor : (taylor Polynomial.X G).coeff (m - 1) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
    have htdeg : (taylor Polynomial.X G).natDegree = m := by rw [natDegree_taylor, hGdeg]
    have htpos : 0 < (taylor Polynomial.X G).natDegree := by omega
    have htnext := nextCoeff_of_natDegree_pos htpos
    rw [htdeg] at htnext
    rw [← htnext, nextCoeff_taylor, hGnext, hGdeg, hGmon.leadingCoeff, zero_add, mul_one]
  simpa [tschirnhausToDepressed, G, ← taylor_apply] using htaylor

private theorem tschirnhausToDepressed_tschirnhausNegBarycenter {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    tschirnhausToDepressed R m (tschirnhausNegBarycenter hmu) = Polynomial.X := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : m - 1 < m := by
    rcases m with _ | n
    · rw [Nat.cast_zero] at hmu
      exact absurd hmu not_isUnit_zero
    · omega
  rw [tschirnhausNegBarycenter, dite_eq_left hm, map_smul, tschirnhausToDepressed_X_sub_one hm,
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
  have hm : m - 1 < m := by
    rcases m with _ | n
    · rw [Nat.cast_zero] at hmu
      exact absurd hmu not_isUnit_zero
    · omega
  have hP₀_eq : tschirnhausCentered hmu =
      taylor (-tschirnhausNegBarycenter hmu) (freeMonic R m) := by
    simp [tschirnhausCentered, taylor_apply, sub_eq_add_neg]
  have hP₀_mon : (tschirnhausCentered hmu).Monic := by
    rw [hP₀_eq, Monic.def, leadingCoeff_taylor, (monic_freeMonic R m).leadingCoeff]
  have hP₀_deg : (tschirnhausCentered hmu).natDegree = m := by
    rw [hP₀_eq, natDegree_taylor, natDegree_freeMonic]
  have hP₀_next : (tschirnhausCentered hmu).nextCoeff = 0 := by
    have hfpos : 0 < (freeMonic R m).natDegree := by rw [natDegree_freeMonic]; omega
    rw [hP₀_eq, nextCoeff_taylor, nextCoeff_of_natDegree_pos hfpos, natDegree_freeMonic,
      (monic_freeMonic R m).leadingCoeff, mul_one, coeff_freeMonic, dite_eq_left hm,
      tschirnhausNegBarycenter, dite_eq_left hm, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    calc MvPolynomial.X ⟨m - 1, hm⟩ +
          (m : MvPolynomial (Fin m) R) * -(MvPolynomial.C (↑hmu.unit⁻¹ : R) *
            MvPolynomial.X ⟨m - 1, hm⟩)
      _ = (1 - MvPolynomial.C ((m : R) * (↑hmu.unit⁻¹ : R))) * MvPolynomial.X ⟨m - 1, hm⟩ := by
          simp only [map_mul, map_natCast]
          ring
      _ = 0 := by simp [hmu.mul_val_inv]
  have hbase : (tschirnhausFromDepressed hmu).toRingHom.comp Polynomial.C =
      (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
        (tschirnhausCentered hmu).coeff (m - 2 - (i : ℕ))).toRingHom :=
    RingHom.ext (Polynomial.aevalTower_C _ _)
  rw [hbase]
  exact map_eval_genericDepressed hP₀_mon hP₀_deg hP₀_next

private theorem tschirnhausToDepressed_comp_tschirnhausFromDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (tschirnhausToDepressed R m).comp (tschirnhausFromDepressed hmu) = AlgHom.id R _ := by
  apply Polynomial.algHom_ext'
  · refine MvPolynomial.algHom_ext fun i ↦ ?_
    have hcomp : (tschirnhausCentered hmu).map (tschirnhausToDepressed R m).toRingHom =
        (genericDepressed R m).map Polynomial.C := by
      rw [tschirnhausCentered, Polynomial.map_comp, map_tschirnhausToDepressed_freeMonic]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, tschirnhausToDepressed_tschirnhausNegBarycenter hmu, comp_assoc]
      have hcancel : (Polynomial.X + Polynomial.C Polynomial.X :
            (MvPolynomial (Fin (m - 1)) R)[X][X]).comp
          (Polynomial.X - Polynomial.C Polynomial.X) = Polynomial.X := by
        simp
      rw [hcancel, comp_X]
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
    have hX_inv : tschirnhausFromDepressed hmu Polynomial.X = tschirnhausNegBarycenter hmu := by
      simp [tschirnhausFromDepressed]
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hX_inv, tschirnhausCentered, comp_assoc]
    have hcancel : (Polynomial.X - Polynomial.C (tschirnhausNegBarycenter hmu)).comp
        (Polynomial.X + Polynomial.C (tschirnhausNegBarycenter hmu)) = Polynomial.X := by
      simp
    rw [hcancel, comp_X]
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

/-- Mapping `Polynomial.freeMonic R m` along `TauCeti.tschirnhausAlgEquiv` produces the generic
depressed polynomial translated by `Polynomial.X`. -/
theorem map_tschirnhausAlgEquiv_freeMonic {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (freeMonic R m).map (tschirnhausAlgEquiv hmu).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) :=
  map_tschirnhausToDepressed_freeMonic R m

/-- `TauCeti.tschirnhausAlgEquiv` maps `X k` to the `k`-th coefficient of the shifted generic
depressed polynomial `((genericDepressed R m).map C).comp (X + C X)`. -/
@[simp]
theorem tschirnhausAlgEquiv_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (k : Fin m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X k) =
      (((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X)).coeff k := by
  have h := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦ p.coeff k)
    (map_tschirnhausAlgEquiv_freeMonic hmu)
  rw [Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.isLt] at h
  exact h

/-- `TauCeti.tschirnhausAlgEquiv` maps the subleading coefficient variable `X ⟨m - 1, hm⟩` to
`m * Polynomial.X`. -/
@[simp high]
theorem tschirnhausAlgEquiv_X_sub_one {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (hm : m - 1 < m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X ⟨m - 1, hm⟩) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X :=
  tschirnhausToDepressed_X_sub_one hm

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
@[simp]
theorem tschirnhausAlgEquiv_symm_C_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (i : Fin (m - 1)) :
    (tschirnhausAlgEquiv hmu).symm (Polynomial.C (MvPolynomial.X i)) =
      ((freeMonic R m).comp
        (Polynomial.X - Polynomial.C ((tschirnhausAlgEquiv hmu).symm Polynomial.X))).coeff
        (m - 2 - (i : ℕ)) := by
  have h := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff (m - 2 - (i : ℕ)))
    (map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed hmu)
  simpa [Polynomial.coeff_map, coeff_genericDepressed_sub_two_sub] using h

end Tschirnhaus

end TauCeti
