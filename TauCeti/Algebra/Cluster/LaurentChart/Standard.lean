/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.LaurentChart.FractionRing

/-!
# Canonical total-quotient Laurent charts

Every commutative coefficient ring, including rings with zero divisors, has a canonical
faithful Laurent chart in the total quotient ring of its Laurent algebra. The standard
polynomial total quotient ring is a second model: polynomial variables are regular and hence
become units. Both charts generate their ambient total quotient rings.
-/

public section

namespace TauCeti.LaurentChart

variable {R K B : Type*} [CommRing R] [CommRing B] [Algebra R B]

variable (R K) in
/-- The canonical faithful chart in the total quotient ring of the Laurent algebra. -/
noncomputable def canonical : LaurentChart R K (FractionRing (LaurentRing R K)) where
  toAlgHom := IsScalarTower.toAlgHom R (LaurentRing R K) (FractionRing (LaurentRing R K))
  injective := IsFractionRing.injective _ _

@[simp]
theorem canonical_apply (p : LaurentRing R K) :
    canonical R K p = algebraMap _ (FractionRing (LaurentRing R K)) p := (rfl)

@[simp]
theorem coordinate_canonical (i : K) :
    (canonical R K).coordinate i =
      algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K)) (LaurentRing.X i) := by
  rw [coordinate_def, canonical_apply]

/-- Canonical Laurent values belong to the canonical chart range. -/
@[simp]
theorem algebraMap_mem_range_canonical (p : LaurentRing R K) :
    algebraMap _ (FractionRing (LaurentRing R K)) p ∈ (canonical R K).range :=
  ((canonical R K).mem_range _).mpr ⟨p, canonical_apply p⟩

/-- Canonical Laurent values expand to their original Laurent polynomials. -/
@[simp↓]
theorem laurentExpansion_canonical_algebraMap (p : LaurentRing R K)
    (h : algebraMap _ (FractionRing (LaurentRing R K)) p ∈ (canonical R K).range) :
    (canonical R K).laurentExpansion
      ⟨algebraMap _ (FractionRing (LaurentRing R K)) p, h⟩ = p := by
  simpa only [canonical_apply] using (canonical R K).laurentExpansion_apply p

/-- Canonical Laurent values retain their original coefficient function. -/
@[simp↓]
theorem coeff_canonical_algebraMap (p : LaurentRing R K)
    (h : algebraMap _ (FractionRing (LaurentRing R K)) p ∈ (canonical R K).range) :
    (canonical R K).coeff ⟨algebraMap _ (FractionRing (LaurentRing R K)) p, h⟩ = p.coeff := by
  rw [coeff_def, laurentExpansion_canonical_algebraMap]

/-- The Laurent total quotient chart is generating over every commutative ring. -/
@[simp]
theorem isGenerating_canonical : (canonical R K).IsGenerating := by
  rw [isGenerating_iff_isFractionRing]
  have hm : (canonical R K).toAlgHom.toRingHom =
      algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K)) := by
    apply RingHom.ext
    intro p
    exact canonical_apply p
  rw [hm, toAlgebra_algebraMap]
  infer_instance

/-- The canonical Laurent fraction equivalence is the identity. -/
@[simp]
theorem fractionRingEquiv_canonical :
    (canonical R K).fractionRingEquiv isGenerating_canonical = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext (nonZeroDivisors (LaurentRing R K))
  apply LaurentRing.algHom_ext
  intro i
  simp [Algebra.algHom]

/-- Evaluation through a generating regular chart carries the canonical chart to that chart. -/
@[simp]
theorem map_canonical_fractionRingEquiv (c : LaurentChart R K B) (h : c.IsGenerating) :
    (canonical R K).map (c.fractionRingEquiv h).toAlgHom (c.fractionRingEquiv h).injective = c := by
  ext i
  rw [(canonical R K).coordinate_map (c.fractionRingEquiv h).toAlgHom
    (c.fractionRingEquiv h).injective i, coordinate_canonical]
  simpa only [AlgEquiv.coe_toAlgHom, apply_X] using
    c.fractionRingEquiv_algebraMap h (LaurentRing.X i)

local notation "P" => MvPolynomial K R
local notation "Q" => FractionRing P

/-- Polynomial variables are regular, so their total-quotient images are units. -/
private noncomputable def standardUnit (i : K) : Qˣ :=
  (IsLocalization.map_units Q
    (⟨MvPolynomial.X i, isRegular_iff_mem_nonZeroDivisors.mp
      (MvPolynomial.isRegular_X (n := i))⟩ : nonZeroDivisors P)).unit

private theorem standardUnit_val (i : K) :
    (standardUnit (R := R) i : Q) = algebraMap P Q (MvPolynomial.X i) := by
  exact IsUnit.unit_spec _

variable (R K) in
/-- The faithful Laurent chart in the polynomial total quotient ring, allowing zero divisors. -/
noncomputable def standard : LaurentChart R K Q :=
  ofCoordinates standardUnit <| by
    simpa only [Function.comp_def, standardUnit_val, IsScalarTower.toAlgHom_apply] using
      (MvPolynomial.algebraicIndependent_X K R).map'
        (f := IsScalarTower.toAlgHom R P Q) (IsFractionRing.injective P Q)

@[simp]
theorem coordinate_standard (i : K) :
    (standard R K).coordinate i = algebraMap P Q (MvPolynomial.X i) := by
  simp [standard, standardUnit_val]

/-- On polynomials the standard chart is the canonical total quotient inclusion. -/
theorem standard_comp_toLaurent :
    (standard R K).toAlgHom.comp MvPolynomial.toLaurent = IsScalarTower.toAlgHom R P Q := by
  rw [comp_toLaurent]
  exact MvPolynomial.algHom_ext fun i ↦ by simp

@[simp]
theorem standard_toLaurent (p : P) :
    standard R K (MvPolynomial.toLaurent p) = algebraMap P Q p :=
  DFunLike.congr_fun standard_comp_toLaurent p

/-- Polynomial values belong to the standard Laurent subalgebra. -/
@[simp]
theorem algebraMap_mem_range_standard (p : P) : algebraMap P Q p ∈ (standard R K).range :=
  ((standard R K).mem_range _).mpr ⟨MvPolynomial.toLaurent p, standard_toLaurent p⟩

/-- Standard polynomial values expand as their polynomial-to-Laurent images. -/
@[simp↓]
theorem laurentExpansion_standard_algebraMap (p : P)
    (h : algebraMap P Q p ∈ (standard R K).range) :
    (standard R K).laurentExpansion ⟨algebraMap P Q p, h⟩ = MvPolynomial.toLaurent p := by
  simpa only [standard_toLaurent] using
    (standard R K).laurentExpansion_apply (MvPolynomial.toLaurent p)

/-- Standard polynomial values retain their Laurent coefficient data. -/
@[simp↓]
theorem coeff_standard_algebraMap (p : P) (h : algebraMap P Q p ∈ (standard R K).range) :
    (standard R K).coeff ⟨algebraMap P Q p, h⟩ = (MvPolynomial.toLaurent p).coeff := by
  rw [coeff_def, laurentExpansion_standard_algebraMap]

/-- The polynomial total quotient model is a generating Laurent chart. -/
@[simp]
theorem isGenerating_standard : (standard R K).IsGenerating := by
  rw [isGenerating_iff_isFractionRing]
  let _ := (standard R K).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower P (LaurentRing R K) Q := .of_algebraMap_eq fun p ↦ by
    exact (standard_toLaurent p).symm
  exact IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.closure (Set.range (MvPolynomial.X : K → P))) (LaurentRing R K) Q
    (Submonoid.closure_le.mpr <| by
      rintro p ⟨i, rfl⟩
      exact isRegular_iff_mem_nonZeroDivisors.mp (MvPolynomial.isRegular_X (n := i)))

/-- The polynomial fraction equivalence of the standard chart is the identity. -/
@[simp]
theorem fractionRingMvPolynomialEquiv_standard :
    (standard R K).fractionRingMvPolynomialEquiv isGenerating_standard = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext (nonZeroDivisors P)
  apply MvPolynomial.algHom_ext
  intro i
  simp [Algebra.algHom]

/-- Inverse fraction evaluation of a standard polynomial gives its Laurent class. -/
@[simp↓]
theorem fractionRingEquiv_standard_symm_algebraMap (p : P) :
    ((standard R K).fractionRingEquiv isGenerating_standard).symm (algebraMap P Q p) =
      algebraMap _ (FractionRing (LaurentRing R K)) (MvPolynomial.toLaurent p) := by
  simpa only [standard_toLaurent] using
    (standard R K).fractionRingEquiv_symm_apply isGenerating_standard (MvPolynomial.toLaurent p)

/-- The standard polynomial total quotient chart transports to any generating regular chart. -/
@[simp]
theorem map_standard_fractionRingMvPolynomialEquiv (c : LaurentChart R K B) (h : c.IsGenerating) :
    (standard R K).map (c.fractionRingMvPolynomialEquiv h).toAlgHom
      (c.fractionRingMvPolynomialEquiv h).injective = c := by
  ext i
  rw [(standard R K).coordinate_map (c.fractionRingMvPolynomialEquiv h).toAlgHom
    (c.fractionRingMvPolynomialEquiv h).injective i, coordinate_standard]
  simpa only [AlgEquiv.coe_toAlgHom, MvPolynomial.aeval_X] using
    c.fractionRingMvPolynomialEquiv_algebraMap h (MvPolynomial.X i)

/-- The polynomial fraction model is obtained from the Laurent fraction model through the
standard chart, over arbitrary commutative coefficient rings. -/
theorem fractionRingMvPolynomialEquiv_eq_standard (c : LaurentChart R K B)
    (h : c.IsGenerating) :
    c.fractionRingMvPolynomialEquiv h =
      ((standard R K).fractionRingEquiv isGenerating_standard).symm.trans
        (c.fractionRingEquiv h) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext (nonZeroDivisors P)
  apply MvPolynomial.algHom_ext
  intro i
  simp [Algebra.algHom]

/-- Laurent and polynomial fraction transitions are conjugate by the standard model
equivalences, including when the two coordinate index types differ. -/
theorem fractionRingMvPolynomialTransition_eq_standard {K' : Type*}
    (c : LaurentChart R K B) (d : LaurentChart R K' B)
    (hc : c.IsGenerating) (hd : d.IsGenerating) :
    c.fractionRingMvPolynomialTransition d hc hd =
      ((standard R K).fractionRingEquiv isGenerating_standard).symm.trans
        ((c.fractionRingTransition d hc hd).trans
          ((standard R K').fractionRingEquiv isGenerating_standard)) := by
  rw [fractionRingMvPolynomialTransition_def, fractionRingTransition_def,
    fractionRingMvPolynomialEquiv_eq_standard, fractionRingMvPolynomialEquiv_eq_standard]
  ext x
  simp

section Domain
variable [IsDomain R]

/-- An inverted Laurent variable belongs to the canonical chart range. -/
@[simp]
theorem inv_X_mem_range_canonical (i : K) :
    (algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K))
      (LaurentRing.X i))⁻¹ ∈ (canonical R K).range := by
  simpa only [coordinate_canonical] using (canonical R K).inv_coordinate_mem_range i

/-- An inverted polynomial variable belongs to the standard chart range. -/
@[simp]
theorem inv_X_mem_range_standard (i : K) :
    (algebraMap P Q (MvPolynomial.X i))⁻¹ ∈ (standard R K).range := by
  simpa only [coordinate_standard] using (standard R K).inv_coordinate_mem_range i

/-- A canonical inverse variable expands to its negative basis monomial. -/
@[simp↓]
theorem laurentExpansion_canonical_inv_X (i : K)
    (h : (algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K))
      (LaurentRing.X i))⁻¹ ∈ (canonical R K).range) :
    (canonical R K).laurentExpansion
      ⟨(algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K))
        (LaurentRing.X i))⁻¹, h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinate_canonical] using
    (canonical R K).laurentExpansion_inv_coordinate i
      (by simpa only [coordinate_canonical] using h)

/-- A canonical inverse variable has one coefficient at its negative basis index. -/
@[simp↓]
theorem coeff_canonical_inv_X (i : K)
    (h : (algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K))
      (LaurentRing.X i))⁻¹ ∈ (canonical R K).range) :
    (canonical R K).coeff
      ⟨(algebraMap (LaurentRing R K) (FractionRing (LaurentRing R K))
        (LaurentRing.X i))⁻¹, h⟩ = Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_canonical_inv_X, AddMonoidAlgebra.coeff_single]

/-- An inverted standard variable expands as its negative standard-basis monomial. -/
@[simp↓]
theorem laurentExpansion_standard_inv_X (i : K)
    (h : (algebraMap P Q (MvPolynomial.X i))⁻¹ ∈ (standard R K).range) :
    (standard R K).laurentExpansion ⟨(algebraMap P Q (MvPolynomial.X i))⁻¹, h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinate_standard] using
    (standard R K).laurentExpansion_inv_coordinate i
      (by simpa only [coordinate_standard] using h)

/-- The coefficient of an inverted standard variable is concentrated at its negative basis. -/
@[simp↓]
theorem coeff_standard_inv_X (i : K)
    (h : (algebraMap P Q (MvPolynomial.X i))⁻¹ ∈ (standard R K).range) :
    (standard R K).coeff ⟨(algebraMap P Q (MvPolynomial.X i))⁻¹, h⟩ =
      Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_standard_inv_X, AddMonoidAlgebra.coeff_single]

/-- Inverse fraction evaluation at an inverted standard variable is its negative Laurent class. -/
@[simp↓]
theorem fractionRingEquiv_standard_symm_inv_X (i : K) :
    ((standard R K).fractionRingEquiv isGenerating_standard).symm
        (algebraMap P Q (MvPolynomial.X i))⁻¹ =
      algebraMap _ (FractionRing (LaurentRing R K))
        (AddMonoidAlgebra.single (-Finsupp.single i 1) 1 : LaurentRing R K) := by
  simpa only [coordinate_standard] using
    (standard R K).fractionRingEquiv_symm_apply_inv_coordinate isGenerating_standard i

end Domain

end TauCeti.LaurentChart
