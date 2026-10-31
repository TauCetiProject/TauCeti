/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Rescale
public import TauCeti.RingTheory.PowerSeries.Coordinate.Graded

/-!
# Graded changes of formal group coordinates

A formal group law with coefficient of `Xⁱ Yʲ` in homological degree `w * (i+j-1)`
retains this grading under a coordinate change whose coefficient of `Xⁿ` has degree
`w * (n-1)`. Conversely, a graded coordinate detects whether the original law was graded,
since its inverse is graded as well. The case `w = 2` applies to complex orientations.

The proof expresses the grading through the map to Laurent polynomials and the action of
homotheties. It applies to arbitrary graded coefficient rings, without commutativity of the
formal group law or strictness of the coordinate.
-/

public section

noncomputable section

namespace FormalGroup

open MvPowerSeries TauCeti.FormalCoordinate TauCeti.GradedAlgebra

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A formal group law is graded precisely when its image under the grading homomorphism
is obtained from its constant base change by the homothety `X ↦ T^(-w) X`. -/
theorem map_toLaurent_eq_homothety_smul_iff (F : FormalGroup A) (w : ℕ) :
    F.map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
        homothety (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial A))⁻¹ •
          F.map LaurentPolynomial.C ↔
      ∀ d : Fin 2 →₀ ℕ, coeff d F.toPowerSeries ∈ 𝒜 (w * (d.degree - 1)) := by
  rw [homothety_smul, inv_inv, FormalGroup.ext_iff, MvPowerSeries.ext_iff]
  refine forall_congr' fun d ↦ ?_
  rw [coeff_rescale, map_toPowerSeries, map_toPowerSeries, coeff_map, coeff_map,
    RingHom.comp_apply]
  simp only [unitOfInvertible, Units.val_mk]
  have hp : (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial A) ^ (d.degree - 1) =
      LaurentPolynomial.T (w * (d.degree - 1) : ℕ) := by
    rw [LaurentPolynomial.T_pow]
    congr 1
    push_cast
    ring
  rw [hp, mul_comm, ← Polynomial.toLaurent_C_mul_T, Polynomial.toLaurent_inj,
    toPolynomial_eq_monomial_iff]

/-- Changing by a graded coordinate preserves the homogeneous degrees of a formal group law.
For homological degree two, take `w = 2`. -/
theorem coeff_smul_mem (F : FormalGroup A) (w : ℕ) (φ : TauCeti.FormalCoordinate A)
    (hφ : φ ∈ gradedSubgroup 𝒜 w)
    (hF : ∀ d : Fin 2 →₀ ℕ, coeff d F.toPowerSeries ∈ 𝒜 (w * (d.degree - 1)))
    (d : Fin 2 →₀ ℕ) : coeff d (φ • F).toPowerSeries ∈ 𝒜 (w * (d.degree - 1)) := by
  have hc := (map_toLaurent_eq_conjugate_iff 𝒜 w φ).2
    ((mem_gradedSubgroup 𝒜 w φ).1 hφ)
  have hf := (F.map_toLaurent_eq_homothety_smul_iff (𝒜 := 𝒜) w).2 hF
  apply ((φ • F).map_toLaurent_eq_homothety_smul_iff (𝒜 := 𝒜) w).1 _ d
  rw [map_smul, hc, hf]
  simp only [map_inv, mul_smul, smul_inv_smul, map_smul]

/-- A graded coordinate change preserves and reflects the grading of formal group laws. -/
@[simp]
theorem forall_coeff_smul_mem_iff (F : FormalGroup A) (w : ℕ)
    (φ : TauCeti.FormalCoordinate A) (hφ : φ ∈ gradedSubgroup 𝒜 w) :
    (∀ d : Fin 2 →₀ ℕ, coeff d (φ • F).toPowerSeries ∈ 𝒜 (w * (d.degree - 1))) ↔
      ∀ d : Fin 2 →₀ ℕ, coeff d F.toPowerSeries ∈ 𝒜 (w * (d.degree - 1)) := by
  constructor
  · intro h d
    simpa using (φ • F).coeff_smul_mem w φ⁻¹ ((gradedSubgroup 𝒜 w).inv_mem hφ) h d
  · intro h
    exact F.coeff_smul_mem w φ hφ h

end FormalGroup
