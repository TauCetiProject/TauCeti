/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
public import TauCeti.RingTheory.Polynomial.HermiteInterpolation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The confluent Vandermonde matrix is the matrix of the Hermite jet map

For nodes `a : Fin r → R` and multiplicities `m : Fin r → ℕ` with `M = ∑ i, m i`, the confluent
Vandermonde matrix `Matrix.confluentVandermonde a m` is the matrix of the Hermite jet map
`TauCeti.hermiteJet a m : degreeLT R M →ₗ[R] ∀ i, Fin (m i) → R` in the monomial basis
`Polynomial.degreeLT.basis R M` of the source, `X ^ j` in increasing degree, and the standard basis
of the jet space with the jets `⟨i, k⟩` in the lexicographic order `finSigmaFinEquiv`.

Consequently the Hermite jet map is bijective iff the confluent Vandermonde determinant is a unit.
Over a field this happens iff `a i ≠ a j` whenever `i ≠ j` and `m i`, `m j` are both nonzero, by
`Matrix.det_confluentVandermonde_ne_zero_iff`; injective nodes are a special case, which gives a
second proof of `TauCeti.hermiteJet_bijective` for nodes indexed by `Fin r`, and a repeated node
of multiplicity `0` is allowed.

## Main definitions

* `TauCeti.lexJetBasis R m`: the standard basis of `∀ i, Fin (m i) → R`, indexed by
  `Fin (∑ i, m i)` through `finSigmaFinEquiv`.

## Main statements

* `TauCeti.toMatrix_hermiteJet`: `LinearMap.toMatrix (degreeLT.basis R M) (lexJetBasis R m)
  (hermiteJet a m) = confluentVandermonde a m`.
* `TauCeti.hermiteJet_bijective_iff_isUnit_det`: over a commutative ring, the Hermite jet map is
  bijective iff `det (confluentVandermonde a m)` is a unit.
* `TauCeti.hermiteJet_bijective_iff`: over a field, the Hermite jet map is bijective iff the nodes
  of nonzero multiplicity are pairwise distinct.
-/

public section

noncomputable section

open Function Polynomial

namespace TauCeti

variable (R : Type*) [CommRing R] {r : ℕ}

/-- The standard basis of the jet space `∀ i, Fin (m i) → R`, indexed by `Fin (∑ i, m i)` in the
lexicographic order `finSigmaFinEquiv ⟨i, k⟩` of the jets. -/
def lexJetBasis (m : Fin r → ℕ) : Module.Basis (Fin (∑ i, m i)) R ((i : Fin r) → Fin (m i) → R) :=
  (Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv

/-- The coordinate of a jet datum at the position `ρ` is its entry at the jet
`finSigmaFinEquiv.symm ρ`. -/
@[simp]
theorem lexJetBasis_repr (m : Fin r → ℕ) (c : (i : Fin r) → Fin (m i) → R) (ρ : Fin (∑ i, m i)) :
    (lexJetBasis R m).repr c ρ = c (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 := by
  simp [lexJetBasis]

variable {R}

/-- The confluent Vandermonde matrix is the matrix of the Hermite jet map in the monomial basis
of `degreeLT R (∑ i, m i)` and the lexicographic standard basis of the jet space. -/
theorem toMatrix_hermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m) (hermiteJet a m) =
      Matrix.confluentVandermonde a m := by
  ext ρ j
  rw [LinearMap.toMatrix_apply, lexJetBasis_repr, hermiteJet_apply, degreeLT.basis_val,
    Matrix.confluentVandermonde_apply]

/-- The Hermite jet map is the linear map of the confluent Vandermonde matrix in the monomial and
the lexicographic jet bases. -/
theorem toLin_confluentVandermonde (a : Fin r → R) (m : Fin r → ℕ) :
    Matrix.toLin (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m)
      (Matrix.confluentVandermonde a m) = hermiteJet a m := by
  rw [← toMatrix_hermiteJet, Matrix.toLin_toMatrix]

/-- The Hermite jet map is bijective iff the confluent Vandermonde determinant is a unit. -/
theorem hermiteJet_bijective_iff_isUnit_det (a : Fin r → R) (m : Fin r → ℕ) :
    Bijective (hermiteJet a m) ↔ IsUnit (Matrix.confluentVandermonde a m).det := by
  set v₁ := degreeLT.basis R (∑ i, m i)
  set v₂ := lexJetBasis R m
  have h : (v₂.equivFun ∘ hermiteJet a m) ∘ v₁.equivFun.symm =
      (Matrix.confluentVandermonde a m).mulVec := by
    ext x ρ
    have := LinearMap.toMatrix_mulVec_repr v₁ v₂ (hermiteJet a m) (v₁.equivFun.symm x)
    rw [toMatrix_hermiteJet] at this
    simp only [comp_apply, Module.Basis.equivFun_apply]
    rw [← this, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← EquivLike.comp_bijective _ v₂.equivFun, ← EquivLike.bijective_comp v₁.equivFun.symm, h,
    ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun hb => Matrix.mulVec_surjective_iff_isUnit.1 hb.2,
    fun hu => ⟨Matrix.mulVec_injective_of_isUnit hu, Matrix.mulVec_surjective_iff_isUnit.2 hu⟩⟩

/-- Over a field, the Hermite jet map is bijective iff the nodes of nonzero multiplicity are
pairwise distinct. A repeated node of multiplicity `0` is allowed. -/
theorem hermiteJet_bijective_iff {K : Type*} [Field K] (a : Fin r → K) (m : Fin r → ℕ) :
    Bijective (hermiteJet a m) ↔ ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  rw [hermiteJet_bijective_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_confluentVandermonde_ne_zero_iff]

/-! ### Checks -/

section Checks

/-- The matrix of the Hermite jet map at the double node `0` and the simple node `1`. -/
example : LinearMap.toMatrix (degreeLT.basis ℤ (∑ i, ![2, 1] i)) (lexJetBasis ℤ ![2, 1])
    (hermiteJet ![(0 : ℤ), 1] ![2, 1]) = !![1, 0, 0; 0, 1, 0; 1, 1, 1] := by
  rw [toMatrix_hermiteJet]
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [Matrix.confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

/-- The nodes `(1, 0)` give the matrix `[[1, 1], [1, 0]]`, whose determinant `-1` pins the sign. -/
example : LinearMap.toMatrix (degreeLT.basis ℤ (∑ i, ![1, 1] i)) (lexJetBasis ℤ ![1, 1])
    (hermiteJet ![(1 : ℤ), 0] ![1, 1]) = !![1, 1; 1, 0] := by
  rw [toMatrix_hermiteJet]
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [Matrix.confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

/-- A repeated node of multiplicity `0` does not obstruct interpolation: the nodes `(0, 0, 1)`
are not injective, yet the Hermite jet map for the multiplicities `(1, 0, 1)` is bijective. -/
example : ¬ Injective ![(0 : ℚ), 0, 1] ∧ Bijective (hermiteJet ![(0 : ℚ), 0, 1] ![1, 0, 1]) := by
  refine ⟨fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide), ?_⟩
  rw [hermiteJet_bijective_iff]
  decide

/-- A repeated simple node: the Hermite jet map for `a = (0, 0)` and `m = (1, 1)` is not
bijective. -/
example : ¬ Bijective (hermiteJet ![(0 : ℚ), 0] ![1, 1]) := by
  rw [hermiteJet_bijective_iff]
  intro h
  exact h 0 1 (by decide) (by decide) (by decide) rfl

end Checks

end TauCeti
