/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.HermiteInterpolation
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The confluent Vandermonde matrix is the matrix of the Hermite jet map

For nodes `a : Fin r → R` and multiplicities `m : Fin r → ℕ` with `M = ∑ i, m i`, the confluent
Vandermonde matrix `Matrix.confluentVandermonde a m` is the matrix of the Hermite jet map
`Polynomial.hermiteJet a m : degreeLT R M →ₗ[R] ∀ i, Fin (m i) → R` in the monomial basis
`Polynomial.degreeLT.basis R M` of the source, `X ^ j` in increasing degree, and the standard basis
of the jet space with the jets `⟨i, k⟩` in the lexicographic order `finSigmaFinEquiv`.

Consequently the Hermite jet map is bijective iff the confluent Vandermonde determinant is a unit.
Over a field this happens iff `a i ≠ a j` whenever `i ≠ j` and `m i`, `m j` are both nonzero, by
`Matrix.det_confluentVandermonde_ne_zero_iff`; injective nodes are a special case, which gives a
second proof of `Polynomial.hermiteJet_bijective` for nodes indexed by `Fin r`, and a repeated node
of multiplicity `0` is allowed. For the ordinary-derivative jet map `Polynomial.ordinaryHermiteJet`,
row `⟨i, k⟩` is scaled by `k !`, so bijectivity over a field additionally requires `k ! ≠ 0` for
every `k < m i`.

## Main definitions

* `Polynomial.lexJetBasis R m`: the standard basis of `∀ i, Fin (m i) → R`, indexed by
  `Fin (∑ i, m i)` through `finSigmaFinEquiv`.

## Main statements

* `Polynomial.toMatrix_hermiteJet`, `Polynomial.toLin_confluentVandermonde`:
  `LinearMap.toMatrix (degreeLT.basis R M) (lexJetBasis R m) (hermiteJet a m) =
  Matrix.confluentVandermonde a m`.
* `Polynomial.toMatrix_ordinaryHermiteJet`, `Polynomial.det_toMatrix_ordinaryHermiteJet`: the
  matrix of `ordinaryHermiteJet a m` and its determinant
  `(∏ i, ∏ k ∈ range (m i), k !) * det (confluentVandermonde a m)`.
* `Polynomial.hermiteJet_bijective_iff_isUnit_det`,
  `Polynomial.ordinaryHermiteJet_bijective_iff_isUnit_det`: over a commutative ring, bijectivity is
  unitness of the corresponding determinant.
* `Polynomial.hermiteJet_bijective_iff`, `Polynomial.ordinaryHermiteJet_bijective_iff`: the
  necessary and sufficient conditions over a field.
-/

public section

noncomputable section

open Function
open scoped Nat

namespace Polynomial

section Semiring

variable (R : Type*) [Semiring R] {r : ℕ}

/-- The standard basis of the jet space `∀ i, Fin (m i) → R`, indexed by `Fin (∑ i, m i)` in the
lexicographic order `finSigmaFinEquiv ⟨i, k⟩` of the jets. -/
def lexJetBasis (m : Fin r → ℕ) : Module.Basis (Fin (∑ i, m i)) R (∀ i, Fin (m i) → R) :=
  (Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv

/-- The coordinate of a jet datum at the position `ρ` is its entry at the jet
`finSigmaFinEquiv.symm ρ`. -/
@[simp]
theorem lexJetBasis_repr (m : Fin r → ℕ) (c : ∀ i, Fin (m i) → R) (ρ : Fin (∑ i, m i)) :
    (lexJetBasis R m).repr c ρ = c (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 := by
  simp [lexJetBasis]

end Semiring

section CommRing

variable {R : Type*} [CommRing R] {r : ℕ}

/-- The confluent Vandermonde matrix is the matrix of the Hermite jet map in the monomial basis
of `degreeLT R (∑ i, m i)` and the lexicographic standard basis of the jet space. -/
theorem toMatrix_hermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m) (hermiteJet a m) =
      Matrix.confluentVandermonde a m := by
  ext ρ j
  rw [LinearMap.toMatrix_apply, lexJetBasis_repr, hermiteJet_apply, hasseJet_apply,
    degreeLT.basis_val, Matrix.confluentVandermonde_apply]

/-- The Hermite jet map is the linear map of the confluent Vandermonde matrix in the monomial and
the lexicographic jet bases. -/
theorem toLin_confluentVandermonde (a : Fin r → R) (m : Fin r → ℕ) :
    Matrix.toLin (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m)
      (Matrix.confluentVandermonde a m) = hermiteJet a m := by
  rw [← toMatrix_hermiteJet, Matrix.toLin_toMatrix]

/-- The matrix of the ordinary Hermite jet map in the monomial and lexicographic jet bases is the
confluent Vandermonde matrix with row `ρ` scaled by `((finSigmaFinEquiv.symm ρ).2) !`. -/
theorem toMatrix_ordinaryHermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m)
      (ordinaryHermiteJet a m) =
    Matrix.diagonal (fun ρ => (((finSigmaFinEquiv.symm ρ).2 : ℕ) ! : R)) *
      Matrix.confluentVandermonde a m := by
  ext ρ j
  rw [LinearMap.toMatrix_apply, lexJetBasis_repr, ordinaryHermiteJet_eq_factorial_mul,
    Matrix.diagonal_mul, ← toMatrix_hermiteJet, LinearMap.toMatrix_apply, lexJetBasis_repr]

/-- The determinant of the matrix of the ordinary Hermite jet map is
`(∏ i, ∏ k ∈ range (m i), k !) * det (confluentVandermonde a m)`. -/
theorem det_toMatrix_ordinaryHermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    (LinearMap.toMatrix (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m)
      (ordinaryHermiteJet a m)).det =
    (∏ i, ∏ k ∈ Finset.range (m i), (k ! : R)) * (Matrix.confluentVandermonde a m).det := by
  rw [toMatrix_ordinaryHermiteJet, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  rw [finSigmaFinEquiv.symm.prod_comp (fun x => ((x.2 : ℕ) ! : R)), Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range (fun k => (k ! : R)) (m i)

private theorem bijective_iff_isUnit_det_toMatrix {M₁ M₂ n : Type*} [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup M₂] [Module R M₂] [Fintype n] [DecidableEq n]
    (v₁ : Module.Basis n R M₁) (v₂ : Module.Basis n R M₂) (f : M₁ →ₗ[R] M₂) :
    Bijective f ↔ IsUnit (LinearMap.toMatrix v₁ v₂ f).det := by
  have h : (v₂.equivFun ∘ f) ∘ v₁.equivFun.symm = (LinearMap.toMatrix v₁ v₂ f).mulVec := by
    ext x i
    have := LinearMap.toMatrix_mulVec_repr v₁ v₂ f (v₁.equivFun.symm x)
    simp only [comp_apply, Module.Basis.equivFun_apply]
    rw [← this, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← EquivLike.comp_bijective _ v₂.equivFun, ← EquivLike.bijective_comp v₁.equivFun.symm, h,
    ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun hb => Matrix.mulVec_surjective_iff_isUnit.1 hb.2,
    fun hu => ⟨Matrix.mulVec_injective_of_isUnit hu, Matrix.mulVec_surjective_iff_isUnit.2 hu⟩⟩

/-- The Hermite jet map is bijective iff the confluent Vandermonde determinant is a unit. -/
theorem hermiteJet_bijective_iff_isUnit_det (a : Fin r → R) (m : Fin r → ℕ) :
    Bijective (hermiteJet a m) ↔ IsUnit (Matrix.confluentVandermonde a m).det := by
  rw [bijective_iff_isUnit_det_toMatrix (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m),
    toMatrix_hermiteJet]

/-- The ordinary Hermite jet map is bijective iff
`(∏ i, ∏ k ∈ range (m i), k !) * det (confluentVandermonde a m)` is a unit. -/
theorem ordinaryHermiteJet_bijective_iff_isUnit_det (a : Fin r → R) (m : Fin r → ℕ) :
    Bijective (ordinaryHermiteJet a m) ↔
      IsUnit ((∏ i, ∏ k ∈ Finset.range (m i), (k ! : R)) *
        (Matrix.confluentVandermonde a m).det) := by
  rw [bijective_iff_isUnit_det_toMatrix (degreeLT.basis R (∑ i, m i)) (lexJetBasis R m),
    det_toMatrix_ordinaryHermiteJet]

end CommRing

section Field

variable {K : Type*} [Field K] {r : ℕ}

/-- Over a field, the Hermite jet map is bijective iff the nodes of nonzero multiplicity are
pairwise distinct. A repeated node of multiplicity `0` is allowed. -/
theorem hermiteJet_bijective_iff (a : Fin r → K) (m : Fin r → ℕ) :
    Bijective (hermiteJet a m) ↔ ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  rw [hermiteJet_bijective_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_confluentVandermonde_ne_zero_iff]

/-- Over a field, the ordinary Hermite jet map is bijective iff `k ! ≠ 0` in `K` for every
`k < m i` and the nodes of nonzero multiplicity are pairwise distinct. -/
theorem ordinaryHermiteJet_bijective_iff (a : Fin r → K) (m : Fin r → ℕ) :
    Bijective (ordinaryHermiteJet a m) ↔
      (∀ i, ∀ k < m i, (k ! : K) ≠ 0) ∧
        (∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j) := by
  simp [ordinaryHermiteJet_bijective_iff_isUnit_det, isUnit_iff_ne_zero,
    Finset.prod_eq_zero_iff, not_or, Matrix.det_confluentVandermonde_ne_zero_iff]

end Field

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
are not injective, yet both jet maps for the multiplicities `(1, 0, 2)` over `ℚ` are bijective. -/
example : ¬ Injective ![(0 : ℚ), 0, 1] ∧ Bijective (hermiteJet ![(0 : ℚ), 0, 1] ![1, 0, 2]) ∧
    Bijective (ordinaryHermiteJet ![(0 : ℚ), 0, 1] ![1, 0, 2]) := by
  refine ⟨fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide), ?_, ?_⟩
  · rw [hermiteJet_bijective_iff]
    decide
  · rw [ordinaryHermiteJet_bijective_iff]
    refine ⟨fun i k hk => ?_, by decide⟩
    fin_cases i <;> simp_all [Nat.factorial_ne_zero]

/-- A repeated simple node: the Hermite jet map for `a = (0, 0)` and `m = (1, 1)` is not
bijective. -/
example : ¬ Bijective (hermiteJet ![(0 : ℚ), 0] ![1, 1]) := by
  rw [hermiteJet_bijective_iff]
  intro h
  exact h 0 1 (by decide) (by decide) (by decide) rfl

/-- Over `ZMod 2`, `ordinaryHermiteJet` is bijective for multiplicity `2` at `0` (`0! = 1` and
`1! = 1`) and not bijective for multiplicity `3` (`2! = 0`). -/
example : Bijective (ordinaryHermiteJet ![(0 : ZMod 2)] ![2]) ∧
    ¬ Bijective (ordinaryHermiteJet ![(0 : ZMod 2)] ![3]) := by
  rw [ordinaryHermiteJet_bijective_iff_isUnit_det, ordinaryHermiteJet_bijective_iff_isUnit_det,
    Matrix.det_confluentVandermonde, Matrix.det_confluentVandermonde]
  decide

end Checks

end Polynomial
