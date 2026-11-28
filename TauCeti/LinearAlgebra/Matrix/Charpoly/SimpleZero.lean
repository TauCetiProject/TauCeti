/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Charpoly.Block

/-!
# Matrices with a simple zero modulo a maximal ideal

Let `R` be a local ring and `K` an `R`-algebra; the case in view is the ring of integers
`R = 𝒪_w` of the completion `K = E_w` of a number field at a finite place `w`. A square matrix `g`
over `K` has a **simple zero** (`Matrix.HasSimpleZero R g`) if its entries come from `R` and `0`
is a simple root of the characteristic polynomial of its reduction modulo the maximal ideal. In
the comparison of traces for unitary groups this is the local condition imposed at an auxiliary
place on the support of a test function.

Over any commutative ring, `0` is a simple root of the characteristic polynomial of `M` exactly when
`det M = 0` and the linear coefficient of the characteristic polynomial is nonzero
(`Matrix.rootMultiplicity_zero_charpoly_eq_one_iff`). If the column `i` of `M` is zero, this holds
exactly when the square block on the other indices has nonzero determinant
(`Matrix.rootMultiplicity_zero_charpoly_eq_one_iff_det_toSquareBlockProp_ne_zero`). Reduced modulo
the maximal ideal, a simple zero means that `det M` lies in the maximal ideal and the linear
coefficient of the characteristic polynomial is a unit (`Matrix.hasSimpleZero_iff`).

The property is invariant under conjugation by `GL_n(R)` (`Matrix.hasSimpleZero_conj_iff`). It
holds for `diag(ϖ, 1, …, 1)` with `ϖ` in the maximal ideal
(`Matrix.hasSimpleZero_diagonal_mulSingle`), and more generally whenever modulo the maximal ideal
one column vanishes and the complementary block is invertible
(`Matrix.HasSimpleZero.of_forall_mem_maximalIdeal`). If `K` is a domain, the characteristic
polynomial of a matrix with a simple zero is not a proper power over `K`
(`Matrix.HasSimpleZero.charpoly_ne_pow`): up to a root of unity, a `j`-th root of a monic
polynomial over `R` has coefficients in the integral closure of `R` in the fraction field of `K`,
and modulo a maximal ideal of that closure lying over the maximal ideal of `R` every root of a
`j`-th power has multiplicity divisible by `j`.

## Main definitions

* `Matrix.HasSimpleZero R g`: the entries of `g` come from `R`, and `0` is a simple root of the
  characteristic polynomial of the reduction of `g` modulo the maximal ideal of `R`.

## Main results

* `Matrix.hasSimpleZero_iff`: `g` has a simple zero exactly when it comes from a matrix `M` over `R`
  with `det M` in the maximal ideal and a unit linear coefficient of the characteristic polynomial.
  The simp lemmas `Matrix.hasSimpleZero_map_iff` and `Matrix.hasSimpleZero_self_iff` state this for
  the image of a given `M`, and for `M` itself over `R`.
* `Matrix.hasSimpleZero_conj_iff`: conjugation by `GL_n(R)` preserves simple zeros.
* `Matrix.HasSimpleZero.of_forall_mem_maximalIdeal`, `Matrix.hasSimpleZero_diagonal_mulSingle`:
  matrices of block shape `(0 ∗; 0 g')` modulo the maximal ideal, with `g'` invertible, have a
  simple zero.
* `Matrix.HasSimpleZero.charpoly_ne_pow`: over a domain, the characteristic polynomial of a matrix
  with a simple zero is no `j`-th power for `j > 1`.

## References

The definition and the statements `HasSimpleZero.charpoly_ne_pow` and the block-shape criterion
follow `New.HasSimpleZero`, `New.HasSimpleZero.charpoly_ne_pow` and
`New.KeepsLine.rootMultiplicity_charpoly` in
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), files
`src/Lib/Adelic/TraceFormula/TestFunction.lean` and `src/Lib/Adelic/TraceFormula/LineCount.lean`.
-/

public section

open Polynomial IsLocalRing

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R]

/-- `0` is a simple root of the characteristic polynomial of `M` exactly when `det M = 0` and the
linear coefficient of the characteristic polynomial is nonzero. -/
theorem rootMultiplicity_zero_charpoly_eq_one_iff (M : Matrix n n R) :
    M.charpoly.rootMultiplicity 0 = 1 ↔ M.det = 0 ∧ M.charpoly.coeff 1 ≠ 0 := by
  rw [rootMultiplicity_zero_eq_one_iff, det_eq_sign_charpoly_coeff, neg_one_pow_mul_eq_zero_iff]

/-- If the column `i` of `M` is zero, then `0` is a simple root of the characteristic polynomial of
`M` exactly when the square block of `M` on the indices other than `i` has nonzero determinant. -/
theorem rootMultiplicity_zero_charpoly_eq_one_iff_det_toSquareBlockProp_ne_zero
    {M : Matrix n n R} {i : n} (hM : ∀ j, M j i = 0) :
    M.charpoly.rootMultiplicity 0 = 1 ↔ (M.toSquareBlockProp (· ≠ i)).det ≠ 0 := by
  -- The characteristic polynomial is `X` times that of the block.
  rw [charpoly_eq_X_sub_C_mul_charpoly_toSquareBlockProp fun j _ ↦ hM j, hM i, C_0, sub_zero,
    rootMultiplicity_zero_eq_one_iff, ← zero_add 1, coeff_X_mul, det_eq_sign_charpoly_coeff]
  simp only [coeff_X_mul_zero, true_and, Ne, neg_one_pow_mul_eq_zero_iff]

end CommRing

section LocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- For a matrix `M` over a local ring, `0` is a simple root of the characteristic polynomial of the
reduction of `M` modulo the maximal ideal exactly when `det M` lies in the maximal ideal and the
linear coefficient of the characteristic polynomial of `M` is a unit. -/
theorem rootMultiplicity_zero_charpoly_map_residue_eq_one_iff (M : Matrix n n R) :
    (M.map (residue R)).charpoly.rootMultiplicity 0 = 1 ↔
      M.det ∈ maximalIdeal R ∧ IsUnit (M.charpoly.coeff 1) := by
  have h_det : (M.map (residue R)).det = residue R M.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [rootMultiplicity_zero_charpoly_eq_one_iff, h_det, residue_eq_zero_iff, charpoly_map,
    coeff_map, residue_ne_zero_iff_isUnit]

variable (R) {K : Type*} [CommRing K] [Algebra R K]

/-- A square matrix `g` over an algebra `K` of a local ring `R` has a **simple zero** (modulo the
maximal ideal of `R`) if it is the image of a matrix `M` over `R` such that `0` is a simple root of
the characteristic polynomial of the reduction of `M` modulo the maximal ideal. For the ring of
integers `R = 𝒪_w` of the completion `K = E_w` of a number field at a finite place `w`, this says
that `g` has entries in `𝒪_w` and a simple zero at `w`. -/
def HasSimpleZero (g : Matrix n n K) : Prop :=
  ∃ M : Matrix n n R, M.map (algebraMap R K) = g ∧
    (M.map (residue R)).charpoly.rootMultiplicity 0 = 1

variable {R}

/-- Unfolding `Matrix.HasSimpleZero`. -/
theorem hasSimpleZero_def {g : Matrix n n K} :
    HasSimpleZero R g ↔ ∃ M : Matrix n n R, M.map (algebraMap R K) = g ∧
      (M.map (residue R)).charpoly.rootMultiplicity 0 = 1 :=
  Iff.rfl

/-- A matrix has a simple zero exactly when it is the image of a matrix `M` over `R` whose
determinant lies in the maximal ideal and whose characteristic polynomial has a unit linear
coefficient. -/
theorem hasSimpleZero_iff {g : Matrix n n K} :
    HasSimpleZero R g ↔ ∃ M : Matrix n n R, M.map (algebraMap R K) = g ∧
      M.det ∈ maximalIdeal R ∧ IsUnit (M.charpoly.coeff 1) := by
  simp only [hasSimpleZero_def, rootMultiplicity_zero_charpoly_map_residue_eq_one_iff]

/-- If `K` is nontrivial, the image of a matrix `M` over `R` has a simple zero exactly when `det M`
lies in the maximal ideal and the characteristic polynomial of `M` has a unit linear coefficient. -/
@[simp]
theorem hasSimpleZero_map_iff [Nontrivial K] {M : Matrix n n R} :
    HasSimpleZero R (M.map (algebraMap R K)) ↔
      M.det ∈ maximalIdeal R ∧ IsUnit (M.charpoly.coeff 1) := by
  rw [← rootMultiplicity_zero_charpoly_map_residue_eq_one_iff]
  refine ⟨fun ⟨M', hM', h⟩ ↦ ?_, fun h ↦ ⟨M, rfl, h⟩⟩
  -- The kernel of `R → K` is a proper ideal, so two lifts of `g` have the same reduction.
  have h_ker : RingHom.ker (algebraMap R K) ≤ maximalIdeal R :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have h_red : M'.map (residue R) = M.map (residue R) := by
    ext a b
    rw [map_apply, map_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine h_ker ?_
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congr_fun (congr_fun hM' a) b
  rwa [← h_red]

/-- A matrix `M` over the local ring `R` itself has a simple zero exactly when `det M` lies in the
maximal ideal and its characteristic polynomial has a unit linear coefficient. -/
@[simp]
theorem hasSimpleZero_self_iff {M : Matrix n n R} :
    HasSimpleZero R M ↔ M.det ∈ maximalIdeal R ∧ IsUnit (M.charpoly.coeff 1) := by
  simpa using hasSimpleZero_map_iff (K := R) (M := M)

/-- Conjugating a matrix with a simple zero by an element of `GL_n(R)` gives a matrix with a simple
zero. -/
theorem HasSimpleZero.conj {g : Matrix n n K} (hg : HasSimpleZero R g) (k : GL n R) :
    HasSimpleZero R ((k : Matrix n n R).map (algebraMap R K) * g *
      ((k : Matrix n n R).map (algebraMap R K))⁻¹) := by
  obtain ⟨M, rfl, hM⟩ := hg
  rw [← GeneralLinearGroup.val_map_apply, ← coe_units_inv, ← map_inv]
  refine ⟨(k : Matrix n n R) * M * (k⁻¹ : GL n R), ?_, ?_⟩
  · simp only [Matrix.map_mul, GeneralLinearGroup.val_map_apply]
  -- Modulo the maximal ideal the conjugate has the same characteristic polynomial.
  rwa [Matrix.map_mul, Matrix.map_mul, ← GeneralLinearGroup.val_map_apply,
    ← GeneralLinearGroup.val_map_apply, map_inv, coe_units_inv, charpoly_units_conj]

/-- Conjugation by an element of `GL_n(R)` preserves and reflects simple zeros. -/
@[simp]
theorem hasSimpleZero_conj_iff {g : Matrix n n K} (k : GL n R) :
    HasSimpleZero R ((k : Matrix n n R).map (algebraMap R K) * g *
      ((k : Matrix n n R).map (algebraMap R K))⁻¹) ↔ HasSimpleZero R g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj k⟩
  convert h.conj k⁻¹ using 1
  simp only [← GeneralLinearGroup.val_map_apply, ← coe_units_inv, map_inv, inv_inv, mul_assoc,
    Units.inv_mul, Units.inv_mul_cancel_left, mul_one]

/-- **Block criterion.** Let `M` be a matrix over `R` whose column `i` lies in the maximal ideal,
and whose square block on the indices other than `i` has a unit determinant. Modulo the maximal
ideal `M` has the block shape `(0 ∗; 0 g')` with `g'` invertible, and its image in `K` has a simple
zero. -/
theorem HasSimpleZero.of_forall_mem_maximalIdeal {M : Matrix n n R} {i : n}
    (hM : ∀ j, M j i ∈ maximalIdeal R) (h_det : IsUnit (M.toSquareBlockProp (· ≠ i)).det) :
    HasSimpleZero R (M.map (algebraMap R K)) := by
  have h_col (j : n) : M.map (residue R) j i = 0 := by
    rw [map_apply, residue_eq_zero_iff]
    exact hM j
  refine ⟨M, rfl,
    (rootMultiplicity_zero_charpoly_eq_one_iff_det_toSquareBlockProp_ne_zero h_col).2 ?_⟩
  exact isUnit_iff_ne_zero.mp (h_det.det_map_toSquareBlockProp (residue R))

/-- For `ϖ` in the maximal ideal of `R`, the diagonal matrix `diag(1, …, ϖ, …, 1)`, with `ϖ` at the
index `i`, has a simple zero. -/
theorem hasSimpleZero_diagonal_mulSingle {ϖ : R} (hϖ : ϖ ∈ maximalIdeal R) (i : n) :
    HasSimpleZero R (diagonal (Pi.mulSingle i (algebraMap R K ϖ))) := by
  have h_map : (diagonal (Pi.mulSingle i ϖ)).map (algebraMap R K) =
      diagonal (Pi.mulSingle i (algebraMap R K ϖ)) := by
    rw [diagonal_map (map_zero _)]
    congr 1
    ext j
    exact Pi.apply_mulSingle (fun _ ↦ algebraMap R K) (fun _ ↦ map_one _) i ϖ j
  rw [← h_map]
  refine HasSimpleZero.of_forall_mem_maximalIdeal (i := i) (fun j ↦ ?_) ?_
  · obtain rfl | hj := eq_or_ne j i
    · simpa using hϖ
    · simp [diagonal_apply_ne _ hj]
  · -- The block on the indices other than `i` is the identity matrix.
    have h_block : ((diagonal (Pi.mulSingle i ϖ)).toSquareBlockProp (· ≠ i)).det = 1 := by
      rw [toSquareBlockProp, toBlock_diagonal_self, det_diagonal]
      exact Finset.prod_eq_one fun j _ ↦ Pi.mulSingle_eq_of_ne j.property _
    rw [h_block]
    exact isUnit_one

end LocalRing

section Domain

variable {R K : Type*} [CommRing R] [IsLocalRing R] [CommRing K] [IsDomain K] [Algebra R K]

/-- If `K` is a domain, the characteristic polynomial of a matrix with a simple zero is not a
`j`-th power over `K` for any `j > 1`. -/
theorem HasSimpleZero.charpoly_ne_pow {g : Matrix n n K} (hg : HasSimpleZero R g) (Q : K[X])
    {j : ℕ} (hj : 1 < j) : g.charpoly ≠ Q ^ j := by
  classical
  intro h_pow
  obtain ⟨M, rfl, hM⟩ := hg
  -- Pass to the fraction field `L` of `K`.
  set L := FractionRing K
  set Q' := Q.map (algebraMap K L)
  have h_map : M.charpoly.map (algebraMap R L) = Q' ^ j := by
    rw [IsScalarTower.algebraMap_eq R K L, ← Polynomial.map_map, ← charpoly_map, h_pow,
      Polynomial.map_pow]
  -- The leading coefficient of `Q'` is a `j`-th root of unity, so `Q'` is monic up to a unit.
  have hQ : Q' ≠ 0 := by
    rintro h
    rw [h, zero_pow (by omega)] at h_map
    exact (M.charpoly_monic.map _).ne_zero h_map
  have h_lead : Q'.leadingCoeff ^ j = 1 := by
    rw [← leadingCoeff_pow, ← h_map, (M.charpoly_monic.map _).leadingCoeff]
  have h_map₀ : M.charpoly.map (algebraMap R L) = (Q' * C Q'.leadingCoeff⁻¹) ^ j := by
    rw [mul_pow, ← C_pow, inv_pow, h_lead, inv_one, C_1, mul_one, h_map]
  -- Dividing a monic polynomial over `R`, the monic polynomial `Q' / lc(Q')` is integral over `R`.
  obtain ⟨P, hP⟩ := integralClosure.mem_lifts_of_monic_of_dvd_map L M.charpoly_monic
    (monic_mul_leadingCoeff_inv hQ) (h_map₀ ▸ dvd_pow_self _ (by omega))
  have h_int : M.charpoly.map (algebraMap R (integralClosure R L)) = P ^ j := by
    refine Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective (integralClosure R L) L) ?_
    rw [coe_mapRingHom] at hP
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_pow, hP, h_map₀]
  -- Reduce modulo a maximal ideal of the integral closure lying over that of `R`.
  obtain ⟨𝔓, h𝔓, h_under⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure R L) (maximalIdeal R) (le_maximalIdeal (RingHom.ker_ne_top _))
  let f := (Ideal.Quotient.mk 𝔓).comp (algebraMap R (integralClosure R L))
  have h_red : (M.map f).charpoly.rootMultiplicity 0 = 1 := by
    obtain ⟨h_det, h_unit⟩ := (rootMultiplicity_zero_charpoly_map_residue_eq_one_iff M).1 hM
    rw [rootMultiplicity_zero_charpoly_eq_one_iff, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      RingHom.mapMatrix_apply, charpoly_map, coeff_map]
    refine ⟨Ideal.Quotient.eq_zero_iff_mem.2 ?_, (h_unit.map f).ne_zero⟩
    rw [← h_under] at h_det
    exact h_det
  -- Over the field `𝒪 / 𝔓` every root of a `j`-th power has multiplicity divisible by `j`.
  have h_count : j * (P.map (Ideal.Quotient.mk 𝔓)).roots.count 0 = 1 := by
    rw [← Multiset.count_nsmul, ← roots_pow, ← Polynomial.map_pow, ← h_int, Polynomial.map_map,
      ← charpoly_map, count_roots, h_red]
  exact hj.ne' (Nat.eq_one_of_mul_eq_one_right h_count)

end Domain

end Matrix
