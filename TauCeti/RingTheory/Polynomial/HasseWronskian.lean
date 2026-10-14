/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# The Wronskian of a family of polynomials built from Hasse derivatives

For a family `g : Fin m → R[X]` of one-variable polynomials over a commutative ring, the
*Hasse Wronskian* is the determinant `det (Dᵏ gₗ)` of the `m × m` matrix whose `(k, l)` entry is
the `k`-th Hasse (divided) derivative of `gₗ`; the rows are the derivative orders `0 ≤ k < m` and
the columns are the members of the family. Multiplying it by `∏ k < m, k!` gives the classical
Wronskian `det (gₗ⁽ᵏ⁾)`, but the divided version has the advantage of being defined and
integral over any commutative ring. Mathlib's `Polynomial.wronskian` is the case of two
polynomials.

Over an integral domain a linearly dependent family has vanishing Hasse Wronskian. Over a field of
characteristic zero the converse holds, so linear independence is equivalent to nonvanishing of
the Hasse Wronskian. The proof of the converse reduces, by column operations that do not change
the determinant, to a family of polynomials of pairwise distinct degrees. For such a family the
coefficient of the determinant in the top possible degree is the product of the leading
coefficients times a Vandermonde determinant in the degrees, which is nonzero in characteristic
zero. In positive characteristic the converse fails: over `𝔽₂` the polynomials `1` and `X²` are
independent, but `D¹ (X²) = 2X = 0`.

This is the one-variable Wronskian used in the proof of Roth's lemma on the index of auxiliary
polynomials.

## Main definitions

* `Polynomial.hasseWronskian g`: the determinant of the Hasse derivatives `Dᵏ gₗ`, `k, l < m`.

## Main results

* `Polynomial.hasseWronskian_fin_two`: for two polynomials it is Mathlib's `wronskian`.
* `Polynomial.prod_factorial_mul_hasseWronskian`: `(∏ k, k!) W(g) = det (derivative^[k] gₗ)`.
* `Polynomial.hasseWronskian_comp_perm`: permuting the family multiplies `W(g)` by the sign.
* `Polynomial.hasseWronskian_map`: `W(g)` commutes with maps of coefficient rings.
* `Polynomial.hasseWronskian_eq_zero_of_not_linearIndependent`: over an integral domain,
  dependent families have vanishing Hasse Wronskian.
* `Polynomial.linearIndependent_iff_hasseWronskian_ne_zero`: over a field of characteristic
  zero, a family is linearly independent if and only if its Hasse Wronskian is nonzero.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3:
  Definition 3.3.1, Lemma 3.3.2, Proposition 3.3.3 and Remark 3.3.6.
-/

public section

noncomputable section

namespace Polynomial

open Matrix Finset

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- The Hasse Wronskian of a family `g : Fin m → R[X]` of polynomials: the determinant of the
matrix whose `(k, l)` entry is the `k`-th Hasse derivative `Dᵏ gₗ` of the `l`-th polynomial. The
Hasse Wronskian of the empty family is `1`. -/
def hasseWronskian (g : Fin m → R[X]) : R[X] :=
  (of fun k l : Fin m ↦ hasseDeriv k (g l)).det

/-- The Hasse Wronskian is the determinant of the matrix of Hasse derivatives `Dᵏ gₗ`. -/
theorem hasseWronskian_def (g : Fin m → R[X]) :
    hasseWronskian g = (of fun k l : Fin m ↦ hasseDeriv k (g l)).det := by
  rw [hasseWronskian]

/-- The Hasse Wronskian of the empty family is `1`. -/
@[simp]
theorem hasseWronskian_fin_zero (g : Fin 0 → R[X]) : hasseWronskian g = 1 := by
  rw [hasseWronskian_def, det_fin_zero]

/-- The Hasse Wronskian of a single polynomial is that polynomial. -/
@[simp]
theorem hasseWronskian_fin_one (g : Fin 1 → R[X]) : hasseWronskian g = g 0 := by
  rw [hasseWronskian_def, det_fin_one, of_apply, Fin.val_zero, hasseDeriv_zero']

/-- The Hasse Wronskian of two polynomials is Mathlib's Wronskian `g₀ g₁' - g₀' g₁`. -/
theorem hasseWronskian_fin_two (g : Fin 2 → R[X]) :
    hasseWronskian g = wronskian (g 0) (g 1) := by
  rw [hasseWronskian_def, det_fin_two, wronskian]
  simp only [of_apply, Fin.val_zero, Fin.val_one, hasseDeriv_zero', hasseDeriv_one']
  ring

/-- Multiplying the Hasse Wronskian by `∏ k < m, k!` gives the classical Wronskian, the
determinant of the iterated ordinary derivatives `derivative^[k] gₗ`. -/
theorem prod_factorial_mul_hasseWronskian (g : Fin m → R[X]) :
    (∏ k : Fin m, ((k : ℕ).factorial : R[X])) * hasseWronskian g =
      (of fun k l : Fin m ↦ derivative^[k] (g l)).det := by
  rw [hasseWronskian_def, ← det_mul_column]
  congr 1
  ext1 k l
  simp only [of_apply]
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]

/-- Permuting the family multiplies the Hasse Wronskian by the sign of the permutation. -/
theorem hasseWronskian_comp_perm (g : Fin m → R[X]) (σ : Equiv.Perm (Fin m)) :
    hasseWronskian (g ∘ σ) = Equiv.Perm.sign σ * hasseWronskian g := by
  rw [hasseWronskian_def, hasseWronskian_def, ← det_permute']
  congr 1

/-- The Hasse Wronskian commutes with maps of coefficient rings. -/
theorem hasseWronskian_map (f : R →+* S) (g : Fin m → R[X]) :
    hasseWronskian (fun l ↦ (g l).map f) = (hasseWronskian g).map f := by
  rw [hasseWronskian_def, hasseWronskian_def, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext1 k l
  simp

/-- Adding a multiple of one member of the family to another does not change the Hasse
Wronskian. -/
theorem hasseWronskian_update_add_smul (g : Fin m → R[X]) {i j : Fin m} (hij : i ≠ j) (a : R) :
    hasseWronskian (Function.update g j (g j + a • g i)) = hasseWronskian g := by
  rw [hasseWronskian_def, hasseWronskian_def]
  conv_rhs => rw [← det_updateCol_add_smul_self _ hij.symm (C a)]
  congr 1
  ext1 k l
  rcases eq_or_ne l j with rfl | hl
  · simp [← smul_eq_C_mul]
  · simp [hl]

/-- Over an integral domain, the Hasse Wronskian of a linearly dependent family vanishes. -/
theorem hasseWronskian_eq_zero_of_not_linearIndependent [IsDomain R] {g : Fin m → R[X]}
    (hg : ¬LinearIndependent R g) : hasseWronskian g = 0 := by
  obtain ⟨a, ha, l, hl⟩ := Fintype.not_linearIndependent_iff.mp hg
  rw [hasseWronskian_def, ← exists_mulVec_eq_zero_iff]
  refine ⟨fun l ↦ C (a l), fun h ↦ hl (C_injective (by simpa using congr_fun h l)), ?_⟩
  ext1 k
  have hk : ∑ l, hasseDeriv k (g l) * C (a l) = hasseDeriv k (∑ l, a l • g l) := by
    rw [map_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, smul_eq_C_mul, mul_comm]
  simpa [mulVec, dotProduct, ha] using hk

/-- Over a domain of characteristic zero, a family of nonzero polynomials of pairwise distinct
degrees has nonzero Hasse Wronskian. -/
theorem hasseWronskian_ne_zero_of_injective_natDegree [IsDomain R] [CharZero R]
    {g : Fin m → R[X]} (hg : ∀ l, g l ≠ 0) (hinj : Function.Injective fun l ↦ (g l).natDegree) :
    hasseWronskian g ≠ 0 := by
  -- Shift the `k`-th row of the classical Wronskian matrix by `X ^ k`: its `l`-th column then has
  -- degree at most `deg gₗ`, with coefficient `(deg gₗ).descFactorial k * lc gₗ` in that degree.
  have hcoeff (k : ℕ) (p : R[X]) (n : ℕ) :
      (X ^ k * derivative^[k] p).coeff n = (n.descFactorial k : R) * p.coeff n := by
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [coeff_iterate_derivative, Nat.sub_add_cancel h, nsmul_eq_mul]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]
  let A : Matrix (Fin m) (Fin m) R[X] := of fun k l ↦ X ^ (k : ℕ) * derivative^[k] (g l)
  have hdeg (k l : Fin m) : (A k l).natDegree ≤ (g l).natDegree :=
    natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ by
      simp [A, hcoeff, coeff_eq_zero_of_natDegree_lt hn]
  -- The matrix of top coefficients is a Vandermonde matrix in the degrees, up to scaling the
  -- columns by the leading coefficients.
  have hV : (of fun k l : Fin m ↦ (descPochhammer R k).eval ((g l).natDegree : R)).det ≠ 0 := by
    have hv := det_vandermonde_ne_zero_iff.mpr
      (Nat.cast_injective.comp hinj : Function.Injective fun l ↦ ((g l).natDegree : R))
    rw [det_eval_matrixOfPolynomials_eq_det_vandermonde _ (fun k : Fin m ↦ descPochhammer R k)
      (fun k ↦ descPochhammer_natDegree R k) (fun k ↦ monic_descPochhammer R k),
      ← det_transpose] at hv
    exact hv
  have htop : A.det.coeff (∑ l, (g l).natDegree) ≠ 0 := by
    rw [coeff_det_sum_eq_of_natDegree_le A _ hdeg]
    convert mul_ne_zero (prod_ne_zero_iff.mpr fun l _ ↦ leadingCoeff_ne_zero.mpr (hg l)) hV
    rw [← det_mul_row]
    congr 1
    ext1 k l
    simp [A, hcoeff, descPochhammer_eval_eq_descFactorial, mul_comm]
  have hA : A.det = (∏ k : Fin m, X ^ (k : ℕ)) *
      ((∏ k : Fin m, ((k : ℕ).factorial : R[X])) * hasseWronskian g) := by
    rw [prod_factorial_mul_hasseWronskian, ← det_mul_column]
    simp [A]
  intro hW
  exact htop (by rw [hA, hW, mul_zero, mul_zero, coeff_zero])

/-- Over a field of characteristic zero, a linearly independent family of polynomials has nonzero
Hasse Wronskian. -/
theorem hasseWronskian_ne_zero_of_linearIndependent {K : Type*} [Field K] [CharZero K]
    {g : Fin m → K[X]} (hg : LinearIndependent K g) : hasseWronskian g ≠ 0 := by
  -- Induct on the sum of the degrees: while two members have the same degree, subtracting a
  -- multiple of one from the other lowers that sum without changing independence or `W(g)`.
  induction hN : ∑ l, (g l).natDegree using Nat.strong_induction_on generalizing g with
  | _ N ih =>
  by_cases hinj : Function.Injective fun l ↦ (g l).natDegree
  · exact hasseWronskian_ne_zero_of_injective_natDegree hg.ne_zero hinj
  obtain ⟨i, j, hdeg, hij⟩ : ∃ i j, (g i).natDegree = (g j).natDegree ∧ i ≠ j := by
    simpa [Function.Injective] using hinj
  set a := (g j).leadingCoeff / (g i).leadingCoeff
  set g' := Function.update g j (g j + (-a) • g i)
  have hgi := hg.ne_zero i
  have hgj := hg.ne_zero j
  have hg' : LinearIndependent K g' := by
    convert (linearIndependent_add_smul_iff (c := Pi.single j (-a)) (i := i)
      (Pi.single_eq_of_ne hij _)).mpr hg using 1
    ext1 l
    rcases eq_or_ne l j with rfl | hl
    · simp [g']
    · simp [g', hl]
  have hlt : (g' j).natDegree < (g j).natDegree := by
    have hg'j : g' j ≠ 0 := hg'.ne_zero j
    simp only [g', Function.update_self, neg_smul, ← sub_eq_add_neg] at hg'j ⊢
    have ha : a ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hgj) (leadingCoeff_ne_zero.mpr hgi)
    refine natDegree_lt_natDegree hg'j (degree_sub_lt_left ?_ hgj ?_)
    · rw [smul_eq_C_mul, degree_C_mul ha, degree_eq_natDegree hgi, degree_eq_natDegree hgj, hdeg]
    · rw [smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C,
        div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hgi)]
  rw [← hasseWronskian_update_add_smul g hij (-a)]
  refine ih _ ?_ hg' rfl
  rw [← hN]
  refine sum_lt_sum (fun l _ ↦ ?_) ⟨j, mem_univ j, hlt⟩
  rcases eq_or_ne l j with rfl | hl
  · exact hlt.le
  · simp [hl]

/-- **The Wronskian criterion.** Over a field of characteristic zero, a family of polynomials is
linearly independent if and only if its Hasse Wronskian is nonzero. -/
theorem linearIndependent_iff_hasseWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    {g : Fin m → K[X]} : LinearIndependent K g ↔ hasseWronskian g ≠ 0 :=
  ⟨hasseWronskian_ne_zero_of_linearIndependent,
    fun h ↦ by_contra fun h' ↦ h (hasseWronskian_eq_zero_of_not_linearIndependent h')⟩

end Polynomial
