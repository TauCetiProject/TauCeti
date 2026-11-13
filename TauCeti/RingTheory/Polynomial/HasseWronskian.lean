/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Polynomial.Wronskian
public import TauCeti.Algebra.Polynomial.Derivative
public import TauCeti.RingTheory.Derivation.Wronskian.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.LinearAlgebra.Vandermonde

/-!
# The Wronskian of a family of polynomials built from Hasse derivatives

For a family `g : Fin m → R[X]` of one-variable polynomials over a commutative ring, the
*Hasse Wronskian* is the determinant `det (Dᵏ gₗ)` of the `m × m` matrix whose `(k, l)` entry is
the `k`-th Hasse (divided) derivative of `gₗ`; the rows are the derivative orders `0 ≤ k < m` and
the columns are the members of the family. Multiplying it by `∏ k < m, k!` gives the classical
Wronskian `det (gₗ⁽ᵏ⁾)`, the `Derivation.wronskian` of the derivation `derivative'`, but the
divided version has the advantage of being defined and integral over any commutative ring.
Mathlib's `Polynomial.wronskian` is the case of two polynomials.

Over an integral domain a linearly dependent family has vanishing Hasse Wronskian. Over a field of
characteristic zero the converse holds, so linear independence is equivalent to nonvanishing of
the Hasse Wronskian. In positive characteristic the converse fails: over `𝔽₂` the polynomials `1`
and `X²` are independent, but `D¹ (X²) = 2X = 0`.

This is the one-variable Wronskian used in the proof of Roth's lemma on the index of auxiliary
polynomials.

The Hasse Wronskian is multilinear and alternating in the family, so changing the family by a
matrix multiplies it by the determinant. Two degree and multiplicity estimates follow. Since the
`k`-th Hasse derivative lowers the degree by at least `k` or vanishes, a nonzero Hasse Wronskian of
`m` polynomials has degree at most `∑ⱼ deg gⱼ - (0 + 1 + ⋯ + (m - 1))`. And for a space `V` of
polynomials with a basis `b` of `m` elements, a nonzero `f ∈ V` vanishing to order `μ` at `a`
forces `(X - a) ^ (μ + 1 - m)` to divide `W(b)`, in every characteristic. In characteristic zero
`W(b) ≠ 0`, so these excesses, summed over distinct points, are at most `deg W(b)`. For two
polynomials the degree estimate is Mathlib's `Polynomial.natDegree_wronskian_lt_add`.

## Main definitions

* `Polynomial.hasseWronskian g`: the determinant of the Hasse derivatives `Dᵏ gₗ`, `k, l < m`.

## Main results

* `Polynomial.hasseWronskian_fin_two`: for two polynomials it is Mathlib's `wronskian`.
* `Polynomial.prod_factorial_mul_hasseWronskian`: `(∏ k, k!) W(g)` is the classical Wronskian
  `derivative'.wronskian g`.
* `Polynomial.hasseWronskian_comp_perm`: permuting the family multiplies `W(g)` by the sign.
* `Polynomial.hasseWronskian_map`: `W(g)` commutes with maps of coefficient rings.
* `Polynomial.hasseWronskian_eq_zero_of_not_linearIndependent`: over an integral domain,
  dependent families have vanishing Hasse Wronskian.
* `Polynomial.linearIndependent_iff_hasseWronskian_ne_zero`: over a field of characteristic
  zero, a family is linearly independent if and only if its Hasse Wronskian is nonzero.
* `Polynomial.hasseWronskian_sum_smul`: changing the family by a matrix `A` multiplies `W(g)` by
  `det A`; `Polynomial.hasseWronskian_basis_eq_C_det_mul` compares two bases of a space `V`.
* `Polynomial.natDegree_hasseWronskian_add_sum_le`: if `W(g) ≠ 0`, then
  `deg W(g) + (0 + 1 + ⋯ + (m - 1)) ≤ ∑ⱼ deg gⱼ`.
* `Polynomial.X_sub_C_pow_rootMultiplicity_add_one_sub_dvd_hasseWronskian`: a nonzero `f ∈ V`
  vanishing to order `μ` at `a` gives `(X - a) ^ (μ + 1 - m) ∣ W(b)`, in every characteristic.
* `Polynomial.sum_rootMultiplicity_add_one_sub_le_natDegree_hasseWronskian`: in characteristic
  zero, `∑ₐ (μₐ + 1 - m) ≤ deg W(b)` over a finite set of points.

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
@[simp]
theorem hasseWronskian_fin_two (g : Fin 2 → R[X]) :
    hasseWronskian g = wronskian (g 0) (g 1) := by
  rw [hasseWronskian_def, det_fin_two, wronskian]
  simp only [of_apply, Fin.val_zero, Fin.val_one, hasseDeriv_zero', hasseDeriv_one']
  ring

/-- Multiplying the Hasse Wronskian by `∏ k < m, k!` gives the classical Wronskian, the
determinant of the iterated ordinary derivatives `derivative^[k] gₗ`. -/
theorem prod_factorial_mul_hasseWronskian (g : Fin m → R[X]) :
    (∏ k : Fin m, ((k : ℕ).factorial : R[X])) * hasseWronskian g =
      (derivative' : Derivation R R[X] R[X]).wronskian g := by
  rw [hasseWronskian_def, Derivation.wronskian_def, ← det_mul_column]
  congr 1
  ext1 k l
  simp only [of_apply]
  rw [coe_derivative', ← factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]

/-- Permuting the family multiplies the Hasse Wronskian by the sign of the permutation. -/
theorem hasseWronskian_comp_perm (g : Fin m → R[X]) (σ : Equiv.Perm (Fin m)) :
    hasseWronskian (g ∘ σ) = Equiv.Perm.sign σ * hasseWronskian g := by
  rw [hasseWronskian_def, hasseWronskian_def, ← det_permute']
  refine congrArg det ?_
  ext1 k l
  simp only [of_apply, submatrix_apply, id_eq, Function.comp_apply]

/-- The Hasse Wronskian commutes with maps of coefficient rings. -/
@[simp]
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

/-- Changing the family by a matrix multiplies the Hasse Wronskian by the determinant: the family
`j ↦ ∑ i, A i j • gᵢ` has Hasse Wronskian `det A • W(g)`. -/
theorem hasseWronskian_sum_smul (A : Matrix (Fin m) (Fin m) R) (g : Fin m → R[X]) :
    hasseWronskian (fun j ↦ ∑ i, A i j • g i) = C A.det * hasseWronskian g := by
  have h : (of fun k l : Fin m ↦ hasseDeriv k (∑ i, A i l • g i)) =
      (of fun k l : Fin m ↦ hasseDeriv k (g l)) * (C : R →+* R[X]).mapMatrix A := by
    ext1 k l
    rw [Matrix.mul_apply, of_apply, map_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, of_apply, RingHom.mapMatrix_apply, map_apply, smul_eq_C_mul, mul_comm]
  rw [hasseWronskian_def, hasseWronskian_def, h, det_mul, RingHom.map_det, mul_comm]

/-- Replacing one member `gⱼ` of the family by a linear combination `∑ i, cᵢ • gᵢ` multiplies the
Hasse Wronskian by the coefficient `cⱼ`. -/
theorem hasseWronskian_update_sum_smul (g : Fin m → R[X]) (j : Fin m) (c : Fin m → R) :
    hasseWronskian (Function.update g j (∑ i, c i • g i)) = C (c j) * hasseWronskian g := by
  have h := det_updateCol_sum (of fun k l : Fin m ↦ hasseDeriv k (g l)) j fun i ↦ C (c i)
  rw [smul_eq_mul] at h
  rw [hasseWronskian_def, hasseWronskian_def, ← h]
  congr 1
  ext1 k l
  rcases eq_or_ne l j with rfl | hl
  · simp only [of_apply, Function.update_self, updateCol_self, map_sum, smul_eq_mul]
    exact sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_C_mul]
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
  have hV : (of fun k l : Fin m ↦ (descPochhammer R k).eval ((g l).natDegree : R)).det ≠ 0 :=
    TauCeti.det_descPochhammer_eval_ne_zero (Nat.cast_injective.comp hinj)
  have htop : A.det.coeff (∑ l, (g l).natDegree) ≠ 0 := by
    rw [coeff_det_sum_eq_of_natDegree_le A _ hdeg]
    convert mul_ne_zero (prod_ne_zero_iff.mpr fun l _ ↦ leadingCoeff_ne_zero.mpr (hg l)) hV
    rw [← det_mul_row]
    congr 1
    ext1 k l
    simp [A, hcoeff, descPochhammer_eval_eq_descFactorial, mul_comm]
  have hA : A.det = (∏ k : Fin m, X ^ (k : ℕ)) *
      ((∏ k : Fin m, ((k : ℕ).factorial : R[X])) * hasseWronskian g) := by
    rw [prod_factorial_mul_hasseWronskian, Derivation.wronskian_def, ← det_mul_column]
    simp [A, coe_derivative']
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

/-! ### Degree and multiplicity estimates -/

/-- **The degree estimate for the Hasse Wronskian.** If the Hasse Wronskian of a family
`g : Fin m → R[X]` is nonzero, then its degree plus `0 + 1 + ⋯ + (m - 1)` is at most the sum of
the degrees of the `gⱼ`. No hypothesis on the commutative ring `R` is needed. -/
theorem natDegree_hasseWronskian_add_sum_le {g : Fin m → R[X]} (hg : hasseWronskian g ≠ 0) :
    (hasseWronskian g).natDegree + ∑ k : Fin m, (k : ℕ) ≤ ∑ j, (g j).natDegree := by
  -- A nonzero term `∏ⱼ D^(σ j) gⱼ` of the Leibniz expansion has every factor nonzero, so
  -- `σ j ≤ deg gⱼ` and the `j`-th factor has degree at most `deg gⱼ - σ j`.
  have hterm (σ : Equiv.Perm (Fin m)) (hσ : ∏ j, hasseDeriv (σ j) (g j) ≠ 0) :
      (∏ j, hasseDeriv (σ j) (g j)).natDegree + ∑ k : Fin m, (k : ℕ) ≤
        ∑ j, (g j).natDegree := by
    have hle (j : Fin m) : (hasseDeriv (σ j) (g j)).natDegree + σ j ≤ (g j).natDegree := by
      have hne : hasseDeriv (σ j) (g j) ≠ 0 := fun h ↦ hσ (prod_eq_zero (mem_univ j) h)
      have h₁ := natDegree_hasseDeriv_le (g j) (σ j)
      have h₂ : (σ j : ℕ) ≤ (g j).natDegree :=
        not_lt.mp fun h ↦ hne (hasseDeriv_eq_zero_of_lt_natDegree _ _ h)
      omega
    calc (∏ j, hasseDeriv (σ j) (g j)).natDegree + ∑ k : Fin m, (k : ℕ)
        ≤ ∑ j, (hasseDeriv (σ j) (g j)).natDegree + ∑ j, (σ j : ℕ) := by
          rw [Equiv.sum_comp σ fun k : Fin m ↦ (k : ℕ)]
          exact Nat.add_le_add_right (natDegree_prod_le _ _) _
      _ = ∑ j, ((hasseDeriv (σ j) (g j)).natDegree + σ j) := sum_add_distrib.symm
      _ ≤ ∑ j, (g j).natDegree := sum_le_sum fun j _ ↦ hle j
  rw [hasseWronskian_def, det_apply'] at hg ⊢
  simp only [of_apply] at hg ⊢
  obtain ⟨σ, -, hσ⟩ := exists_ne_zero_of_sum_ne_zero hg
  have hS := le_of_add_le_right (hterm σ (right_ne_zero_of_mul hσ))
  have hdeg : (∑ τ : Equiv.Perm (Fin m), (Equiv.Perm.sign τ : ℤ) *
      ∏ j, hasseDeriv (τ j) (g j)).natDegree ≤
        ∑ j, (g j).natDegree - ∑ k : Fin m, (k : ℕ) := by
    refine natDegree_sum_le_of_forall_le _ _ fun τ _ ↦ (natDegree_mul_le.trans ?_)
    rw [natDegree_intCast, zero_add]
    by_cases hτ : ∏ j, hasseDeriv (τ j) (g j) = 0
    · simp [hτ]
    · have := hterm τ hτ
      omega
  omega

/-- The degree of the Hasse Wronskian of a family is at most the sum of the degrees of its
members. Unlike `Polynomial.natDegree_hasseWronskian_add_sum_le`, this also holds when the
Hasse Wronskian vanishes. -/
theorem natDegree_hasseWronskian_le (g : Fin m → R[X]) :
    (hasseWronskian g).natDegree ≤ ∑ j, (g j).natDegree := by
  by_cases hg : hasseWronskian g = 0
  · simp [hg]
  · exact le_of_add_le_left (natDegree_hasseWronskian_add_sum_le hg)

/-- If `(X - a) ^ n` divides one member of a family of `m` polynomials, then
`(X - a) ^ (n + 1 - m)` divides its Hasse Wronskian, in every characteristic. -/
theorem X_sub_C_pow_add_one_sub_dvd_hasseWronskian {g : Fin m → R[X]} {a : R} {n : ℕ}
    {j : Fin m} (h : (X - C a) ^ n ∣ g j) : (X - C a) ^ (n + 1 - m) ∣ hasseWronskian g := by
  -- Every entry `Dᵏ gⱼ`, `k < m`, of the column of `gⱼ` is divisible by `(X - a) ^ (n - k)`.
  have hcol (k : Fin m) : (X - C a) ^ (n + 1 - m) ∣ hasseDeriv k (g j) :=
    (pow_dvd_pow _ (by omega)).trans (pow_sub_dvd_hasseDeriv_of_pow_dvd k h)
  choose u hu using hcol
  have hM : (of fun k l : Fin m ↦ hasseDeriv k (g l)) =
      (of fun k l : Fin m ↦ hasseDeriv k (g l)).updateCol j ((X - C a) ^ (n + 1 - m) • u) := by
    ext1 k l
    rcases eq_or_ne l j with rfl | hl
    · simp [hu]
    · simp [hl]
  rw [hasseWronskian_def, hM, det_updateCol_smul]
  exact dvd_mul_right _ _

section Basis

variable {V : Submodule R R[X]}

/-- The Hasse Wronskians of two bases of a space `V` of polynomials differ by the determinant of
the change of basis, a unit of `R`. -/
theorem hasseWronskian_basis_eq_C_det_mul (b b' : Module.Basis (Fin m) R V) :
    hasseWronskian (fun j ↦ (b' j : R[X])) =
      C (b.det b') * hasseWronskian fun j ↦ (b j : R[X]) := by
  rw [Module.Basis.det_apply, ← hasseWronskian_sum_smul]
  congr 1
  ext1 j
  conv_lhs => rw [← b.sum_repr (b' j)]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.toMatrix_apply]

variable [IsDomain R]

/-- Over an integral domain, the root multiplicity of the Hasse Wronskian of a basis of a space `V`
of polynomials at any point does not depend on the basis. -/
theorem rootMultiplicity_hasseWronskian_basis (b b' : Module.Basis (Fin m) R V) (a : R) :
    (hasseWronskian fun j ↦ (b' j : R[X])).rootMultiplicity a =
      (hasseWronskian fun j ↦ (b j : R[X])).rootMultiplicity a := by
  rw [hasseWronskian_basis_eq_C_det_mul b b', rootMultiplicity_C_mul (b.isUnit_det b').ne_zero]

/-- Let `V` be a space of polynomials over an integral domain with a basis `b` of `m` elements. If a
nonzero `f ∈ V` vanishes to order `μ` at `a`, then `(X - a) ^ (μ + 1 - m)` divides the Hasse
Wronskian of `b`, in every characteristic. -/
theorem X_sub_C_pow_rootMultiplicity_add_one_sub_dvd_hasseWronskian
    (b : Module.Basis (Fin m) R V) {f : V} (hf : f ≠ 0) (a : R) :
    (X - C a) ^ ((f : R[X]).rootMultiplicity a + 1 - m) ∣
      hasseWronskian fun j ↦ (b j : R[X]) := by
  -- Replace a member of `b` whose coordinate in `f` is nonzero by `f` itself; this multiplies the
  -- Hasse Wronskian by that nonzero coordinate, which is prime to `X - a`.
  obtain ⟨i, hi⟩ : ∃ i, b.repr f i ≠ 0 := by
    by_contra! h
    exact hf (b.repr.map_eq_zero_iff.mp (Finsupp.ext h))
  have hsum : (f : R[X]) = ∑ j, b.repr f j • (b j : R[X]) := by
    conv_lhs => rw [← b.sum_repr f]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hW := hasseWronskian_update_sum_smul (fun j ↦ (b j : R[X])) i (b.repr f)
  rw [← hsum] at hW
  have hdvd := X_sub_C_pow_add_one_sub_dvd_hasseWronskian (j := i)
    (g := Function.update (fun j ↦ (b j : R[X])) i f)
    (by simpa using pow_rootMultiplicity_dvd (f : R[X]) a)
  rw [hW] at hdvd
  exact (prime_X_sub_C a).pow_dvd_of_dvd_mul_left _ (by simpa [dvd_iff_isRoot] using hi) hdvd

variable {K : Type*} [Field K] [CharZero K] {V : Submodule K K[X]}

/-- Over a field of characteristic zero, if a nonzero member `f` of a space `V` of polynomials with
a basis `b` of `m` elements vanishes to order `μ` at `a`, then the Hasse Wronskian of `b` vanishes
to order at least `μ + 1 - m` at `a`. -/
theorem rootMultiplicity_add_one_sub_le_rootMultiplicity_hasseWronskian
    (b : Module.Basis (Fin m) K V) {f : V} (hf : f ≠ 0) (a : K) :
    (f : K[X]).rootMultiplicity a + 1 - m ≤
      (hasseWronskian fun j ↦ (b j : K[X])).rootMultiplicity a :=
  (le_rootMultiplicity_iff (hasseWronskian_ne_zero_of_linearIndependent
    (b.linearIndependent.map' V.subtype V.ker_subtype))).mpr
      (X_sub_C_pow_rootMultiplicity_add_one_sub_dvd_hasseWronskian b hf a)

/-- **The multiplicity estimate for a space of polynomials.** Let `V` be a space of polynomials
over a field of characteristic zero with a basis `b` of `m` elements. If at each point `a` of a
finite set `S` some nonzero `f a ∈ V` vanishes to order `μₐ`, then the excesses `μₐ + 1 - m` sum
to at most the degree of the Hasse Wronskian of `b`. -/
theorem sum_rootMultiplicity_add_one_sub_le_natDegree_hasseWronskian
    (b : Module.Basis (Fin m) K V) {S : Finset K} {f : K → V} (hf : ∀ a ∈ S, f a ≠ 0) :
    ∑ a ∈ S, ((f a : K[X]).rootMultiplicity a + 1 - m) ≤
      (hasseWronskian fun j ↦ (b j : K[X])).natDegree :=
  (sum_le_sum fun a ha ↦
    rootMultiplicity_add_one_sub_le_rootMultiplicity_hasseWronskian b (hf a ha) a).trans
      (sum_rootMultiplicity_le_natDegree _ S)

end Basis

end Polynomial
