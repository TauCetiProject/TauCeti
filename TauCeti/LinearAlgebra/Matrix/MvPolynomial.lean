/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Determinants of matrices of multivariate polynomials

Let `A` be a square matrix with entries in `MvPolynomial σ R` whose `l`-th column has partial
degree at most `e l` in the variable `Xᵢ`. Every term of the Leibniz expansion of `det A` is, up
to sign, a product containing exactly one entry from each column, so `det A` has partial degree
at most `∑ l, e l` in `Xᵢ`.

The minors of a matrix `Z`, and of its powers, are polynomials in the entries of `Z`: they are
the values at `Z` of the corresponding minors of the generic matrix `Matrix.mvPolynomialX`.

The generic determinant is a non-zero-divisor over every commutative ring.
Translating the generic matrix by the identity and embedding into power series
reduces this to its constant coefficient being one.

Order the variables `X (i, j)` of the generic matrix row by row, by renaming them along `toLex`
to the lexicographically ordered pairs `m ×ₗ n`, and use the lexicographic monomial order
`MonomialOrder.lex`, for which `X (0, 0)` is the largest variable, followed by `X (0, 1)`. Every
minor on sorted rows `r` and sorted columns `c` then has its main diagonal `∏ i, X (r i, c i)` as
leading term, with coefficient one: in the Leibniz expansion, a permutation other than the
identity first differs from the diagonal at some row `r j₀`, where it uses a column to the right
of `c j₀`, so the diagonal exponent is lexicographically larger. Thus this order is a diagonal
term order on the generic matrix. Leading terms of minors are the input to Gröbner and SAGBI
bases of determinantal and flag-minor algebras. For finite index types such as `Fin p` and
`Fin q`, the hypothesis `WellFoundedGT (m ×ₗ n)` is found by instance search.

## Main results

* `Matrix.degreeOf_det_le_sum`: the partial degree of a determinant is bounded by
  the sum of the column-wise partial-degree bounds.
* `Matrix.aeval_det_submatrix_mvPolynomialX` and `Matrix.aeval_det_submatrix_pow_mvPolynomialX`:
  the minors of a matrix `Z`, and of `Z ^ j`, are evaluations of minors of the generic matrix.
* `Matrix.det_mvPolynomialX_mem_nonZeroDivisors`: the generic determinant is regular.
* `Matrix.degree_rename_toLex_det_submatrix_mvPolynomialX`,
  `Matrix.monic_rename_toLex_det_submatrix_mvPolynomialX` and
  `Matrix.leadingTerm_rename_toLex_det_submatrix_mvPolynomialX`: for the row-major
  lexicographic order, a minor of the generic matrix on sorted rows and columns is monic with
  leading term the product of its diagonal entries.

## References

* E. Miller, B. Sturmfels, *Combinatorial Commutative Algebra*, Graduate Texts in Mathematics
  227, Springer, 2005, Chapter 14 (diagonal term orders and leading terms of minors).
-/

public section

namespace Matrix

open MvPolynomial Finset

section Degree

variable {R σ n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- If the `l`-th column of a matrix `A` of multivariate polynomials has partial degree at most
`e l` in `Xᵢ`, then `det A` has partial degree at most `∑ l, e l` in `Xᵢ`. -/
theorem degreeOf_det_le_sum (A : Matrix n n (MvPolynomial σ R)) (i : σ) (e : n → ℕ)
    (hA : ∀ k l, (A k l).degreeOf i ≤ e l) :
    A.det.degreeOf i ≤ ∑ l, e l := by
  rw [det_apply]
  refine (degreeOf_sum_le i univ _).trans (Finset.sup_le fun p _ ↦ ?_)
  calc
    (Equiv.Perm.sign p • ∏ l, A (p l) l).degreeOf i =
        (∏ l, A (p l) l).degreeOf i := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
      · rw [hp, one_smul]
      · rw [hp, Units.neg_smul, one_smul, degreeOf_neg]
    _ ≤ ∑ l, (A (p l) l).degreeOf i := degreeOf_prod_le i univ _
    _ ≤ ∑ l, e l := Finset.sum_le_sum fun l _ ↦ hA (p l) l

/-- The generic determinant is a non-zero-divisor over every commutative ring,
including the zero ring and matrices of size zero. -/
theorem det_mvPolynomialX_mem_nonZeroDivisors :
    (mvPolynomialX n n R).det ∈ nonZeroDivisors (MvPolynomial (n × n) R) := by
  let t : MvPolynomial (n × n) R →ₐ[R] MvPolynomial (n × n) R :=
    aeval fun ij => X ij + C ((1 : Matrix n n R) ij.1 ij.2)
  let u : MvPolynomial (n × n) R →ₐ[R] MvPolynomial (n × n) R :=
    aeval fun ij => X ij - C ((1 : Matrix n n R) ij.1 ij.2)
  have hut : u.comp t = AlgHom.id R _ := by
    ext ij
    simp [t, u]
  have hleft : Function.LeftInverse u t := fun p => DFunLike.congr_fun hut p
  have ht : Function.Injective t := hleft.injective
  let f : MvPolynomial (n × n) R →+* MvPowerSeries (n × n) R :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp t.toRingHom
  have hf : Function.Injective f := (MvPolynomial.coe_injective _ _).comp ht
  apply mem_nonZeroDivisors_of_injective hf
  apply MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff
  have hm : (MvPowerSeries.constantCoeff.comp f).mapMatrix (mvPolynomialX n n R) = 1 := by
    ext i j
    simp [f, t]
  -- Bundle the constant-coefficient evaluation so map_det applies to the ring homomorphism.
  change (MvPowerSeries.constantCoeff.comp f) (mvPolynomialX n n R).det ∈ _
  rw [RingHom.map_det, hm, det_one]
  exact one_mem _

end Degree

section Minors

variable {R S m n l : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype l] [DecidableEq l]

/-- The minors of a matrix `Z` are the values at the entries of `Z` of the corresponding minors
of the generic matrix `Matrix.mvPolynomialX`. -/
theorem aeval_det_submatrix_mvPolynomialX (Z : Matrix m n S) (r : l → m) (c : l → n) :
    aeval (Function.uncurry Z) ((mvPolynomialX m n R).submatrix r c).det =
      (Z.submatrix r c).det := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← submatrix_map]
  congr 2
  ext i j
  rw [map_apply, mvPolynomialX_apply, aeval_X]
  exact Function.uncurry_apply_pair (f := Z) i j

/-- The minors of the `j`-th power of a matrix `Z` are the values at the entries of `Z` of the
corresponding minors of the `j`-th power of the generic matrix `Matrix.mvPolynomialX`. -/
theorem aeval_det_submatrix_pow_mvPolynomialX [Fintype n] [DecidableEq n] (Z : Matrix n n S)
    (j : ℕ) (r c : l → n) :
    aeval (Function.uncurry Z) ((mvPolynomialX n n R ^ j).submatrix r c).det =
      ((Z ^ j).submatrix r c).det := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← submatrix_map, ← AlgHom.mapMatrix_apply,
    map_pow]
  exact congrArg (fun A : Matrix n n S ↦ ((A ^ j).submatrix r c).det)
    (mvPolynomialX_mapMatrix_aeval R Z)

end Minors

section LeadingTerm

open MonomialOrder

variable {R m n ι : Type*} [CommRing R] [LinearOrder ι] [Fintype ι]

/-- The Leibniz expansion of a minor of the generic matrix, with its variables indexed by the
lexicographically ordered pairs: the term of `σ` is the monomial `∏ i, X (r i, c (σ i))`. -/
private theorem rename_toLex_det_submatrix_mvPolynomialX (r : ι → m) (c : ι → n) :
    rename toLex ((mvPolynomialX m n R).submatrix r c).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) •
        monomial (∑ i, Finsupp.single (toLex (r i, c (σ i))) 1) (1 : R)) := by
  rw [← det_transpose, det_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Units.smul_def, map_zsmul, map_prod, monomial_sum_one]
  simp [X, rename_monomial]

variable [LinearOrder m] [LinearOrder n]

/-- For sorted rows `r` and columns `c`, the exponent of the main diagonal is lexicographically
larger than the exponent of the term of any other permutation in the Leibniz expansion. -/
private theorem toLex_sum_single_lt {r : ι → m} {c : ι → n} (hr : StrictMono r)
    (hc : StrictMono c) {σ : Equiv.Perm ι} (hσ : σ ≠ 1) :
    toLex (∑ i, Finsupp.single (toLex (r i, c (σ i))) 1) <
      toLex (∑ i, Finsupp.single (toLex (r i, c i)) 1) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
    by_contra! h
    exact hσ (Equiv.ext h)
  -- Let `j₀` be the first index moved by `σ`. It is sent to a larger index.
  set s := Finset.univ.filter fun j ↦ σ j ≠ j
  have hs : s.Nonempty := ⟨j, by simp [s, hj]⟩
  let j₀ := s.min' hs
  have hj₀ : σ j₀ ≠ j₀ := by simpa [s] using s.min'_mem hs
  have hfix : ∀ i < j₀, σ i = i := fun i hi ↦ by
    by_contra h
    exact (s.min'_le i (by simp [s, h])).not_gt hi
  have hlt : j₀ < σ j₀ :=
    lt_of_le_of_ne (not_lt.1 fun h ↦ hj₀ (σ.injective (hfix _ h))) hj₀.symm
  -- From row `j₀` on, both monomials only involve variables at least `(r j₀, c j₀)`.
  have hge : ∀ i, j₀ ≤ i → toLex (r j₀, c j₀) ≤ toLex (r i, c (σ i)) ∧
      toLex (r j₀, c j₀) ≤ toLex (r i, c i) := by
    intro i hi
    rcases hi.eq_or_lt with rfl | hi
    · simp [Prod.Lex.toLex_le_toLex, (hc hlt).le]
    · simp [Prod.Lex.toLex_le_toLex, hr hi]
  rw [Finsupp.Lex.lt_iff]
  refine ⟨toLex (r j₀, c j₀), fun w hw ↦ ?_, ?_⟩
  · simp only [ofLex_toLex, Finset.sum_apply']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : i < j₀
    · rw [hfix i hi]
    · obtain ⟨h₁, h₂⟩ := hge i (not_lt.1 hi)
      rw [Finsupp.single_eq_of_ne (hw.trans_le h₁).ne, Finsupp.single_eq_of_ne (hw.trans_le h₂).ne]
  · simp only [ofLex_toLex, Finset.sum_apply']
    -- The variable `(r j₀, c j₀)` occurs on the diagonal but not in the term of `σ`.
    rw [Finset.sum_eq_zero fun i _ ↦ Finsupp.single_eq_of_ne fun h ↦ ?_]
    · exact (Finset.single_le_sum (f := fun i ↦ Finsupp.single (toLex (r i, c i)) 1 _)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j₀)).trans_lt' (by simp)
    · obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 (toLex.injective h)
      obtain rfl := hr.injective h₁
      exact hj₀ (hc.injective h₂.symm)

/-- The diagonal monomial occurs with coefficient one in a minor on sorted rows and columns. -/
private theorem coeff_rename_toLex_det_submatrix_mvPolynomialX {r : ι → m} {c : ι → n}
    (hr : StrictMono r) (hc : StrictMono c) :
    (rename toLex ((mvPolynomialX m n R).submatrix r c).det).coeff
      (∑ i, Finsupp.single (toLex (r i, c i)) 1) = 1 := by
  classical
  rw [rename_toLex_det_submatrix_mvPolynomialX, coeff_sum, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    have h : ∑ i, Finsupp.single (toLex (r i, c (σ i))) 1 ≠
        ∑ i, Finsupp.single (toLex (r i, c i)) 1 :=
      fun h ↦ (toLex_sum_single_lt hr hc hσ).ne (congrArg toLex h)
    rw [coeff_smul, coeff_monomial]
    simp [h]
  · simp

variable [WellFoundedGT (m ×ₗ n)]

/-- Every monomial of a minor on sorted rows and columns is at most the diagonal monomial. -/
private theorem le_of_mem_support_rename_toLex_det_submatrix_mvPolynomialX {r : ι → m}
    {c : ι → n} (hr : StrictMono r) (hc : StrictMono c) {a : m ×ₗ n →₀ ℕ}
    (ha : a ∈ (rename toLex ((mvPolynomialX m n R).submatrix r c).det).support) :
    a ≼[lex] ∑ i, Finsupp.single (toLex (r i, c i)) 1 := by
  classical
  rw [mem_support_iff, rename_toLex_det_submatrix_mvPolynomialX, coeff_sum] at ha
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  rw [coeff_smul, coeff_monomial] at hσ
  obtain rfl : ∑ i, Finsupp.single (toLex (r i, c (σ i))) 1 = a := by
    by_contra h
    simp [h] at hσ
  rw [lex_le_iff]
  rcases eq_or_ne σ 1 with rfl | hσ₁
  · simp
  · exact (toLex_sum_single_lt hr hc hσ₁).le

/-- For the lexicographic order on the variables `X (i, j)` ordered row by row, a minor of the
generic matrix on sorted rows `r` and sorted columns `c` has the main diagonal
`∏ i, X (r i, c i)` as its leading monomial. -/
@[simp]
theorem degree_rename_toLex_det_submatrix_mvPolynomialX [Nontrivial R] {r : ι → m}
    {c : ι → n} (hr : StrictMono r) (hc : StrictMono c) :
    lex.degree (rename toLex ((mvPolynomialX m n R).submatrix r c).det) =
      ∑ i, Finsupp.single (toLex (r i, c i)) 1 :=
  lex.toSyn.injective <| le_antisymm
    (lex.degree_le_iff.2 fun _ ↦ le_of_mem_support_rename_toLex_det_submatrix_mvPolynomialX hr hc)
    (lex.le_degree <| by
      rw [mem_support_iff, coeff_rename_toLex_det_submatrix_mvPolynomialX hr hc]
      exact one_ne_zero)

/-- For the lexicographic order on the variables `X (i, j)` ordered row by row, a minor of the
generic matrix on sorted rows and sorted columns is monic. -/
@[simp]
theorem monic_rename_toLex_det_submatrix_mvPolynomialX {r : ι → m} {c : ι → n}
    (hr : StrictMono r) (hc : StrictMono c) :
    lex.Monic (rename toLex ((mvPolynomialX m n R).submatrix r c).det) := by
  nontriviality R
  rw [Monic, leadingCoeff, degree_rename_toLex_det_submatrix_mvPolynomialX hr hc,
    coeff_rename_toLex_det_submatrix_mvPolynomialX hr hc]

/-- For the lexicographic order on the variables `X (i, j)` ordered row by row, the leading term
of a minor of the generic matrix on sorted rows `r` and sorted columns `c` is the product
`∏ i, X (r i, c i)` of its diagonal entries. -/
@[simp]
theorem leadingTerm_rename_toLex_det_submatrix_mvPolynomialX {r : ι → m} {c : ι → n}
    (hr : StrictMono r) (hc : StrictMono c) :
    lex.leadingTerm (rename toLex ((mvPolynomialX m n R).submatrix r c).det) =
      ∏ i, X (toLex (r i, c i)) := by
  nontriviality R
  rw [leadingTerm, degree_rename_toLex_det_submatrix_mvPolynomialX hr hc,
    (monic_rename_toLex_det_submatrix_mvPolynomialX hr hc).leadingCoeff_eq_one, monomial_sum_one]
  simp [X]

end LeadingTerm

end Matrix
