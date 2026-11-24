/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial.Subst
public import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.LinearAlgebra.Matrix.Block
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal

/-!
# Products of leading principal minors as highest weight vectors

Let `R` be a commutative ring and `ι` a finite linearly ordered index type. The group
`GL_ι(R) × GL_ι(R)` acts on the polynomial functions `MvPolynomial (ι × ι) R` in the entries of a
matrix by `((g₁, g₂) • f)(X) = f (g₁⁻¹ * X * g₂)` (`TauCeti.mvPolynomialMatrixRep`).

Over a field of characteristic zero, the homogeneous components of this representation carry the
Cauchy decomposition `⊕_λ F_λ^∨ ⊗ F_λ` into tensor products of irreducible representations, and
with respect to the lower triangular Borel subgroup in the first factor and the upper triangular
Borel subgroup in the second, the highest weight line of the summand indexed by
`λ = (c₁ ≥ c₂ ≥ ⋯)` is spanned by the product of leading principal minors

`Δ_λ = ∏ᵢ Δᵢ ^ (cᵢ - cᵢ₊₁)`,

where `Δᵢ` is the determinant of the upper left `i × i` block of the generic matrix. Over a general
commutative ring there is only a filtration. This file proves neither statement; it shows, over an
arbitrary `R`, that `Δ_λ` is a Borel weight vector of weight `(-c, c)` and normalizes its diagonal
coefficient.

We index these products by the exponents: for `m : ι → ℕ`, `TauCeti.leadingMinorProd R m` is the
product over `a : ι` of the minors on `{j | j ≤ a}` raised to the power `m a`, and its weight is
`TauCeti.leadingMinorWeight m j = ∑_{a ≥ j} m a`, which is antitone in `j`. Conversely, every
antitone `c : ι → ℕ` is the weight of exactly one exponent vector,
`TauCeti.leadingMinorExponent c`. For `ι = Fin u` and `λ = (c₁ ≥ ⋯ ≥ c_u)` the exponents are
`m i = cᵢ - cᵢ₊₁` with `c_{u+1} = 0` (`TauCeti.leadingMinorExponent_of_covBy` and
`TauCeti.leadingMinorExponent_of_isMax`).

For a lower triangular `A` and an upper triangular `B`, the minor on an initial segment `p` of
`X ↦ A * X * B` is the product of the minors of `A`, `X` and `B` on `p`. Hence substitution
multiplies a leading minor by the diagonal entries of `A` and `B` on that segment, and `Δ_λ` by
`∏ⱼ (A j j * B j j) ^ cⱼ`.

## Main definitions

* `TauCeti.leadingMinorProd R m`: the product of leading principal minors with exponents `m`.
* `TauCeti.leadingMinorWeight m`: its weight `c`, with `c j = ∑_{a ≥ j} m a`.
* `TauCeti.leadingMinorExponent c`: the exponents of the product of weight `c`.

## Main results

* `Matrix.mvPolynomialSubst_mvPolynomialMinor_of_isLowerTriangular_of_isUpperTriangular`: the
  minor on a down-closed set of indices is a weight vector for the two triangular Borel subgroups.
* `TauCeti.leadingMinorProd_zero`, `TauCeti.leadingMinorProd_add`,
  `TauCeti.leadingMinorWeight_zero` and `TauCeti.leadingMinorWeight_add`: `Δ_λ` and its weight are
  multiplicative, respectively additive, in the exponents.
* `TauCeti.leadingMinorWeight_leadingMinorExponent` and
  `TauCeti.leadingMinorExponent_leadingMinorWeight`: exponents and antitone weights correspond
  bijectively; in particular `TauCeti.leadingMinorWeight_injective`.
* `TauCeti.leadingMinorExponent_of_covBy` and `TauCeti.leadingMinorExponent_of_isMax`: for an
  antitone `c` the exponents are the differences `cᵢ - cᵢ₊₁`, and `c` itself at a maximal index.
* `TauCeti.mvPolynomialMatrixRep_leadingMinorProd`: `(g₁, g₂) • Δ_λ` is the multiple of `Δ_λ` by
  `∏ⱼ ((g₁⁻¹) j j * g₂ j j) ^ cⱼ` for lower triangular `g₁` and upper triangular `g₂`;
  `TauCeti.mvPolynomialMatrixRep_leadingMinorProd_of_unitriangular` (both unipotent
  radicals fix `Δ_λ`) and `TauCeti.mvPolynomialMatrixRep_diagGL_leadingMinorProd` (the torus acts
  through the weight `(-c, c)`) are the two halves of this statement.
* `TauCeti.isHomogeneous_leadingMinorProd`: `Δ_λ` is homogeneous of degree `∑ⱼ cⱼ`.
* `TauCeti.monic_rename_toLex_leadingMinorProd` and
  `TauCeti.degree_rename_toLex_leadingMinorProd`: for the row-major lexicographic order, `Δ_λ` is
  monic with leading monomial the diagonal monomial `∏ⱼ X (j, j) ^ cⱼ`.
* `TauCeti.coeff_diag_leadingMinorProd`: the diagonal monomial has coefficient `1` in `Δ_λ`; in
  particular `Δ_λ ≠ 0` over a nontrivial ring (`TauCeti.leadingMinorProd_ne_zero`).

## References

* E. Eischen, M. Harris, J.-S. Li and C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), Lemma 4.4.8 and (100).
-/

public section

open MvPolynomial Finset

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]

/-- **Generic minors on initial segments are Borel weight vectors.** For a lower triangular `A`,
an upper triangular `B` and a set of indices `{j | p j}` closed under passing to smaller indices,
substituting `A * X * B` for the generic matrix multiplies the minor on `{j | p j}` by the
diagonal entries of `A` and `B` on that set. -/
theorem mvPolynomialSubst_mvPolynomialMinor_of_isLowerTriangular_of_isUpperTriangular
    {A B : Matrix ι ι R} (hA : A.IsLowerTriangular) (hB : B.IsUpperTriangular) {p : ι → Prop}
    [DecidablePred p] (hp : ∀ ⦃i j⦄, j ≤ i → p i → p j) :
    mvPolynomialSubst A B
        (mvPolynomialMinor R (Subtype.val : {j // p j} → ι) Subtype.val) =
      (∏ j with p j, A j j * B j j) • mvPolynomialMinor R (Subtype.val : {j // p j} → ι)
        Subtype.val := by
  have hp' : ∀ ⦃i j⦄, id j ≤ id i → p i → p j := hp
  have hval : StrictMono (Subtype.val : {j // p j} → ι) := Subtype.strictMono_coe _
  rw [mvPolynomialMinor_eq_det_submatrix, AlgHom.map_det, AlgHom.mapMatrix_apply, ← submatrix_map,
    mvPolynomialX_map_mvPolynomialSubst, ← toSquareBlockProp_eq_submatrix _ p,
    det_toSquareBlockProp_mul_mul (b := id) (hA.map C) (hB.map C) hp']
  simp only [toSquareBlockProp_eq_submatrix]
  rw [det_of_isLowerTriangular ((A.map C).submatrix Subtype.val Subtype.val)
      fun _ _ h ↦ (hA.map C) (hval h),
    det_of_isUpperTriangular (M := (B.map C).submatrix Subtype.val Subtype.val)
      fun _ _ h ↦ (hB.map C) (hval h), ← prod_subtype_eq_prod_filter,
    subtype_univ]
  simp [smul_eq_C_mul, prod_mul_distrib, mul_right_comm]

end Matrix

namespace TauCeti

open Matrix

/-! ### Products of leading principal minors -/

variable {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]

variable (R) in
/-- The product of leading principal minors of the generic matrix with exponents `m`: the
product over `a : ι` of the minor on the initial segment `{j | j ≤ a}`, raised to the power
`m a`. -/
noncomputable def leadingMinorProd (m : ι → ℕ) : MvPolynomial (ι × ι) R :=
  ∏ a, mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val ^ m a

/-- The defining formula of `TauCeti.leadingMinorProd`. -/
theorem leadingMinorProd_def (m : ι → ℕ) :
    leadingMinorProd R m =
      ∏ a, mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val ^ m a := (rfl)

/-- The weight `c` of the product of leading principal minors with exponents `m`:
`c j = ∑_{a ≥ j} m a` is the number of minors in the product, counted with multiplicity, that
involve the `j`-th row and column. -/
def leadingMinorWeight (m : ι → ℕ) (j : ι) : ℕ :=
  ∑ a with j ≤ a, m a

/-- The defining formula of `TauCeti.leadingMinorWeight`. -/
theorem leadingMinorWeight_def (m : ι → ℕ) (j : ι) :
    leadingMinorWeight m j = ∑ a with j ≤ a, m a := (rfl)

/-- With all exponents zero, the product of leading principal minors is `1`. -/
@[simp]
theorem leadingMinorProd_zero : leadingMinorProd R (0 : ι → ℕ) = 1 := by
  simp [leadingMinorProd]

/-- Adding exponents multiplies the products of leading principal minors. -/
theorem leadingMinorProd_add (m m' : ι → ℕ) :
    leadingMinorProd R (m + m') = leadingMinorProd R m * leadingMinorProd R m' := by
  simp only [leadingMinorProd, Pi.add_apply, pow_add, prod_mul_distrib]

/-- With all exponents zero, the weight is zero. -/
@[simp]
theorem leadingMinorWeight_zero : leadingMinorWeight (0 : ι → ℕ) = 0 := by
  ext
  simp [leadingMinorWeight]

/-- The weight is additive in the exponents. -/
theorem leadingMinorWeight_add (m m' : ι → ℕ) :
    leadingMinorWeight (m + m') = leadingMinorWeight m + leadingMinorWeight m' := by
  ext
  simp only [leadingMinorWeight, Pi.add_apply, sum_add_distrib]

/-- The weight of a product of leading principal minors is a partition: it decreases along `ι`. -/
theorem antitone_leadingMinorWeight (m : ι → ℕ) : Antitone (leadingMinorWeight m) :=
  fun _ _ hij ↦ sum_le_sum_of_subset_of_nonneg
    (fun _ ha ↦ by simpa using hij.trans (by simpa using ha)) fun _ _ _ ↦ Nat.zero_le _

/-- The weight at `j` is the exponent at `j` plus the largest weight at a later index (`0` if
there is none). -/
theorem leadingMinorWeight_eq_add_sup (m : ι → ℕ) (j : ι) :
    leadingMinorWeight m j = m j + (univ.filter fun a ↦ j < a).sup (leadingMinorWeight m) := by
  rw [leadingMinorWeight, ← add_sum_erase _ _ (mem_filter.2 ⟨mem_univ j, le_rfl⟩)]
  congr 1
  rw [show (univ.filter fun a ↦ j ≤ a).erase j = univ.filter fun a ↦ j < a by
    ext a
    simp [lt_iff_le_and_ne, ne_comm, and_comm]]
  rcases (univ.filter fun a ↦ j < a).eq_empty_or_nonempty with h | h
  · simp [h]
  -- The later indices form the initial segment from the first of them.
  have hb := min'_mem _ h
  have hseg : (univ.filter fun a ↦ (univ.filter fun a ↦ j < a).min' h ≤ a) =
      univ.filter fun a ↦ j < a := by
    ext a
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact ⟨hb.trans_le, fun ha ↦ min'_le _ _ (by simpa using ha)⟩
  calc ∑ a with j < a, m a = leadingMinorWeight m ((univ.filter fun a ↦ j < a).min' h) := by
        rw [leadingMinorWeight, hseg]
    _ = _ := le_antisymm (le_sup hb)
        (Finset.sup_le fun a ha ↦ antitone_leadingMinorWeight m (min'_le _ _ ha))

/-- The exponents of the product of leading principal minors of weight `c`: `c a` minus the
largest value of `c` at a later index (`0` if there is none). For an antitone `c` indexed by
`Fin u` these are the differences `cᵢ - cᵢ₊₁`, with `c_{u+1} = 0`. -/
def leadingMinorExponent (c : ι → ℕ) (a : ι) : ℕ :=
  c a - (univ.filter fun b ↦ a < b).sup c

/-- The defining formula of `TauCeti.leadingMinorExponent`. -/
theorem leadingMinorExponent_def (c : ι → ℕ) (a : ι) :
    leadingMinorExponent c a = c a - (univ.filter fun b ↦ a < b).sup c := (rfl)

/-- For an antitone `c`, the exponent at `a` is the difference `c a - c b` with the successor `b`
of `a`, as in `cᵢ - cᵢ₊₁`. -/
theorem leadingMinorExponent_of_covBy {c : ι → ℕ} (hc : Antitone c) {a b : ι} (h : a ⋖ b) :
    leadingMinorExponent c a = c a - c b := by
  rw [leadingMinorExponent_def]
  congr 1
  exact le_antisymm (Finset.sup_le fun x hx ↦ hc (h.lt_iff_le_right.1 (mem_filter.1 hx).2))
    (le_sup (f := c) (mem_filter.2 ⟨mem_univ b, h.lt⟩))

/-- At a maximal index the exponent is the weight itself: the convention `c_{u+1} = 0`. -/
theorem leadingMinorExponent_of_isMax (c : ι → ℕ) {a : ι} (h : IsMax a) :
    leadingMinorExponent c a = c a := by
  simp [leadingMinorExponent_def, filter_eq_empty_iff.2 fun b _ ↦ h.not_lt (b := b)]

/-- Every partition is the weight of a product of leading principal minors: the one with exponents
`TauCeti.leadingMinorExponent c`. -/
theorem leadingMinorWeight_leadingMinorExponent {c : ι → ℕ} (hc : Antitone c) :
    leadingMinorWeight (leadingMinorExponent c) = c := by
  ext j
  induction j using WellFoundedGT.induction with
  | _ j ih =>
    rw [leadingMinorWeight_eq_add_sup, sup_congr rfl fun b hb ↦ ih b (by simpa using hb),
      leadingMinorExponent_def,
      Nat.sub_add_cancel (Finset.sup_le fun b hb ↦ hc (mem_filter.1 hb).2.le)]

/-- The exponents are recovered from the weight. -/
@[simp]
theorem leadingMinorExponent_leadingMinorWeight (m : ι → ℕ) :
    leadingMinorExponent (leadingMinorWeight m) = m := by
  ext j
  rw [leadingMinorExponent_def, leadingMinorWeight_eq_add_sup m j, Nat.add_sub_cancel]

/-- Products of leading principal minors with different exponents have different weights. -/
theorem leadingMinorWeight_injective :
    Function.Injective (leadingMinorWeight : (ι → ℕ) → ι → ℕ) :=
  Function.LeftInverse.injective leadingMinorExponent_leadingMinorWeight

/-- Collecting, for each `j`, the factors `x j` from the products over initial segments. -/
@[to_additive /-- Collecting, for each `j`, the summands `x j` from the sums over initial
segments. -/]
private theorem prod_prod_le_pow_eq_prod_pow_leadingMinorWeight {M : Type*} [CommMonoid M]
    (x : ι → M) (m : ι → ℕ) :
    ∏ a, (∏ j with j ≤ a, x j) ^ m a = ∏ j, x j ^ leadingMinorWeight m j :=
  calc ∏ a, (∏ j with j ≤ a, x j) ^ m a = ∏ a, ∏ j with j ≤ a, x j ^ m a := by
        simp only [prod_pow]
    _ = ∏ j, ∏ a with j ≤ a, x j ^ m a := prod_comm' (by simp)
    _ = ∏ j, x j ^ leadingMinorWeight m j := by
        simp only [prod_pow_eq_pow_sum, leadingMinorWeight]

/-- **Products of leading principal minors are Borel weight vectors.** For a lower triangular `A`
and an upper triangular `B`, substituting `A * X * B` multiplies `Δ_λ` by
`∏ⱼ (A j j * B j j) ^ cⱼ`. -/
theorem mvPolynomialSubst_leadingMinorProd {A B : Matrix ι ι R} (hA : A.IsLowerTriangular)
    (hB : B.IsUpperTriangular) (m : ι → ℕ) :
    mvPolynomialSubst A B (leadingMinorProd R m) =
      (∏ j, (A j j * B j j) ^ leadingMinorWeight m j) • leadingMinorProd R m := by
  rw [leadingMinorProd, map_prod, smul_eq_C_mul, ← prod_prod_le_pow_eq_prod_pow_leadingMinorWeight,
    map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ ↦ ?_
  rw [map_pow, mvPolynomialSubst_mvPolynomialMinor_of_isLowerTriangular_of_isUpperTriangular hA hB
    fun _ _ hji hi ↦ hji.trans hi, smul_eq_C_mul, mul_pow, map_pow]

/-- **The highest weight vectors `Δ_λ`.** For `g₁` lower triangular and `g₂` upper triangular,
`(g₁, g₂) • Δ_λ = ∏ⱼ ((g₁⁻¹) j j * g₂ j j) ^ cⱼ • Δ_λ`. -/
theorem mvPolynomialMatrixRep_leadingMinorProd {g : GL ι R × GL ι R}
    (h₁ : (g.1 : Matrix ι ι R).IsLowerTriangular) (h₂ : (g.2 : Matrix ι ι R).IsUpperTriangular)
    (m : ι → ℕ) :
    mvPolynomialMatrixRep R ι g (leadingMinorProd R m) =
      (∏ j, ((g.1⁻¹ : GL ι R) j j * g.2 j j) ^ leadingMinorWeight m j) •
        leadingMinorProd R m := by
  rw [mvPolynomialMatrixRep_apply, mvPolynomialSubst_leadingMinorProd ?_ h₂]
  rw [coe_units_inv]
  exact blockTriangular_inv_of_blockTriangular h₁

/-- **Both unipotent radicals fix `Δ_λ`.** A lower unitriangular `g₁` and an upper
unitriangular `g₂` fix every product of leading principal minors. -/
theorem mvPolynomialMatrixRep_leadingMinorProd_of_unitriangular {g : GL ι R × GL ι R}
    (h₁ : (g.1 : Matrix ι ι R).IsLowerTriangular) (h₁' : ∀ j, g.1 j j = 1)
    (h₂ : (g.2 : Matrix ι ι R).IsUpperUnitriangular) (m : ι → ℕ) :
    mvPolynomialMatrixRep R ι g (leadingMinorProd R m) = leadingMinorProd R m := by
  have hdiag (j : ι) : (g.1⁻¹ : GL ι R) j j = 1 := by
    rw [coe_units_inv]
    exact inv_apply_diag_of_isLowerTriangular h₁ (h₁' j)
  simp [mvPolynomialMatrixRep_leadingMinorProd h₁ h₂.isUpperTriangular, hdiag, h₂.apply_diag]

/-- **The torus weight of `Δ_λ`.** The diagonal torus acts on `Δ_λ` through the weight
`(-c, c)`: `(diag t₁, diag t₂) • Δ_λ = ∏ⱼ (t₁ⱼ⁻¹ t₂ⱼ) ^ cⱼ • Δ_λ`. -/
theorem mvPolynomialMatrixRep_diagGL_leadingMinorProd (t₁ t₂ : ι → Rˣ) (m : ι → ℕ) :
    mvPolynomialMatrixRep R ι (diagGL t₁, diagGL t₂) (leadingMinorProd R m) =
      (∏ j, (((t₁ j)⁻¹ * t₂ j : Rˣ) : R) ^ leadingMinorWeight m j) • leadingMinorProd R m := by
  rw [mvPolynomialMatrixRep_leadingMinorProd (by rw [diagGL_coe]; exact blockTriangular_diagonal _)
    (by rw [diagGL_coe]; exact blockTriangular_diagonal _), ← map_inv diagGL t₁]
  simp only [diagGL_apply, ite_true, Pi.inv_apply, Units.val_mul]

/-- **`Δ_λ` is homogeneous of degree `∑ⱼ cⱼ`.** -/
theorem isHomogeneous_leadingMinorProd (m : ι → ℕ) :
    (leadingMinorProd R m).IsHomogeneous (∑ j, leadingMinorWeight m j) := by
  have h := sum_sum_le_nsmul_eq_sum_nsmul_leadingMinorWeight (fun _ ↦ (1 : ℕ)) m
  simp only [sum_const, smul_eq_mul, mul_one] at h
  rw [← h, leadingMinorProd]
  refine IsHomogeneous.prod _ _ _ fun a _ ↦ ?_
  rw [mul_comm, ← Fintype.card_subtype]
  exact (isHomogeneous_mvPolynomialMinor R _ _).pow _

section Normalization

open MonomialOrder

/- The lexicographic lemmas on minors use the decidable equality of `{j // j ≤ a}` coming from its
linear order; `convert` identifies it with the one used in `leadingMinorProd`. -/

private theorem monic_rename_toLex_mvPolynomialMinor_le (a : ι) : lex.Monic (rename toLex
    (mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val)) := by
  have hval : StrictMono (Subtype.val : {j // j ≤ a} → ι) := Subtype.strictMono_coe _
  convert monic_rename_toLex_mvPolynomialMinor R hval hval

private theorem degree_rename_toLex_mvPolynomialMinor_le [Nontrivial R] (a : ι) :
    lex.degree (rename toLex (mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val)) =
      ∑ j with j ≤ a, Finsupp.single (toLex (j, j)) 1 := by
  rw [sum_subtype (p := fun j ↦ j ≤ a) (F := inferInstance) _ (by simp)]
  have hval : StrictMono (Subtype.val : {j // j ≤ a} → ι) := Subtype.strictMono_coe _
  convert degree_rename_toLex_mvPolynomialMinor R hval hval

/-- For the row-major lexicographic order on the variables, `Δ_λ` is monic. -/
theorem monic_rename_toLex_leadingMinorProd (m : ι → ℕ) :
    lex.Monic (rename toLex (leadingMinorProd R m)) := by
  rw [leadingMinorProd, map_prod]
  exact Monic.prod fun a _ ↦ by
    rw [map_pow]
    exact (monic_rename_toLex_mvPolynomialMinor_le a).pow

/-- For the row-major lexicographic order on the variables, the leading monomial of `Δ_λ` is the
diagonal monomial `∏ⱼ X (j, j) ^ cⱼ`. -/
theorem degree_rename_toLex_leadingMinorProd [Nontrivial R] (m : ι → ℕ) :
    lex.degree (rename toLex (leadingMinorProd R m)) =
      ∑ j, Finsupp.single (toLex (j, j)) (leadingMinorWeight m j) := by
  have hnil (a : ι) : ¬IsNilpotent (lex.leadingCoeff (rename toLex
      (mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val))) := by
    rw [(monic_rename_toLex_mvPolynomialMinor_le a).leadingCoeff_eq_one]
    exact not_isNilpotent_one
  rw [leadingMinorProd, map_prod, degree_prod_of_regular fun a _ ↦ by
    rw [map_pow, (monic_rename_toLex_mvPolynomialMinor_le a).pow.leadingCoeff_eq_one]
    exact isRegular_one]
  simp_rw [map_pow, degree_pow_of_not_isNilpotent _ (hnil _),
    degree_rename_toLex_mvPolynomialMinor_le, sum_sum_le_nsmul_eq_sum_nsmul_leadingMinorWeight,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **Normalization of `Δ_λ`.** The diagonal monomial `∏ⱼ X (j, j) ^ cⱼ` occurs in the product
of leading principal minors with coefficient `1`. -/
theorem coeff_diag_leadingMinorProd (m : ι → ℕ) :
    (leadingMinorProd R m).coeff (∑ j, Finsupp.single (j, j) (leadingMinorWeight m j)) = 1 := by
  nontriviality R
  rw [← coeff_rename_mapDomain toLex toLex.injective, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  rw [← degree_rename_toLex_leadingMinorProd (R := R)]
  exact (monic_rename_toLex_leadingMinorProd m).coeff_degree

/-- Over a nontrivial ring, the products of leading principal minors are nonzero. -/
theorem leadingMinorProd_ne_zero [Nontrivial R] (m : ι → ℕ) : leadingMinorProd R m ≠ 0 :=
  fun h ↦ by simpa [h] using coeff_diag_leadingMinorProd (R := R) m

end Normalization

end TauCeti
