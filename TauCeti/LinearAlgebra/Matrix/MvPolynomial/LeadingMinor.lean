/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal

/-!
# Products of leading principal minors as highest weight vectors

Let `R` be a commutative ring and `ι` a finite linearly ordered index type. The group
`GL_ι(R) × GL_ι(R)` acts on the polynomial functions `MvPolynomial (ι × ι) R` in the entries of a
matrix by

`((g₁, g₂) • f)(X) = f (g₁⁻¹ * X * g₂)`.

This is the action whose homogeneous components carry the Cauchy decomposition
`⊕_λ F_λ^∨ ⊗ F_λ` into tensor products of Weyl modules. With respect to the lower triangular
Borel subgroup in the first factor and the upper triangular Borel subgroup in the second, the
highest weight line of the summand indexed by `λ = (c₁ ≥ c₂ ≥ ⋯)` is spanned by the product of
leading principal minors

`Δ_λ = ∏ᵢ Δᵢ ^ (cᵢ - cᵢ₊₁)`,

where `Δᵢ` is the determinant of the upper left `i × i` block of the generic matrix. We index
these products by the exponents: for `m : ι → ℕ`, `TauCeti.leadingMinorProd R m` is the product
over `a : ι` of the minors on `{j | j ≤ a}` raised to the power `m a`, and its weight is
`TauCeti.leadingMinorWeight m j = ∑_{a ≥ j} m a`, which is antitone in `j`. For `ι = Fin u` and
`λ = (c₁ ≥ ⋯ ≥ c_u)` the exponents are `m i = cᵢ - cᵢ₊₁` with `c_{u+1} = 0`.

The substitution `f ↦ f (A * X * B)` is defined for arbitrary matrices `A` and `B`
(`Matrix.mvPolynomialSubst`). For a lower triangular `A` and an upper triangular `B`, the minor on
an initial segment `p` of `X ↦ A * X * B` is the product of the minors of `A`, `X` and `B` on `p`.
Hence substitution multiplies a leading minor by the diagonal entries of `A` and `B` on that
segment, and `Δ_λ` by `∏ⱼ (A j j * B j j) ^ cⱼ`.

## Main definitions

* `Matrix.mvPolynomialSubst A B`: the algebra endomorphism `f ↦ f (A * X * B)` of
  `MvPolynomial (ι × ι) R`.
* `TauCeti.mvPolynomialMatrixRep R ι`: the representation of `GL ι R × GL ι R` on
  `MvPolynomial (ι × ι) R` by `(g₁, g₂) • f = f (g₁⁻¹ * X * g₂)`.
* `TauCeti.leadingMinorProd R m`: the product of leading principal minors with exponents `m`.
* `TauCeti.leadingMinorWeight m`: its weight `c`, with `c j = ∑_{a ≥ j} m a`.

## Main results

* `MvPolynomial.IsHomogeneous.mvPolynomialSubst`: substitution preserves homogeneous components.
* `Matrix.mvPolynomialSubst_mvPolynomialMinor_of_isLowerTriangular_of_isUpperTriangular`: the
  minor on a down-closed set of indices is a weight vector for the two triangular Borel subgroups.
* `TauCeti.mvPolynomialMatrixRep_leadingMinorProd`: `(g₁, g₂) • Δ_λ` is the multiple of `Δ_λ` by
  `∏ⱼ ((g₁⁻¹) j j * g₂ j j) ^ cⱼ` for lower triangular `g₁` and upper triangular `g₂`;
  `TauCeti.mvPolynomialMatrixRep_leadingMinorProd_of_unitriangular` (both unipotent
  radicals fix `Δ_λ`) and `TauCeti.mvPolynomialMatrixRep_diagGL_leadingMinorProd` (the torus acts
  through the weight `(-c, c)`) are the two halves of this statement.
* `TauCeti.isHomogeneous_leadingMinorProd`: `Δ_λ` is homogeneous of degree `∑ⱼ cⱼ`.
* `TauCeti.monic_rename_toLex_leadingMinorProd` and
  `TauCeti.degree_rename_toLex_leadingMinorProd`: for the row-major lexicographic order, `Δ_λ` is
  monic with leading monomial the diagonal monomial `∏ⱼ X (j, j) ^ cⱼ`.
* `TauCeti.coeff_leadingMinorProd`: the diagonal monomial has coefficient `1` in `Δ_λ`; in
  particular `Δ_λ ≠ 0` over a nontrivial ring (`TauCeti.leadingMinorProd_ne_zero`).

## References

* E. Eischen, M. Harris, J.-S. Li and C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), Lemma 4.4.8 and (100).
-/

public section

open MvPolynomial Finset

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The substitution of `A * X * B` for the generic matrix `X`: the algebra endomorphism of the
polynomial functions in the entries of an `ι × ι` matrix sending `f` to `X ↦ f (A * X * B)`. -/
noncomputable def mvPolynomialSubst (A B : Matrix ι ι R) :
    MvPolynomial (ι × ι) R →ₐ[R] MvPolynomial (ι × ι) R :=
  aeval fun p ↦ (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R))
    p.1 p.2

/-- The defining formula of `Matrix.mvPolynomialSubst`. -/
theorem mvPolynomialSubst_apply (A B : Matrix ι ι R) (f : MvPolynomial (ι × ι) R) :
    mvPolynomialSubst A B f = aeval (fun p ↦
      (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) p.1 p.2)
        f := (rfl)

/-- Substitution replaces the variable `X (i, j)` by the `(i, j)` entry of `A * X * B`. -/
@[simp]
theorem mvPolynomialSubst_X (A B : Matrix ι ι R) (p : ι × ι) :
    mvPolynomialSubst A B (X p) =
      (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) p.1 p.2 :=
  aeval_X _ _

/-- Evaluating `f (A * X * B)` at a matrix `Z` evaluates `f` at `A * Z * B`. -/
theorem aeval_mvPolynomialSubst {S : Type*} [CommRing S] [Algebra R S] (A B : Matrix ι ι R)
    (Z : Matrix ι ι S) (f : MvPolynomial (ι × ι) R) :
    aeval (fun p ↦ Z p.1 p.2) (mvPolynomialSubst A B f) =
      aeval (fun p ↦ (A.map (algebraMap R S) * Z * B.map (algebraMap R S)) p.1 p.2) f := by
  rw [mvPolynomialSubst_apply, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext p
  simp [Matrix.mul_apply, Finset.sum_mul]

/-- The entries of `A * X * B` are linear forms. -/
theorem isHomogeneous_map_mul_mvPolynomialX_mul_map_apply (A B : Matrix ι ι R) (i j : ι) :
    (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) i j
      |>.IsHomogeneous 1 := by
  simp only [Matrix.mul_apply, Matrix.map_apply, mvPolynomialX_apply]
  exact IsHomogeneous.sum _ _ _ fun k _ ↦ by
    simpa using (IsHomogeneous.sum _ _ _ fun l _ ↦
      (isHomogeneous_C_mul_X (A i l) (l, k))).mul (isHomogeneous_C _ (B k j))

/-- Substitution sends the generic matrix `X` to `A * X * B`. -/
@[simp]
theorem mvPolynomialX_map_mvPolynomialSubst (A B : Matrix ι ι R) :
    (mvPolynomialX ι ι R).map (mvPolynomialSubst A B) =
      A.map C * mvPolynomialX ι ι R * B.map C := by
  ext i j
  simp only [map_apply, mvPolynomialX_apply, mvPolynomialSubst_X]

/-- Substituting `1 * X * 1` is the identity. -/
@[simp]
theorem mvPolynomialSubst_one_one [DecidableEq ι] :
    mvPolynomialSubst (1 : Matrix ι ι R) 1 = AlgHom.id R (MvPolynomial (ι × ι) R) := by
  refine algHom_ext fun p ↦ ?_
  rw [mvPolynomialSubst_X, ← RingHom.mapMatrix_apply, map_one, Matrix.one_mul, Matrix.mul_one]
  simp

/-- Substituting `A' * X * B'` and then `A * X * B` substitutes `A' * A * X * B * B'`. -/
theorem mvPolynomialSubst_comp_mvPolynomialSubst (A B A' B' : Matrix ι ι R) :
    (mvPolynomialSubst A B).comp (mvPolynomialSubst A' B') =
      mvPolynomialSubst (A' * A) (B * B') := by
  classical
  refine algHom_ext fun p ↦ ?_
  have hC (M : Matrix ι ι R) : (mvPolynomialSubst A B).mapMatrix (M.map C) = M.map C := by
    ext i j
    simp
  rw [AlgHom.comp_apply, mvPolynomialSubst_X, mvPolynomialSubst_X]
  calc mvPolynomialSubst A B
        ((A'.map C * mvPolynomialX ι ι R * B'.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) p.1 p.2)
      = (mvPolynomialSubst A B).mapMatrix (A'.map C * mvPolynomialX ι ι R * B'.map C) p.1 p.2 := by
        rw [AlgHom.mapMatrix_apply, map_apply]
    _ = _ := by
      rw [map_mul, map_mul, hC, hC, AlgHom.mapMatrix_apply, mvPolynomialX_map_mvPolynomialSubst,
        Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]

end Matrix

namespace MvPolynomial.IsHomogeneous

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- Substitution of `A * X * B` for the generic matrix preserves homogeneous polynomials and
their degree. -/
theorem mvPolynomialSubst {f : MvPolynomial (ι × ι) R} {d : ℕ} (hf : f.IsHomogeneous d)
    (A B : Matrix ι ι R) : (mvPolynomialSubst A B f).IsHomogeneous d := by
  rw [mvPolynomialSubst_apply]
  simpa only [one_mul] using
    hf.aeval _ fun p ↦ isHomogeneous_map_mul_mvPolynomialX_mul_map_apply A B p.1 p.2

end MvPolynomial.IsHomogeneous

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
  have hblock (M : Matrix ι ι (MvPolynomial (ι × ι) R)) :
      M.toSquareBlockProp p = M.submatrix (Subtype.val : {j // p j} → ι) Subtype.val := by
    ext
    simp [toSquareBlockProp_def]
  have hval : StrictMono (Subtype.val : {j // p j} → ι) := Subtype.strictMono_coe _
  rw [mvPolynomialMinor_eq_det_submatrix, AlgHom.map_det, AlgHom.mapMatrix_apply, ← submatrix_map,
    mvPolynomialX_map_mvPolynomialSubst, ← hblock,
    BlockTriangular.toSquareBlockProp_mul (b := id) (hB.map C) hp',
    BlockTriangular.toSquareBlockProp_mul_of_toDual (b := id) (hA.map C) hp', det_mul, det_mul,
    hblock, hblock, hblock,
    det_of_isLowerTriangular ((A.map C).submatrix Subtype.val Subtype.val)
      fun _ _ h ↦ (hA.map C) (hval h),
    det_of_isUpperTriangular (M := (B.map C).submatrix Subtype.val Subtype.val)
      fun _ _ h ↦ (hB.map C) (hval h),
    prod_subtype (p := p) (F := inferInstance) (univ.filter p) (by simp), smul_eq_C_mul, map_prod]
  simp only [submatrix_apply, map_apply, map_mul, prod_mul_distrib]
  ring

end Matrix

namespace TauCeti

open Matrix

section Representation

variable (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The representation of `GL ι R × GL ι R` on the polynomial functions in the entries of an
`ι × ι` matrix by `((g₁, g₂) • f)(X) = f (g₁⁻¹ * X * g₂)`. -/
noncomputable def mvPolynomialMatrixRep :
    Representation R (GL ι R × GL ι R) (MvPolynomial (ι × ι) R) where
  toFun g := (mvPolynomialSubst (g.1⁻¹ : GL ι R) (g.2 : Matrix ι ι R)).toLinearMap
  map_one' := LinearMap.ext fun f ↦ by simp
  map_mul' g h := LinearMap.ext fun f ↦ by
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply,
      mvPolynomialSubst_comp_mvPolynomialSubst]
    simp

variable {R ι}

/-- The defining formula of `TauCeti.mvPolynomialMatrixRep`. -/
theorem mvPolynomialMatrixRep_apply (g : GL ι R × GL ι R) (f : MvPolynomial (ι × ι) R) :
    mvPolynomialMatrixRep R ι g f =
      mvPolynomialSubst (g.1⁻¹ : GL ι R) (g.2 : Matrix ι ι R) f := (rfl)

/-- The representation acts by algebra automorphisms. -/
@[simp]
theorem mvPolynomialMatrixRep_mul (g : GL ι R × GL ι R) (f f' : MvPolynomial (ι × ι) R) :
    mvPolynomialMatrixRep R ι g (f * f') =
      mvPolynomialMatrixRep R ι g f * mvPolynomialMatrixRep R ι g f' := by
  simp only [mvPolynomialMatrixRep_apply, map_mul]

/-- Evaluating `(g₁, g₂) • f` at a matrix `Z` evaluates `f` at `g₁⁻¹ * Z * g₂`. -/
theorem eval_mvPolynomialMatrixRep (g : GL ι R × GL ι R) (f : MvPolynomial (ι × ι) R)
    (Z : Matrix ι ι R) :
    eval (fun p ↦ Z p.1 p.2) (mvPolynomialMatrixRep R ι g f) =
      eval (fun p ↦ ((g.1⁻¹ : GL ι R) * Z * (g.2 : Matrix ι ι R) : Matrix ι ι R) p.1 p.2) f := by
  simpa [mvPolynomialMatrixRep_apply] using
    aeval_mvPolynomialSubst (S := R) (g.1⁻¹ : GL ι R) (g.2 : Matrix ι ι R) Z f

/-- The representation preserves homogeneous polynomials and their degree. -/
theorem isHomogeneous_mvPolynomialMatrixRep {f : MvPolynomial (ι × ι) R} {d : ℕ}
    (hf : f.IsHomogeneous d) (g : GL ι R × GL ι R) :
    (mvPolynomialMatrixRep R ι g f).IsHomogeneous d :=
  hf.mvPolynomialSubst _ _

end Representation

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

/-- The weight of a product of leading principal minors is a partition: it decreases along `ι`. -/
theorem antitone_leadingMinorWeight (m : ι → ℕ) : Antitone (leadingMinorWeight m) :=
  fun _ _ hij ↦ sum_le_sum_of_subset_of_nonneg
    (fun _ ha ↦ by simpa using hij.trans (by simpa using ha)) fun _ _ _ ↦ Nat.zero_le _

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
    (h₂ : (g.2 : Matrix ι ι R).IsUpperTriangular) (h₂' : ∀ j, g.2 j j = 1) (m : ι → ℕ) :
    mvPolynomialMatrixRep R ι g (leadingMinorProd R m) = leadingMinorProd R m := by
  have hinv : ((g.1⁻¹ : GL ι R) : Matrix ι ι R).IsLowerTriangular := by
    rw [coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular h₁
  have hdiag (j : ι) : (g.1⁻¹ : GL ι R) j j = 1 := by
    have h := congrArg (fun M : Matrix ι ι R ↦ M j j) (congrArg Units.val (inv_mul_cancel g.1))
    simp only [Units.val_mul, Units.val_one, one_apply_eq] at h
    rwa [mul_apply_diag_of_isLowerTriangular hinv h₁, h₁', mul_one] at h
  simp [mvPolynomialMatrixRep_leadingMinorProd h₁ h₂, hdiag, h₂']

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

omit [Fintype ι] in
/-- The order on `{j // j ≤ a}` used by the lexicographic lemmas is the one induced from `ι`. -/
private theorem strictMono_val_le (a : ι) : StrictMono (Subtype.val : {j // j ≤ a} → ι) :=
  fun _ _ h ↦ h

/- The lexicographic lemmas on minors use the decidable equality of `{j // j ≤ a}` coming from its
linear order; `convert` identifies it with the one used in `leadingMinorProd`. -/

private theorem monic_rename_toLex_mvPolynomialMinor_le (a : ι) : lex.Monic (rename toLex
    (mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val)) := by
  convert monic_rename_toLex_mvPolynomialMinor R (strictMono_val_le a) (strictMono_val_le a)

private theorem degree_rename_toLex_mvPolynomialMinor_le [Nontrivial R] (a : ι) :
    lex.degree (rename toLex (mvPolynomialMinor R (Subtype.val : {j // j ≤ a} → ι) Subtype.val)) =
      ∑ j with j ≤ a, Finsupp.single (toLex (j, j)) 1 := by
  rw [sum_subtype (p := fun j ↦ j ≤ a) (F := inferInstance) _ (by simp)]
  convert degree_rename_toLex_mvPolynomialMinor R (strictMono_val_le a) (strictMono_val_le a)

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
theorem coeff_leadingMinorProd (m : ι → ℕ) :
    (leadingMinorProd R m).coeff (∑ j, Finsupp.single (j, j) (leadingMinorWeight m j)) = 1 := by
  nontriviality R
  rw [← coeff_rename_mapDomain toLex toLex.injective, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  rw [← degree_rename_toLex_leadingMinorProd (R := R)]
  exact (monic_rename_toLex_leadingMinorProd m).coeff_degree

/-- Over a nontrivial ring, the products of leading principal minors are nonzero. -/
theorem leadingMinorProd_ne_zero [Nontrivial R] (m : ι → ℕ) : leadingMinorProd R m ≠ 0 :=
  fun h ↦ by simpa [h] using coeff_leadingMinorProd (R := R) m

end Normalization

end TauCeti
