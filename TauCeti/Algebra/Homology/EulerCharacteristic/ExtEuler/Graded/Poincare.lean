/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# The diagonal Ext Poincaré polynomial

For graded modules `M` and `N`, the **diagonal Ext Poincaré polynomial**
`TauCeti.diagonalExtPoincarePolynomial` is `∑ n < b, dim_k Extⁿ(M,N{n}) tⁿ`, truncated below a
cohomological degree `b`. It records only the diagonal bigraded pieces `Ext^{n,n}(M,N)`. For a
family `S` of graded modules, `TauCeti.diagonalExtPoincareMatrix` collects these polynomials
into a matrix with `(i, j)` entry the polynomial of `(Sᵢ, Sⱼ)`.

Both are defined for arbitrary graded modules, and neither depends on `b` once `b` bounds the
cohomological support (`TauCeti.diagonalExtPoincarePolynomial_eq_of_le` and
`TauCeti.diagonalExtPoincareMatrix_eq_of_le`). The coefficient of `tⁿ` is read off by
`TauCeti.coeff_diagonalExtPoincarePolynomial`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 2.11, for the Poincaré series of diagonal Ext.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M N : GradedModuleCat.{v} 𝒜} [HasExt.{w} (GradedModuleCat.{v} 𝒜)]
  {I : Type*}

variable (k) in
/-- The **diagonal Ext Poincaré polynomial** `∑ n < b, dim_k Extⁿ(M,N{n}) tⁿ` of two graded
modules, truncated below the cohomological degree `b`. It records only the diagonal bigraded
pieces `Ext^{n,n}(M,N)`; when `M` has a linear resolution and `N` is concentrated in degree zero,
these are the only nonzero pieces. -/
noncomputable def diagonalExtPoincarePolynomial (M N : GradedModuleCat.{v} 𝒜) (b : ℕ) :
    Polynomial ℤ :=
  ∑ n ∈ Finset.range b, Polynomial.monomial n (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ)

variable (k) in
/-- The diagonal Ext Poincaré polynomial is the truncated sum of the monomials
`dim_k Extⁿ(M,N{n}) tⁿ`. -/
theorem diagonalExtPoincarePolynomial_def (M N : GradedModuleCat.{v} 𝒜) (b : ℕ) :
    diagonalExtPoincarePolynomial.{w} k M N b =
      ∑ n ∈ Finset.range b,
        Polynomial.monomial n (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) := by
  rw [diagonalExtPoincarePolynomial]

variable (k) in
/-- The coefficient of `tⁿ` in the diagonal Ext Poincaré polynomial is `dim_k Extⁿ(M,N{n})`
below the truncation degree, and zero from it on. -/
@[simp]
theorem coeff_diagonalExtPoincarePolynomial (M N : GradedModuleCat.{v} 𝒜) (b n : ℕ) :
    (diagonalExtPoincarePolynomial.{w} k M N b).coeff n =
      if n < b then (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) else 0 := by
  simp [diagonalExtPoincarePolynomial_def, Polynomial.coeff_monomial]

/-- The diagonal Ext Poincaré polynomial is unchanged by raising its truncation degree past a
cohomological vanishing bound. -/
theorem diagonalExtPoincarePolynomial_eq_of_le {b b' : ℕ}
    (hb : IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) M N b) (hbb' : b ≤ b') :
    diagonalExtPoincarePolynomial.{w} k M N b' = diagonalExtPoincarePolynomial.{w} k M N b := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 hbb') fun n _ hn ↦ ?_).symm
  have : Subsingleton (Ext.{w} M (N.shiftObj n) n) := by
    have := hb.subsingleton (by simpa using hn) n
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 n).app N) n).symm.injective.subsingleton
  simp [Module.finrank_zero_of_subsingleton]

variable (k) in
/-- The **diagonal Ext Poincaré matrix** of a family `S` of graded modules, truncated below the
cohomological degree `b`: its `(i, j)` entry is the diagonal Ext Poincaré polynomial
`∑ n < b, dim_k Extⁿ(Sᵢ, Sⱼ{n}) tⁿ`. -/
noncomputable def diagonalExtPoincareMatrix (S : I → GradedModuleCat.{v} 𝒜) (b : ℕ) :
    Matrix I I (Polynomial ℤ) :=
  Matrix.of fun i j ↦ diagonalExtPoincarePolynomial.{w} k (S i) (S j) b

variable (k) in
/-- An entry of the diagonal Ext Poincaré matrix is the diagonal Ext Poincaré polynomial of the
corresponding pair. -/
@[simp]
theorem diagonalExtPoincareMatrix_apply (S : I → GradedModuleCat.{v} 𝒜) (b : ℕ)
    (i j : I) :
    diagonalExtPoincareMatrix.{w} k S b i j =
      diagonalExtPoincarePolynomial.{w} k (S i) (S j) b := by
  rw [diagonalExtPoincareMatrix, Matrix.of_apply]

/-- The diagonal Ext Poincaré matrix is unchanged by raising its truncation degree past a common
cohomological vanishing bound of all pairs in the family. -/
theorem diagonalExtPoincareMatrix_eq_of_le {S : I → GradedModuleCat.{v} 𝒜}
    {b b' : ℕ} (hb : ∀ i j, IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) (S i) (S j) b)
    (hbb' : b ≤ b') :
    diagonalExtPoincareMatrix.{w} k S b' = diagonalExtPoincareMatrix.{w} k S b :=
  Matrix.ext fun i j ↦ diagonalExtPoincarePolynomial_eq_of_le (hb i j) hbb'

end TauCeti
