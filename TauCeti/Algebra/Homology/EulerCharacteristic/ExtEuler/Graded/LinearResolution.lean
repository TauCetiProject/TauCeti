/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# The signed Poincaré polynomial of a linear resolution

If `M` has a linear graded projective resolution and `N` is concentrated in internal degree
zero, then `Extⁿ(M,N{j})` vanishes unless `j = n`. Its target-shift graded dimension is therefore
the single monomial `dim Extⁿ(M,N{n}) q⁻ⁿ`.

For an Euler-admissible pair and any uniform cohomological vanishing bound `b`, this gives
`χ_q(M,N) = ∑ n < b, (-1)ⁿ dim Extⁿ(M,N{n}) q⁻ⁿ`. Equivalently, applying
`LaurentPolynomial.invert` to `χ_q` evaluates the diagonal Ext Poincaré polynomial
`TauCeti.diagonalExtPoincarePolynomial`, `∑ n < b, dim Extⁿ(M,N{n}) tⁿ`, at `t = -q`.
This identifies the polynomial substitution and involution used to compare graded Cartan and
Poincaré matrices. Finiteness and eventual vanishing are explicit hypotheses; a linear resolution
alone does not imply them. The diagonal Poincaré polynomial itself, and the matrix
`TauCeti.diagonalExtPoincareMatrix` of these polynomials for a family of graded modules, are
defined for arbitrary graded modules, and do not depend on `b` once `b` bounds the cohomological
support (`TauCeti.diagonalExtPoincarePolynomial_eq_of_le`).

The statements include cohomological degree zero and do not require a nonnegative algebra
grading, semisimplicity, or finite-dimensionality of the algebra.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for the diagonal Ext criterion and the Cartan/Poincaré series identity.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Section 2.2,
  for the target-shift q-Euler convention.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

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

variable [DirectSum.Decomposition 𝒜]

namespace GradedProjectiveResolution

variable {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
  (hr : r.IsLinear) (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥)

include hr hN

/-- The graded dimension of Ext from a linearly resolved module into a degree-zero target
is a single monomial, with exponent the negative cohomological degree. -/
theorem IsLinear.gradedExtDimension_eq (n : ℕ)
    (h : HasFiniteLaurentSupport k (GradedExt.{w} (GradedModuleCat.shift 𝒜) M N n)) :
    gradedExtDimension k (GradedModuleCat.shift 𝒜) h =
      C (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) * T (-(n : ℤ)) := by
  have hzero (j : ℤ) (hj : j ∉ ({(n : ℤ)} : Finset ℤ)) :
      Subsingleton (GradedExt.{w} (GradedModuleCat.shift 𝒜) M N n j) := by
    have : Subsingleton (Ext.{w} M ((GradedModuleCat.shiftFunctor j).obj N) n) := by
      rw [GradedModuleCat.shiftFunctor_obj]
      exact hr.subsingleton_ext_shiftObj_of_ne hN n j (by simpa [ne_comm] using hj)
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 j).app N) n).injective.subsingleton
  rw [gradedExtDimension_eq_targetShiftGradedDimension,
    targetShiftGradedDimension_eq_sum h {(n : ℤ)} hzero, Finset.sum_singleton,
    (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 n).app N) n).finrank_eq,
    GradedModuleCat.shiftFunctor_obj]

/-- For a linear resolution and a degree-zero target, the q-Euler value is the finite
signed diagonal Ext polynomial in `q⁻¹`. Any uniform cohomological vanishing bound may be used. -/
theorem IsLinear.gradedExtEuler_eq_sum
    (h : IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) M N) {b : ℕ}
    (hb : IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) M N b) :
    gradedExtEuler k (GradedModuleCat.shift 𝒜) h =
      ∑ n ∈ Finset.range b, ((-1 : ℤ) ^ n) •
        (C (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) * T (-(n : ℤ))) := by
  rw [gradedExtEuler_eq k _ h hb]
  have heq (b : ℕ) : truncatedGradedExtEuler k (GradedModuleCat.shift 𝒜) h.internallyFinite b =
      ∑ n ∈ Finset.range b, ((-1 : ℤ) ^ n) •
        (C (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) * T (-(n : ℤ))) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [truncatedGradedExtEuler_succ, Finset.sum_range_succ, ih,
        hr.gradedExtDimension_eq hN]
  exact heq b

/-- The coefficient of `q⁻ⁿ` in the q-Euler value is the signed dimension of diagonal Ext.
No choice of truncation bound occurs in this coefficient formula. -/
theorem IsLinear.coeff_gradedExtEuler_neg_natCast
    (h : IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) M N) (n : ℕ) :
    (gradedExtEuler k (GradedModuleCat.shift 𝒜) h).coeff (-(n : ℤ)) =
      (-1 : ℤ) ^ n * (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) := by
  classical
  obtain ⟨b, hb⟩ := h.bounded.exists_bound
  rw [hr.gradedExtEuler_eq_sum hN h (hb.mono (le_max_left b (n + 1)))]
  simp only [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_smul, Finset.sum_apply', Finsupp.smul_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, neg_inj, Nat.cast_inj]
  rw [Finset.sum_eq_single n]
  · simp
  · intro m _ hmn
    simp [hmn]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

/-- Inverting the q-Euler value of a linearly resolved module against a degree-zero target
is evaluation of the diagonal Ext Poincaré polynomial at `-q`. -/
theorem IsLinear.invert_gradedExtEuler_eq_eval₂
    (h : IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) M N) {b : ℕ}
    (hb : IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) M N b) :
    invert (gradedExtEuler k (GradedModuleCat.shift 𝒜) h) =
      (diagonalExtPoincarePolynomial.{w} k M N b).eval₂ C (-T 1) := by
  rw [hr.gradedExtEuler_eq_sum hN h hb, map_sum, diagonalExtPoincarePolynomial,
    Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_zsmul, map_mul, invert_C, invert_T, neg_neg,
    Polynomial.eval₂_monomial]
  rw [neg_pow (T 1 : LaurentPolynomial ℤ), T_pow, mul_one, zsmul_eq_mul]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  ring

end GradedProjectiveResolution

end TauCeti
