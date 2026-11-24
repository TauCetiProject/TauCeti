/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Module.ZLattice.ChangeOfVariables
import TauCeti.Analysis.Complex.Euclidean.Space
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Covolumes of lattices in `ℂ^g` from their period matrices

A complex torus `ℂ^g / Λ`, such as the complex points of an abelian variety, is described by the
`g × 2g` complex *period matrix* whose columns are a `ℤ`-basis of `Λ`. This file computes the
Lebesgue covolume of `Λ` in `ι → ℂ` (with the product of the Lebesgue measures of the factors
`ℂ ≅ ℝ²`) from its period matrix.

* For a full lattice `L` with a `ℤ`-basis `b` indexed by `ι ⊕ ι` and period matrix `P`, so that
  `b k = (P i k)ᵢ`, the covolume of `L` is the absolute value of the determinant of the real
  `2g × 2g` matrix whose rows are the real and the imaginary parts of the rows of `P`
  (`ZLattice.covolume_eq_abs_det_fromRows_re_im`).
* **Normalized periods.** For the period matrix `(1 | τ)`, the lattice `ℤ^g + τ ℤ^g`, the real
  matrix is block upper triangular with diagonal blocks `1` and `Im τ`, so the covolume is
  `|det (Im τ)|` (`ZLattice.covolume_eq_abs_det_im`). For `τ` in the Siegel upper half space,
  `Im τ` is positive definite and this is `det (Im τ)`. When `Im τ` is invertible, the columns of
  `(1 | τ)` form a real basis `Matrix.normalizedPeriodBasis τ` of `ι → ℂ`, and the `ℤ`-span of
  this basis is a lattice of covolume `|det (Im τ)|`
  (`ZLattice.covolume_span_normalizedPeriodBasis`).
* **General periods.** A `ℂ`-linear automorphism `A` of a finite-dimensional complex normed space
  is an `ℝ`-linear map of determinant `|det A|²`, so pulling a lattice back along it divides its
  covolume by `|det A|²` (`ZLattice.covolume_comap_restrictScalars`). Hence for a period matrix
  `(Ω₁ | Ω₂)` with `Ω₁` invertible, which is `Ω₁ (1 | τ)` for `τ = Ω₁⁻¹ Ω₂`, the covolume is
  `|det Ω₁|² |det (Im τ)|` (`ZLattice.covolume_eq_normSq_det_mul_abs_det_im`).

For an abelian variety `A(ℂ) = ℂ^g / Λ` with linear coordinates `z₁, …, z_g`, the integral of
`(i^(g²) / 2^g) dz₁ ∧ ⋯ ∧ dz_g ∧ conj (dz₁ ∧ ⋯ ∧ dz_g)` over `A(ℂ)` is the covolume of `Λ`, so
these formulas compute the squared Faltings norm `‖dz₁ ∧ ⋯ ∧ dz_g‖²` in terms of the periods.

## References

* G. Faltings and C.-L. Chai, *Degeneration of abelian varieties*, Ergebnisse der Mathematik 22,
  Springer (1990), Ch. V, proof of Proposition 4.5.
* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch (d'après G. Faltings)*,
  Séminaire Bourbaki 616 (1983/84), §1.10.
-/

public section

open Module Submodule MeasureTheory Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real period matrix of `(1 | τ)` is block upper triangular, with diagonal blocks `1` and
`Im τ`, so its determinant is `det (Im τ)`. -/
theorem det_fromRows_re_im_fromCols_one (τ : Matrix ι ι ℂ) :
    (fromRows ((fromCols (1 : Matrix ι ι ℂ) τ).map Complex.re)
      ((fromCols (1 : Matrix ι ι ℂ) τ).map Complex.im)).det = (τ.map Complex.im).det := by
  have h : fromRows ((fromCols (1 : Matrix ι ι ℂ) τ).map Complex.re)
      ((fromCols (1 : Matrix ι ι ℂ) τ).map Complex.im) =
      fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im) := by
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [hij]
  rw [h, det_fromBlocks_zero₂₁, det_one, one_mul]

/-- For a complex square matrix `τ` whose imaginary part is invertible, the columns of the period
matrix `(1 | τ)` form a real basis of `ι → ℂ`. Its `ℤ`-span is the lattice `ℤ^g + τ ℤ^g`, whose
covolume is `ZLattice.covolume_span_normalizedPeriodBasis`. -/
noncomputable def normalizedPeriodBasis (τ : Matrix ι ι ℂ) (hτ : (τ.map Complex.im).det ≠ 0) :
    Basis (ι ⊕ ι) ℝ (ι → ℂ) :=
  (Pi.basisFun ℝ (ι ⊕ ι)).map <|
    (toLinearEquiv (Pi.basisFun ℝ (ι ⊕ ι))
      (fromRows ((fromCols 1 τ).map Complex.re) ((fromCols 1 τ).map Complex.im))
      (by rw [det_fromRows_re_im_fromCols_one]; exact isUnit_iff_ne_zero.2 hτ)).trans
    (TauCeti.complexToRealPi ι).symm.toLinearEquiv

/-- The `k`-th vector of `normalizedPeriodBasis τ` is the `k`-th column of `(1 | τ)`. -/
@[simp]
theorem normalizedPeriodBasis_apply (τ : Matrix ι ι ℂ) (hτ : (τ.map Complex.im).det ≠ 0) (k : ι ⊕ ι)
    (i : ι) : normalizedPeriodBasis τ hτ k i = fromCols 1 τ i k := by
  apply Complex.ext <;>
    simp [normalizedPeriodBasis, toLinearEquiv_apply, toLin_eq_toLin']

end Matrix

namespace ZLattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The covolume of a lattice in `ℂ^g` from its period matrix.** If the `ℤ`-basis `b` of a full
lattice `L` in `ι → ℂ` has period matrix `P`, that is `b k = (P i k)ᵢ`, then the covolume of `L`
is the absolute value of the determinant of the real matrix whose rows are the real and the
imaginary parts of the rows of `P`. -/
theorem covolume_eq_abs_det_fromRows_re_im (L : Submodule ℤ (ι → ℂ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (P : Matrix ι (ι ⊕ ι) ℂ) (b : Basis (ι ⊕ ι) ℤ L)
    (hb : ∀ i k, (b k : ι → ℂ) i = P i k) :
    covolume L = |(fromRows (P.map Complex.re) (P.map Complex.im)).det| := by
  -- Move `L` to `ι ⊕ ι → ℝ` along the volume-preserving real coordinates.
  let e : (ι ⊕ ι → ℝ) ≃L[ℝ] (ι → ℂ) := (TauCeti.complexToRealPi ι).symm
  have he : MeasurePreserving e volume volume :=
    TauCeti.volume_preserving_complexToRealPi.symm
      (TauCeti.complexToRealPi ι).toHomeomorph.toMeasurableEquiv
  rw [← covolume_comap L volume volume he,
    covolume_eq_det (ZLattice.comap ℝ L e.toLinearMap) (b.ofZLatticeComap ℝ L e.toLinearEquiv),
    ← det_transpose]
  congr 2
  ext (i | i) k <;>
    simp only [transpose_apply, of_apply, Function.comp_apply, Basis.ofZLatticeComap_apply] <;>
    simp [e, hb]

/-- **The covolume of `ℤ^g + τ ℤ^g`.** If the `ℤ`-basis `b` of a full lattice `L` in `ι → ℂ` has
period matrix `(1 | τ)`, then the covolume of `L` is `|det (Im τ)|`. For `τ` in the Siegel upper
half space this is `det (Im τ)`. -/
theorem covolume_eq_abs_det_im (L : Submodule ℤ (ι → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (τ : Matrix ι ι ℂ) (b : Basis (ι ⊕ ι) ℤ L) (hb : ∀ i k, (b k : ι → ℂ) i = fromCols 1 τ i k) :
    covolume L = |(τ.map Complex.im).det| := by
  rw [covolume_eq_abs_det_fromRows_re_im L _ b hb, Matrix.det_fromRows_re_im_fromCols_one]

/-- **The covolume of a lattice with period matrix `(Ω₁ | Ω₂)`.** If the `ℤ`-basis `b` of a full
lattice `L` in `ι → ℂ` has period matrix `(Ω₁ | Ω₂)` with `Ω₁` invertible, then the covolume of
`L` is `|det Ω₁|² |det (Im τ)|` for the normalized period matrix `τ = Ω₁⁻¹ Ω₂`. -/
theorem covolume_eq_normSq_det_mul_abs_det_im (L : Submodule ℤ (ι → ℂ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (Ω₁ Ω₂ : Matrix ι ι ℂ) (hΩ₁ : IsUnit Ω₁.det) (b : Basis (ι ⊕ ι) ℤ L)
    (hb : ∀ i k, (b k : ι → ℂ) i = fromCols Ω₁ Ω₂ i k) :
    covolume L = Complex.normSq Ω₁.det * |((Ω₁⁻¹ * Ω₂).map Complex.im).det| := by
  -- Pull `L` back along `Ω₁`: the pulled-back basis has period matrix `(1 | Ω₁⁻¹ Ω₂)`.
  let A : (ι → ℂ) ≃L[ℂ] (ι → ℂ) :=
    (Matrix.toLinearEquiv (Pi.basisFun ℂ ι) Ω₁ hΩ₁).toContinuousLinearEquiv
  have hA : LinearMap.det (A.toLinearMap : (ι → ℂ) →ₗ[ℂ] ι → ℂ) = Ω₁.det := by
    -- The linear map underlying `A` is `toLin` of `Ω₁` in the standard basis.
    have hlin : (A.toLinearMap : (ι → ℂ) →ₗ[ℂ] ι → ℂ) =
        toLin (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) Ω₁ := by
      ext x
      simp [A, toLinearEquiv_apply]
    rw [hlin, LinearMap.det_toLin]
  let e := (A.restrictScalars ℝ).toLinearEquiv
  have hcols : ∀ i k, (b.ofZLatticeComap ℝ L e k : ι → ℂ) i = fromCols 1 (Ω₁⁻¹ * Ω₂) i k := by
    intro i k
    rw [Basis.ofZLatticeComap_apply]
    have hk : (b k : ι → ℂ) = Ω₁ *ᵥ fun i ↦ fromCols 1 (Ω₁⁻¹ * Ω₂) i k := by
      ext i
      rcases k with k | k <;> simp [hb, mulVec, dotProduct, ← Matrix.mul_apply,
        mul_nonsing_inv_cancel_left _ _ hΩ₁]
    -- `e` multiplies by `Ω₁`, so `e⁻¹` sends `b k` back to the column of `(1 | Ω₁⁻¹ Ω₂)`.
    have hsymm : e.symm (b k) = fun i ↦ fromCols 1 (Ω₁⁻¹ * Ω₂) i k := by
      rw [LinearEquiv.symm_apply_eq, hk]
      simp [e, A, toLinearEquiv_apply, toLin_eq_toLin']
    exact congr_fun hsymm i
  have h := (covolume_comap_restrictScalars L A).symm.trans
    (covolume_eq_abs_det_im _ _ (b.ofZLatticeComap ℝ L e) hcols)
  rw [hA] at h
  have hne : Complex.normSq Ω₁.det ≠ 0 := Complex.normSq_pos.2 hΩ₁.ne_zero |>.ne'
  rw [← h, mul_inv_cancel_left₀ hne]

/-- **The covolume of `ℤ^g + τ ℤ^g`.** For a complex square matrix `τ` whose imaginary part is
invertible, the `ℤ`-span of the columns of `(1 | τ)` is a full lattice in `ι → ℂ` of covolume
`|det (Im τ)|`. -/
theorem covolume_span_normalizedPeriodBasis (τ : Matrix ι ι ℂ) (hτ : (τ.map Complex.im).det ≠ 0) :
    covolume (span ℤ (Set.range (τ.normalizedPeriodBasis hτ))) = |(τ.map Complex.im).det| :=
  covolume_eq_abs_det_im _ τ ((τ.normalizedPeriodBasis hτ).restrictScalars ℤ) fun i k ↦ by
    rw [Basis.restrictScalars_apply, normalizedPeriodBasis_apply]

end ZLattice
