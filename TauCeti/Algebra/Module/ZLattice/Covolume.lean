/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The covolume of a lattice in an inner product space

In a finite-dimensional real inner product space, equipped with the volume measure of its inner
product, the square of the covolume of a `ℤ`-lattice is the determinant of the Gram matrix of any
of its `ℤ`-bases. This is the metric form of `ZLattice.covolume_eq_det`, which computes the
covolume in the coordinate space `ι → ℝ` as the absolute determinant of a basis.

The proof measures a fundamental parallelepiped against an orthonormal basis: the parallelepiped
of an orthonormal basis has volume `1`, so the covolume is the absolute value of the determinant
`M` of the lattice basis in orthonormal coordinates, and the Gram matrix is `Mᵀ M`.

## Main results

* `ZLattice.covolume_sq_eq_det_gram`: `covolume L ^ 2` is the determinant of the Gram matrix of
  any `ℤ`-basis of `L`.
-/

public section

open Module MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The square of the covolume of a lattice in a finite-dimensional real inner product space is
the determinant of the Gram matrix of any `ℤ`-basis of the lattice. -/
theorem _root_.ZLattice.covolume_sq_eq_det_gram (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ fun i ↦ (b i : E)).det := by
  have hcard : finrank ℝ E = Fintype.card ι := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hcard.symm).symm
  -- The matrix of orthonormal coordinates of the basis vectors.
  have hM : o.toBasis.toMatrix ((↑) ∘ b) = Matrix.of fun i j ↦ o.repr (b j : E) i := by
    ext i j
    simp [Basis.toMatrix_apply]
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one,
    mul_one, sq_abs, Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul,
    Matrix.det_conjTranspose, star_trivial, Basis.det_apply, hM, sq]

end TauCeti
