/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular.Real
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Commutator
public import TauCeti.Algebra.Lie.GeneralLinear.Borel
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Complete solvability of the real-diagonal upper-triangular Lie algebra

Upper-triangular matrices over an `RCLike` field whose diagonal entries are real form a real
Lie algebra. It is solvable and each adjoint characteristic polynomial splits over the reals.
Equivalently, every eigenvalue of the complexified real adjoint operator is real.
The coefficient field may be any `RCLike` field and the index type may be any finite linearly
ordered type. For any faithful real Lie representation, the same adjoint conclusions hold at
each vector whose matrix image is upper triangular with real diagonal.

## Main definitions and results

* `TauCeti.upperTriangularRealDiagonalLieSubalgebra`: the actual real matrix Lie subalgebra.
* `TauCeti.isSolvable_upperTriangularRealDiagonalLieSubalgebra`: its solvability instance.
* `LieHom.splits_charpoly_ad_of_isUpperTriangular_of_im_diag_eq_zero`: if `f` is injective and
  `f X` is upper triangular with real diagonal, the characteristic polynomial of `ad X` splits.
* `LieHom.im_eq_zero_of_hasEigenvalue_baseChange_ad_of_isUpperTriangular_of_im_diag_eq_zero`:
  under those same hypotheses at `X`, every eigenvalue of the complexified `ad X` is real.
* `TauCeti.splits_charpoly_ad_upperTriangularRealDiagonalLieSubalgebra`:
  real splitting for the matrix Lie algebra itself.
* `TauCeti.im_eq_zero_of_hasEigenvalue_baseChange_ad_upperTriangularRealDiagonalLieSubalgebra`:
  reality of the complexified adjoint eigenvalues.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Chapter I, §5,
  Corollary 1.30, p.22, for split solvability and real adjoint eigenvalues; p.21 for the
  characteristic-polynomial product on an invariant subspace and its quotient.
-/

public noncomputable section

open Matrix Module Polynomial
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- Upper-triangular matrices with real diagonal, with their real commutator Lie algebra. -/
def upperTriangularRealDiagonalLieSubalgebra (𝕜 : Type*) [RCLike 𝕜]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] : LieSubalgebra ℝ (Matrix ι ι 𝕜) :=
  lieSubalgebraOfSubalgebra ℝ (Matrix ι ι 𝕜) (TauCeti.upperTriangularRealDiagonalSubalgebra 𝕜 ι)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {𝕜 : Type*} [RCLike 𝕜]

/-- Membership is upper triangularity together with a real diagonal. -/
@[simp]
theorem mem_upperTriangularRealDiagonalLieSubalgebra_iff {A : Matrix ι ι 𝕜} :
    A ∈ upperTriangularRealDiagonalLieSubalgebra 𝕜 ι ↔
      A.IsUpperTriangular ∧ ∀ i, RCLike.im (A i i) = 0 := by
  exact TauCeti.mem_upperTriangularRealDiagonalSubalgebra_iff

/-- The real-diagonal upper-triangular Lie algebra is solvable. -/
instance isSolvable_upperTriangularRealDiagonalLieSubalgebra :
    LieAlgebra.IsSolvable (upperTriangularRealDiagonalLieSubalgebra 𝕜 ι) := by
  -- Both carriers inherit addition, integer scalar multiplication and Lie brackets from
  -- the matrix ring, so the subtype maps preserve these operations definitionally.
  let f : upperTriangularRealDiagonalLieSubalgebra 𝕜 ι →ₗ⁅ℤ⁆ upperTriangular 𝕜 ι :=
    { toFun := fun x ↦ ⟨x.val, mem_upperTriangular_iff_blockTriangular.mpr
        (mem_upperTriangularRealDiagonalLieSubalgebra_iff.mp x.property).1⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := by intros; rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : upperTriangular 𝕜 ι ↦ (z : Matrix ι ι 𝕜)) h)
  exact hf.lieAlgebra_isSolvable

end TauCeti

namespace LieHom
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] [LinearOrder ι]

/-- If `f` is injective and `f X` is upper triangular with real diagonal entries, the
characteristic polynomial of `ad X` splits over the reals. -/
theorem splits_charpoly_ad_of_isUpperTriangular_of_im_diag_eq_zero
    (f : L →ₗ⁅ℝ⁆ Matrix ι ι 𝕜) (hf : Function.Injective f)
    (X : L) (hX : (f X).IsUpperTriangular) (hr : ∀ i, RCLike.im (f X i i) = 0) :
    (LieAlgebra.ad ℝ L X).charpoly.Splits := by
  let j := (Matrix.interleavedRealifyAlgHom (ι := ι) (𝕜 := 𝕜)).toLieHom.comp f
  have hj : Function.Injective j := by
    intro Y Z hYZ
    exact hf (Matrix.interleavedRealifyAlgHom_injective hYZ)
  have hcomm : j.toLinearMap.comp (LieAlgebra.ad ℝ L X) =
      (LieAlgebra.ad ℝ (Matrix (ι ×ₗ Bool) (ι ×ₗ Bool) ℝ) (j X)).comp j.toLinearMap := by
    apply LinearMap.ext
    intro Y
    exact j.map_lie X Y
  exact (Matrix.isUpperTriangular_interleavedRealifyAlgHom (f X)
    (TauCeti.mem_upperTriangularRealDiagonalSubalgebra_iff.mpr ⟨hX, hr⟩)).splits_charpoly_ad.of_dvd
    (LinearMap.charpoly_monic _).ne_zero
    (LinearMap.charpoly_dvd_of_injective_of_comp_eq_comp _ _ _ hj hcomm)

/-- If `f` is injective and `f X` is upper triangular with real diagonal entries, every
eigenvalue of the complexified real adjoint operator at `X` has zero imaginary part. -/
theorem im_eq_zero_of_hasEigenvalue_baseChange_ad_of_isUpperTriangular_of_im_diag_eq_zero
    (f : L →ₗ⁅ℝ⁆ Matrix ι ι 𝕜) (hf : Function.Injective f)
    (X : L) (z : ℂ)
    (hz : Module.End.HasEigenvalue ((LieAlgebra.ad ℝ L X).baseChange ℂ) z)
    (hX : (f X).IsUpperTriangular) (hr : ∀ i, RCLike.im (f X i i) = 0) : z.im = 0 := by
  have hs := f.splits_charpoly_ad_of_isUpperTriangular_of_im_diag_eq_zero hf X hX hr
  have hz' := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ z).mp hz
  rw [LinearMap.charpoly_baseChange] at hz'
  obtain ⟨r, h⟩ := hs.mem_range_of_isRoot (LinearMap.charpoly_monic _).ne_zero hz'
  simp [← h]

end LieHom

namespace TauCeti
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {𝕜 : Type*} [RCLike 𝕜]

/-- The adjoint characteristic polynomial of a real-diagonal upper-triangular matrix splits
into real linear factors. -/
theorem splits_charpoly_ad_upperTriangularRealDiagonalLieSubalgebra
    (X : upperTriangularRealDiagonalLieSubalgebra 𝕜 ι) :
    (LieAlgebra.ad ℝ (upperTriangularRealDiagonalLieSubalgebra 𝕜 ι) X).charpoly.Splits :=
  LieHom.splits_charpoly_ad_of_isUpperTriangular_of_im_diag_eq_zero
    (upperTriangularRealDiagonalLieSubalgebra 𝕜 ι).incl Subtype.val_injective X
      (mem_upperTriangularRealDiagonalLieSubalgebra_iff.mp X.property).1
      (mem_upperTriangularRealDiagonalLieSubalgebra_iff.mp X.property).2

/-- Every eigenvalue of the complexified adjoint of the real-diagonal upper-triangular Lie
algebra has zero imaginary part. -/
theorem im_eq_zero_of_hasEigenvalue_baseChange_ad_upperTriangularRealDiagonalLieSubalgebra
    (X : upperTriangularRealDiagonalLieSubalgebra 𝕜 ι) (z : ℂ)
    (hz : Module.End.HasEigenvalue
      ((LieAlgebra.ad ℝ (upperTriangularRealDiagonalLieSubalgebra 𝕜 ι) X).baseChange ℂ) z) :
    z.im = 0 :=
  LieHom.im_eq_zero_of_hasEigenvalue_baseChange_ad_of_isUpperTriangular_of_im_diag_eq_zero
    (upperTriangularRealDiagonalLieSubalgebra 𝕜 ι).incl Subtype.val_injective X z hz
      (mem_upperTriangularRealDiagonalLieSubalgebra_iff.mp X.property).1
      (mem_upperTriangularRealDiagonalLieSubalgebra_iff.mp X.property).2

end TauCeti
