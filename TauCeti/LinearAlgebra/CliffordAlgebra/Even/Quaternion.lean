/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Scaling
public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import TauCeti.Algebra.Quaternion.NormForm
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Quaternion models of ternary even Clifford algebras

For the diagonal form `⟨a, b, c⟩`, with `c` a unit, its even Clifford algebra is the
quaternion algebra with symbols `-a/c` and `-b/c`. Clifford reversal becomes quaternion
conjugation and the reverse norm becomes the quaternion norm form. The explicit equivalence
works over a commutative ring; over a field of characteristic different from two, diagonalization
therefore supplies such a model for every nondegenerate ternary form.

The construction composes `TauCeti.CliffordAlgebra.evenProdSMulSqEquiv` with Mathlib's
`CliffordAlgebraQuaternion.equiv`, and uses Mathlib's unit-weight diagonalization for arbitrary
forms. The symbols need not be squares, so the model includes nonsplit quaternion algebras.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion
open CliffordAlgebra

namespace CliffordAlgebra

variable {R : Type*} [CommRing R]

private def scaledQuaternionIsometry (a b : R) (c : Rˣ) :
    (-(↑c⁻¹ : R) • CliffordAlgebraQuaternion.Q a b).IsometryEquiv
      (CliffordAlgebraQuaternion.Q (-(↑c⁻¹ : R) * a) (-(↑c⁻¹ : R) * b)) where
  toLinearEquiv := LinearEquiv.refl R _
  map_app' x := by
    -- The structure projection hides the identity linear map's application;
    -- expose its argument before distributing the scalar across the two coefficients.
    change CliffordAlgebraQuaternion.Q (-(↑c⁻¹ : R) * a) (-(↑c⁻¹ : R) * b) x =
      (-(↑c⁻¹ : R) • CliffordAlgebraQuaternion.Q a b) x
    simp only [smul_apply, smul_eq_mul, CliffordAlgebraQuaternion.Q_apply]
    ring

/-- The even Clifford algebra of `⟨a, b, c⟩` is the quaternion algebra `(-a/c, -b/c)`. -/
noncomputable def evenQuaternionEquiv (a b : R) (c : Rˣ) :
    even ((CliffordAlgebraQuaternion.Q a b).prod ((c : R) • QuadraticMap.sq)) ≃ₐ[R]
      ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b] :=
  ((TauCeti.CliffordAlgebra.evenProdSMulSqEquiv _ c).trans
    (equivOfIsometry (scaledQuaternionIsometry a b c))).trans
      CliffordAlgebraQuaternion.equiv

/-- The quaternion coordinates of a product of two ternary Clifford generators. -/
theorem evenQuaternionEquiv_ι (a b : R) (c : Rˣ) (x y : (R × R) × R) :
    evenQuaternionEquiv a b c
        ((even.ι ((CliffordAlgebraQuaternion.Q a b).prod
          ((c : R) • QuadraticMap.sq))).bilin x y) =
      -(c : R) •
        ((⟨x.2, x.1.1, x.1.2, 0⟩ : ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b]) *
          ⟨-y.2, y.1.1, y.1.2, 0⟩) := by
  simp only [evenQuaternionEquiv, AlgEquiv.trans_apply,
    TauCeti.CliffordAlgebra.evenProdSMulSqEquiv_ι, map_smul, map_mul, map_add, map_sub,
    AlgEquiv.commutes, equivOfIsometry_apply, map_apply_ι, CliffordAlgebraQuaternion.equiv_apply,
    CliffordAlgebraQuaternion.toQuaternion_ι]
  -- The remaining coordinates are projections of the bundled identity isometry.
  congr 2 <;> ext <;> simp [scaledQuaternionIsometry]
  all_goals rfl

/-- The inverse quaternion model expresses the coordinates in the scalar and three even
Clifford basis elements. -/
theorem evenQuaternionEquiv_symm_mk (a b : R) (c : Rˣ) (r i j k : R) :
    (evenQuaternionEquiv a b c).symm
        (⟨r, i, j, k⟩ : ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b]) =
      algebraMap R _ r +
        (-(↑c⁻¹ : R) * i) •
          (even.ι ((CliffordAlgebraQuaternion.Q a b).prod
            ((c : R) • QuadraticMap.sq))).bilin ((0, 0), 1) ((1, 0), 0) +
        (-(↑c⁻¹ : R) * j) •
          (even.ι ((CliffordAlgebraQuaternion.Q a b).prod
            ((c : R) • QuadraticMap.sq))).bilin ((0, 0), 1) ((0, 1), 0) +
        (-(↑c⁻¹ : R) * k) •
          (even.ι ((CliffordAlgebraQuaternion.Q a b).prod
            ((c : R) • QuadraticMap.sq))).bilin ((1, 0), 0) ((0, 1), 0) := by
  apply (evenQuaternionEquiv a b c).injective
  simp only [AlgEquiv.apply_symm_apply, map_add, map_smul, AlgEquiv.commutes,
    evenQuaternionEquiv_ι]
  ext <;> simp [mul_left_comm, mul_comm]

/-- Quaternion conjugation is the image of reversal in the ternary even Clifford algebra. -/
@[simp]
theorem evenQuaternionEquiv_reverseEven (a b : R) (c : Rˣ)
    (x : even ((CliffordAlgebraQuaternion.Q a b).prod ((c : R) • QuadraticMap.sq))) :
    evenQuaternionEquiv a b c (reverseEven _ x) = star (evenQuaternionEquiv a b c x) := by
  simp only [evenQuaternionEquiv, AlgEquiv.trans_apply,
    TauCeti.CliffordAlgebra.evenProdSMulSqEquiv_reverseEven,
    equivOfIsometry_apply, map_star, CliffordAlgebraQuaternion.equiv_apply,
    CliffordAlgebraQuaternion.toQuaternion_star]

/-- The reverse norm becomes the norm form of the corresponding quaternion algebra. -/
theorem evenQuaternionEquiv_reverseEven_mul_self (a b : R) (c : Rˣ)
    (x : even ((CliffordAlgebraQuaternion.Q a b).prod ((c : R) • QuadraticMap.sq))) :
    evenQuaternionEquiv a b c (reverseEven _ x * x) =
      (QuaternionAlgebra.normForm (-(↑c⁻¹ : R) * a) 0 (-(↑c⁻¹ : R) * b)
        (evenQuaternionEquiv a b c x) : ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b]) := by
  rw [map_mul, evenQuaternionEquiv_reverseEven, QuaternionAlgebra.star_mul_self]

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

private def ternaryDiagonalIsometry (w : Fin 3 → Kˣ) :
    (QuadraticMap.weightedSumSquares K w).IsometryEquiv
      ((CliffordAlgebraQuaternion.Q (w 0 : K) (w 1 : K)).prod
        ((w 2 : K) • QuadraticMap.sq)) where
  toFun x := ((x 0, x 1), x 2)
  invFun x := ![x.1.1, x.1.2, x.2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' x := by
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, Units.smul_def,
      CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply,
      QuadraticMap.sq_apply, smul_eq_mul]

/-- Every regular ternary quadratic form admits a quaternion model of its even Clifford
algebra, in which reversal is quaternion conjugation. The two symbols are units and need not
be squares. -/
theorem exists_evenQuaternionEquiv_of_finrank_eq_three (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ∃ a b : Kˣ, ∃ e : even Q ≃ₐ[K] ℍ[K, (a : K), 0, (b : K)],
      ∀ x, e (reverseEven Q x) = star (e x) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have hex : ∃ w : Fin 3 → Kˣ,
      Q.Equivalent (QuadraticMap.weightedSumSquares K w) := by
    rw [← hV]
    exact Q.equivalent_weightedSumSquares_units_of_nondegenerate'
      (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  obtain ⟨w, ⟨f⟩⟩ := hex
  let g := f.trans (ternaryDiagonalIsometry w)
  refine ⟨-(w 2)⁻¹ * w 0, -(w 2)⁻¹ * w 1,
    (evenEquivOfIsometry g).trans (evenQuaternionEquiv (w 0 : K) (w 1 : K) (w 2)), ?_⟩
  intro x
  simp only [AlgEquiv.trans_apply, evenEquivOfIsometry_reverseEven]
  exact evenQuaternionEquiv_reverseEven _ _ _ _

end Field

end CliffordAlgebra
