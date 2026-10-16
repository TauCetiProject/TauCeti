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

For the sum of three squares, the generic diagonal model is identified with the Hamilton
quaternions. Compatible pure-quaternion coordinates identify the original quadratic space with
the pure Hamilton norm form.

## Main results

* `CliffordAlgebra.evenWeightedSumSquaresThreeQuaternionEquiv` models a diagonal ternary even
  Clifford algebra by a quaternion algebra.
* `CliffordAlgebra.evenHamiltonEquivWeightedSumSquaresOne` specializes this model to the Hamilton
  quaternions for the sum of three squares.
* `CliffordAlgebra.pureHamiltonEquivWeightedSumSquaresOne` gives compatible pure-quaternion
  coordinates for the underlying quadratic space.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion
open CliffordAlgebra
open QuadraticMap TauCeti

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

private def ternaryDiagonalIsometry (a b : R) (c : Rˣ) :
    (QuadraticMap.weightedSumSquares R ![a, b, (c : R)]).IsometryEquiv
      ((CliffordAlgebraQuaternion.Q a b).prod ((c : R) • QuadraticMap.sq)) where
  toFun x := ((x 0, x 1), x 2)
  invFun x := ![x.1.1, x.1.2, x.2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' x := by
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three,
      CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply,
      QuadraticMap.sq_apply, smul_eq_mul]

/-- The even Clifford algebra of the diagonal ternary form `⟨a, b, c⟩` is the quaternion
algebra `(-a/c, -b/c)`. -/
noncomputable def evenWeightedSumSquaresThreeQuaternionEquiv (a b : R) (c : Rˣ) :
    even (QuadraticMap.weightedSumSquares R ![a, b, (c : R)]) ≃ₐ[R]
      ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b] :=
  (evenEquivOfIsometry (ternaryDiagonalIsometry a b c)).trans (evenQuaternionEquiv a b c)

/-- The quaternion coordinates of a product of two generators of the even Clifford algebra of
the diagonal ternary form. -/
theorem evenWeightedSumSquaresThreeQuaternionEquiv_ι (a b : R) (c : Rˣ) (x y : Fin 3 → R) :
    evenWeightedSumSquaresThreeQuaternionEquiv a b c
        ((even.ι (QuadraticMap.weightedSumSquares R ![a, b, (c : R)])).bilin x y) =
      -(c : R) •
        ((⟨x 2, x 0, x 1, 0⟩ : ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b]) *
          ⟨-y 2, y 0, y 1, 0⟩) := by
  rw [evenWeightedSumSquaresThreeQuaternionEquiv, AlgEquiv.trans_apply, evenEquivOfIsometry_ι]
  exact evenQuaternionEquiv_ι a b c ((x 0, x 1), x 2) ((y 0, y 1), y 2)

/-- The inverse quaternion model of the diagonal ternary form expresses the coordinates in the
scalar and three products of basis generators. -/
theorem evenWeightedSumSquaresThreeQuaternionEquiv_symm_mk (a b : R) (c : Rˣ) (r i j k : R) :
    (evenWeightedSumSquaresThreeQuaternionEquiv a b c).symm
        (⟨r, i, j, k⟩ : ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b]) =
      algebraMap R _ r +
        (-(↑c⁻¹ : R) * i) •
          (even.ι (QuadraticMap.weightedSumSquares R ![a, b, (c : R)])).bilin
            (Pi.single 2 1) (Pi.single 0 1) +
        (-(↑c⁻¹ : R) * j) •
          (even.ι (QuadraticMap.weightedSumSquares R ![a, b, (c : R)])).bilin
            (Pi.single 2 1) (Pi.single 1 1) +
        (-(↑c⁻¹ : R) * k) •
          (even.ι (QuadraticMap.weightedSumSquares R ![a, b, (c : R)])).bilin
            (Pi.single 0 1) (Pi.single 1 1) := by
  apply (evenWeightedSumSquaresThreeQuaternionEquiv a b c).injective
  simp only [AlgEquiv.apply_symm_apply, map_add, map_smul, AlgEquiv.commutes,
    evenWeightedSumSquaresThreeQuaternionEquiv_ι]
  ext <;> simp [mul_left_comm, mul_comm]

/-- Quaternion conjugation is the image of reversal in the even Clifford algebra of the diagonal
ternary form. -/
@[simp]
theorem evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven (a b : R) (c : Rˣ)
    (x : even (QuadraticMap.weightedSumSquares R ![a, b, (c : R)])) :
    evenWeightedSumSquaresThreeQuaternionEquiv a b c (reverseEven _ x) =
      star (evenWeightedSumSquaresThreeQuaternionEquiv a b c x) := by
  simp only [evenWeightedSumSquaresThreeQuaternionEquiv, AlgEquiv.trans_apply,
    evenEquivOfIsometry_reverseEven]
  exact evenQuaternionEquiv_reverseEven _ _ _ _

/-- The reverse norm of the diagonal ternary form becomes the norm form of the corresponding
quaternion algebra. -/
theorem evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven_mul_self (a b : R) (c : Rˣ)
    (x : even (QuadraticMap.weightedSumSquares R ![a, b, (c : R)])) :
    evenWeightedSumSquaresThreeQuaternionEquiv a b c (reverseEven _ x * x) =
      (QuaternionAlgebra.normForm (-(↑c⁻¹ : R) * a) 0 (-(↑c⁻¹ : R) * b)
        (evenWeightedSumSquaresThreeQuaternionEquiv a b c x) :
          ℍ[R, -(↑c⁻¹ : R) * a, 0, -(↑c⁻¹ : R) * b]) := by
  rw [map_mul, evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven,
    QuaternionAlgebra.star_mul_self]

/-! ### The Hamilton model of the sum of three squares -/

private abbrev hamiltonOneSymbol : R := -(↑(1 : Rˣ)⁻¹ : R) * 1

private def hamiltonOneSymbolToHamiltonBasis :
    QuaternionAlgebra.Basis ℍ[R] (hamiltonOneSymbol (R := R)) (0 : R)
      (hamiltonOneSymbol (R := R)) where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by ext <;> simp [hamiltonOneSymbol]
  j_mul_j := by ext <;> simp [hamiltonOneSymbol]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

private def hamiltonToHamiltonOneSymbolBasis :
    QuaternionAlgebra.Basis
      ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)]
      (-1 : R) (0 : R) (-1 : R) where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by ext <;> simp [hamiltonOneSymbol]
  j_mul_j := by ext <;> simp [hamiltonOneSymbol]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- The coordinate-preserving identification between the quaternion symbol produced by the
ternary Clifford model at coefficients `1, 1, 1` and the Hamilton quaternions. -/
private def hamiltonOneSymbolEquivHamilton :
    ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)] ≃ₐ[R] ℍ[R] :=
  AlgEquiv.ofAlgHom (hamiltonOneSymbolToHamiltonBasis (R := R)).liftHom
    (hamiltonToHamiltonOneSymbolBasis (R := R)).liftHom
    (by
      apply QuaternionAlgebra.hom_ext <;> ext <;>
        simp [QuaternionAlgebra.Basis.lift, hamiltonOneSymbolToHamiltonBasis,
          hamiltonToHamiltonOneSymbolBasis])
    (by
      apply QuaternionAlgebra.hom_ext <;> ext <;>
        simp [QuaternionAlgebra.Basis.lift, hamiltonOneSymbolToHamiltonBasis,
          hamiltonToHamiltonOneSymbolBasis])

private theorem hamiltonOneSymbolEquivHamilton_apply
    (q : ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)]) :
    hamiltonOneSymbolEquivHamilton q = ⟨q.re, q.imI, q.imJ, q.imK⟩ := by
  ext <;> simp [hamiltonOneSymbolEquivHamilton, hamiltonOneSymbolToHamiltonBasis,
    QuaternionAlgebra.Basis.lift]

private theorem hamiltonOneSymbolEquivHamilton_star
    (q : ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)]) :
    hamiltonOneSymbolEquivHamilton (star q) = star (hamiltonOneSymbolEquivHamilton q) := by
  rw [hamiltonOneSymbolEquivHamilton_apply, hamiltonOneSymbolEquivHamilton_apply]
  rfl

/-- The even Clifford algebra of the sum of three squares is canonically the Hamilton quaternion
algebra. -/
noncomputable def evenHamiltonEquivWeightedSumSquaresOne :
    even (weightedSumSquares R ![(1 : R), 1, 1]) ≃ₐ[R] ℍ[R] :=
  (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ)).trans
    hamiltonOneSymbolEquivHamilton

/-- The Hamilton coordinates of a product of two generators in the even Clifford algebra of the
sum of three squares. -/
theorem evenHamiltonEquivWeightedSumSquaresOne_ι (x y : Fin 3 → R) :
    evenHamiltonEquivWeightedSumSquaresOne
        ((even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin x y) =
      -((⟨x 2, x 0, x 1, 0⟩ : ℍ[R]) * ⟨-y 2, y 0, y 1, 0⟩) := by
  -- Expose the defining composite so the generic ternary-coordinate theorem applies.
  change hamiltonOneSymbolEquivHamilton
      (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ)
        ((even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin x y)) = _
  have h := evenWeightedSumSquaresThreeQuaternionEquiv_ι
    (R := R) (1 : R) 1 (1 : Rˣ) x y
  change evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ)
      ((even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin x y) = _ at h
  rw [h, hamiltonOneSymbolEquivHamilton_apply]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- The inverse Hamilton model writes a quaternion in the scalar and standard bivector basis. -/
@[simp]
theorem evenHamiltonEquivWeightedSumSquaresOne_symm_mk (r i j k : R) :
    evenHamiltonEquivWeightedSumSquaresOne.symm (⟨r, i, j, k⟩ : ℍ[R]) =
      algebraMap R _ r +
        (-i) • (even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin
          (Pi.single 2 1) (Pi.single 0 1) +
        (-j) • (even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin
          (Pi.single 2 1) (Pi.single 1 1) +
        (-k) • (even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin
          (Pi.single 0 1) (Pi.single 1 1) := by
  apply evenHamiltonEquivWeightedSumSquaresOne.injective
  simp only [AlgEquiv.apply_symm_apply, map_add, map_smul, AlgEquiv.commutes,
    evenHamiltonEquivWeightedSumSquaresOne_ι]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- The canonical Hamilton model carries Clifford reversal to quaternion conjugation. -/
@[simp]
theorem evenHamiltonEquivWeightedSumSquaresOne_reverseEven
    (x : even (weightedSumSquares R ![(1 : R), 1, 1])) :
    evenHamiltonEquivWeightedSumSquaresOne (reverseEven _ x) =
      star (evenHamiltonEquivWeightedSumSquaresOne x) := by
  -- Expose the defining composite to transport reversal through its two factors.
  change hamiltonOneSymbolEquivHamilton
      (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ) (reverseEven _ x)) =
    star (hamiltonOneSymbolEquivHamilton
      (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ) x))
  rw [evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven,
    hamiltonOneSymbolEquivHamilton_star]

/-- In the canonical Hamilton model, the reverse norm is the quaternion norm-square. -/
theorem evenHamiltonEquivWeightedSumSquaresOne_reverseEven_mul_self
    (x : even (weightedSumSquares R ![(1 : R), 1, 1])) :
    evenHamiltonEquivWeightedSumSquaresOne (reverseEven _ x * x) =
      Quaternion.normSq (evenHamiltonEquivWeightedSumSquaresOne x) := by
  rw [map_mul, evenHamiltonEquivWeightedSumSquaresOne_reverseEven,
    Quaternion.star_mul_self]

/-- The sum-of-three-squares quadratic space in the coordinates compatible with the canonical
Hamilton even-Clifford model. Its image is the pure Hamilton quaternions. -/
noncomputable def pureHamiltonEquivWeightedSumSquaresOne :
    (weightedSumSquares R ![(1 : R), 1, 1]).IsometryEquiv
      (QuaternionAlgebra.pureNormForm (-1 : R) (-1 : R)) where
  toFun v := ⟨⟨0, -v 1, v 0, -v 2⟩, by simp⟩
  invFun q := ![(q : ℍ[R]).imJ, -(q : ℍ[R]).imI, -(q : ℍ[R]).imK]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv q := by
    apply Subtype.ext
    have hre : (q : ℍ[R]).re = 0 := q.2
    ext <;> simp [hre]
  map_add' _ _ := by apply Subtype.ext; ext <;> simp <;> abel
  map_smul' _ _ := by apply Subtype.ext; ext <;> simp
  map_app' v := by
    rw [QuaternionAlgebra.pureNormForm_apply_coordinates]
    simp [weightedSumSquares_apply, Fin.sum_univ_three]
    ring

/-- The pure Hamilton quaternion corresponding to a vector in the sum-of-three-squares model. -/
@[simp]
theorem coe_pureHamiltonEquivWeightedSumSquaresOne_apply (v : Fin 3 → R) :
    (pureHamiltonEquivWeightedSumSquaresOne v : ℍ[R]) =
      ⟨0, -v 1, v 0, -v 2⟩ := by
  rfl

/-- The vector coordinates recovered from a pure Hamilton quaternion. -/
@[simp]
theorem pureHamiltonEquivWeightedSumSquaresOne_symm_apply
    (q : LinearMap.ker (QuaternionAlgebra.reₗ (-1 : R) (0 : R) (-1 : R))) :
    pureHamiltonEquivWeightedSumSquaresOne.symm q =
      ![(q : ℍ[R]).imJ, -(q : ℍ[R]).imI, -(q : ℍ[R]).imK] := by
  rfl

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

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
  have hw : QuadraticMap.weightedSumSquares K w =
      QuadraticMap.weightedSumSquares K ![(w 0 : K), (w 1 : K), (w 2 : K)] := by
    ext x
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, Units.smul_def]
  rw [hw] at f
  refine ⟨-(w 2)⁻¹ * w 0, -(w 2)⁻¹ * w 1,
    (evenEquivOfIsometry f).trans
      (evenWeightedSumSquaresThreeQuaternionEquiv (w 0 : K) (w 1 : K) (w 2)), ?_⟩
  intro x
  simp only [AlgEquiv.trans_apply, evenEquivOfIsometry_reverseEven]
  exact evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven _ _ _ _

end Field

end CliffordAlgebra
