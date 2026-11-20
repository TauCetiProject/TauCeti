/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.QuadraticForm.Binary.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.StdBasis

/-!
# Normal forms for binary quadratic spaces

The polar matrix of `[a, b] = a x² + xy + b y²` detects nonsingularity by the condition
`1 - 4ab ≠ 0`. A basis whose two vectors pair to one identifies any binary quadratic space
with a block `[a, b]`. Over a field, this gives a hyperbolicity criterion for isotropic planes
without inverting two, and a normal form with prescribed first coefficient.

The binary block and normal-form arguments follow Elman–Karpenko–Merkurjev,
*The Algebraic and Geometric Theory of Quadratic Forms*, §7.B.
-/

public section

open Module QuadraticMap

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R]

/-- The polar matrix of `[a, b]` in the standard coordinate basis. -/
@[simp]
theorem toMatrix_polarBilin_binaryQuadraticForm (a b : R) :
    LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin 2)) (binaryQuadraticForm R a b).polarBilin =
      !![2 * a, 1; 1, 2 * b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply, polar_binaryQuadraticForm]

/-- The determinant of the polar matrix of `[a, b]` is `4ab - 1`. -/
theorem det_toMatrix_polarBilin_binaryQuadraticForm (a b : R) :
    (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin 2))
      (binaryQuadraticForm R a b).polarBilin).det = 4 * a * b - 1 := by
  rw [toMatrix_polarBilin_binaryQuadraticForm]
  simp [Matrix.det_fin_two]
  ring

/-- The block `[a, b]` over a domain is nonsingular exactly when `1 - 4ab` is nonzero. -/
@[simp]
theorem nondegenerate_polarBilin_binaryQuadraticForm_iff [IsDomain R] (a b : R) :
    (binaryQuadraticForm R a b).polarBilin.Nondegenerate ↔ 1 - 4 * a * b ≠ 0 := by
  refine (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun R (Fin 2))).trans ?_
  rw [det_toMatrix_polarBilin_binaryQuadraticForm]
  exact not_congr (sub_eq_zero.trans (eq_comm.trans sub_eq_zero.symm))

end CommRing

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The coordinate plane `[0, 0]` is the hyperbolic plane on a line and its dual. -/
def isometryEquivBinaryQuadraticFormZeroDualProd :
    (binaryQuadraticForm R 0 0).IsometryEquiv (QuadraticForm.dualProd R R) where
  toLinearEquiv := (LinearEquiv.finTwoArrow R R).trans
    ((LinearMap.ringLmapEquivSelf R R R).symm.prodCongr (LinearEquiv.refl R R))
  map_app' x := by
    simp [LinearEquiv.finTwoArrow, QuadraticForm.dualProd_apply, mul_comm]

/-- The hyperbolic comparison sends the first coordinate to a functional and keeps the second
coordinate as the vector. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormZeroDualProd_toLinearEquiv :
    (isometryEquivBinaryQuadraticFormZeroDualProd (R := R)).toLinearEquiv =
      (LinearEquiv.finTwoArrow R R).trans
        ((LinearMap.ringLmapEquivSelf R R R).symm.prodCongr (LinearEquiv.refl R R)) :=
  (rfl)

/-- When `a` is a unit, changing `y` to `a⁻¹y` identifies `[a, b]` with `a [1, ab]`. -/
def isometryEquivBinaryQuadraticFormSmul (a : Rˣ) (b : R) :
    (binaryQuadraticForm R a b).IsometryEquiv
      ((a : R) • binaryQuadraticForm R 1 (a * b)) where
  toLinearEquiv := (LinearEquiv.finTwoArrow R R).trans
    (((LinearEquiv.refl R R).prodCongr (LinearEquiv.smulOfUnit a⁻¹)).trans
      (LinearEquiv.finTwoArrow R R).symm)
  map_app' x := by
    -- Expose the rescaled pair of coordinates in the bundled linear equivalence.
    change ((a : R) • binaryQuadraticForm R 1 (a * b)) ![x 0, (↑(a⁻¹) : R) * x 1] = _
    simp only [smul_apply, binaryQuadraticForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, smul_eq_mul]
    calc
      _ = (a : R) * x 0 ^ 2 + ((a : R) * ↑(a⁻¹)) * (x 0 * x 1) +
          b * ((a : R) * ↑(a⁻¹)) ^ 2 * x 1 ^ 2 := by ring
      _ = _ := by simp

/-- The rescaling isometry divides the second coordinate by the unit `a`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormSmul_apply (a : Rˣ) (b : R) (x : Fin 2 → R) :
    isometryEquivBinaryQuadraticFormSmul a b x = ![x 0, (↑(a⁻¹) : R) * x 1] :=
  (rfl)

end CommSemiring

end TauCeti

namespace QuadraticMap

open TauCeti

section Basis

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- In a basis whose two vectors have polar pairing one, the binary coefficients are the values
on those vectors. -/
noncomputable def isometryEquivBinaryQuadraticFormOfBasis (Q : QuadraticForm R V)
    (b : Basis (Fin 2) R V) (hb : polar Q (b 0) (b 1) = 1) :
    (binaryQuadraticForm R (Q (b 0)) (Q (b 1))).IsometryEquiv Q where
  toLinearEquiv := b.equivFun.symm
  map_app' x := by
    -- Expose the basis equivalence in order to expand the vector in its two coordinates.
    change Q (b.equivFun.symm x) = _
    rw [Basis.equivFun_symm_apply, Fin.sum_univ_two, QuadraticMap.map_add Q]
    simp only [QuadraticMap.map_smul, polar_smul_left, polar_smul_right, hb,
      binaryQuadraticForm_apply, smul_eq_mul]
    ring

/-- In the binary presentation, the isometry is the coordinate-to-vector map of the basis. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormOfBasis_apply (Q : QuadraticForm R V)
    (b : Basis (Fin 2) R V) (hb : polar Q (b 0) (b 1) = 1) (x : Fin 2 → R) :
    Q.isometryEquivBinaryQuadraticFormOfBasis b hb x = x 0 • b 0 + x 1 • b 1 := by
  -- The isometry coerces to the inverse of the basis coordinate equivalence.
  change b.equivFun.symm x = _
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_two]

end Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A vector outside the polar kernel in a binary quadratic space can be used as the first
basis vector of a block `[Q x, b]`. -/
theorem exists_equivalent_binaryQuadraticForm_of_polarBilin_ne_zero (Q : QuadraticForm K V)
    (hdim : finrank K V = 2) {x : V} (hx : Q.polarBilin x ≠ 0) :
    ∃ b : K, Q.Equivalent (binaryQuadraticForm K (Q x) b) := by
  have hx0 : x ≠ 0 := fun h ↦ hx (by simp [h])
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K)
    (by rw [hdim]; decide) hx0
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_eq_succ hdim
  -- If the first choice of partner pairs to zero, add `x` to it. In that case the
  -- self-pairing of `x` must be nonzero, since `x` and `y` span the space.
  obtain ⟨z, hli, hz⟩ : ∃ z, LinearIndependent K ![x, z] ∧ polar Q x z ≠ 0 := by
    by_cases hy : polar Q x y = 0
    · let b := basisOfLinearIndependentOfCardEqFinrank hxy (by simp [hdim])
      have hb : ⇑b = ![x, y] := coe_basisOfLinearIndependentOfCardEqFinrank ..
      have hxx : polar Q x x ≠ 0 := by
        intro hxx
        apply hx
        apply b.ext
        intro i
        fin_cases i <;> simp [hb, hxx, hy]
      exact ⟨x + y, LinearIndependent.pair_add_right_iff.mpr hxy,
        by simpa [polar_add_right, hy] using hxx⟩
    · exact ⟨y, hxy, hy⟩
  let w := (polar Q x z)⁻¹ • z
  have hw : polar Q x w = 1 := by simp [w, polar_smul_right, smul_eq_mul, hz]
  have hiw : LinearIndependent K ![x, w] := by
    simpa [w] using
      (LinearIndependent.pair_smul_smul_iff (u := (1 : K)) (v := (polar Q x z)⁻¹)
        isUnit_one (Ne.isUnit (inv_ne_zero hz))).mpr hli
  let b := basisOfLinearIndependentOfCardEqFinrank hiw (by simp [hdim])
  have hb : ⇑b = ![x, w] := coe_basisOfLinearIndependentOfCardEqFinrank ..
  have e := (Q.isometryEquivBinaryQuadraticFormOfBasis b (by simpa [hb] using hw)).symm
  have he : Q.Equivalent (binaryQuadraticForm K (Q (b 0)) (Q (b 1))) := ⟨e⟩
  exact ⟨Q w, by simpa [hb] using he⟩

/-- A binary quadratic form with nonzero polar form is isometric to a block `[a, b]`, even when
its polar form is singular. -/
theorem exists_equivalent_binaryQuadraticForm (Q : QuadraticForm K V) (hdim : finrank K V = 2)
    (hQ : Q.polarBilin ≠ 0) : ∃ a b : K, Q.Equivalent (binaryQuadraticForm K a b) := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hQ
  obtain ⟨b, hb⟩ := Q.exists_equivalent_binaryQuadraticForm_of_polarBilin_ne_zero hdim
    (by simpa using hx)
  exact ⟨Q x, b, hb⟩

/-- A nonzero value represented by a nonsingular binary form can be taken as its first
coefficient. -/
theorem exists_equivalent_binaryQuadraticForm_of_represents (Q : QuadraticForm K V)
    (hdim : finrank K V = 2) (hQ : Q.polarBilin.Nondegenerate) {a : K} (ha : a ≠ 0)
    (h : Q.Represents a) : ∃ b : K, Q.Equivalent (binaryQuadraticForm K a b) := by
  obtain ⟨x, rfl⟩ := (represents_iff Q a).mp h
  apply Q.exists_equivalent_binaryQuadraticForm_of_polarBilin_ne_zero hdim
  intro hx
  exact ha (by rw [hQ.1 x (fun y ↦ by rw [hx, LinearMap.zero_apply]), Q.map_zero])

/-- A binary quadratic form with trivial quadratic radical is hyperbolic exactly when it is
isotropic. This criterion holds in every characteristic. -/
theorem equivalent_dualProd_iff_not_anisotropic_of_finrank_eq_two (Q : QuadraticForm K V)
    (hdim : finrank K V = 2) (hQ : Q.radical = ⊥) :
    Q.Equivalent (QuadraticForm.dualProd K K) ↔ ¬Q.Anisotropic := by
  let e := isometryEquivBinaryQuadraticFormZeroDualProd (R := K)
  refine ⟨fun h ↦ ((h.trans ⟨e.symm⟩).anisotropic_iff.not).mpr
    not_anisotropic_binaryQuadraticForm_zero, fun h ↦ ?_⟩
  obtain ⟨x, y, hx0, hx, hy, hxy⟩ := exists_isotropic_pair_of_radical_eq_bot hQ h
  have hli : LinearIndependent K ![x, y] := by
    refine (LinearIndependent.pair_iff' hx0).mpr fun c hc ↦ ?_
    rw [← hc, polar_smul_right, polar_self, hx, nsmul_zero, smul_zero] at hxy
    exact zero_ne_one hxy
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_eq_succ hdim
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ⇑b = ![x, y] := coe_basisOfLinearIndependentOfCardEqFinrank ..
  have hplane : Q.Equivalent (binaryQuadraticForm K (Q (b 0)) (Q (b 1))) :=
    ⟨(Q.isometryEquivBinaryQuadraticFormOfBasis b (by simpa [hb] using hxy)).symm⟩
  have hzero : Q.Equivalent (binaryQuadraticForm K 0 0) := by simpa [hb, hx, hy] using hplane
  exact hzero.trans ⟨e⟩

end QuadraticMap
