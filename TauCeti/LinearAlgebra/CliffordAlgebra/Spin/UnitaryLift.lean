/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The `Spinᶜ` lift of the unitary group `U(2)`

An almost Hermitian four-manifold carries a canonical `Spinᶜ` structure: its unitary frames form a
principal `U(2)`-bundle, and the canonical `Spinᶜ` structure is associated to it through a
homomorphism `U(2) → Spinᶜ(4)` lifting `g ↦ (g, det g)` along the double cover
`Spinᶜ(4) → SO(4) × U(1)`. This file constructs that homomorphism and characterizes it.

Let `V` be a four-dimensional real inner product space with the geometric Clifford convention
`Q v = -‖v‖²`, and let `b = (b₀, b₁, b₂, b₃)` be an orthonormal frame. Read `V` as `ℂ²` through the
complex coordinates `(⟪b₀, v⟫ + ⟪b₁, v⟫ i, ⟪b₂, v⟫ + ⟪b₃, v⟫ i)`
(`OrthonormalBasis.complexCoords`), so that the complex structure `J b₀ = b₁`, `J b₂ = b₃` becomes
multiplication by `i`. Then `OrthonormalBasis.spinCUnitary b : U(2) →* Spinᶜ(Q)` satisfies:

* the rotation of `spinCUnitary g` acts on `V` as the matrix `g` in these coordinates
  (`OrthonormalBasis.complexCoords_toSpecialOrthogonal_spinCUnitary_apply`);
* its determinant character is `det g` (`OrthonormalBasis.det_spinCUnitary`);
* it is the only homomorphism with these two properties (`OrthonormalBasis.eq_spinCUnitary`);
* on the circle of matrices `diag (1, z)`, which turn the plane `⟨b₂, b₃⟩` by `z`, it is the lift
  `CliffordAlgebra.spinCCircle` of the rotations of that plane
  (`OrthonormalBasis.spinCUnitary_unitaryTorusHom_mulSingle_one`).

Uniqueness holds because two such lifts differ by a homomorphism from `U(2)` to the central kernel
`{1, [1, -1]}` of `Spinᶜ(4) → SO(4) × U(1)`, and every element of `U(2)` is a square
(`Matrix.UnitaryGroup.isSquare`), so `CliffordAlgebra.spinCGroup.hom_ext_of_isSquare` applies.
Together with the naturality of the plane lift under quadratic isometries
(`CliffordAlgebra.spinCGroupMap_spinCCircle`), applied to the stabilization of a
three-space by a line, the last property compares, at the structure-group level, the `Spinᶜ`
structure of an oriented plane field on a three-manifold `Y`, stabilized to `S¹ × Y`, with the
canonical `Spinᶜ` structure of an almost complex structure on `S¹ × Y` that sends `∂ₛ` into `Y`
and preserves the plane field.

## Construction

Existence uses quaternions. The group `U(2)` is the quotient of `Sp(1) × U(1)` by `±(1, 1)`, with
`(a, w)` acting on `ℂ²` by `w • a` (`Quaternion.unitaryProdCircleToUnitaryGroup`); identifying `ℂ²`
with `ℍ` by the first column of the matrix of a quaternion, this is `q ↦ a q w`, with `w` a unit
quaternion in the complex line `ℝ ⊕ ℝ i`. The compact group `Spin(4)` is `Sp(1) × Sp(1)`, with
`(a, c)` acting by `q ↦ a q (star c)` (`TauCeti.realSpinFourEquivQuaternionUnitaryProd_action`).
So `(a, w)` lifts to the class `[(a, w⁻¹), w]` in `Spinᶜ(4)`, which is unchanged when `(a, w)` is
replaced by `(-a, -w)`; its determinant character is `w² = det (w • a)`. The resulting lift on the
compact coordinate model is transported to `V` along a reordering of the frame
(`OrthonormalBasis.realSpinCGroupHom`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4 (`Spin(4)` and pairs
  of unit quaternions) and Appendix D (the `Spinᶜ` structure of an almost complex manifold).
-/

public section

noncomputable section

open scoped Quaternion

open CliffordAlgebra Matrix TauCeti

/-! ### The lift in the compact coordinate model -/

/-- The class `[(a, w⁻¹), w]` in `Spinᶜ(4)` of the compact coordinate model, whose rotation is
`q ↦ a q w` in quaternion coordinates. -/
private def spinCOfPair :
    unitary ℍ[ℝ] × Circle →*
      spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero :=
  (spinCGroup.mk _ _).comp
    ((realSpinFourEquivQuaternionUnitaryProd.symm.toMonoidHom.comp
      ((MonoidHom.fst _ _).prod
        (Quaternion.circleToUnitary.comp
          ((invMonoidHom : Circle →* Circle).comp (MonoidHom.snd _ _))))).prod
      (MonoidHom.snd _ _))

private theorem spinCOfPair_apply (p : unitary ℍ[ℝ] × Circle) :
    spinCOfPair p = spinCGroup.mk _ _
      (realSpinFourEquivQuaternionUnitaryProd.symm (p.1, Quaternion.circleToUnitary p.2⁻¹),
        p.2) :=
  (rfl)

/-- `spinCOfPair` is trivial on the kernel `{1, -1}` of `Sp(1) × U(1) → U(2)`. -/
private theorem ker_le_ker_spinCOfPair :
    Quaternion.unitaryProdCircleToUnitaryGroup.ker ≤ spinCOfPair.ker := by
  intro p hp
  rcases Quaternion.mem_ker_unitaryProdCircleToUnitaryGroup_iff.mp hp with rfl | rfl
  · exact one_mem _
  · have hc : Quaternion.circleToUnitary (-1 : Circle)⁻¹ = -1 :=
      Subtype.ext (by ext <;> simp [Unitary.coe_neg])
    rw [MonoidHom.mem_ker, spinCOfPair_apply, Prod.fst_neg, Prod.snd_neg, Prod.fst_one,
      Prod.snd_one, hc, ← Prod.neg_mk, Prod.mk_one_one, (MulEquiv.symm_apply_eq _).mpr
        (realSpinFourEquivQuaternionUnitaryProd_negOne
          (nondegenerate_realCliffordForm 4 0).ne_zero).symm,
      spinCGroup.mk_negOne_neg_one]

/-- The lift `U(2) → Spinᶜ(4)` of the compact coordinate model, descended from `spinCOfPair`. -/
private def realSpinCUnitary :
    unitaryGroup (Fin 2) ℂ →*
      spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero :=
  Quaternion.unitaryProdCircleToUnitaryGroup.liftOfRightInverse _
    (Function.rightInverse_surjInv Quaternion.unitaryProdCircleToUnitaryGroup_surjective)
    ⟨spinCOfPair, ker_le_ker_spinCOfPair⟩

private theorem realSpinCUnitary_apply (p : unitary ℍ[ℝ] × Circle) :
    realSpinCUnitary (Quaternion.unitaryProdCircleToUnitaryGroup p) = spinCOfPair p :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p

/-- The vector of the compact coordinate model whose quaternion coordinate is
`Quaternion.ofFirstColumn z`. -/
private def coordVec (z : Fin 2 → ℂ) : Fin (4 + 0) → ℝ :=
  realCliffordFourZeroQuaternionEquiv.symm (Quaternion.ofFirstColumn z)

/-- In the coordinates `coordVec`, the rotation of `spinCOfPair (a, w)` is the matrix `w • a`. -/
private theorem toSpecialOrthogonal_spinCOfPair_coordVec (p : unitary ℍ[ℝ] × Circle)
    (z : Fin 2 → ℂ) :
    (spinCGroup.toSpecialOrthogonal _ _ (spinCOfPair p) :
        (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ)) (coordVec z) =
      coordVec
        ((Quaternion.unitaryProdCircleToUnitaryGroup p : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) := by
  rw [spinCOfPair_apply, spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply,
    ← spinGroup_smul_apply]
  -- Compare quaternion coordinates: both sides are `a q w`.
  refine EquivLike.injective realCliffordFourZeroQuaternionEquiv ?_
  rw [realSpinFourEquivQuaternionUnitaryProd_action, MulEquiv.apply_symm_apply, coordVec,
    coordVec, QuadraticMap.IsometryEquiv.apply_symm_apply,
    QuadraticMap.IsometryEquiv.apply_symm_apply, Unitary.star_eq_inv, ← map_inv, inv_inv,
    Quaternion.coe_circleToUnitary,
    Quaternion.coe_unitaryProdCircleToUnitaryGroup_apply, smul_mulVec,
    Quaternion.ofFirstColumn_smul, Quaternion.ofFirstColumn_toComplexMatrix_mulVec]

private theorem det_spinCOfPair (p : unitary ℍ[ℝ] × Circle) :
    spinCGroup.det _ _ (spinCOfPair p) =
      UnitaryGroup.detCircle (Quaternion.unitaryProdCircleToUnitaryGroup p) := by
  apply Circle.ext
  rw [spinCOfPair_apply, spinCGroup.det_mk, UnitaryGroup.coe_detCircle,
    Quaternion.coe_unitaryProdCircleToUnitaryGroup_apply, det_smul,
    Quaternion.det_toComplexMatrix, (Quaternion.mem_unitary_iff_normSq_eq_one _).mp p.1.2]
  simp

/-! ### Complex coordinates in a frame and the lift -/

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 4) ℝ V)

/-- The reordered frame `(b₂, b₁, -b₀, b₃)`, along which the quaternion coordinates `coordVec` of
the compact model become the complex coordinates `b.complexCoords`. -/
private def quaternionFrame : OrthonormalBasis (Fin 4) ℝ V :=
  OrthonormalBasis.mk (v := ![b 2, b 1, -b 0, b 3])
    (by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [b.inner_eq_ite])
    (by
      rw [← b.toBasis.span_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hmem (k : Fin 4) :
          ![b 2, b 1, -b 0, b 3] k ∈ Submodule.span ℝ (Set.range ![b 2, b 1, -b 0, b 3]) :=
        Submodule.subset_span (Set.mem_range_self k)
      fin_cases i
      · simpa using Submodule.neg_mem _ (hmem 2)
      · simpa using hmem 1
      · simpa using hmem 0
      · simpa using hmem 3)

variable {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)

private theorem quaternionFrame_negRealCliffordFormIsometryEquiv_coordVec (z : Fin 2 → ℂ) :
    b.quaternionFrame.negRealCliffordFormIsometryEquiv hQ (coordVec z) =
      b.complexCoords.symm z := by
  rw [negRealCliffordFormIsometryEquiv_apply, quaternionFrame, OrthonormalBasis.coe_mk,
    Fin.sum_univ_four, complexCoords_symm_apply]
  simp [coordVec]
  abel

variable (hQ₀ : Q ≠ 0)

/-- **The `Spinᶜ` lift of `U(2)`.** For an orthonormal frame `b` of a four-dimensional space with
`Q v = -‖v‖²`, the homomorphism `U(2) → Spinᶜ(Q)` lifting `g ↦ (g, det g)` along
`Spinᶜ(Q) → SO(Q) × U(1)`, where `g` acts on `V` through the complex coordinates
`b.complexCoords` (`complexCoords_toSpecialOrthogonal_spinCUnitary_apply`, `det_spinCUnitary`).
It is the only such homomorphism (`eq_spinCUnitary`). -/
def spinCUnitary : unitaryGroup (Fin 2) ℂ →* spinCGroup Q hQ₀ :=
  (b.quaternionFrame.realSpinCGroupHom hQ (nondegenerate_realCliffordForm 4 0).ne_zero hQ₀).comp
    realSpinCUnitary

/-- **The rotation of `spinCUnitary g` is `g`** in the complex coordinates of the frame. -/
theorem complexCoords_toSpecialOrthogonal_spinCUnitary_apply (g : unitaryGroup (Fin 2) ℂ)
    (v : V) :
    b.complexCoords
        ((spinCGroup.toSpecialOrthogonal Q hQ₀ (b.spinCUnitary hQ hQ₀ g) : V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ b.complexCoords v := by
  obtain ⟨z, rfl⟩ := b.complexCoords.symm.surjective v
  obtain ⟨p, rfl⟩ := Quaternion.unitaryProdCircleToUnitaryGroup_surjective g
  rw [← quaternionFrame_negRealCliffordFormIsometryEquiv_coordVec b hQ, spinCUnitary,
    MonoidHom.comp_apply, toSpecialOrthogonal_realSpinCGroupHom_apply, realSpinCUnitary_apply,
    toSpecialOrthogonal_spinCOfPair_coordVec]
  simp only [quaternionFrame_negRealCliffordFormIsometryEquiv_coordVec,
    LinearEquiv.apply_symm_apply]

/-- **The determinant character of `spinCUnitary g` is `det g`.** -/
@[simp]
theorem det_spinCUnitary (g : unitaryGroup (Fin 2) ℂ) :
    spinCGroup.det Q hQ₀ (b.spinCUnitary hQ hQ₀ g) = UnitaryGroup.detCircle g := by
  obtain ⟨p, rfl⟩ := Quaternion.unitaryProdCircleToUnitaryGroup_surjective g
  rw [spinCUnitary, MonoidHom.comp_apply, det_realSpinCGroupHom, realSpinCUnitary_apply,
    det_spinCOfPair]

/-- **Uniqueness of the lift.** A homomorphism `U(2) → Spinᶜ(Q)` whose rotations act as the unitary
matrices in the complex coordinates of `b` and whose determinant character is `det` is
`b.spinCUnitary`. -/
theorem eq_spinCUnitary {φ : unitaryGroup (Fin 2) ℂ →* spinCGroup Q hQ₀}
    (hrot : ∀ g v, b.complexCoords
        ((spinCGroup.toSpecialOrthogonal Q hQ₀ (φ g) : V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ b.complexCoords v)
    (hdet : ∀ g, spinCGroup.det Q hQ₀ (φ g) = UnitaryGroup.detCircle g) :
    φ = b.spinCUnitary hQ hQ₀ := by
  have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  refine spinCGroup.hom_ext_of_isSquare Q hQ₀
    (QuadraticMap.Anisotropic.nondegenerate fun v hv => by simpa [hQ] using hv)
    UnitaryGroup.isSquare (MonoidHom.ext fun g => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.prod_apply, hdet,
    det_spinCUnitary]
  refine Prod.ext (Subtype.ext (LinearEquiv.ext fun v => b.complexCoords.injective ?_)) rfl
  rw [hrot, complexCoords_toSpecialOrthogonal_spinCUnitary_apply]

/-- **Comparison with the lift of the plane rotations.** The lift of the unitary matrix
`diag (1, z)`, which turns the plane `⟨b₂, b₃⟩` by `z` and fixes `b₀` and `b₁`, is the `Spinᶜ`
lift `spinCCircle` of the rotations of that plane. -/
theorem spinCUnitary_unitaryTorusHom_mulSingle_one (z : Circle) :
    b.spinCUnitary hQ hQ₀ (unitaryTorusHom (Fin 2) (Pi.mulSingle 1 z)) =
      spinCCircle Q hQ₀ (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
        (b.map_apply_mul_map_apply hQ 2 3) z := by
  have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  have hQb (i : Fin 4) : Q (b i) = -1 := by simp [hQ]
  have hortho {i j : Fin 4} (hij : i ≠ j) : Q.IsOrtho (b i) (b j) := b.isOrtho_apply hQ hij
  have huw := b.isOrtho_apply hQ (by decide : (2 : Fin 4) ≠ 3)
  have h := b.map_apply_mul_map_apply hQ 2 3
  let φ : Circle →* spinCGroup Q hQ₀ := (b.spinCUnitary hQ hQ₀).comp
    ((unitaryTorusHom (Fin 2)).comp (MonoidHom.mulSingle (fun _ : Fin 2 => Circle) 1))
  have hφ : φ = spinCCircle Q hQ₀ (b 2) (b 3) huw h := by
    refine eq_spinCCircle hQ₀ huw h
      (QuadraticMap.Anisotropic.nondegenerate fun v hv => by simpa [hQ] using hv) ?_ ?_
    · -- Compare the two rotations on the frame, using the complex coordinates for `φ`.
      refine MonoidHom.ext fun w => Subtype.ext (LinearEquiv.toLinearMap_injective
        (b.toBasis.ext fun i => ?_))
      have hrot := b.complexCoords_toSpecialOrthogonal_spinCUnitary_apply hQ hQ₀
        (unitaryTorusHom (Fin 2) (Pi.mulSingle 1 w)) (b i)
      rw [← LinearEquiv.eq_symm_apply] at hrot
      simp only [MonoidHom.comp_apply, LinearEquiv.coe_coe, OrthonormalBasis.coe_toBasis,
        MonoidHom.mulSingle_apply, φ]
      rw [hrot]
      fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue]
      · rw [toSpecialOrthogonal_spinCCircle_apply_of_isOrtho _ _ _ (hortho (by decide))
          (hortho (by decide))]
        simp [mulVec_diagonal]
      · rw [toSpecialOrthogonal_spinCCircle_apply_of_isOrtho _ _ _ (hortho (by decide))
          (hortho (by decide))]
        simp [mulVec_diagonal]
      · rw [toSpecialOrthogonal_spinCCircle_apply_left, hQb]
        simp [mulVec_diagonal]
      · rw [toSpecialOrthogonal_spinCCircle_apply_right, hQb]
        simp [mulVec_diagonal, add_comm]
    · refine MonoidHom.ext fun w => Circle.ext ?_
      simp [φ, Fin.prod_univ_two]
  exact DFunLike.congr_fun hφ z

end OrthonormalBasis
