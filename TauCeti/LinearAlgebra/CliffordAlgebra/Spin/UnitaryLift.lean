/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Matrix.UnitaryGroup.Quaternion
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
import TauCeti.Analysis.Normed.Module.QuadraticMap

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

This is a frame model of the canonical lift `TauCeti.SeibergWitten.unitaryLift` of the unitary
group of an almost Hermitian four-space, which is defined through a spin module as the inverse of
the rotation homomorphism on the subgroup of `Spinᶜ(4)` fixing Taubes's canonical line. For
`J b₀ = b₁`, `J b₂ = b₃`, the two agree
(`TauCeti.SeibergWitten.unitaryLift_eq_spinCUnitary`); the model here needs
neither a spin module nor an orientation of `b`.

Uniqueness holds because two such lifts differ by a homomorphism from `U(2)` to the central kernel
`{1, [1, -1]}` of `Spinᶜ(4) → SO(4) × U(1)`, and every element of `U(2)` is a square
(`Matrix.UnitaryGroup.isSquare`), so `CliffordAlgebra.spinCGroup.hom_ext_of_isSquare` applies.
Together with the naturality of the plane lift under quadratic isometries
(`CliffordAlgebra.spinCGroupMap_spinCCircle`), applied to the stabilization of a
three-space by a line, the last property compares, at the structure-group level, the `Spinᶜ`
structure of an oriented plane field on a three-manifold `Y`, stabilized to `S¹ × Y`, with the
canonical `Spinᶜ` structure of an almost complex structure on `S¹ × Y` that sends `∂ₛ` into `Y`
and preserves the plane field.

For a unitary frame `e`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, of an orthogonal complex structure `J₀`,
reading the orthogonal transformations commuting with `J₀` as unitary matrices
(`OrthonormalBasis.centralizerToUnitaryGroup`) and composing with `spinCUnitary` gives a lift
`U(V, J₀) → Spinᶜ(Q)` of the inclusion into the rotations, whose determinant character is the
complex determinant (`OrthonormalBasis.centralizerSpinCLift`). On `ℝ⁴` the standard basis carries
it to the coordinate group `Spinᶜ(4)` of the positive-definite form `realCliffordForm 4 0`
(`TauCeti.unitarySpinCLift`), the structure-group homomorphism of the `Spinᶜ` structure that
`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure` builds from an almost complex rank-four
bundle and the chosen frame `e`. Continuity of these lifts is in
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitaryLift`.

## Construction

Existence uses quaternions. The group `U(2)` is the quotient of `Sp(1) × U(1)` by `±(1, 1)`, with
`(a, w)` acting on `ℂ²` by `w • a` (`Quaternion.unitaryProdCircleToUnitaryGroup`); identifying `ℂ²`
with `ℍ` by the first column of the matrix of a quaternion, this is `q ↦ a q w`, with `w` a unit
quaternion in the complex line `ℝ ⊕ ℝ i`. The compact group `Spin(4)` is `Sp(1) × Sp(1)`, with
`(a, c)` acting by `q ↦ a q (star c)` (`TauCeti.realSpinFourEquivQuaternionUnitaryProd_action`).
So `(a, w)` lifts to the class `[(a, w⁻¹), w]` in `Spinᶜ(4)`, which is unchanged when `(a, w)` is
replaced by `(-a, -w)`; its determinant character is `w² = det (w • a)`. The resulting lift on the
compact coordinate model, `TauCeti.realSpinCUnitary`, is transported to `V` along a reordering
of the frame (`OrthonormalBasis.realSpinCGroupHom`, `OrthonormalBasis.spinCUnitary_eq_comp`).

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
  · have hc : Quaternion.circleToUnitary (-1 : Circle) = -1 :=
      Subtype.ext (by ext <;> simp [Unitary.coe_neg])
    have hs : realSpinFourEquivQuaternionUnitaryProd.symm (-1, -1) =
        spinGroup.negOne _ (nondegenerate_realCliffordForm 4 0).ne_zero :=
      (MulEquiv.symm_apply_eq _).mpr (realSpinFourEquivQuaternionUnitaryProd_negOne _).symm
    simp [spinCOfPair_apply, hc, hs]

/-- The lift `U(2) → Spinᶜ(4)` of the compact coordinate model: the class `[(a, w⁻¹), w]` of
`w • a`, for a unit quaternion `a` and `w` in the circle
(`TauCeti.realSpinCUnitary_unitaryProdCircleToUnitaryGroup`). Its transport along a frame is
`OrthonormalBasis.spinCUnitary` (`OrthonormalBasis.spinCUnitary_eq_comp`). -/
def TauCeti.realSpinCUnitary :
    unitaryGroup (Fin 2) ℂ →*
      spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero :=
  Quaternion.unitaryProdCircleToUnitaryGroup.liftOfRightInverse _
    (Function.rightInverse_surjInv Quaternion.unitaryProdCircleToUnitaryGroup_surjective)
    ⟨spinCOfPair, ker_le_ker_spinCOfPair⟩

private theorem realSpinCUnitary_apply (p : unitary ℍ[ℝ] × Circle) :
    realSpinCUnitary (Quaternion.unitaryProdCircleToUnitaryGroup p) = spinCOfPair p :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p

/-- On `w • a`, for a unit quaternion `a` and `w` in the circle, the lift of the compact coordinate
model is the class `[(a, w⁻¹), w]`, where `Spin(4) = Sp(1) × Sp(1)`. -/
@[simp]
theorem TauCeti.realSpinCUnitary_unitaryProdCircleToUnitaryGroup (p : unitary ℍ[ℝ] × Circle) :
    realSpinCUnitary (Quaternion.unitaryProdCircleToUnitaryGroup p) =
      spinCGroup.mk _ _
        (realSpinFourEquivQuaternionUnitaryProd.symm (p.1, Quaternion.circleToUnitary p.2⁻¹),
          p.2) :=
  realSpinCUnitary_apply p

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
  rw [realSpinFourEquivQuaternionUnitaryProd_action,
    Quaternion.coe_unitaryProdCircleToUnitaryGroup_apply, smul_mulVec, coordVec, coordVec,
    Quaternion.ofFirstColumn_smul, Quaternion.ofFirstColumn_toComplexMatrix_mulVec]
  simp only [MulEquiv.apply_symm_apply, QuadraticMap.IsometryEquiv.apply_symm_apply,
    Unitary.star_eq_inv, ← map_inv, inv_inv, Quaternion.coe_circleToUnitary]

private theorem det_spinCOfPair (p : unitary ℍ[ℝ] × Circle) :
    spinCGroup.det _ _ (spinCOfPair p) =
      UnitaryGroup.detCircle (Quaternion.unitaryProdCircleToUnitaryGroup p) := by
  apply Circle.ext
  rw [spinCOfPair_apply, spinCGroup.det_mk, UnitaryGroup.coe_detCircle,
    Quaternion.coe_unitaryProdCircleToUnitaryGroup_apply, det_smul,
    Quaternion.det_toComplexMatrix, (Quaternion.mem_unitary_iff_normSq_eq_one _).mp p.1.property]
  simp

/-! ### Complex coordinates in a frame and the lift -/

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 4) ℝ V)

/-- The reordered frame `(b₂, b₁, -b₀, b₃)`, along which the quaternion coordinates of the compact
coordinate model of `TauCeti.realSpinCUnitary` become the complex coordinates
`b.complexCoords 2`. -/
def quaternionFrame : OrthonormalBasis (Fin 4) ℝ V :=
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

@[simp]
theorem coe_quaternionFrame : ⇑b.quaternionFrame = ![b 2, b 1, -b 0, b 3] :=
  OrthonormalBasis.coe_mk _ _

variable {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)

private theorem quaternionFrame_negRealCliffordFormIsometryEquiv_coordVec (z : Fin 2 → ℂ) :
    b.quaternionFrame.negRealCliffordFormIsometryEquiv hQ (coordVec z) =
      (b.complexCoords 2).symm z := by
  rw [negRealCliffordFormIsometryEquiv_apply, coe_quaternionFrame, Fin.sum_univ_four,
    complexCoords_two_symm_apply]
  simp [coordVec]
  abel

variable (hQ₀ : Q ≠ 0)

/-- **The `Spinᶜ` lift of `U(2)`.** For an orthonormal frame `b` of a four-dimensional space with
`Q v = -‖v‖²`, the homomorphism `U(2) → Spinᶜ(Q)` lifting `g ↦ (g, det g)` along
`Spinᶜ(Q) → SO(Q) × U(1)`, where `g` acts on `V` through the complex coordinates
`b.complexCoords 2` (`complexCoords_toSpecialOrthogonal_spinCUnitary_apply`, `det_spinCUnitary`).
It is the only such homomorphism (`eq_spinCUnitary`). -/
def spinCUnitary : unitaryGroup (Fin 2) ℂ →* spinCGroup Q hQ₀ :=
  (b.quaternionFrame.realSpinCGroupHom hQ (nondegenerate_realCliffordForm 4 0).ne_zero hQ₀).comp
    realSpinCUnitary

/-- The lift `spinCUnitary` is the lift `TauCeti.realSpinCUnitary` of the compact coordinate model,
transported along the reordered frame `b.quaternionFrame`. -/
theorem spinCUnitary_eq_comp :
    b.spinCUnitary hQ hQ₀ =
      (b.quaternionFrame.realSpinCGroupHom hQ (nondegenerate_realCliffordForm 4 0).ne_zero
        hQ₀).comp realSpinCUnitary :=
  (rfl)

/-- **The rotation of `spinCUnitary g` is `g`** in the complex coordinates of the frame. -/
theorem complexCoords_toSpecialOrthogonal_spinCUnitary_apply (g : unitaryGroup (Fin 2) ℂ)
    (v : V) :
    b.complexCoords 2
        ((spinCGroup.toSpecialOrthogonal Q hQ₀ (b.spinCUnitary hQ hQ₀ g) : V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ b.complexCoords 2 v := by
  obtain ⟨z, rfl⟩ := (b.complexCoords 2).symm.surjective v
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
    (hrot : ∀ g v, b.complexCoords 2
        ((spinCGroup.toSpecialOrthogonal Q hQ₀ (φ g) : V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ b.complexCoords 2 v)
    (hdet : ∀ g, spinCGroup.det Q hQ₀ (φ g) = UnitaryGroup.detCircle g) :
    φ = b.spinCUnitary hQ hQ₀ := by
  have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  refine spinCGroup.hom_ext_of_isSquare Q hQ₀ (QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ)
    UnitaryGroup.isSquare (MonoidHom.ext fun g => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.prod_apply, hdet,
    det_spinCUnitary]
  refine Prod.ext (Subtype.ext (LinearEquiv.ext fun v => (b.complexCoords 2).injective ?_)) rfl
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
  let φ : Circle →* spinCGroup Q hQ₀ := (b.spinCUnitary hQ hQ₀).comp
    ((unitaryTorusHom (Fin 2)).comp (MonoidHom.mulSingle (fun _ : Fin 2 => Circle) 1))
  have hφ : φ = spinCCircle Q hQ₀ (b 2) (b 3) (hortho (by decide))
      (b.map_apply_mul_map_apply hQ 2 3) := by
    refine eq_spinCCircle hQ₀ _ _ (QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ) ?_ ?_
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

/-! ### The lift of the centralizer of a complex structure -/

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (e : OrthonormalBasis (Fin 4) ℝ V) {J₀ : unitary (V →L[ℝ] V)}
  (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
  (h₀ : (J₀ : V →L[ℝ] V) (e 0) = e 1) (h₂ : (J₀ : V →L[ℝ] V) (e 2) = e 3)
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₀ : Q ≠ 0)

/-- **The `Spinᶜ` lift of the unitary group of a complex structure.** For a unitary frame `e` of
an orthogonal complex structure `J₀`, the homomorphism `U(V, J₀) → Spinᶜ(Q)`, lifting the
inclusion of the orthogonal transformations commuting with `J₀` along the rotation homomorphism
(`OrthonormalBasis.toSpecialOrthogonal_centralizerSpinCLift_apply`), with determinant character
the determinant of the unitary matrix (`OrthonormalBasis.det_centralizerSpinCLift`): the lift
`spinCUnitary` of `U(2)` read through `centralizerToUnitaryGroup`. -/
def centralizerSpinCLift : Subgroup.centralizer {J₀} →* spinCGroup Q hQ₀ :=
  (e.spinCUnitary hQ hQ₀).comp (e.centralizerToUnitaryGroup hJ₀ h₀ h₂)

/-- The lift `centralizerSpinCLift` is the lift `spinCUnitary` of `U(2)` read through
`centralizerToUnitaryGroup`. -/
theorem centralizerSpinCLift_eq_comp :
    e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀ =
      (e.spinCUnitary hQ hQ₀).comp (e.centralizerToUnitaryGroup hJ₀ h₀ h₂) :=
  (rfl)

/-- **The rotation of `centralizerSpinCLift g` is `g`.** -/
theorem toSpecialOrthogonal_centralizerSpinCLift_apply (g : Subgroup.centralizer {J₀}) (v : V) :
    (spinCGroup.toSpecialOrthogonal Q hQ₀ (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀ g) :
        V ≃ₗ[ℝ] V) v = ((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V) v := by
  refine (e.complexCoords 2).injective ?_
  rw [centralizerSpinCLift, MonoidHom.comp_apply,
    complexCoords_toSpecialOrthogonal_spinCUnitary_apply,
    e.complexCoords_centralizerToUnitaryGroup_apply hJ₀ h₀ h₂]

/-- **The determinant character of `centralizerSpinCLift g` is the determinant of its unitary
matrix**, the complex determinant of `g`. -/
@[simp]
theorem det_centralizerSpinCLift (g : Subgroup.centralizer {J₀}) :
    spinCGroup.det Q hQ₀ (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀ g) =
      UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) :=
  e.det_spinCUnitary hQ hQ₀ _

end OrthonormalBasis

/-! ### The lift of the unitary group of `ℝ⁴` to the coordinate group `Spinᶜ(4)` -/

namespace TauCeti

section Lift

/-- The form `Q v = -‖v‖²` on `ℝ⁴` with the Euclidean norm. -/
private def negNormSqForm : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 4)) :=
  -LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 4)))

private theorem negNormSqForm_apply (v : EuclideanSpace ℝ (Fin 4)) :
    negNormSqForm v = -‖v‖ ^ 2 := by
  simp [negNormSqForm]

private theorem negNormSqForm_ne_zero : negNormSqForm ≠ 0 :=
  (QuadraticForm.nondegenerate_of_eq_neg_norm_sq negNormSqForm_apply).ne_zero

/-- The coordinates of the standard basis of `ℝ⁴` are the identification of `ℝ⁴` with the
Euclidean space. -/
private theorem basisFun_negRealCliffordFormIsometryEquiv_apply (x : Fin (4 + 0) → ℝ) :
    (EuclideanSpace.basisFun (Fin 4) ℝ).negRealCliffordFormIsometryEquiv negNormSqForm_apply x =
      WithLp.toLp 2 x := by
  ext i
  simp [OrthonormalBasis.negRealCliffordFormIsometryEquiv_apply, Finset.sum_apply,
    Pi.single_apply]

variable {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The `Spinᶜ` lift of the unitary group of `ℝ⁴`.** For an orthogonal complex structure `J₀` on
`ℝ⁴` and a unitary frame `e`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, the homomorphism
`U(ℝ⁴, J₀) → Spinᶜ(4)` from the orthogonal transformations commuting with `J₀`, lifting their
inclusion into `SO(4)` along the rotation homomorphism
(`TauCeti.toSpecialOrthogonal_unitarySpinCLift_apply`), with determinant character the
determinant of the unitary matrix (`TauCeti.det_unitarySpinCLift`). -/
def unitarySpinCLift :
    Subgroup.centralizer {J₀} →*
      spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero :=
  ((EuclideanSpace.basisFun (Fin 4) ℝ).realSpinCGroupEquiv negNormSqForm_apply
      (nondegenerate_realCliffordForm 4 0).ne_zero negNormSqForm_ne_zero).symm.toMonoidHom.comp
    (e.centralizerSpinCLift hJ₀ h₀ h₂ negNormSqForm_apply negNormSqForm_ne_zero)

/-- The lift `unitarySpinCLift` is the lift `centralizerSpinCLift` for any form `Q v = -‖v‖²` on
`ℝ⁴`, transported to the coordinate group `Spinᶜ(4)` along the standard basis. -/
theorem unitarySpinCLift_eq_comp {Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 4))}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₀ : Q ≠ 0) :
    unitarySpinCLift hJ₀ e h₀ h₂ =
      ((EuclideanSpace.basisFun (Fin 4) ℝ).realSpinCGroupEquiv hQ
        (nondegenerate_realCliffordForm 4 0).ne_zero hQ₀).symm.toMonoidHom.comp
          (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀) := by
  obtain rfl : Q = negNormSqForm :=
    QuadraticMap.ext fun v ↦ (hQ v).trans (negNormSqForm_apply v).symm
  rfl

/-- **The rotation of `unitarySpinCLift g` is `g`**, read on coordinate vectors. -/
theorem toSpecialOrthogonal_unitarySpinCLift_apply (g : Subgroup.centralizer {J₀})
    (v : Fin (4 + 0) → ℝ) :
    (spinCGroup.toSpecialOrthogonal _ _ (unitarySpinCLift hJ₀ e h₀ h₂ g) :
        (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ)) v =
      WithLp.ofLp (((g : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))) :
        EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (WithLp.toLp 2 v)) := by
  have h := (EuclideanSpace.basisFun (Fin 4) ℝ).toSpecialOrthogonal_realSpinCGroupHom_apply
    negNormSqForm_apply (nondegenerate_realCliffordForm 4 0).ne_zero negNormSqForm_ne_zero
    (unitarySpinCLift hJ₀ e h₀ h₂ g) v
  rw [← OrthonormalBasis.coe_realSpinCGroupEquiv, unitarySpinCLift, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    e.toSpecialOrthogonal_centralizerSpinCLift_apply,
    basisFun_negRealCliffordFormIsometryEquiv_apply,
    basisFun_negRealCliffordFormIsometryEquiv_apply] at h
  rw [unitarySpinCLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, WithLp.ofLp_toLp]

/-- **The determinant character of `unitarySpinCLift g` is the complex determinant of `g`**, the
determinant of its unitary matrix in the frame `e`. -/
@[simp]
theorem det_unitarySpinCLift (g : Subgroup.centralizer {J₀}) :
    spinCGroup.det _ _ (unitarySpinCLift hJ₀ e h₀ h₂ g) =
      Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) := by
  rw [← e.det_centralizerSpinCLift hJ₀ h₀ h₂ negNormSqForm_apply negNormSqForm_ne_zero,
    unitarySpinCLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← (EuclideanSpace.basisFun (Fin 4) ℝ).det_realSpinCGroupHom negNormSqForm_apply
      (nondegenerate_realCliffordForm 4 0).ne_zero negNormSqForm_ne_zero,
    ← OrthonormalBasis.coe_realSpinCGroupEquiv, MulEquiv.apply_symm_apply]

/-- `unitarySpinCLift` lifts the inclusion of `U(ℝ⁴, J₀)` into the linear automorphisms of `ℝ⁴`
along the rotation homomorphism of `Spinᶜ(4)`. -/
theorem toSpecialOrthogonal_comp_unitarySpinCLift :
    ((QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm 4 0) _)).comp
          (unitarySpinCLift hJ₀ e h₀ h₂) =
      (euclideanLinearEquivHom ℝ (Fin 4)).comp (Subgroup.centralizer {J₀}).subtype :=
  MonoidHom.ext fun g ↦ LinearEquiv.ext fun v ↦ by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, euclideanLinearEquivHom_apply]
    exact toSpecialOrthogonal_unitarySpinCLift_apply hJ₀ e h₀ h₂ g v

end Lift

end TauCeti
