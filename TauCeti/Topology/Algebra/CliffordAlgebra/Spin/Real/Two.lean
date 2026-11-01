/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal
import Mathlib.Analysis.Complex.Isometry
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.Two
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic

/-!
# The real Spin group in dimension two and the squaring map

Let `Q = realCliffordForm 2 0` be the positive-definite form `x₀² + x₁²` on the plane, and write
`J = e₀ e₁`, so that `J * J = -1`. The compact Spin group `Spin(2)` consists of the elements
`u + v J` with `u² + v² = 1`. This file identifies both `Spin(2)` and the special orthogonal group
`SO(2)` of `Q` with Mathlib's `Circle` as topological groups, and shows that under these
identifications the Spin double cover `Spin(2) → SO(2)` is the squaring map `z ↦ z²`.

The conventions are pinned as follows.

* `Spin(2) ≃ₜ* Circle` sends `u + v J` to `u - v i`. Thus `cos θ - sin θ e₀e₁` goes to
  `exp (i θ)`.
* `SO(2) ≃ₜ* Circle` sends `z` back to multiplication by `z` in the complex coordinate
  `m ↦ m₀ + m₁ i` of the plane, so a rotation by the angle `φ` goes to `exp (i φ)`.

With these choices the Spin element `cos θ - sin θ e₀e₁` acts on the plane as the rotation by the
angle `2θ`. The sign is forced by the Clifford relations:
`(u + v J) e₀ (u - v J) = (u² - v²) e₀ - 2 u v e₁`.

## Main definitions

* `CliffordAlgebra.realCliffordSpinTwoContinuousMulEquivCircle`: `Spin(2) ≃ₜ* Circle`.
* `CliffordAlgebra.realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle`: `SO(2) ≃ₜ* Circle`.

## Main results

* `CliffordAlgebra.coe_realCliffordSpinTwoContinuousMulEquivCircle_symm_apply`: the Spin element
  attached to `z` is `Re z - (Im z) e₀e₁`, and
  `CliffordAlgebra.coe_realCliffordSpinTwoContinuousMulEquivCircle_apply_of_coe_eq_ι_mul_ι`: a
  product `ι a * ι b` goes to `(a₀ + a₁ i) (b₀ - b₁ i)`.
* `CliffordAlgebra.coe_realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_apply` and
  `CliffordAlgebra.realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply`: the two
  directions of the identification of `SO(2)` with the circle, in the complex coordinate, with
  the coordinate forms `realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply_zero`
  and `realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply_one`.
* `realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_spinToSpecialOrthogonal`:
  the Spin projection, which is the covering map `realCliffordSpinProjectionZero 2`, becomes
  `z ↦ z²`.

## Implementation notes

The Clifford algebra of the plane acts on `ℂ` by letting a vector `m` act as `w ↦ m * conj w`, in
the complex coordinate of `m`; since `m * conj (m * conj w) = |m|² w`, this is a representation. An
even element acts by multiplication by its value at `1`, reversal conjugates that value, and so
the Spin action `m ↦ x m x⋆` becomes multiplication by the square of the value of `x`. Injectivity
uses that every even element is `ι e₀ * ι w` for a vector `w`
(`CliffordAlgebra.mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two`), surjectivity onto `SO(2)` the
surjectivity of the Spin projection, and the continuity of the inverses the compactness of
`Spin(2)` and of the circle.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open Complex ComplexConjugate

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- The complex coordinate `m ↦ m₀ + m₁ i` of the Euclidean plane. -/
private def planeCoord : (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] ℂ := Complex.basisOneI.equivFun.symm

private theorem planeCoord_apply (m : Fin (2 + 0) → ℝ) :
    planeCoord m = (m 0 : ℂ) + (m 1 : ℂ) * I := by
  simp [planeCoord, Fin.sum_univ_two, mul_comm]

private theorem realCliffordForm_two_apply (m : Fin (2 + 0) → ℝ) :
    realCliffordForm 2 0 m = normSq (planeCoord m) := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one, planeCoord_apply]
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, normSq_apply]

/-- The Clifford algebra of the Euclidean plane acting on `ℂ`: a vector `m` acts by
`w ↦ m * conj w`, in the complex coordinate of `m`. -/
private def planeAction : CliffordAlgebra (realCliffordForm 2 0) →ₐ[ℝ] Module.End ℝ ℂ :=
  lift _ ⟨((LinearMap.mul ℝ ℂ).compl₂ conjAe.toLinearMap).comp planeCoord.toLinearMap,
    fun m ↦ by
      ext w
      simp only [Module.End.mul_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.compl₂_apply, LinearMap.mul_apply', AlgEquiv.toLinearMap_apply, conjAe_coe,
        LinearEquiv.coe_coe, map_mul, conj_conj, Module.algebraMap_end_apply,
        realCliffordForm_two_apply]
      rw [← mul_assoc, mul_conj, real_smul]⟩

private theorem planeAction_ι_apply (m : Fin (2 + 0) → ℝ) (w : ℂ) :
    planeAction (ι _ m) w = planeCoord m * conj w := by
  simp [planeAction]

/-- The value at `1` of the action on `ℂ`; on even elements it is the action itself. -/
private def planeValue : CliffordAlgebra (realCliffordForm 2 0) →ₗ[ℝ] ℂ :=
  LinearMap.applyₗ (1 : ℂ) ∘ₗ planeAction.toLinearMap

private theorem planeValue_apply (x : CliffordAlgebra (realCliffordForm 2 0)) :
    planeValue x = planeAction x 1 := rfl

/-- An even element acts on `ℂ` by multiplication by its value at `1`. -/
private theorem planeAction_apply_of_mem_even {x : CliffordAlgebra (realCliffordForm 2 0)}
    (hx : x ∈ evenOdd (realCliffordForm 2 0) 0) (w : ℂ) :
    planeAction x w = planeValue x * w := by
  induction x, hx using even_induction with
  | algebraMap r => simp [planeValue_apply, AlgHom.commutes, Algebra.smul_def]
  | add x y _ _ hx hy => simp [map_add, hx, hy, add_mul]
  | ι_mul_ι_mul a b x _ h =>
    simp only [planeValue_apply, map_mul, Module.End.mul_apply, planeAction_ι_apply, h,
      map_mul, conj_conj]
    ring

private theorem planeValue_mul_of_mem_even {x : CliffordAlgebra (realCliffordForm 2 0)}
    (hx : x ∈ evenOdd (realCliffordForm 2 0) 0) (y : CliffordAlgebra (realCliffordForm 2 0)) :
    planeValue (x * y) = planeValue x * planeValue y := by
  rw [planeValue_apply, map_mul, Module.End.mul_apply, planeAction_apply_of_mem_even hx,
    ← planeValue_apply]

private theorem planeValue_ι_mul_ι (a b : Fin (2 + 0) → ℝ) :
    planeValue (ι _ a * ι _ b) = planeCoord a * conj (planeCoord b) := by
  simp [planeValue_apply, planeAction_ι_apply]

/-- Reversal conjugates the value of an even element. -/
private theorem planeValue_reverse_of_mem_even {x : CliffordAlgebra (realCliffordForm 2 0)}
    (hx : x ∈ evenOdd (realCliffordForm 2 0) 0) :
    planeValue (reverse x) = conj (planeValue x) := by
  induction x, hx using even_induction with
  | algebraMap r => simp [planeValue_apply, AlgHom.commutes]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | ι_mul_ι_mul a b x hx h =>
    simp [reverse_ι, planeValue_mul_of_mem_even ((reverse_mem_evenOdd_iff _).2 hx), h,
      planeValue_mul_of_mem_even (ι_mul_ι_mem_evenOdd_zero _ _ _), planeValue_ι_mul_ι]
    ring

private theorem planeValue_one : planeValue 1 = 1 := by
  simp [planeValue_apply]

private theorem planeCoord_single_zero : planeCoord (Pi.single 0 1 : Fin (2 + 0) → ℝ) = 1 := by
  simp [planeCoord_apply]

private theorem coe_mem_evenOdd_zero (x : realCliffordSpinGroupZero 2) :
    (x : CliffordAlgebra (realCliffordForm 2 0)) ∈ evenOdd (realCliffordForm 2 0) 0 := by
  rw [← even_toSubmodule]
  exact spinGroup.mem_even x.2

/-- The value of a Spin element has norm one. -/
private theorem norm_planeValue (x : realCliffordSpinGroupZero 2) :
    ‖planeValue (x : CliffordAlgebra (realCliffordForm 2 0))‖ = 1 := by
  have hx := coe_mem_evenOdd_zero x
  have h := congrArg planeValue (spinGroup.mul_star_self_of_mem x.2)
  rw [planeValue_mul_of_mem_even hx, star_def, involute_eq_of_mem_even hx,
    planeValue_reverse_of_mem_even hx] at h
  simpa [mul_conj, planeValue_one, normSq_eq_norm_sq, ← ofReal_pow,
    pow_eq_one_iff_of_nonneg (norm_nonneg _)] using h

/-- In complex coordinates, a Spin element `x` acts on the plane by multiplication by the square
of its value. -/
private theorem planeCoord_spinVectorAction (x : realCliffordSpinGroupZero 2)
    (m : Fin (2 + 0) → ℝ) :
    planeCoord (spinVectorAction _ x m) =
      planeValue (x : CliffordAlgebra (realCliffordForm 2 0)) ^ 2 * planeCoord m := by
  have hx := coe_mem_evenOdd_zero x
  have h := planeAction_ι_apply (spinVectorAction _ x m) 1
  simp [ι_spinVectorAction_apply, planeAction_apply_of_mem_even hx, planeAction_ι_apply,
    ← planeValue_apply, star_def, involute_eq_of_mem_even hx,
    planeValue_reverse_of_mem_even hx] at h
  linear_combination -h

/-- The value of `ι e₀ * ι w` is the conjugate of the complex coordinate of `w`. -/
private theorem planeValue_ι_single_mul_ι (w : Fin (2 + 0) → ℝ) :
    planeValue (ι _ (Pi.single 0 1 : Fin (2 + 0) → ℝ) * ι _ w) = conj (planeCoord w) := by
  rw [planeValue_ι_mul_ι, planeCoord_single_zero, one_mul]

/-- The value of a Spin element, as a point of the unit circle. -/
private def spinTwoToCircle : realCliffordSpinGroupZero 2 →* Circle where
  toFun x := ⟨planeValue (x : CliffordAlgebra (realCliffordForm 2 0)),
    mem_sphere_zero_iff_norm.2 (norm_planeValue x)⟩
  map_one' := Circle.ext planeValue_one
  map_mul' x _ := Circle.ext (planeValue_mul_of_mem_even (coe_mem_evenOdd_zero x) _)

private theorem coe_spinTwoToCircle (x : realCliffordSpinGroupZero 2) :
    (spinTwoToCircle x : ℂ) = planeValue (x : CliffordAlgebra (realCliffordForm 2 0)) := rfl

/-- Every Spin element is `ι e₀ * ι w` for a vector `w`. -/
private theorem exists_coe_eq_ι_single_mul_ι (x : realCliffordSpinGroupZero 2) :
    ∃ w, (x : CliffordAlgebra (realCliffordForm 2 0)) =
      ι _ (Pi.single 0 1 : Fin (2 + 0) → ℝ) * ι _ w := by
  let _ : Invertible (realCliffordForm 2 0 (Pi.single 0 1 : Fin (2 + 0) → ℝ)) :=
    invertibleOfNonzero (by simp [realCliffordForm_zero_single_one])
  exact (mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two _ (by simp) _).1 (spinGroup.mem_even x.2)

private theorem spinTwoToCircle_injective : Function.Injective spinTwoToCircle := by
  intro x y hxy
  obtain ⟨w, hw⟩ := exists_coe_eq_ι_single_mul_ι x
  obtain ⟨w', hw'⟩ := exists_coe_eq_ι_single_mul_ι y
  have h := congrArg ((↑) : Circle → ℂ) hxy
  rw [coe_spinTwoToCircle, coe_spinTwoToCircle, hw, hw', planeValue_ι_single_mul_ι,
    planeValue_ι_single_mul_ι] at h
  have hww' : w = w' := planeCoord.injective ((starRingEnd ℂ).injective h)
  exact Subtype.ext (hw.trans (hww' ▸ hw'.symm))

/-- The Spin element `ι e₀ * ι w` attached to a point `z` of the circle, with `w` the vector of
complex coordinate `conj z`. -/
private theorem ι_single_mul_ι_mem_realCliffordSpinGroupZero (z : Circle) :
    ι _ (Pi.single 0 1 : Fin (2 + 0) → ℝ) * ι _ (planeCoord.symm (conj (z : ℂ))) ∈
      realCliffordSpinGroupZero 2 :=
  ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ (by
    simp [realCliffordForm_two_apply, normSq_eq_norm_sq])

private theorem spinTwoToCircle_surjective : Function.Surjective spinTwoToCircle := fun z ↦
  ⟨⟨_, ι_single_mul_ι_mem_realCliffordSpinGroupZero z⟩, Circle.ext (by
    rw [coe_spinTwoToCircle, planeValue_ι_single_mul_ι, LinearEquiv.apply_symm_apply, conj_conj])⟩

/-- Rotation of the plane by a point `z` of the circle: multiplication by `z` in the complex
coordinate. -/
private def circleToSpecialOrthogonal :
    Circle →* QuadraticMap.specialOrthogonalGroup (realCliffordForm 2 0) where
  toFun z := ⟨(planeCoord.trans (rotation z).toLinearEquiv).trans planeCoord.symm, by
    refine QuadraticMap.mem_specialOrthogonalGroup_iff.2
      ⟨QuadraticMap.mem_orthogonalGroup_iff.2 fun m ↦ ?_, ?_⟩
    · simp [realCliffordForm_two_apply, normSq_eq_norm_sq]
    · simpa using LinearEquiv.det_conj (rotation z).toLinearEquiv planeCoord.symm⟩
  map_one' := by ext; simp
  map_mul' z z' := by ext; simp

private theorem planeCoord_circleToSpecialOrthogonal_apply (z : Circle) (m : Fin (2 + 0) → ℝ) :
    planeCoord ((circleToSpecialOrthogonal z : (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) m) =
      z * planeCoord m := by
  simp [circleToSpecialOrthogonal]

/-- The rotation by the square of the value of a Spin element is its vector action. -/
private theorem circleToSpecialOrthogonal_spinTwoToCircle_sq (x : realCliffordSpinGroupZero 2) :
    circleToSpecialOrthogonal (spinTwoToCircle x ^ 2) = spinToSpecialOrthogonal _ x := by
  refine Subtype.ext (LinearEquiv.ext fun m ↦ planeCoord.injective ?_)
  rw [planeCoord_circleToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_apply,
    planeCoord_spinVectorAction, Circle.coe_pow, coe_spinTwoToCircle]

private theorem circleToSpecialOrthogonal_injective :
    Function.Injective circleToSpecialOrthogonal := fun z z' h ↦ by
  have hz := planeCoord_circleToSpecialOrthogonal_apply z (planeCoord.symm 1)
  rw [h, planeCoord_circleToSpecialOrthogonal_apply, LinearEquiv.apply_symm_apply, mul_one,
    mul_one] at hz
  exact Circle.ext hz.symm

private theorem circleToSpecialOrthogonal_surjective :
    Function.Surjective circleToSpecialOrthogonal := fun g ↦ by
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef _
    (posDef_realCliffordForm_zero 2) g
  exact ⟨_, circleToSpecialOrthogonal_spinTwoToCircle_sq x⟩

private theorem continuous_spinTwoToCircle : Continuous spinTwoToCircle := by
  let _ : ContinuousAdd (CliffordAlgebra (realCliffordForm 2 0)) :=
    IsModuleTopology.toContinuousAdd ℝ _
  exact ((IsModuleTopology.continuous_of_linearMap planeValue).comp
    continuous_subtype_val).subtype_mk _

private theorem continuous_circleToSpecialOrthogonal : Continuous circleToSpecialOrthogonal := by
  apply (QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear _).isInducing.continuous_iff.2
  have h : Continuous ((QuadraticMap.specialOrthogonalToGeneralLinear _).comp
      circleToSpecialOrthogonal) := by
    apply Continuous.of_coeHom_comp
    apply continuous_matrix
    intro i j
    have hc : Continuous fun z : Circle ↦
        planeCoord.symm ((z : ℂ) * planeCoord (Pi.single j 1)) :=
      (LinearMap.continuous_of_finiteDimensional planeCoord.symm.toLinearMap).comp
        (continuous_subtype_val.mul continuous_const)
    convert (continuous_apply i).comp hc using 2 with z
    simp only [MonoidHom.comp_apply, Units.coeHom_apply,
      QuadraticMap.specialOrthogonalToGeneralLinear_apply, Function.comp_apply]
    rw [← planeCoord_circleToSpecialOrthogonal_apply, LinearEquiv.symm_apply_apply]
  rw [← MonoidHom.coe_comp]
  -- The embedding uses the classical decidable equality on `Fin 2`; `convert` identifies it with
  -- the one found for `h`.
  convert h

/-- **The compact real Spin group in dimension two is the circle group.** A Spin element
`x = u + v e₀e₁` of the positive-definite form `realCliffordForm 2 0` goes to `u - v i`; in
particular `cos θ - sin θ e₀e₁` goes to `exp (i θ)`. -/
def realCliffordSpinTwoContinuousMulEquivCircle : realCliffordSpinGroupZero 2 ≃ₜ* Circle where
  toMulEquiv := MulEquiv.ofBijective spinTwoToCircle
    ⟨spinTwoToCircle_injective, spinTwoToCircle_surjective⟩
  continuous_toFun := continuous_spinTwoToCircle
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective spinTwoToCircle
      ⟨spinTwoToCircle_injective, spinTwoToCircle_surjective⟩).toEquiv)
    continuous_spinTwoToCircle

/-- The rotations of the plane by the points of the circle, as an isomorphism of topological
groups. -/
private def circleContinuousMulEquivSpecialOrthogonal :
    Circle ≃ₜ* QuadraticMap.specialOrthogonalGroup (realCliffordForm 2 0) where
  toMulEquiv := MulEquiv.ofBijective circleToSpecialOrthogonal
    ⟨circleToSpecialOrthogonal_injective, circleToSpecialOrthogonal_surjective⟩
  continuous_toFun := continuous_circleToSpecialOrthogonal
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective circleToSpecialOrthogonal
      ⟨circleToSpecialOrthogonal_injective, circleToSpecialOrthogonal_surjective⟩).toEquiv)
    continuous_circleToSpecialOrthogonal

private theorem circleContinuousMulEquivSpecialOrthogonal_apply (z : Circle) :
    circleContinuousMulEquivSpecialOrthogonal z = circleToSpecialOrthogonal z := (rfl)

/-- **The special orthogonal group of the Euclidean plane is the circle group**: a point `z` of
the circle corresponds to multiplication by `z` in the complex coordinate `m ↦ m₀ + m₁ i`. -/
def realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm 2 0) ≃ₜ* Circle :=
  circleContinuousMulEquivSpecialOrthogonal.symm

private theorem realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_eq (z : Circle) :
    realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle.symm z =
      circleToSpecialOrthogonal z := by
  rw [realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle, ContinuousMulEquiv.symm_symm,
    circleContinuousMulEquivSpecialOrthogonal_apply]

private theorem coe_realCliffordSpinTwoContinuousMulEquivCircle_apply_eq_planeValue
    (x : realCliffordSpinGroupZero 2) :
    (realCliffordSpinTwoContinuousMulEquivCircle x : ℂ) =
      planeValue (x : CliffordAlgebra (realCliffordForm 2 0)) := (rfl)

/-- On a Spin element written as a product `ι a * ι b` of two vectors, the circle coordinate is
`(a₀ + a₁ i) (b₀ - b₁ i)`. -/
theorem coe_realCliffordSpinTwoContinuousMulEquivCircle_apply_of_coe_eq_ι_mul_ι
    (x : realCliffordSpinGroupZero 2) {a b : Fin (2 + 0) → ℝ}
    (h : (x : CliffordAlgebra (realCliffordForm 2 0)) = ι _ a * ι _ b) :
    (realCliffordSpinTwoContinuousMulEquivCircle x : ℂ) =
      ((a 0 : ℂ) + a 1 * I) * ((b 0 : ℂ) - b 1 * I) := by
  rw [coe_realCliffordSpinTwoContinuousMulEquivCircle_apply_eq_planeValue, h, planeValue_ι_mul_ι,
    planeCoord_apply, planeCoord_apply]
  simp [sub_eq_add_neg]

/-- The Spin element attached to a point `z` of the circle is `Re z - (Im z) e₀e₁`. -/
@[simp]
theorem coe_realCliffordSpinTwoContinuousMulEquivCircle_symm_apply (z : Circle) :
    ((realCliffordSpinTwoContinuousMulEquivCircle.symm z : realCliffordSpinGroupZero 2) :
        CliffordAlgebra (realCliffordForm 2 0)) =
      algebraMap ℝ _ (z : ℂ).re -
        (z : ℂ).im • (ι _ (Pi.single 0 1 : Fin (2 + 0) → ℝ) * ι _ (Pi.single 1 1)) := by
  have hz : realCliffordSpinTwoContinuousMulEquivCircle.symm z =
      ⟨_, ι_single_mul_ι_mem_realCliffordSpinGroupZero z⟩ := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact Circle.ext (by
      rw [coe_realCliffordSpinTwoContinuousMulEquivCircle_apply_eq_planeValue]
      -- Reduce the coercion of the anonymous Spin element to its Clifford value.
      dsimp only
      rw [planeValue_ι_single_mul_ι, LinearEquiv.apply_symm_apply, conj_conj])
  have hw : planeCoord.symm (conj (z : ℂ)) =
      (z : ℂ).re • (Pi.single 0 1 : Fin (2 + 0) → ℝ) - (z : ℂ).im • Pi.single 1 1 := by
    apply planeCoord.injective
    rw [LinearEquiv.apply_symm_apply, planeCoord_apply]
    apply Complex.ext <;> simp
  rw [hz]
  -- Reduce the coercion of the anonymous Spin element to its Clifford value.
  dsimp only
  simp [hw, mul_sub, ι_sq_scalar, realCliffordForm_zero_single_one,
    Algebra.algebraMap_eq_smul_one]

/-- The circle coordinate of a special orthogonal transformation `g` is the complex coordinate of
`g e₀`. -/
@[simp]
theorem coe_realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_apply
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm 2 0)) :
    (realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle g : ℂ) =
      ((g : (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) (Pi.single 0 1) 0 : ℂ) +
        ((g : (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) (Pi.single 0 1) 1 : ℂ) * I := by
  obtain ⟨z, rfl⟩ := circleContinuousMulEquivSpecialOrthogonal.surjective g
  rw [realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle,
    ContinuousMulEquiv.symm_apply_apply, ← planeCoord_apply]
  simp [circleContinuousMulEquivSpecialOrthogonal_apply,
    planeCoord_circleToSpecialOrthogonal_apply, planeCoord_single_zero]

private theorem planeCoord_realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply
    (z : Circle) (m : Fin (2 + 0) → ℝ) :
    planeCoord ((realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle.symm z :
        (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) m) = z * planeCoord m := by
  rw [realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_eq,
    planeCoord_circleToSpecialOrthogonal_apply]

/-- The first coordinate of the rotation of `m` by a point `z` of the circle is
`Re z * m₀ - Im z * m₁`. -/
@[simp]
theorem realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply_zero (z : Circle)
    (m : Fin (2 + 0) → ℝ) :
    (realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle.symm z :
        (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) m 0 =
      (z : ℂ).re * m 0 - (z : ℂ).im * m 1 := by
  simpa [planeCoord_apply] using congrArg re
    (planeCoord_realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply z m)

/-- The second coordinate of the rotation of `m` by a point `z` of the circle is
`Im z * m₀ + Re z * m₁`. -/
@[simp]
theorem realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply_one (z : Circle)
    (m : Fin (2 + 0) → ℝ) :
    (realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle.symm z :
        (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) m 1 =
      (z : ℂ).im * m 0 + (z : ℂ).re * m 1 := by
  simpa [planeCoord_apply, add_comm] using congrArg im
    (planeCoord_realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply z m)

/-- The special orthogonal transformation attached to a point `z` of the circle is multiplication
by `z` in the complex coordinate `m ↦ m₀ + m₁ i`. -/
theorem realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_apply (z : Circle)
    (m : Fin (2 + 0) → ℝ) :
    ((realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle.symm z :
        (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) m 0 : ℂ) +
      ((realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle.symm z :
        (Fin (2 + 0) → ℝ) ≃ₗ[ℝ] (Fin (2 + 0) → ℝ)) m 1 : ℂ) * I =
      z * ((m 0 : ℂ) + m 1 * I) := by
  apply Complex.ext <;> simp [add_comm]

/-- **The real Spin double cover in dimension two is the squaring map of the circle.** Under the
identifications of `Spin(2)` and `SO(2)` with the circle group, the Spin projection is `z ↦ z²`:
the Spin element `cos θ - sin θ e₀e₁` acts on the plane as the rotation by the angle `2θ`. The
projection is stated as `spinToSpecialOrthogonal`, the simp normal form of the covering map
`realCliffordSpinProjectionZero 2`. -/
@[simp]
theorem realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_spinToSpecialOrthogonal
    (x : realCliffordSpinGroupZero 2) :
    realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle
        (spinToSpecialOrthogonal (realCliffordForm 2 0) x) =
      realCliffordSpinTwoContinuousMulEquivCircle x ^ 2 := by
  rw [← ContinuousMulEquiv.eq_symm_apply,
    realCliffordSpecialOrthogonalTwoContinuousMulEquivCircle_symm_eq]
  exact (circleToSpecialOrthogonal_spinTwoToCircle_sq x).symm

end

end CliffordAlgebra
