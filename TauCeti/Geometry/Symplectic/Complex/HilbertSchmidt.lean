/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hilbert–Schmidt pairing of complex-antilinear parts

For orthogonal almost complex structures `J` and `K`, the projection
`A ↦ ½ (A + K ∘ A ∘ J)` is self-adjoint for the real Hilbert–Schmidt pairing.
A complex-antilinear map therefore pairs identically against a map and its antilinear part.
In real source dimension two the pairing of two complex-antilinear maps is twice their
pairing on any unit vector. This factor two cancels the projection's factor one half.

The source is finite-dimensional; the target may have arbitrary dimension and need not be
complete. The self-adjoint identity includes source dimension zero.

## Main results

* `TauCeti.AlmostComplexStructure.hilbertSchmidtInner_complexAntilinearPart_left_eq_right`:
  self-adjointness of the complex-antilinear projection.
* `TauCeti.IsComplexAntilinear.hilbertSchmidtInner_complexAntilinearPart_right`:
  pairing against an antilinear map.
* `TauCeti.IsComplexAntilinear.hilbertSchmidtInner_eq_two_mul_inner_apply`:
  the factor-two formula in real dimension two.
* `TauCeti.IsComplexAntilinear.hilbertSchmidtInner_complexAntilinearPart_eq_inner_apply`:
  cancellation with the half-normalized projection.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, in particular the metric convention preceding Lemma C.1.9.
-/

public noncomputable section

open ContinuousLinearMap
open scoped InnerProductSpace

namespace TauCeti

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (J : AlmostComplexStructure W) (K : AlmostComplexStructure V)

/-- The complex-antilinear projection for orthogonal `J` and `K` is self-adjoint for the real
Hilbert–Schmidt pairing. -/
theorem AlmostComplexStructure.hilbertSchmidtInner_complexAntilinearPart_left_eq_right
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hK : ∀ u v, ⟪K u, K v⟫_ℝ = ⟪u, v⟫_ℝ) (A B : W →L[ℝ] V) :
    hilbertSchmidtInner
        (complexAntilinearPart J.toLinearMap K.toLinearMap A.toLinearMap).toContinuousLinearMap B =
      hilbertSchmidtInner A
        (complexAntilinearPart J.toLinearMap K.toLinearMap
          B.toLinearMap).toContinuousLinearMap := by
  let T (C : W →L[ℝ] V) :=
    (K.toLinearMap ∘ₗ C.toLinearMap ∘ₗ J.toLinearMap).toContinuousLinearMap
  have hT (C : W →L[ℝ] V) (v : W) : T C v = K (C (J v)) := by
    simp only [T, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, coe_coe]
  have hp (C : W →L[ℝ] V) :
      (complexAntilinearPart J.toLinearMap K.toLinearMap C.toLinearMap).toContinuousLinearMap =
        (2⁻¹ : ℝ) • (C + T C) := by
    ext v
    simp only [LinearMap.coe_toContinuousLinearMap', complexAntilinearPart_apply,
      smul_apply, add_apply, hT, coe_coe]
  let e := LinearIsometryEquiv.ofSurjective (J.toLinearMap.isometryOfInner hJ) J.surjective
  -- `ofSurjective` adds the inverse without changing the isometry's underlying function.
  have he (v : W) : e v = J v := rfl
  let b := stdOrthonormalBasis ℝ W
  have htwist : hilbertSchmidtInner (T A) B = hilbertSchmidtInner A (T B) := by
    rw [hilbertSchmidtInner_eq_sum _ _ b, hilbertSchmidtInner_eq_sum _ _ (b.map e)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hT, OrthonormalBasis.map_apply, he, J.apply_apply, map_neg,
      inner_neg_right]
    exact K.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hK _ _
  rw [hp, hp, hilbertSchmidtInner_smul_left, hilbertSchmidtInner_add_left,
    hilbertSchmidtInner_smul_right, hilbertSchmidtInner_add_right, htwist]

variable {J K}

/-- A complex-antilinear map pairs identically against a real-linear map and its antilinear
part, for orthogonal source and target complex structures. -/
theorem IsComplexAntilinear.hilbertSchmidtInner_complexAntilinearPart_right
    {η : W →L[ℝ] V} (hη : IsComplexAntilinear J.toLinearMap K.toLinearMap η.toLinearMap)
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hK : ∀ u v, ⟪K u, K v⟫_ℝ = ⟪u, v⟫_ℝ) (A : W →L[ℝ] V) :
    hilbertSchmidtInner η
        (complexAntilinearPart J.toLinearMap K.toLinearMap A.toLinearMap).toContinuousLinearMap =
      hilbertSchmidtInner η A := by
  have hfix :
      (complexAntilinearPart J.toLinearMap K.toLinearMap η.toLinearMap).toContinuousLinearMap =
        η := by
    rw [hη.complexAntilinearPart_eq K.square_neg]
    ext v
    simp only [LinearMap.coe_toContinuousLinearMap', coe_coe]
  rw [← J.hilbertSchmidtInner_complexAntilinearPart_left_eq_right K hJ hK η A, hfix]

/-- In real source dimension two, the Hilbert–Schmidt pairing of two complex-antilinear maps
is twice their real target pairing on any unit source vector, for orthogonal `J` and `K`. -/
theorem IsComplexAntilinear.hilbertSchmidtInner_eq_two_mul_inner_apply
    {η θ : W →L[ℝ] V} (hη : IsComplexAntilinear J.toLinearMap K.toLinearMap η.toLinearMap)
    (hθ : IsComplexAntilinear J.toLinearMap K.toLinearMap θ.toLinearMap)
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hK : ∀ u v, ⟪K u, K v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hDim : Module.finrank ℝ W = 2) (v : W) (hv : ‖v‖ = 1) :
    hilbertSchmidtInner η θ = 2 * ⟪η v, θ v⟫_ℝ := by
  have hvself : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hjself : ⟪J v, J v⟫_ℝ = 1 := (hJ v v).trans hvself
  have hcross : ⟪v, J v⟫_ℝ = 0 := (real_inner_comm _ _).trans (J.inner_apply_self hJ v)
  have hon : Orthonormal ℝ ![v, J v] := by
    rw [orthonormal_iff_ite]
    intro i k
    fin_cases i <;> fin_cases k
    · exact hvself
    · exact hcross
    · exact (real_inner_comm _ _).trans hcross
    · exact hjself
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank
    (by simpa only [Fintype.card_fin] using hDim.symm)
  let b := OrthonormalBasis.mk hon hspan.ge
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = J v := by simp [b]
  have hηv : η (J v) = -K (η v) := hη.apply v
  have hθv : θ (J v) = -K (θ v) := hθ.apply v
  rw [hilbertSchmidtInner_eq_sum η θ b, Fin.sum_univ_two, hb0, hb1, hηv, hθv,
    inner_neg_neg, hK]
  ring

/-- In real source dimension two, the Hilbert–Schmidt factor two cancels the antilinear
projection's factor one half, giving the full expression `A v + K (A (J v))`. -/
theorem IsComplexAntilinear.hilbertSchmidtInner_complexAntilinearPart_eq_inner_apply
    {η : W →L[ℝ] V} (hη : IsComplexAntilinear J.toLinearMap K.toLinearMap η.toLinearMap)
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hK : ∀ u v, ⟪K u, K v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hDim : Module.finrank ℝ W = 2) (v : W) (hv : ‖v‖ = 1) (A : W →L[ℝ] V) :
    hilbertSchmidtInner η
        (complexAntilinearPart J.toLinearMap K.toLinearMap A.toLinearMap).toContinuousLinearMap =
      ⟪η v, A v + K (A (J v))⟫_ℝ := by
  have hpart := isComplexAntilinear_complexAntilinearPart J.square_neg K.square_neg A.toLinearMap
  rw [hη.hilbertSchmidtInner_eq_two_mul_inner_apply (by
      simpa only [LinearMap.coe_toContinuousLinearMap] using hpart) hJ hK hDim v hv]
  simp only [LinearMap.coe_toContinuousLinearMap', complexAntilinearPart_apply,
    coe_coe, real_inner_smul_right]
  ring

end TauCeti
