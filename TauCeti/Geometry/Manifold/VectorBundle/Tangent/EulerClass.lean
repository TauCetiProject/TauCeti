/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Manifold
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Manifold.Morse.PoincareHopf
public import TauCeti.Geometry.Manifold.VectorBundle.Section.EulerNumber
public import TauCeti.Geometry.Manifold.VectorField.Chart.Linearization
import TauCeti.Geometry.Manifold.Morse.Generic.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# The Euler number of the tangent bundle is the Euler characteristic

Let `M` be a compact boundaryless smooth manifold of dimension `n + 1`, modelled on a real inner
product space `X`, with a smooth orientation `oM`. Its tangent bundle carries the induced
orientation (`TauCeti.Manifold.Orientation.toVectorBundleOrientation`), hence an Euler class
`e(TM) ∈ Hⁿ⁺¹(M; ℤ)`, and `oM` determines a fundamental class `[M]`. This file proves
`e(TM)[M] = χ(M)` (`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`),
where `χ(M)` is the finite-CW Euler characteristic `TauCeti.eulerChar M` for the finite CW type
of `TauCeti.FiniteCWType.of_isManifold`.

The proof evaluates the Euler class on the gradient of a Morse function.

* A vector field `V` read as a section of `TM` has linearization `T_p M → T_p M`
  (`TauCeti.sectionLinearization`) equal to its chart derivative
  (`TauCeti.vectorFieldChartDerivative`), the derivative of its coordinate field in the chart at
  `p` (`TauCeti.sectionLinearization_eq_vectorFieldChartDerivative`).
* So at a zero `p` with invertible linearization the local index of `V`, the orientation sign of
  its linearization
  (`TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_ite`), is the sign of
  the determinant of the chart derivative, since source and target carry the same orientation
  (`TauCeti.Manifold.Orientation.sectionIndex_eq_sign_det_vectorFieldChartDerivative`). In
  particular it does not depend on `oM`.
* For a `C¹` metric (`TauCeti.nonempty_contMDiffRiemannianMetric`) and a Morse function
  (`TauCeti.exists_isMorse`), the zeros of the gradient are the finitely many critical points, each
  nondegenerate, and the sum of the signs of the determinants is the alternating sum of the
  rational Betti numbers (`TauCeti.IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient`),
  which is `eulerChar M` (`TauCeti.eulerChar_eq_sum_range_finrank_singularHomology`).

Combined with the sum-of-local-indices formula
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`) this is the
Poincaré–Hopf theorem for the gradient of a Morse function, stated for the Euler class.

## Main results

* `TauCeti.Manifold.Orientation.sectionIndex_eq_sign_det_vectorFieldChartDerivative`: at a
  nondegenerate zero of a vector field the local index is the sign of the determinant of its chart
  derivative.
* `TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`: `e(TM)[M] = χ(M)`.

## Implementation notes

The statements need positive dimension `n + 1`, as do the homological orientation of a smooth
orientation and the local index of a section. The proof goes through a Morse function, so it
covers smooth manifolds; it does not identify the Euler class with the self-intersection of the
diagonal.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6 (the Poincaré–Hopf theorem and the index of a gradient field).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Corollary 11.12 (the Euler number of the tangent bundle).
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff

namespace TauCeti

namespace Manifold.Orientation

variable {X M : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [TopologicalSpace M] [ChartedSpace X M] [T2Space M] {n : ℕ}
  (hX : finrank ℝ X = n + 1) (oM : Manifold.Orientation 𝓘(ℝ, X) M (Fin (n + 1)))

section Index

variable [IsManifold 𝓘(ℝ, X) 1 M]

/-- **The local index of a vector field at a nondegenerate zero.** Let `V` be a vector field on a
boundaryless manifold of dimension `n + 1` oriented by `oM`, and `z` a zero of `V` at which the
chart derivative of `V` has nonzero determinant (so `V` is differentiable at `z`). Then the local
index of `V`, as a section of the tangent bundle oriented by `oM`, with respect to the homological
orientation of `oM`, is the sign of that determinant. -/
theorem sectionIndex_eq_sign_det_vectorFieldChartDerivative {V : (x : M) → TangentSpace 𝓘(ℝ, X) x}
    (hV : Continuous fun x ↦ TotalSpace.mk' X x (V x)) {z : M} (hz : V z = 0)
    (hdet : LinearMap.det (vectorFieldChartDerivative 𝓘(ℝ, X) V z) ≠ 0) :
    oM.toVectorBundleOrientation.sectionIndex hX (oM.toHomologicalOrientation hX) hV z =
      SignType.sign (LinearMap.det (vectorFieldChartDerivative 𝓘(ℝ, X) V z)) := by
  classical
  have hVd := mdifferentiableAt_of_det_vectorFieldChartDerivative_ne_zero hdet
  have hL := sectionLinearization_apply_eq_vectorFieldChartDerivative (I := 𝓘(ℝ, X)) V z
  -- The chart derivative has nonzero determinant, so it is surjective, and so is the
  -- linearization.
  have hsurj : Function.Surjective (vectorFieldChartDerivative 𝓘(ℝ, X) V z) :=
    ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 hdet))).2
  have hreg : Function.Surjective (sectionLinearization (F := X) 𝓘(ℝ, X) id V z) := fun w ↦ by
    obtain ⟨v, hv⟩ := hsurj w
    exact ⟨v, (hL v).trans hv⟩
  rw [VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_ite hX
    oM.toVectorBundleOrientation hX oM hV hz hVd hreg]
  -- Source and target of the linearization carry the same orientation, so it preserves
  -- orientation exactly when its determinant is positive.
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ (TangentSpace 𝓘(ℝ, X) z) := by
    rw [Fintype.card_fin]
    exact hX.symm
  have hdetD (D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] TangentSpace 𝓘(ℝ, X) z)
      (hD : (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] TangentSpace 𝓘(ℝ, X) z) =
        sectionLinearization (F := X) 𝓘(ℝ, X) id V z) :
      (oM.orientationAt z).map _ D.toLinearEquiv = oM.toVectorBundleOrientation z ↔
        0 < LinearMap.det (vectorFieldChartDerivative 𝓘(ℝ, X) V z) := by
    have hDL : (D.toLinearEquiv : TangentSpace 𝓘(ℝ, X) z →ₗ[ℝ] TangentSpace 𝓘(ℝ, X) z) =
        vectorFieldChartDerivative 𝓘(ℝ, X) V z := by
      ext v
      rw [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ← ContinuousLinearEquiv.coe_coe, hD]
      exact hL v
    rw [toVectorBundleOrientation_apply, Orientation.map_eq_iff_det_pos _ _ hcard, hDL]
    -- Both sides are the same determinant, of `vectorFieldChartDerivative` on the model space,
    -- read once on `TangentSpace 𝓘(ℝ, X) z` and once on `X`, which is its definition.
    exact Iff.rfl
  have hiff : (∃ D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] TangentSpace 𝓘(ℝ, X) z,
      (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] TangentSpace 𝓘(ℝ, X) z) =
          sectionLinearization (F := X) 𝓘(ℝ, X) id V z ∧
        (oM.orientationAt z).map _ D.toLinearEquiv = oM.toVectorBundleOrientation z) ↔
      0 < LinearMap.det (vectorFieldChartDerivative 𝓘(ℝ, X) V z) := by
    constructor
    · rintro ⟨D, hD, ho⟩
      exact (hdetD D hD).1 ho
    · intro hpos
      obtain ⟨D, hD⟩ := exists_continuousLinearEquiv_eq_sectionLinearization_of_surjective
        (E := TangentSpace 𝓘(ℝ, X)) (rfl : finrank ℝ X = finrank ℝ X) hreg
      exact ⟨D, hD, (hdetD D hD).2 hpos⟩
  rw [if_congr hiff rfl rfl]
  rcases hdet.lt_or_gt with h | h
  · rw [ite_eq_right_iff.2 fun h' ↦ absurd h' h.not_gt, sign_neg h, SignType.coe_neg_one]
  · rw [ite_eq_left_iff.2 fun h' ↦ absurd h h', sign_pos h, SignType.coe_one]

end Index

variable [CompactSpace M] [IsManifold 𝓘(ℝ, X) ∞ M]

/-- **The Euler number of the tangent bundle is the Euler characteristic.** Let `M` be a compact
boundaryless smooth manifold of dimension `n + 1` with a smooth orientation `oM`. The Euler class of
its tangent bundle, oriented by `oM`, evaluated on the fundamental class of `oM`, is the finite-CW
Euler characteristic of `M`: `e(TM)[M] = χ(M)`. -/
theorem evalFundamentalClass_eulerClass_eq_eulerChar :
    haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, X)) M
    ((oM.toHomologicalOrientation hX).evalFundamentalClass hX (ModuleCat.of ℤ (ULift.{0} ℤ))
        (ContinuousMap.id M) (oM.toVectorBundleOrientation.eulerClass hX)).down = eulerChar M := by
  have := FiniteCWType.of_isManifold (I := 𝓘(ℝ, X)) M
  classical
  -- A `C¹` metric and a Morse function `f`; the section is the gradient of `f`.
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := 𝓘(ℝ, X)) (n := 1) (F := X)
    (E := TangentSpace 𝓘(ℝ, X) (M := M))
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, X) x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨f, hf⟩ := exists_isMorse (I := 𝓘(ℝ, X)) (M := M)
  have hf2 : ContMDiff 𝓘(ℝ, X) 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_num)
  set V := Manifold.mgradient 𝓘(ℝ, X) f
  have hVd : ∀ z, MDifferentiableAt 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, X))
      (fun x ↦ TotalSpace.mk' X x (V x)) z := Manifold.mdifferentiable_mgradient hf2
  have hV : Continuous fun x ↦ TotalSpace.mk' X x (V x) :=
    continuous_iff_continuousAt.2 fun z ↦ (hVd z).continuousAt
  -- The zeros of the gradient are the finitely many critical points.
  have hmem (x : M) : x ∈ hf.finite_criticalPoints.toFinset ↔ V x = 0 := by
    rw [Set.Finite.mem_toFinset, mem_criticalPoints, Manifold.mgradient_eq_zero_iff]
  have hZ : {x | V x = 0}.Finite := hf.finite_criticalPoints.subset fun x hx ↦
    (Set.Finite.mem_toFinset _).1 ((hmem x).2 hx)
  rw [VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex
    oM.toVectorBundleOrientation hX (oM.toHomologicalOrientation hX) hV hX hZ,
    eulerChar_eq_sum_range_finrank_singularHomology (E := X) M ℚ,
    ← hf.finsum_sign_det_vectorFieldChartDerivative_mgradient ℚ]
  let : Fintype {x // V x = 0} := hZ.fintype
  rw [finsum_eq_sum_of_fintype, Finset.sum_subtype hZ.toFinset (fun x ↦ hZ.mem_toFinset)
    (fun x ↦ oM.toVectorBundleOrientation.sectionIndex hX (oM.toHomologicalOrientation hX) hV x)]
  refine Fintype.sum_congr _ _ fun ⟨z, hz⟩ ↦ ?_
  exact sectionIndex_eq_sign_det_vectorFieldChartDerivative hX oM hV hz
    (hf.det_vectorFieldChartDerivative_mgradient_ne_zero hz)

end Manifold.Orientation

end TauCeti
