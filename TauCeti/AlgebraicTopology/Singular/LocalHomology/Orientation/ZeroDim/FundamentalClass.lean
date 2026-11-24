/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.ZeroDim.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# The signed fundamental class of a zero-dimensional point manifold

The homological orientation constructed from a smooth orientation of a point has fundamental
class equal to its signed actual singular point class. The examples include both orientations of
`Fin 0 → ℝ` and opposite local signs on the disjoint sum of two copies of that native manifold.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set Topology
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {M E : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [Subsingleton M] [ChartedSpace H M] [IsManifold I 1 M]
  [ChartedSpace E M]

open Classical in
/-- On an actual point manifold, the fundamental class of a smooth rank-zero orientation is
its positive or negative singular point class, with the sign of the given tangent orientation. -/
theorem fundamentalClass_toHomologicalOrientationOfZeroDim_of_subsingleton
    (o : Manifold.Orientation I M (Fin 0)) (x : M) :
    o.toHomologicalOrientationOfZeroDim.fundamentalClass
        (o.finrank_eq_zero) =
      if o.orientationAt x = positiveOrientation then
        singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of M) x 1
      else -(singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of M) x 1) := by
  classical
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have hpt : singularHomologyToLocalHomology R x 0
      (singularHomology₀Section R (X := TopCat.of M) x 1) = localHomologyPointClass R {x} x 1 :=
    (singularHomologyToLocalHomology_eq_singularHomologyπ R x _).trans
      (localHomologyPointClass_def_apply R {x} x 1).symm
  symm
  apply HomologicalOrientation.eq_fundamentalClass
  intro y
  have hy : y = x := Subsingleton.elim _ _
  subst y
  rw [toHomologicalOrientationOfZeroDim_apply, localOrientationOfZeroDim_coe]
  dsimp only [R] at hpt
  split_ifs
  · exact hpt
  · exact ((singularHomologyToLocalHomology R x 0).map_neg _).trans
      (congrArg Neg.neg hpt)

end TauCeti.Manifold.Orientation

namespace TauCeti

/-! ### Native point and disconnected checks -/

private abbrev PointModel := Fin 0 → ℝ

private def positivePointOrientation : Manifold.Orientation 𝓘(ℝ, PointModel) PointModel (Fin 0) :=
  Manifold.Orientation.model positiveOrientation (by simp [PointModel])

/-- The positively oriented point gives its actual absolute singular point generator. -/
private theorem point_fundamentalClass_positive :
    positivePointOrientation.toHomologicalOrientationOfZeroDim.fundamentalClass
        (by simp [PointModel]) =
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
        (X := TopCat.of PointModel) (0 : PointModel) 1 := by
  have hp : positivePointOrientation.orientationAt (0 : PointModel) = positiveOrientation :=
    Manifold.Orientation.orientationAt_model (I := 𝓘(ℝ, PointModel))
      positiveOrientation (by simp [PointModel]) 0
  simpa only [hp, ↓reduceIte] using
    Manifold.Orientation.fundamentalClass_toHomologicalOrientationOfZeroDim_of_subsingleton
      positivePointOrientation (0 : PointModel)

/-- Reversing the actual smooth point orientation gives the negative singular point generator. -/
example : (-positivePointOrientation).toHomologicalOrientationOfZeroDim.fundamentalClass
      (by simp [PointModel]) =
    -(singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
      (X := TopCat.of PointModel) (0 : PointModel) 1) := by
  rw [Manifold.Orientation.toHomologicalOrientationOfZeroDim_neg,
    HomologicalOrientation.fundamentalClass_neg]
  exact congrArg Neg.neg point_fundamentalClass_positive

private def mixedVectorOrientation :
    VectorBundleOrientation PointModel (TangentSpace 𝓘(ℝ, PointModel) :
      PointModel ⊕ PointModel → Type) (Fin 0) where
  toFun x := match x with
    | .inl _ => positiveOrientation
    | .inr _ => -positiveOrientation
  eventually_mapOrientation_eq' b := by
    simp [nhds_discrete]

private def mixedOrientation :
    Manifold.Orientation 𝓘(ℝ, PointModel) (PointModel ⊕ PointModel) (Fin 0) :=
  Manifold.Orientation.ofVectorBundleOrientation positiveOrientation (by simp [PointModel])
    mixedVectorOrientation

private theorem orientationAt_mixedOrientation (x : PointModel ⊕ PointModel) :
    mixedOrientation.orientationAt x = mixedVectorOrientation x := by
  rw [mixedOrientation, Manifold.Orientation.orientationAt_ofVectorBundleOrientation]

/-- The native two-point manifold has an actual smooth orientation whose two components give
opposite signed local point generators. -/
example : ∃ o : Manifold.Orientation 𝓘(ℝ, PointModel) (PointModel ⊕ PointModel) (Fin 0),
    (o.toHomologicalOrientationOfZeroDim (.inl 0)).val =
        localHomologyPointClass (M := PointModel ⊕ PointModel)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) {(.inl 0)} (.inl 0) 1 ∧
      (o.toHomologicalOrientationOfZeroDim (.inr 0)).val =
        -(localHomologyPointClass (M := PointModel ⊕ PointModel)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) {(.inr 0)} (.inr 0) 1) := by
  refine ⟨mixedOrientation, ?_, ?_⟩
  · have hp : mixedOrientation.orientationAt (.inl (0 : PointModel)) = positiveOrientation := by
      exact orientationAt_mixedOrientation (.inl 0)
    rw [Manifold.Orientation.toHomologicalOrientationOfZeroDim_apply,
      Manifold.Orientation.localOrientationOfZeroDim_coe]
    simp only [hp, ↓reduceIte]
  · have hp : mixedOrientation.orientationAt (.inr (0 : PointModel)) = -positiveOrientation := by
      exact orientationAt_mixedOrientation (.inr 0)
    rw [Manifold.Orientation.toHomologicalOrientationOfZeroDim_apply,
      Manifold.Orientation.localOrientationOfZeroDim_coe]
    have hn : -(positiveOrientation :
        _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, PointModel)
          (Sum.inr (0 : PointModel) : PointModel ⊕ PointModel)) (Fin 0)) ≠
        positiveOrientation := (Module.Ray.ne_neg_self _).symm
    simp only [hp, hn, ↓reduceIte]

end TauCeti
