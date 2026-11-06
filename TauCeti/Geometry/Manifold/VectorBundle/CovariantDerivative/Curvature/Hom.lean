/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Curvature of the induced Hom connection

The curvature of the connection on `Hom(V, W)` induced by connections on `V` and `W` is
`Rᴴ(X,Y) A = Rᵂ(X,Y) ∘ A - A ∘ Rⱽ(X,Y)`. In particular, the induced endomorphism
connection acts by the commutator with curvature. This is the curvature action used in
exterior covariant differentiation of endomorphism-valued forms.

We prove the identity both on smooth sections and on arbitrary fibre vectors, using the
evaluation rule `CovariantDerivative.hom_apply` and the existing pointwise curvature tensor.
No metric or torsion assumption is needed.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4 and 7
  (induced connections and their curvature).
-/

public noncomputable section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)
  [ContMDiffCovariantDerivative covV ∞] [ContMDiffCovariantDerivative covW ∞]
  {A : Π x : M, V x →L[ℝ] W x} {σ : Π x : M, V x}
  {X Y : Π x : M, TangentSpace I x}

omit [FiniteDimensional ℝ G] in
/-- Expand two successive Hom derivatives after evaluation on a smooth section. -/
private theorem hom_covariantDerivative_apply
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x (A x)))
    (hσ : CMDiff ∞ (T% σ)) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (x : M) :
    covV.hom covW (fun y ↦ covV.hom covW A y (Y y)) x (X x) (σ x) =
      covW (fun y ↦ covW (fun z ↦ A z (σ z)) y (Y y)) x (X x) -
        covW (fun y ↦ A y (covV σ y (Y y))) x (X x) -
        covW (fun y ↦ A y (covV σ y (X y))) x (Y x) +
        A x (covV (fun y ↦ covV σ y (X y)) x (Y x)) := by
  have hYσ := covV.contMDiff_apply hY hσ
  have hXσ := covV.contMDiff_apply hX hσ
  have hAs := hA.clm_bundle_apply hσ
  have hYA := (covV.hom covW).contMDiff_apply hY hA
  have heval : (fun y ↦ covV.hom covW A y (Y y) (σ y)) =
      (fun y ↦ covW (fun z ↦ A z (σ z)) y (Y y)) -
        fun y ↦ A y (covV σ y (Y y)) := by
    funext y
    exact hom_apply covV covW (hA.mdifferentiableAt (by simp))
      (hσ.mdifferentiableAt (by simp)) (Y y)
  rw [hom_apply covV covW (hYA.mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp)), heval,
    covW.isCovariantDerivativeOnUniv.sub
      ((covW.contMDiff_apply hY hAs).mdifferentiableAt (by simp))
      ((hA.clm_bundle_apply hYσ).mdifferentiableAt (by simp)),
    hom_apply covV covW (hA.mdifferentiableAt (by simp))
      (hXσ.mdifferentiableAt (by simp))]
  simp only [sub_apply]
  abel

omit [FiniteDimensional ℝ G] in
/-- Curvature of the induced Hom connection, evaluated on smooth sections:
`(Rᴴ(X,Y) A) σ = Rᵂ(X,Y)(A σ) - A(Rⱽ(X,Y) σ)`.
For the endomorphism connection this is the commutator with curvature. -/
theorem curvatureOperator_hom_apply
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x (A x)))
    (hσ : CMDiff ∞ (T% σ)) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (x : M) :
    curvatureOperator (covV.hom covW) X Y A x (σ x) =
      curvatureOperator covW X Y (fun y ↦ A y (σ y)) x -
        A x (curvatureOperator covV X Y σ x) := by
  rw [curvatureOperator_apply, sub_apply, sub_apply,
    hom_covariantDerivative_apply covV covW hA hσ hX hY,
    hom_covariantDerivative_apply covV covW hA hσ hY hX,
    hom_apply covV covW (hA.mdifferentiableAt (by simp))
      (hσ.mdifferentiableAt (by simp)),
    curvatureOperator_apply, curvatureOperator_apply]
  simp only [map_sub]
  abel

/-- The pointwise curvature tensor of the induced Hom connection acts by the difference
of the target and source curvature actions. The homomorphism and all three vectors are
arbitrary fibre elements, with no choice of section in the statement. -/
@[simp]
theorem curvatureTensor_hom_apply (x : M) (u v : TangentSpace I x)
    (B : V x →L[ℝ] W x) (w : V x) :
    (covV.hom covW).curvatureTensor x u v B w =
      covW.curvatureTensor x u v (B w) - B (covV.curvatureTensor x u v w) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨A, hA, rfl⟩ :=
    exists_contMDiff_section_eq (V := fun y ↦ V y →L[ℝ] W y) I (F →L[ℝ] G) ∞ B
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F ∞ w
  rw [curvatureTensor_apply _ x hX hY hA,
    curvatureTensor_apply _ x hX hY (hA.clm_bundle_apply hσ),
    curvatureTensor_apply _ x hX hY hσ]
  exact curvatureOperator_hom_apply covV covW hA hσ hX hY x

end CovariantDerivative
