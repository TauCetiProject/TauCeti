/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# The Ricci identities for the third covariant derivative

Let `∇` be a smooth connection on a vector bundle `V` and `∇ᵀ` a smooth torsion-free connection
on the tangent bundle. For a smooth section `σ` of `V`, the third covariant derivative is
`∇³σ(u, w, z) = (∇_u ∇²σ)(w, z)`, the covariant derivative of the section `∇²σ` of
`Hom(TM, Hom(TM, V))`. By `CovariantDerivative.secondCovariantDerivative_covariantDerivative` it is
also the second covariant derivative of the section `∇σ` of `Hom(TM, V)`. This file proves the two
Ricci identities that permute its slots:

* `covariantDerivative_secondCovariantDerivative_sub_swap_left_of_isTorsionFree`:
  `∇³σ(u, w, z) - ∇³σ(w, u, z) = R(u, w) ∇_z σ - ∇_{Rᵀ(u, w) z} σ`, the Ricci identity for the
  section `∇σ` of `Hom(TM, V)`, whose curvature is computed from `R` and `Rᵀ`;
* `covariantDerivative_secondCovariantDerivative_sub_swap_right_of_isTorsionFree`:
  `∇³σ(u, w, z) - ∇³σ(u, z, w) = (∇_u R)(w, z) σ + R(w, z) ∇_u σ`, the covariant derivative of the
  Ricci identity `∇²σ(w, z) - ∇²σ(z, w) = R(w, z) σ`.

Here `R` and `Rᵀ` are the curvatures of `∇` and `∇ᵀ`, and `∇R` is
`CovariantDerivative.derivCurvatureTensor`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the Ricci identities).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  {covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)}
  [ContMDiffCovariantDerivative covT ∞]
  {σ : Π y : M, V y}

omit [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
/-- The covariant derivative `∇σ` of a smooth section is a smooth section of `Hom(TM, V)`. -/
private theorem contMDiff_covariantDerivative_section (hσ : CMDiff ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun x : M ↦ TangentSpace I x →L[ℝ] V x) x
        (cov σ x)) :=
  contMDiffOn_univ.mp ((ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := ∞)).contMDiff
    (by simpa using hσ.contMDiffOn))

/-- The second covariant derivative `∇²σ` of a smooth section, read as the covariant derivative of
`∇σ`, is a smooth section of `Hom(TM, Hom(TM, V))`. -/
theorem contMDiff_hom_covariantDerivative (hσ : CMDiff ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) x
        (covT.hom cov (cov σ) x)) :=
  contMDiff_hom covT cov (contMDiff_covariantDerivative_section cov hσ)

variable [FiniteDimensional ℝ F]

/-- **The Ricci identity in the first two slots of the third covariant derivative.** For a
torsion-free connection `∇ᵀ`,
`∇³σ(u, w, z) - ∇³σ(w, u, z) = R(u, w) ∇_z σ - ∇_{Rᵀ(u, w) z} σ`, where `R` and `Rᵀ` are the
curvatures of `∇` and `∇ᵀ`: this is the Ricci identity for the section `∇σ` of `Hom(TM, V)`. -/
theorem covariantDerivative_secondCovariantDerivative_sub_swap_left_of_isTorsionFree
    (ht : covT.IsTorsionFree) (hσ : CMDiff ∞ (T% σ)) (x : M) (u w z : TangentSpace I x) :
    covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x u w z -
        covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x w u z =
      cov.curvatureTensor x u w (cov σ x z) - cov σ x (covT.curvatureTensor x u w z) := by
  have h := (covT.hom cov).secondCovariantDerivative_sub_swap_of_isTorsionFree covT ht
    (contMDiff_covariantDerivative_section cov hσ) x u w
  rw [secondCovariantDerivative_covariantDerivative cov hσ,
    secondCovariantDerivative_covariantDerivative cov hσ] at h
  simpa only [sub_apply, curvatureTensor_hom_apply] using
    congrArg (fun B : TangentSpace I x →L[ℝ] V x ↦ B z) h

omit [ContMDiffCovariantDerivative covT ∞] in
/-- The Ricci identity for the second covariant derivative, read on the section `∇²σ` of
`Hom(TM, Hom(TM, V))`: `∇²σ(w, z) - ∇²σ(z, w) = R(w, z) σ`. -/
private theorem hom_covariantDerivative_sub_swap (ht : covT.IsTorsionFree)
    (hσ : CMDiff ∞ (T% σ)) (y : M) (w z : TangentSpace I y) :
    covT.hom cov (cov σ) y w z - covT.hom cov (cov σ) y z w = cov.curvatureTensor y w z (σ y) := by
  rw [← secondCovariantDerivative_eq_hom_apply cov covT hσ,
    ← secondCovariantDerivative_eq_hom_apply cov covT hσ,
    cov.secondCovariantDerivative_sub_swap_of_isTorsionFree covT ht hσ]

/-- **The Ricci identity in the last two slots of the third covariant derivative.** For a
torsion-free connection `∇ᵀ`,
`∇³σ(u, w, z) - ∇³σ(u, z, w) = (∇_u R)(w, z) σ + R(w, z) ∇_u σ`, where `∇R` is the covariant
derivative of the curvature `R` of `∇` (`CovariantDerivative.derivCurvatureTensor`): this is the
covariant derivative of the Ricci identity `∇²σ(w, z) - ∇²σ(z, w) = R(w, z) σ`. -/
theorem covariantDerivative_secondCovariantDerivative_sub_swap_right_of_isTorsionFree
    (ht : covT.IsTorsionFree) (hσ : CMDiff ∞ (T% σ)) (x : M) (u w z : TangentSpace I x) :
    covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x u w z -
        covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x u z w =
      cov.derivCurvatureTensor covT x u w z (σ x) + cov.curvatureTensor x w z (cov σ x u) := by
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E ∞ z
  have hWx : MDiffAt (T% W) x := hW.mdifferentiable (by simp) x
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiable (by simp) x
  have hD2x :=
    (contMDiff_hom_covariantDerivative cov (covT := covT) hσ).mdifferentiableAt (x := x) (by simp)
  -- Expand both sides by the Leibniz rule for the iterated Hom connection.
  rw [hom_hom_apply covT covT cov hD2x hWx hZx, hom_hom_apply covT covT cov hD2x hZx hWx,
    cov.derivCurvatureTensor_apply covT x u hW hZ hσ]
  -- Differentiate the Ricci identity for `σ` along `u`.
  have hWZ : MDiffAt (T% fun y ↦ covT.hom cov (cov σ) y (W y) (Z y)) x :=
    (hD2x.clm_bundle_apply hWx).clm_bundle_apply hZx
  have hZW : MDiffAt (T% fun y ↦ covT.hom cov (cov σ) y (Z y) (W y)) x :=
    (hD2x.clm_bundle_apply hZx).clm_bundle_apply hWx
  have hdiff : cov (fun y ↦ covT.hom cov (cov σ) y (W y) (Z y)) x u -
      cov (fun y ↦ covT.hom cov (cov σ) y (Z y) (W y)) x u =
        cov (curvatureOperator cov W Z σ) x u := by
    rw [← sub_apply, ← cov.isCovariantDerivativeOnUniv.sub hWZ hZW]
    congr 2
    funext y
    rw [Pi.sub_apply, hom_covariantDerivative_sub_swap cov ht hσ y (W y) (Z y),
      curvatureTensor_apply cov y hW hZ hσ]
  have h₁ := hom_covariantDerivative_sub_swap cov ht hσ x (covT W x u) (Z x)
  have h₂ := hom_covariantDerivative_sub_swap cov ht hσ x (W x) (covT Z x u)
  rw [← hdiff, ← h₁, ← h₂]
  abel

end CovariantDerivative
