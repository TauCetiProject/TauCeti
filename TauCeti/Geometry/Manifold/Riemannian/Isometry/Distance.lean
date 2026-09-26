/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Riemannian isometries preserve distance

A smooth Riemannian isometry preserves the length of each curve. Applying this fact to curves
in both directions shows that it preserves the infimum of their lengths, even when that infimum
is infinite because the points lie in different components. When the ambient extended distances
are the Riemannian distances, the smooth isometry is also an isometry of extended metric spaces.

The geometric fact is the invariance of Riemannian distance under isometries; see J. M. Lee,
*Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

private theorem riemannianEDist_apply_le (Φ : RiemannianIsometry I J M N) (x y : M) :
    Manifold.riemannianEDist J (Φ x) (Φ y) ≤ Manifold.riemannianEDist I x y := by
  apply Manifold.le_riemannianEDist_of_forall_le_pathELength
  intro γ h0 h1 hγ
  have hγ' : CMDiff[Set.Icc 0 1] 1 (Φ ∘ γ) :=
    (Φ.toDiffeomorph.contMDiff.of_le (by simp)).comp_contMDiffOn hγ
  have h := Manifold.riemannianEDist_le_pathELength (x := Φ x) (y := Φ y) hγ'
    (by simp only [Function.comp_apply, h0])
    (by simp only [Function.comp_apply, h1])
    (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [Φ.pathELength_comp] using h

/-- A smooth Riemannian isometry preserves Riemannian extended distance, including between
points in distinct connected components. -/
@[simp]
theorem riemannianEDist_apply (Φ : RiemannianIsometry I J M N) (x y : M) :
    Manifold.riemannianEDist J (Φ x) (Φ y) = Manifold.riemannianEDist I x y := by
  apply le_antisymm (riemannianEDist_apply_le Φ x y)
  simpa using riemannianEDist_apply_le Φ.symm (Φ x) (Φ y)

end Intrinsic

section Ambient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [hM : IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [PseudoEMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [hN : IsRiemannianManifold J N]

/-- A smooth Riemannian isometry preserves the ambient extended distance when each ambient
distance agrees with its Riemannian distance. -/
@[simp]
theorem edist_apply (Φ : RiemannianIsometry I J M N) (x y : M) :
    edist (Φ x) (Φ y) = edist x y := by
  rw [IsRiemannianManifold.out (I := J), IsRiemannianManifold.out (I := I),
    Φ.riemannianEDist_apply]

/-- A smooth Riemannian isometry between spaces equipped with their Riemannian extended distances
is an isometry equivalence. -/
def toIsometryEquiv (Φ : RiemannianIsometry I J M N) : M ≃ᵢ N where
  toEquiv := Φ.toDiffeomorph.toEquiv
  isometry_toFun := fun x y ↦ Φ.edist_apply x y

include hM hN in
@[simp]
theorem toIsometryEquiv_apply (Φ : RiemannianIsometry I J M N) (x : M) :
    Φ.toIsometryEquiv x = Φ x := by rfl

end Ambient

end TauCeti.RiemannianIsometry

end
