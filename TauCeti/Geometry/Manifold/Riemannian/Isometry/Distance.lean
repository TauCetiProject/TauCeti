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
theorem riemannianEDist_eq (Φ : RiemannianIsometry I J M N) (x y : M) :
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

/-- A smooth Riemannian isometry between spaces equipped with their Riemannian extended distances
is an isometry of extended metric spaces; in particular it coerces to `M ≃ᵢ N`. -/
instance : IsometryClass (RiemannianIsometry I J M N) M N where
  isometry Φ := by
    intro x y
    rw [IsRiemannianManifold.out (I := J), IsRiemannianManifold.out (I := I),
      Φ.riemannianEDist_eq]

/-- The metric equivalence of the inverse is the inverse metric equivalence. -/
@[simp]
theorem toIsometryEquiv_symm (Φ : RiemannianIsometry I J M N) :
    ((Φ.symm : RiemannianIsometry J I N M) : N ≃ᵢ M) = (Φ : M ≃ᵢ N).symm := by
  ext x
  apply (Φ : M ≃ᵢ N).injective
  simp

/-- The identity Riemannian isometry induces the identity metric equivalence. -/
@[simp]
theorem toIsometryEquiv_refl :
    ((RiemannianIsometry.refl I M : RiemannianIsometry I I M M) : M ≃ᵢ M) =
      IsometryEquiv.refl M := by
  ext x
  rw [IsometryClass.coe_coe, RiemannianIsometry.refl_apply]
  simp only [IsometryEquiv.coe_eq_toEquiv, IsometryEquiv.refl, Equiv.refl_apply]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [PseudoEMetricSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)] [hP : IsRiemannianManifold K P]

/-- The metric equivalence of a composite is the composite metric equivalence. -/
@[simp]
theorem toIsometryEquiv_trans (Φ : RiemannianIsometry I J M N)
    (Ψ : RiemannianIsometry J K N P) :
    ((Φ.trans Ψ : RiemannianIsometry I K M P) : M ≃ᵢ P) =
      (Φ : M ≃ᵢ N).trans (Ψ : N ≃ᵢ P) := by
  ext x
  simp

end Ambient

end TauCeti.RiemannianIsometry

end
