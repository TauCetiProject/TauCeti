/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorField.Pullback

-- Access the constructor only to supply its missing public characterization.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Differentials of diffeomorphisms

The differentials of a diffeomorphism and its inverse undo each other, and the differential of a
diffeomorphism undoes the pullback of vector fields along it.
Differentiability at a point is also preserved by precomposition and postcomposition with a
diffeomorphism, and
the tangent images of a map, the ranges of its differentials, are unchanged by precomposition
with a diffeomorphism and are mapped by the differential under postcomposition.
These facts support inverse isometries and transport of curve differentiability through
diffeomorphisms. The underlying equivalence of a diffeomorphism viewed as a partial
diffeomorphism is also characterized, for composition with partial coordinates.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- The partial equivalence underlying a diffeomorphism viewed as a partial diffeomorphism
is its everywhere-defined equivalence. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv (h : M ≃ₘ^n⟮I, J⟯ N) :
    h.toPartialDiffeomorph.toPartialEquiv = h.toEquiv.toPartialEquiv := (rfl)

/-- The differentials of a diffeomorphism and its inverse compose to the identity. -/
@[simp]
theorem mfderiv_apply_mfderiv_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (x : M) (v : TangentSpace J (h x)) :
    mfderiv I J h x (mfderiv J I h.symm (h x) v) = v := by
  have hid : (h : M → N) ∘ h.symm = id := funext h.apply_symm_apply
  have hder : mfderiv J J ((h : M → N) ∘ h.symm) (h x) v =
      mfderiv I J h (h.symm (h x)) (mfderiv J I h.symm (h x) v) :=
    mfderiv_comp_apply (h x) (h.mdifferentiable hn (h.symm (h x)))
      (h.symm.mdifferentiable hn (h x)) v
  rw [hid, mfderiv_id, h.symm_apply_apply] at hder
  exact hder.symm

/-- The differential of the inverse undoes the differential of a diffeomorphism. -/
@[simp]
theorem mfderiv_symm_apply_mfderiv_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (x : M) (v : TangentSpace I x) :
    mfderiv J I h.symm (h x) (mfderiv I J h x v) = v := by
  have hss : h.symm.symm = h := Diffeomorph.ext (fun _ => rfl)
  have hh := mfderiv_apply_mfderiv_symm_apply h.symm hn (h x) v
  rw [hss, h.symm_apply_apply] at hh
  exact hh

/-- The differential of a diffeomorphism maps the pullback of a vector field at `x` to the value
of the field at `h x`. -/
@[simp]
theorem mfderiv_apply_mpullback (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (V : Π y : N, TangentSpace J y)
    (x : M) : mfderiv I J h x (VectorField.mpullback I J h V x) = V (h x) :=
  (h.isInvertible_mfderiv hn).self_apply_inverse _

/-- Applying the tangent map of a diffeomorphism and then that of its inverse returns the
original tangent vector. -/
@[simp]
theorem tangentMap_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (z : TangentBundle I M) :
    tangentMap J I h.symm (tangentMap I J h z) = z := by
  rw [← tangentMap_comp_at z ((h.symm.mdifferentiable hn) (h z.1))
    ((h.mdifferentiable hn) z.1)]
  have hinv : (h.symm : N → M) ∘ h = id := funext h.symm_apply_apply
  rw [hinv]
  exact congrFun tangentMap_id z

/-- Applying the tangent map of the inverse of a diffeomorphism and then that of the
diffeomorphism returns the original tangent vector. -/
@[simp]
theorem tangentMap_apply_symm (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (z : TangentBundle J N) :
    tangentMap I J h (tangentMap J I h.symm z) = z := by
  have hss : h.symm.symm = h := Diffeomorph.ext fun _ ↦ rfl
  have hh := tangentMap_symm_apply h.symm hn z
  rw [hss] at hh
  exact hh

/-- Postcomposition with a diffeomorphism preserves differentiability at a point. -/
theorem mdifferentiableAt_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E' H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {f : P → M} {x : P} :
    MDifferentiableAt K J (h ∘ f) x ↔ MDifferentiableAt K I f x := by
  constructor
  · intro hf
    have hg := (h.symm.mdifferentiable hn (h (f x))).comp x hf
    have heq : (h.symm : N → M) ∘ ((h : M → N) ∘ f) = f := by
      funext y
      exact h.symm_apply_apply (f y)
    rw [heq] at hg
    exact hg
  · intro hf
    exact (h.mdifferentiable hn (f x)).comp x hf

/-- Precomposition with a diffeomorphism preserves differentiability at the corresponding point. -/
theorem mdifferentiableAt_comp_diffeomorph_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E' H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {f : N → P} {x : M} :
    MDifferentiableAt I K (f ∘ h) x ↔ MDifferentiableAt J K f (h x) := by
  constructor
  · intro hfh
    have hfh' : MDifferentiableAt I K (f ∘ h) (h.symm (h x)) := by
      rwa [h.symm_apply_apply]
    have hg := hfh'.comp (h x) (h.symm.mdifferentiable hn (h x))
    have heq : (f ∘ h) ∘ h.symm = f := funext fun y ↦ congrArg f (h.apply_symm_apply y)
    rwa [heq] at hg
  · intro hf
    exact hf.comp x (h.mdifferentiable hn x)

section TangentImage

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Postcomposition with a diffeomorphism maps tangent images by its differential: the range of
the differential of `h ∘ f` at `x` is the image of the range of the differential of `f` under the
linear equivalence `dh`, `Diffeomorph.mfderivToContinuousLinearEquiv`.
No differentiability of `f` is assumed: when `f` is not differentiable at `x`, neither is `h ∘ f`,
and both ranges are zero. -/
theorem range_mfderiv_diffeomorph_comp (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (x : P) :
    LinearMap.range (mfderiv K J (h ∘ f) x).toLinearMap =
      (LinearMap.range (mfderiv K I f x).toLinearMap).map
        (h.mfderivToContinuousLinearEquiv hn (f x)).toLinearEquiv.toLinearMap := by
  by_cases hf : MDifferentiableAt K I f x
  · have hder : (h.mfderivToContinuousLinearEquiv hn (f x)).toLinearEquiv.toLinearMap =
        (mfderiv I J h (f x)).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap
        (h.mfderivToContinuousLinearEquiv_coe hn (x := f x))
    rw [mfderiv_comp x (h.mdifferentiable hn (f x)) hf, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp, hder]
  · have hhf : ¬MDifferentiableAt K J (h ∘ f) x := (h.mdifferentiableAt_comp_iff hn).not.mpr hf
    simp only [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hhf,
      ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, Submodule.map_bot]

/-- Precomposition with a diffeomorphism does not change tangent images: the range of the
differential of `f ∘ h` at `x` is the range of the differential of `f` at `h x`. No
differentiability of `f` is assumed. -/
theorem range_mfderiv_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : N → P) (x : M) :
    LinearMap.range (mfderiv I K (f ∘ h) x).toLinearMap =
      LinearMap.range (mfderiv J K f (h x)).toLinearMap := by
  by_cases hf : MDifferentiableAt J K f (h x)
  · rw [mfderiv_comp x hf (h.mdifferentiable hn x), ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr (h.isInvertible_mfderiv hn).surjective
  · have hfh : ¬MDifferentiableAt I K (f ∘ h) x :=
      (h.mdifferentiableAt_comp_diffeomorph_iff hn).not.mpr hf
    simp only [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hfh,
      ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]

end TangentImage

end Diffeomorph

end
