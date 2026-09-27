/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Differentials of diffeomorphisms

The differentials of a diffeomorphism and its inverse undo each other.
Differentiability at a point is also preserved by postcomposition with a diffeomorphism.
These facts support inverse isometries and transport of curve differentiability through
diffeomorphisms.
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

end Diffeomorph

end
