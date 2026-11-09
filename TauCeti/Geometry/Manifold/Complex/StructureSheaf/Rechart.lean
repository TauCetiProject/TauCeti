/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic

/-!
# Holomorphic stalks under biholomorphisms

A biholomorphism induces a ring equivalence on holomorphic stalks by pullback. This allows
local equations and their ideal-theoretic properties to be transported between coordinates.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace Diffeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℂ F G}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace G Y]

private theorem stalkPrecomp_symm_rightInverse (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X) :
    Function.RightInverse
      (fun s ↦ stalkPrecomp J Y e.symm e.symm.contMDiff (e x)
        ((e.symm_apply_apply x).symm ▸ s))
      (stalkPrecomp I X e e.contMDiff x) := by
  intro s
  rw [← stalkPrecomp_comp]
  -- Transport the source germ along the equality of the composite with the identity.
  have transport (f : X → X) (hf : ContMDiff I I ω f) (h : f = id) :
      stalkPrecomp I X f hf x ((congrFun h x).symm ▸ s) = s := by
    subst f
    exact RingHom.congr_fun (stalkPrecomp_id I X x) s
  exact transport _ _ (funext e.symm_apply_apply)

/-- Pullback by a biholomorphism is bijective on the holomorphic stalks. -/
theorem stalkPrecomp_bijective (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X) :
    Function.Bijective (stalkPrecomp I X e e.contMDiff x) := by
  have left : Function.LeftInverse
      (fun s ↦ stalkPrecomp J Y e.symm e.symm.contMDiff (e x)
        ((e.symm_apply_apply x).symm ▸ s))
      (stalkPrecomp I X e e.contMDiff x) := by
    intro s
    -- Read the opposite inverse identity with the double inverse identified with `e`.
    have h : stalkPrecomp J Y e.symm e.symm.contMDiff (e x)
        (stalkPrecomp I X e e.contMDiff (e.symm (e x))
          ((e.apply_symm_apply (e x)).symm ▸ s)) = s :=
      stalkPrecomp_symm_rightInverse e.symm (e x) s
    -- Pullback commutes with transport of the source and target base points.
    have transport (z : X) (hz : z = x) :
        stalkPrecomp I X e e.contMDiff z ((congrArg e hz).symm ▸ s) =
          hz.symm ▸ stalkPrecomp I X e e.contMDiff x s := by
      subst z
      rfl
    rw [transport _ (e.symm_apply_apply x)] at h
    exact h
  exact ⟨left.injective, (stalkPrecomp_symm_rightInverse e x).surjective⟩

/-- The contravariant ring equivalence on holomorphic stalks induced by a biholomorphism. -/
def holomorphicStalkEquiv (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X) :
    (holomorphicStructureSheaf J Y).presheaf.stalk (e x) ≃+*
      (holomorphicStructureSheaf I X).presheaf.stalk x :=
  RingEquiv.ofBijective (stalkPrecomp I X e e.contMDiff x)
    (e.stalkPrecomp_bijective x)

/-- The stalk equivalence acts by pullback of germs. -/
@[simp]
theorem holomorphicStalkEquiv_apply (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (e x)) :
    e.holomorphicStalkEquiv x s = stalkPrecomp I X e e.contMDiff x s := (rfl)

/-- The inverse stalk equivalence pulls germs back along the inverse biholomorphism.
The source germ is transported along `e.symm (e x) = x`. -/
@[simp]
theorem holomorphicStalkEquiv_symm_apply (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X)
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    (e.holomorphicStalkEquiv x).symm s =
      stalkPrecomp J Y e.symm e.symm.contMDiff (e x)
        ((e.symm_apply_apply x).symm ▸ s) := by
  apply (e.holomorphicStalkEquiv x).injective
  rw [RingEquiv.apply_symm_apply, holomorphicStalkEquiv_apply]
  exact (stalkPrecomp_symm_rightInverse e x s).symm

end Diffeomorph
