/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ

/-!
# Holomorphic stalks under biholomorphisms

A biholomorphism `e : X ≃ₘ^ω⟮I, J⟯ Y` induces a contravariant ring equivalence
`Diffeomorph.holomorphicStalkEquiv` on holomorphic stalks by pullback. It acts on function germs by
precomposition with `e`, preserves base-point evaluation, and is functorial with respect to
`Diffeomorph.refl`, `Diffeomorph.trans`, and `Diffeomorph.symm`. This allows local equations and
their ideal-theoretic properties to be transported between coordinates.
-/

public noncomputable section

open Filter Topology
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

/-- Pulling a holomorphic germ back along a biholomorphism `e` composes its function germ with
`e`. -/
theorem toFilterGerm_holomorphicStalkEquiv (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (e x)) :
    toFilterGerm I X x (𝓝 x) le_rfl (e.holomorphicStalkEquiv x s) =
      (toFilterGerm J Y (e x) (𝓝 (e x)) le_rfl s).compTendsto e (e.continuous.tendsto x) :=
  toFilterGerm_stalkPrecomp e e.contMDiff x s

/-- If `s` is represented near `e x` by `f`, then `e.holomorphicStalkEquiv x s` is represented near
`x` by `f ∘ e`. -/
theorem toFilterGerm_holomorphicStalkEquiv_of_eq (e : X ≃ₘ^ω⟮I, J⟯ Y) {x : X}
    {s : (holomorphicStructureSheaf J Y).presheaf.stalk (e x)} {f : Y → ℂ}
    (hs : toFilterGerm J Y (e x) (𝓝 (e x)) le_rfl s = f) :
    toFilterGerm I X x (𝓝 x) le_rfl (e.holomorphicStalkEquiv x s) = f ∘ e := by
  rw [toFilterGerm_holomorphicStalkEquiv, hs, Germ.coe_compTendsto]

/-- Pulling a holomorphic germ back along a biholomorphism preserves its value at the base point. -/
theorem eval_holomorphicStalkEquiv (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (e x)) :
    eval I X x (e.holomorphicStalkEquiv x s) = eval J Y (e x) s :=
  eval_stalkPrecomp I X e e.contMDiff x s

/-- The inverse stalk equivalence preserves the value of a holomorphic germ at the base point. -/
theorem eval_holomorphicStalkEquiv_symm (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X)
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    eval J Y (e x) ((e.holomorphicStalkEquiv x).symm s) = eval I X x s := by
  rw [← e.eval_holomorphicStalkEquiv x, RingEquiv.apply_symm_apply]

/-- The identity biholomorphism induces the identity equivalence on holomorphic stalks. -/
@[simp]
theorem holomorphicStalkEquiv_refl (x : X) :
    (Diffeomorph.refl I X ω).holomorphicStalkEquiv x = RingEquiv.refl _ := by
  ext s
  exact RingHom.congr_fun (stalkPrecomp_id I X x) s

/-- The inverse of `e.holomorphicStalkEquiv x` is `e.symm.holomorphicStalkEquiv (e x)` after
transporting the source stalk along `x = e.symm (e x)`. -/
theorem holomorphicStalkEquiv_symm (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X) :
    (e.holomorphicStalkEquiv x).symm =
      (RingEquiv.cast (R := fun z ↦ (holomorphicStructureSheaf I X).presheaf.stalk z)
        (e.symm_apply_apply x).symm).trans (e.symm.holomorphicStalkEquiv (e x)) := by
  ext s
  apply (e.holomorphicStalkEquiv x).injective
  obtain ⟨f, -, hfs⟩ := exists_toFilterGerm_eq x s
  apply toFilterGerm_nhds_injective x
  rw [RingEquiv.apply_symm_apply, RingEquiv.trans_apply,
    e.toFilterGerm_holomorphicStalkEquiv_of_eq
      (e.symm.toFilterGerm_holomorphicStalkEquiv_of_eq
        (toFilterGerm_ringEquivCast _ (hfs _ le_rfl))),
    hfs _ le_rfl, Germ.coe_eq]
  exact Eventually.of_forall fun z ↦ congrArg f (e.symm_apply_apply z).symm

/-- If `s` is represented near `x` by `f`, then `(e.holomorphicStalkEquiv x).symm s` is represented
near `e x` by `f ∘ e.symm`. -/
theorem toFilterGerm_holomorphicStalkEquiv_symm_of_eq (e : X ≃ₘ^ω⟮I, J⟯ Y) {x : X}
    {s : (holomorphicStructureSheaf I X).presheaf.stalk x} {f : X → ℂ}
    (hs : toFilterGerm I X x (𝓝 x) le_rfl s = f) :
    toFilterGerm J Y (e x) (𝓝 (e x)) le_rfl ((e.holomorphicStalkEquiv x).symm s) =
      f ∘ e.symm := by
  rw [holomorphicStalkEquiv_symm, RingEquiv.trans_apply,
    e.symm.toFilterGerm_holomorphicStalkEquiv_of_eq
      (toFilterGerm_ringEquivCast (e.symm_apply_apply x).symm hs)]

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- Pulling holomorphic germs back along `e₁.trans e₂` is pulling back along `e₂` and then along
`e₁`. -/
@[simp]
theorem holomorphicStalkEquiv_trans (e₁ : X ≃ₘ^ω⟮I, J⟯ Y) (e₂ : Y ≃ₘ^ω⟮J, K⟯ Z) (x : X) :
    (e₁.trans e₂).holomorphicStalkEquiv x =
      (e₂.holomorphicStalkEquiv (e₁ x)).trans (e₁.holomorphicStalkEquiv x) := by
  ext s
  exact stalkPrecomp_comp I X e₂ e₂.contMDiff e₁ e₁.contMDiff x s

end Diffeomorph
