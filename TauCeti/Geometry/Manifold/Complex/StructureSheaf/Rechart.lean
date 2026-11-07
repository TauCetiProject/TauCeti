/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ

/-!
# Holomorphic stalks under biholomorphisms

A biholomorphism induces a ring equivalence on holomorphic stalks by pullback. This allows
local equations and their ideal-theoretic properties to be transported between coordinates.
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

/-- Pullback by a biholomorphism is bijective on the holomorphic stalks. -/
theorem stalkPrecomp_bijective (e : X ≃ₘ^ω⟮I, J⟯ Y) (x : X) :
    Function.Bijective (stalkPrecomp I X e e.contMDiff x) := by
  constructor
  · intro s t hst
    obtain ⟨f, _, hfs⟩ := exists_toFilterGerm_eq (e x) s
    obtain ⟨g, _, hgt⟩ := exists_toFilterGerm_eq (e x) t
    apply toFilterGerm_nhds_injective (e x)
    have h := congrArg (toFilterGerm I X x (𝓝 x) le_rfl) hst
    rw [toFilterGerm_stalkPrecomp, toFilterGerm_stalkPrecomp, hfs, hgt,
      Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq] at h
    have he := e.toHomeomorph.map_nhds_eq x
    simp only [coe_toHomeomorph] at he
    rw [hfs, hgt, Germ.coe_eq, ← he]
    exact h
  · intro s
    obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq x s
    have hf' : ∀ᶠ y in 𝓝 (e x), ContMDiffAt J 𝓘(ℂ) ω (f ∘ e.symm) y := by
      have hf0 : ∀ᶠ z in 𝓝 (e.symm (e x)), ContMDiffAt I 𝓘(ℂ) ω f z := by
        simpa only [e.symm_apply_apply] using hf
      exact (e.symm.continuous.continuousAt.tendsto.eventually hf0).mono
        fun y hy ↦ hy.comp y e.symm.contMDiff.contMDiffAt
    obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt hf'
    refine ⟨t, toFilterGerm_nhds_injective x ?_⟩
    rw [toFilterGerm_stalkPrecomp, ht, hfs, Germ.coe_compTendsto]
    congr 1
    funext z
    simp

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
  obtain ⟨f, _, hfs⟩ := exists_toFilterGerm_eq x s
  -- Eliminate the base-point equality dependently, including the stalk ring instances.
  have transport (z : X) (hz : z = x) :
      toFilterGerm I X z (𝓝 z) le_rfl (hz.symm ▸ s) = f := by
    subst z
    exact hfs _ le_rfl
  have hfs' := transport _ (e.symm_apply_apply x)
  apply toFilterGerm_nhds_injective x
  rw [toFilterGerm_stalkPrecomp, toFilterGerm_stalkPrecomp, hfs', hfs _ le_rfl,
    Germ.coe_compTendsto, Germ.coe_compTendsto]
  congr 1
  funext z
  simp

end Diffeomorph
