/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Module.AuslanderReiten.Morphism
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.LinearAlgebra.Dual.FiniteProjective

/-!
# The transpose on stable morphisms

A map of modules lifts to a square between projective presentations. Transposing that square
reverses the map. Passing to the projective stable category makes this independent of the lift:
the difference of two lifts factors through the dual of the first presenting projective.
When that projective is finitely generated, its opposite dual is projective too.

This file constructs the resulting additive map on stable Hom groups. It preserves identities
and reverses composition, providing the morphism part of the stable transpose duality.
Presentations are explicit parameters; the construction does not choose presentations for all
modules or assert the stable equivalence itself.

The stable categories used here are the existing projective stable quotients for the canonical
exact structures on `ModuleCat`. The source diagram needs only a zero composite;
exactness and surjectivity are required of the target presentation. No minimality, finite length,
commutativity, or field hypothesis is needed.

## Main results

* `TauCeti.AuslanderReitenTranspose.stableMap`: the additive map on stable Hom groups.
* `TauCeti.AuslanderReitenTranspose.stableMap_quotient_map`: computation using any lift.
* `TauCeti.AuslanderReitenTranspose.stableMap_id`: identities are preserved.
* `TauCeti.AuslanderReitenTranspose.stableMap_comp`: composition is reversed.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti.AuslanderReitenTranspose

open CategoryTheory LinearMap

universe u v

variable {A : Type u} [Ring A]

local notation "S" => ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))
local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

variable {M N P₀ P₁ Q₀ Q₁ : Type v}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Projective A P₀] [Module.Projective A P₁] [Module.Finite A P₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀} {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

private theorem quotient_map_eq (hq : Function.Exact q ρ)
    (f₀ g₀ : P₀ →ₗ[A] Q₀) (f₁ g₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀ ∘ₗ p = q ∘ₗ f₁) (hg : g₀ ∘ₗ p = q ∘ₗ g₁)
    (hfg : ρ ∘ₗ f₀ = ρ ∘ₗ g₀) :
    (T).map (ModuleCat.ofHom (map f₀ f₁ hf)) = (T).map (ModuleCat.ofHom (map g₀ g₁ hg)) := by
  obtain ⟨h, hh⟩ := exists_map_sub_eq_mk_comp hq f₀ g₀ f₁ g₁ hf hg hfg
  rw [← sub_eq_zero, ← Functor.map_sub,
    ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
  have hdual := (ExactStructure.abelian_isProjective_iff
    (ModuleCat.of Aᵐᵒᵖ (Module.Dual A P₁))).mpr inferInstance
  have hfactor := ObjectProperty.factorsThrough_comp _ hdual
    (ModuleCat.ofHom h) (ModuleCat.ofHom (mk p))
  have heq : ModuleCat.ofHom (map f₀ f₁ hf) - ModuleCat.ofHom (map g₀ g₁ hg) =
      ModuleCat.ofHom h ≫ ModuleCat.ofHom (mk p) :=
    ModuleCat.hom_ext (by simpa using hh)
  exact heq.symm ▸ hfactor

private noncomputable def stableLift (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) (f : M →ₗ[A] N) :
    (T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose q)) ⟶
      (T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) :=
  let H := exists_lift_projective_presentation hp hq hρ f
  (T).map (ModuleCat.ofHom (map H.choose H.choose_spec.choose H.choose_spec.choose_spec.2))

private theorem stableLift_eq (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) (f : M →ₗ[A] N)
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf₀ : ρ ∘ₗ f₀ = f ∘ₗ π) (hf₁ : f₀ ∘ₗ p = q ∘ₗ f₁) :
    stableLift hp hq hρ f = (T).map (ModuleCat.ofHom (map f₀ f₁ hf₁)) := by
  unfold stableLift
  exact quotient_map_eq hq _ _ _ _ _ _
    ((exists_lift_projective_presentation hp hq hρ f).choose_spec.choose_spec.1.trans hf₀.symm)

private theorem stableLift_add (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) (f g : M →ₗ[A] N) :
    stableLift hp hq hρ (f + g) = stableLift hp hq hρ f + stableLift hp hq hρ g := by
  obtain ⟨f₀, f₁, hf₀, hf₁⟩ := exists_lift_projective_presentation hp hq hρ f
  obtain ⟨g₀, g₁, hg₀, hg₁⟩ := exists_lift_projective_presentation hp hq hρ g
  rw [stableLift_eq hp hq hρ f f₀ f₁ hf₀ hf₁,
    stableLift_eq hp hq hρ g g₀ g₁ hg₀ hg₁,
    stableLift_eq hp hq hρ (f + g) (f₀ + g₀) (f₁ + g₁)
      (by simp [comp_add, add_comp, hf₀, hg₀])
      (by simp [comp_add, add_comp, hf₁, hg₁])]
  rw [map_add f₀ g₀ f₁ g₁ hf₁ hg₁, ModuleCat.ofHom_add, Functor.map_add]

private noncomputable def stableLiftAddHom (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) :
    (ModuleCat.of A M ⟶ ModuleCat.of A N) →+
      ((T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose q)) ⟶
        (T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p))) where
  toFun f := stableLift hp hq hρ f.hom
  map_zero' := by
    rw [ModuleCat.hom_zero, stableLift_eq hp hq hρ 0 0 0 (by simp) (by simp)]
    simp
  map_add' f g := by
    simp only [ModuleCat.hom_add]
    exact stableLift_add hp hq hρ f.hom g.hom

variable [Small.{v} A]

private theorem stableLiftAddHom_kills (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) :
    (ExactStructure.abelian (ModuleCat.{v} A)).projectiveStableIdeal.hom
      (ModuleCat.of A M) (ModuleCat.of A N) ≤ (stableLiftAddHom hp hq hρ).ker := by
  intro f hf
  obtain ⟨C, hC, i, j, hfactor⟩ := (ObjectProperty.factorsThrough_iff _ _).mp
    ((ExactStructure.mem_projectiveStableIdeal_iff _).mp hf)
  have : Projective C := (ExactStructure.abelian_isProjective_iff C).mp hC
  have : Module.Projective A C := inferInstance
  obtain ⟨f₀, f₁, hf₀, hf₁⟩ := exists_lift_projective_presentation hp hq hρ f.hom
  obtain ⟨h, hh⟩ := exists_map_eq_mk_comp_of_factor hp hq hρ i.hom j.hom f₀ f₁ hf₁
    (by simpa only [hfactor, ModuleCat.hom_comp, comp_assoc] using hf₀)
  rw [AddMonoidHom.mem_ker]
  refine (stableLift_eq hp hq hρ f.hom f₀ f₁ hf₀ hf₁).trans ?_
  rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
  have hdual := (ExactStructure.abelian_isProjective_iff
    (ModuleCat.of Aᵐᵒᵖ (Module.Dual A P₁))).mpr inferInstance
  simpa only [hh, ModuleCat.ofHom_comp] using
    ObjectProperty.factorsThrough_comp _ hdual (ModuleCat.ofHom h) (ModuleCat.ofHom (mk p))

/-- The transpose on stable morphisms, as an additive map from stable maps `M → N` to stable
maps `Tr q → Tr p`. The presentations need not be minimal. -/
noncomputable def stableMap (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) :
    ((S).obj (ModuleCat.of A M) ⟶ (S).obj (ModuleCat.of A N)) →+
      ((T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose q)) ⟶
        (T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p))) :=
  (QuotientAddGroup.lift _ (stableLiftAddHom hp hq hρ) (stableLiftAddHom_kills hp hq hρ)).comp
    ((ExactStructure.abelian (ModuleCat.{v} A)).projectiveStableIdeal.homAddEquiv
      (ModuleCat.of A M) (ModuleCat.of A N)).symm.toAddMonoidHom

/-- Any square lifting a module map computes its stable transpose, independently of the
chosen lift and of the representative of the stable module map. -/
theorem stableMap_quotient_map (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ)
    (hρ : Function.Surjective ρ) (f : M →ₗ[A] N)
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf₀ : ρ ∘ₗ f₀ = f ∘ₗ π) (hf₁ : f₀ ∘ₗ p = q ∘ₗ f₁) :
    stableMap hp hq hρ ((S).map (ModuleCat.ofHom f)) =
      (T).map (ModuleCat.ofHom (map f₀ f₁ hf₁)) := by
  rw [stableMap, AddMonoidHom.comp_apply, ← MorphismIdeal.homAddEquiv_mk]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    AddEquiv.symm_apply_apply, QuotientAddGroup.lift_mk]
  exact stableLift_eq hp hq hρ f f₀ f₁ hf₀ hf₁

/-- Transposition preserves the identity stable morphism. -/
@[simp]
theorem stableMap_id (hex : Function.Exact p π)
    (hπ : Function.Surjective π) :
    stableMap hex.linearMap_comp_eq_zero hex hπ (𝟙 ((S).obj (ModuleCat.of A M))) =
      𝟙 ((T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p))) := by
  rw [← (S).map_id]
  simpa using stableMap_quotient_map hex.linearMap_comp_eq_zero hex hπ (id : M →ₗ[A] M)
    id id (by simp) (by simp)

/-- Transposition reverses composition of stable morphisms. -/
theorem stableMap_comp [Module.Projective A Q₀] [Module.Projective A Q₁] [Module.Finite A Q₁]
    {L R₀ R₁ : Type v} [AddCommGroup L] [Module A L]
    [AddCommGroup R₀] [Module A R₀] [AddCommGroup R₁] [Module A R₁]
    {r : R₁ →ₗ[A] R₀} {σ : R₀ →ₗ[A] L}
    (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (hr : Function.Exact r σ) (hσ : Function.Surjective σ)
    (f : (S).obj (ModuleCat.of A M) ⟶ (S).obj (ModuleCat.of A N))
    (g : (S).obj (ModuleCat.of A N) ⟶ (S).obj (ModuleCat.of A L)) :
    stableMap hp hr hσ (f ≫ g) =
      stableMap hq.linearMap_comp_eq_zero hr hσ g ≫ stableMap hp hq hρ f := by
  obtain ⟨f, rfl⟩ := (S).map_surjective f
  obtain ⟨g, rfl⟩ := (S).map_surjective g
  obtain ⟨f₀, f₁, hf₀, hf₁⟩ := exists_lift_projective_presentation hp hq hρ f.hom
  obtain ⟨g₀, g₁, hg₀, hg₁⟩ :=
    exists_lift_projective_presentation hq.linearMap_comp_eq_zero hr hσ g.hom
  rw [← (S).map_comp, ← ModuleCat.ofHom_hom (f ≫ g), ModuleCat.hom_comp,
    ← ModuleCat.ofHom_hom f, ← ModuleCat.ofHom_hom g]
  rw [stableMap_quotient_map hp hr hσ (g.hom ∘ₗ f.hom) (g₀ ∘ₗ f₀) (g₁ ∘ₗ f₁)
    (by rw [← comp_assoc, hg₀, comp_assoc, hf₀, ← comp_assoc])
    (by rw [comp_assoc, hf₁, ← comp_assoc, hg₁, comp_assoc])]
  rw [stableMap_quotient_map hp hq hρ f.hom f₀ f₁ hf₀ hf₁,
    stableMap_quotient_map hq.linearMap_comp_eq_zero hr hσ g.hom g₀ g₁ hg₀ hg₁,
    ← (T).map_comp, ← ModuleCat.ofHom_comp, map_comp_map]

end TauCeti.AuslanderReitenTranspose
