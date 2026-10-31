/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import TauCeti.CategoryTheory.Action.Tannaka

/-!
# Effective epimorphic families of `G`-sets

A family of maps `π a : X a ⟶ B` of `G`-sets is an effective epimorphic family in
`Action (Type u) G` exactly when it is jointly surjective on underlying types
(`Action.effectiveEpiFamily_iff`). This is the `G`-equivariant form of
`CategoryTheory.Types.effectiveEpiFamily_iff`.

A jointly surjective family is effective: a compatible family `e a : X a ⟶ W` descends to `B` by
evaluating `e` at any preimage. Compatibility on elements follows from compatibility on maps of
`G`-sets by testing against the orbit maps `CategoryTheory.Action.leftRegularHom` out of the left
regular `G`-set, and the descended map is equivariant because preimages may be translated by `G`.
Conversely, an effective epimorphic family is jointly epimorphic, and the two maps from `B` to the
trivial `G`-set of propositions, constantly true and membership in the joint image, agree after
composing with every `π a`; the joint image is `G`-stable, so the second map is equivariant.
-/

public section

universe u

open CategoryTheory

namespace Action

variable {α : Type*}

section Monoid

variable {G : Type u} [Monoid G] {B : Action (Type u) G} (X : α → Action (Type u) G)
  (π : (a : α) → X a ⟶ B)

/-- Compatibility of a family of maps of `G`-sets, tested on maps out of `G`-sets, implies
compatibility on elements. -/
private theorem apply_eq_apply_of_compatible {W : Action (Type u) G} (e : (a : α) → X a ⟶ W)
    (h : ∀ {Z : Action (Type u) G} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
    {a₁ a₂ : α} {x₁ : ToType (X a₁)} {x₂ : ToType (X a₂)}
    (hx : (π a₁).hom x₁ = (π a₂).hom x₂) : (e a₁).hom x₁ = (e a₂).hom x₂ := by
  have := h a₁ a₂ (Action.leftRegularHom x₁) (Action.leftRegularHom x₂) (by simp [hx])
  rw [Action.leftRegularHom_comp, Action.leftRegularHom_comp] at this
  exact Action.leftRegularHom_injective this

/-- The descent data of a jointly surjective family of maps of `G`-sets: a compatible family is
evaluated at a chosen preimage. -/
noncomputable def effectiveEpiFamilyStructOfSurjective
    (hπ : ∀ b : ToType B, ∃ a x, (π a).hom x = b) : EffectiveEpiFamilyStruct X π where
  desc {W} e h :=
    { hom := TypeCat.ofHom fun b ↦ (e (hπ b).choose).hom (hπ b).choose_spec.choose
      comm g := by
        ext b
        have hb := (hπ b).choose_spec.choose_spec
        have hgb := (hπ (B.ρ g b)).choose_spec.choose_spec
        refine (apply_eq_apply_of_compatible X π e h ?_).trans (hom_comm_apply _ g _)
        rw [hgb, hom_comm_apply, hb] }
  fac {W} e h a := by
    ext x
    exact apply_eq_apply_of_compatible X π e h (hπ ((π a).hom x)).choose_spec.choose_spec
  uniq {W} e h m hm := by
    ext b
    have hb := (hπ b).choose_spec.choose_spec
    simp only [← hm]
    exact congrArg m.hom hb.symm

end Monoid

variable {G : Type u} [Group G] {B : Action (Type u) G} (X : α → Action (Type u) G)
  (π : (a : α) → X a ⟶ B)

/-- In the category of `G`-sets, a family of maps is effective epimorphic if and only if it is
jointly surjective. -/
theorem effectiveEpiFamily_iff :
    EffectiveEpiFamily X π ↔ ∀ b : ToType B, ∃ a x, (π a).hom x = b := by
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiFamilyStructOfSurjective X π hπ⟩⟩⟩
  -- Membership in the joint image is an equivariant map to the trivial `G`-set of propositions,
  -- since the joint image is `G`-stable. It agrees with the constant map `True` after composing
  -- with every `π a`. The two maps are built with `TypeCat.ofHom`, so their values are computed
  -- by definitional unfolding.
  have h := EffectiveEpiFamily.hom_ext X π (W := trivial G (ULift.{u} Prop))
    ⟨TypeCat.ofHom fun _ ↦ ULift.up True, fun _ ↦ rfl⟩
    ⟨TypeCat.ofHom fun b ↦ ULift.up (∃ a x, (π a).hom x = b), fun g ↦ by
      ext b
      refine congrArg ULift.up (propext ⟨fun ⟨a, x, hx⟩ ↦ ⟨a, (X a).ρ g⁻¹ x, ?_⟩,
        fun ⟨a, x, hx⟩ ↦ ⟨a, (X a).ρ g x, ?_⟩⟩)
      · rw [hom_comm_apply]
        exact (congrArg (B.ρ g⁻¹) hx).trans (ρ_inv_self_apply g b)
      · rw [hom_comm_apply, hx]
        rfl⟩
    fun a ↦ by
      ext x
      exact congrArg ULift.up (propext ⟨fun _ ↦ ⟨a, x, rfl⟩, fun _ ↦ True.intro⟩)
  intro b
  exact (congrArg ULift.down (ConcreteCategory.congr_hom (congrArg Hom.hom h) b)).mp True.intro

end Action
