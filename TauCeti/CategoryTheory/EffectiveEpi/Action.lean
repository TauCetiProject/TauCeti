/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import TauCeti.CategoryTheory.Action.Basic

/-!
# Effective epimorphic families of `G`-sets

For a monoid `G`, a family of maps `π a : X a ⟶ B` of `G`-sets is an effective epimorphic family
in `Action (Type u) G` exactly when it is jointly surjective on underlying types
(`Action.effectiveEpiFamily_iff`). This is the `G`-equivariant form of
`CategoryTheory.Types.effectiveEpiFamily_iff`.

Effective epimorphic families are the covers of a topos, so this criterion translates categorical
statements about covers of `G`-sets into statements about points: it is how finiteness conditions
such as quasicompactness are computed for `G`-sets, and how covers of a `G`-set are constructed,
for instance by the orbit maps `CategoryTheory.Action.leftRegularHom` of its points. For a jointly
surjective family, `Action.effectiveEpiFamilyStructOfSurjective` provides the descent data
explicitly.
-/

public section

universe u

open CategoryTheory

namespace Action

variable {α : Type*} {G : Type u} [Monoid G] {B : Action (Type u) G} (X : α → Action (Type u) G)
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

/-- The `G`-set of `G`-indexed families of propositions, with `g` acting by
`(g • φ) m = φ (m * g)`. A point `b` of a `G`-set gives the family recording which translates of
`b` satisfy a property, which is how `Action.effectiveEpiFamily_iff` tests membership. -/
private def predicates : Action (Type u) G where
  V := G → ULift.{u} Prop
  ρ := (TypeCat.endEquiv _).toMonoidHom.comp
    { toFun g φ m := φ (m * g)
      map_one' := funext fun φ ↦ funext fun m ↦ congrArg φ (mul_one m)
      map_mul' g h := funext fun φ ↦ funext fun m ↦ congrArg φ (mul_assoc m g h).symm }

/-- In the category of `G`-sets, a family of maps is effective epimorphic if and only if it is
jointly surjective. -/
theorem effectiveEpiFamily_iff :
    EffectiveEpiFamily X π ↔ ∀ b : ToType B, ∃ a x, (π a).hom x = b := by
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiFamilyStructOfSurjective X π hπ⟩⟩⟩
  -- Recording which translates of a point lie in the joint image is an equivariant map to
  -- `predicates`. It agrees with the constant map `True` after composing with every `π a`, since
  -- the joint image is `G`-stable. The two maps are built with `TypeCat.ofHom`, so their values
  -- are computed by definitional unfolding.
  have h := EffectiveEpiFamily.hom_ext X π (W := predicates)
    ⟨TypeCat.ofHom fun _ _ ↦ ULift.up True, fun _ ↦ rfl⟩
    ⟨TypeCat.ofHom fun b m ↦ ULift.up (∃ a x, (π a).hom x = B.ρ m b), fun g ↦ by
      ext b
      funext m
      change ULift.up (∃ a x, (π a).hom x = B.ρ m (B.ρ g b)) =
        ULift.up (∃ a x, (π a).hom x = B.ρ (m * g) b)
      rw [map_mul]
      rfl⟩
    fun a ↦ by
      ext x
      funext m
      exact congrArg ULift.up
        (propext ⟨fun _ ↦ ⟨a, (X a).ρ m x, hom_comm_apply _ m x⟩, fun _ ↦ True.intro⟩)
  intro b
  have := congrFun (ConcreteCategory.congr_hom (congrArg Hom.hom h) b) 1
  obtain ⟨a, x, hx⟩ := (congrArg ULift.down this).mp True.intro
  exact ⟨a, x, hx.trans (by simp)⟩

end Action
