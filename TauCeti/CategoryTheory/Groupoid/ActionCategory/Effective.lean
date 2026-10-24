/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic
public import TauCeti.GroupTheory.GroupAction.Effective

/-!
# The projection to the faithful action groupoid

Dividing a group by the kernel of its action gives a functor between the native action
groupoids. It fixes the underlying points and projects arrow labels to their cosets. The
functor is full, and on each isotropy group it is the surjective stabilizer projection whose
kernel is the original action kernel. Thus effective reduction of a connected finite smooth
action chart preserves its orbit space but can destroy isotropy. The projection is faithful
on a nonempty space exactly when there was no kernel to remove.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory MulAction

namespace TauCeti

variable (G X : Type*) [Group G] [MulAction G X]

/-- Project the labels of an action groupoid to the quotient by its action kernel. -/
def effectiveActionFunctor :
    ActionCategory G X ⥤ ActionCategory (G ⧸ (toPermHom G X).ker) X where
  obj a := ActionCategory.objEquiv _ X a.back
  map f := Functor.Elements.homMk (QuotientGroup.mk f.hom)
    ((quotientKerToPermHom_mk_smul G X f.hom _).trans f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem effectiveActionFunctor_obj (x : X) :
    (effectiveActionFunctor G X).obj (ActionCategory.objEquiv G X x) =
      ActionCategory.objEquiv (G ⧸ (toPermHom G X).ker) X x := (rfl)

@[simp]
theorem effectiveActionFunctor_map_hom {a b : ActionCategory G X} (f : a ⟶ b) :
    ((effectiveActionFunctor G X).map f).hom =
      (QuotientGroup.mk f.hom : G ⧸ (toPermHom G X).ker) := (rfl)

/-- On isotropy groups, the effective action functor is the stabilizer projection. -/
@[simp]
theorem effectiveActionFunctor_mapAut_stabilizerMulEquivAut (x : X) (g : stabilizer G x) :
    (effectiveActionFunctor G X).mapAut _ (ActionCategory.stabilizerMulEquivAut G x g) =
      ActionCategory.stabilizerMulEquivAut (G ⧸ (toPermHom G X).ker) x
        (effectiveStabilizerMap G X x g) := by
  ext : 2
  apply Functor.Elements.hom_ext
  rfl

/-- Every arrow of the faithful action groupoid lifts, with its source and target fixed. -/
instance effectiveActionFunctor_full : (effectiveActionFunctor G X).Full where
  map_surjective {a b} f := by
    -- Unfold the object map so that the dependent labels are read in the quotient group.
    dsimp only [effectiveActionFunctor] at f ⊢
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective f.hom
    have hq := ActionCategory.hom_smul f
    have h : g • a.back = b.back := by
      rw [← quotientKerToPermHom_mk_smul G X, hg]
      exact hq
    exact ⟨Functor.Elements.homMk g h, Functor.Elements.hom_ext hg⟩

/-- On a nonempty space, the projection is faithful exactly when the action kernel is trivial.
In particular a coarse-space identification does not make this projection an equivalence. -/
theorem effectiveActionFunctor_faithful_iff [Nonempty X] :
    (effectiveActionFunctor G X).Faithful ↔ (toPermHom G X).ker = ⊥ := by
  constructor
  · intro hF
    apply le_antisymm _ bot_le
    intro g hg
    obtain ⟨x⟩ := ‹Nonempty X›
    have hfix : g • x = x := Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hg) x
    let f : ActionCategory.objEquiv G X x ⟶ ActionCategory.objEquiv G X x :=
      Functor.Elements.homMk g hfix
    have hmap : (effectiveActionFunctor G X).map f =
        (effectiveActionFunctor G X).map (𝟙 (ActionCategory.objEquiv G X x)) := by
      apply Functor.Elements.hom_ext
      simpa only [effectiveActionFunctor_map_hom, ActionCategory.id_hom,
        QuotientGroup.mk_one] using (QuotientGroup.eq_one_iff g).mpr hg
    exact Subgroup.mem_bot.mpr (by
      simpa only [ActionCategory.id_hom] using
        congrArg Functor.Elements.Hom.hom (hF.map_injective hmap))
  · intro hker
    have hinj : Function.Injective (QuotientGroup.mk' (toPermHom G X).ker) :=
      (MonoidHom.ker_eq_bot_iff _).mp ((QuotientGroup.ker_mk' _).trans hker)
    exact ⟨fun h ↦ Functor.Elements.hom_ext (hinj (congrArg Functor.Elements.Hom.hom h))⟩

end TauCeti
