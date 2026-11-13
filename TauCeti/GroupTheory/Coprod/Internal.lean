/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Internal free products of two subgroups

A group `G` is the internal free product of two subgroups `A` and `B` when the homomorphism
`A ∗ B →* G` induced by the inclusions is bijective. For injective homomorphisms `f : A →* G` and
`g : B →* G`, this compares the internal free product of the images of `f` and `g` with the
external free product `A ∗ B` mapped to `G` by `f` and `g`.

## Main results

* `Monoid.Coprod.lift_subtype_range_bijective_iff`: for injective `f : A →* G`, `g : B →* G`, the
  group `G` is the internal free product of the images of `f` and `g` exactly when `f` and `g`
  exhibit `G` as `A ∗ B`.
-/

public section

namespace Monoid.Coprod

variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- For injective homomorphisms `f : A →* G` and `g : B →* G`, the group `G` is the free product
of the images of `f` and `g` exactly when it is the free product of `A` and `B` via `f` and `g`. -/
theorem lift_subtype_range_bijective_iff {f : A →* G} {g : B →* G} (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Bijective (lift f.range.subtype g.range.subtype) ↔ Function.Bijective (lift f g) := by
  have : lift f g = (lift f.range.subtype g.range.subtype).comp
      (MulEquiv.coprodCongr (MonoidHom.ofInjective hf) (MonoidHom.ofInjective hg)).toMonoidHom := by
    ext <;> simp [MulEquiv.coprodCongr, MonoidHom.ofInjective_apply]
  rw [this, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (Function.Bijective.of_comp_iff _ (MulEquiv.bijective _)).symm

end Monoid.Coprod
