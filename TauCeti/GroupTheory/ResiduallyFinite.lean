/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.ResiduallyFinite
import TauCeti.GroupTheory.Finiteness

/-!
# Finitely generated residually finite groups are Hopfian

Malcev's theorem: a surjective endomorphism `f` of a finitely generated residually finite group
`G` is injective. Indeed, for a finite quotient `π : G →* Q`, precomposition with `f` is an
injective self-map of the set `G →* Q`, which is finite because a finitely generated group has
only finitely many homomorphisms to a finite one (`Monoid.FG.finite_monoidHom`). It is therefore a
bijection, so `π` factors through `f` and kills its kernel. Residual finiteness then forces the
kernel to be trivial. Free groups of finite rank are therefore Hopfian, which is how one
recognizes that a surjection between free groups of the same finite rank is an isomorphism.

## Main result

* `Group.ResiduallyFinite.injective_of_surjective`: a surjective endomorphism of a finitely
  generated residually finite group is injective.

## References

* A. I. Malcev, *On isomorphic matrix representations of infinite groups*, Mat. Sb. 8 (50)
  (1940), 405–422.
-/

public section

namespace Group.ResiduallyFinite

variable {G : Type*} [Group G] [Group.FG G] [Group.ResiduallyFinite G]

/-- **Malcev's theorem.** A surjective endomorphism of a finitely generated residually finite
group is injective: such a group is Hopfian. -/
theorem injective_of_surjective {f : G →* G} (hf : Function.Surjective f) :
    Function.Injective f := by
  refine (injective_iff_map_eq_one f).mpr fun x hx => ?_
  by_contra hx1
  obtain ⟨N, hxN⟩ := exists_finiteIndexNormalSubgroup_notMem x hx1
  have : Finite (G ⧸ N.toSubgroup) := Subgroup.finite_quotient_of_finiteIndex
  -- Precomposition with `f` is injective on the finite set of homomorphisms to `G ⧸ N`, hence
  -- surjective, so the quotient map factors through `f`.
  have hinj : Function.Injective fun ψ : G →* G ⧸ N.toSubgroup => ψ.comp f :=
    fun ψ χ h => (MonoidHom.cancel_right hf).mp h
  obtain ⟨ψ, hψ⟩ := Finite.surjective_of_injective hinj (QuotientGroup.mk' N.toSubgroup)
  have hπ : (QuotientGroup.mk' N.toSubgroup) x = 1 := by
    rw [← hψ, MonoidHom.comp_apply, hx, map_one]
  exact hxN ((QuotientGroup.eq_one_iff x).mp hπ)

end Group.ResiduallyFinite
