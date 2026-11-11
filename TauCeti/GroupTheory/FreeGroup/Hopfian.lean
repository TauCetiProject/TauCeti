/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.GroupTheory.FreeGroup.Rank
import TauCeti.GroupTheory.FreeGroup.ResiduallyP
import TauCeti.GroupTheory.ResiduallyFinite

/-!
# Surjections between free groups of the same finite rank are injective

Free groups are residually finite, and a finitely generated residually finite group is Hopfian
(Malcev): each of its surjective endomorphisms is injective. Consequently, if `FreeGroup α` with
`α` finite surjects onto a group with a free basis `ι` having at least as many elements as `α`,
the surjection is an isomorphism. This is the usual way to recognise that a generating family of
the right cardinality is a free basis.

## Main results

* `FreeGroupBasis.injective_of_surjective_of_card_le`: a surjection from `FreeGroup α` onto a group
  with a free basis `ι`, where `#α ≤ #ι`, is injective.
* `FreeGroupBasis.injective_of_surjective_of_forall_exists_comp_eq`: a surjection from
  `FreeGroup α` onto a group with a free basis is injective if every homomorphism
  `FreeGroup α →* ℤ/2` factors through it.
* `PresentedGroup.not_isFreeGroup`: a group presented on finitely many generators, with a
  nontrivial relator, all of whose relators die in `ℤ/2` under every assignment of the generators,
  is not free.

## References

* A. I. Malcev, *On isomorphic matrix representations of infinite groups*, Mat. Sb. 8 (50)
  (1940), 405–422.
* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter I,
  Proposition 3.5.
-/

public section

namespace FreeGroupBasis

variable {ι α H : Type*} [Group H] {f : FreeGroup α →* H}

/-- **Free groups of finite rank are Hopfian.** A surjection from the free group on a finite type
`α` onto a group with a free basis `ι` is injective as soon as `#α ≤ #ι`. -/
theorem injective_of_surjective_of_card_le (b : FreeGroupBasis ι H) [Finite α]
    (hf : Function.Surjective f) (h : Nat.card α ≤ Nat.card ι) : Function.Injective f := by
  have := b.finite_of_surjective hf
  obtain ⟨e⟩ := Finite.card_eq.mp ((b.card_le_of_surjective hf).antisymm h)
  -- Identifying `H` with `FreeGroup α`, `f` becomes a surjective endomorphism.
  let r : H ≃* FreeGroup α := b.repr.trans (FreeGroup.freeGroupCongr e)
  have hr : Function.Injective (r.toMonoidHom.comp f) :=
    Group.ResiduallyFinite.injective_of_surjective (r.surjective.comp hf)
  rw [MonoidHom.coe_comp] at hr
  exact hr.of_comp

/-- A surjection from the free group on a finite type `α` onto a group `H` with a free basis is
injective as soon as every homomorphism `FreeGroup α →* ℤ/2` factors through `H`: the group `H`
then has as many homomorphisms to `ℤ/2` as `FreeGroup α`, hence the same rank. -/
theorem injective_of_surjective_of_forall_exists_comp_eq (b : FreeGroupBasis ι H) [Finite α]
    (hf : Function.Surjective f)
    (h : ∀ v : α → Multiplicative (ZMod 2),
      ∃ φ : H →* Multiplicative (ZMod 2), φ.comp f = FreeGroup.lift v) :
    Function.Injective f :=
  b.injective_of_surjective_of_card_le hf (b.card_le_of_forall_exists_comp_eq hf h)

end FreeGroupBasis

namespace PresentedGroup

variable {α : Type*} [Finite α] {rels : Set (FreeGroup α)}

/-- If a group presented on finitely many generators is free, and every assignment of elements of
`ℤ/2` to the generators kills the relators, then the presentation map from the free group on the
generators is injective. -/
theorem injective_mk_of_isFreeGroup [IsFreeGroup (PresentedGroup rels)]
    (h : ∀ v : α → Multiplicative (ZMod 2), ∀ r ∈ rels, FreeGroup.lift v r = 1) :
    Function.Injective (mk rels) :=
  (IsFreeGroup.basis _).injective_of_surjective_of_forall_exists_comp_eq (mk_surjective rels)
    fun v ↦ ⟨toGroup (h v), FreeGroup.ext_hom _ _ fun _ ↦
      (toGroup.of (h v)).trans FreeGroup.lift_apply_of.symm⟩

/-- A group presented on finitely many generators is not free if it has a nontrivial relator and
every assignment of elements of `ℤ/2` to the generators kills the relators. -/
theorem not_isFreeGroup
    (h : ∀ v : α → Multiplicative (ZMod 2), ∀ r ∈ rels, FreeGroup.lift v r = 1)
    {r : FreeGroup α} (hr : r ∈ rels) (hr1 : r ≠ 1) : ¬IsFreeGroup (PresentedGroup rels) :=
  fun _ ↦ hr1 <| injective_mk_of_isFreeGroup h <| by rw [one_of_mem hr, map_one]

end PresentedGroup
