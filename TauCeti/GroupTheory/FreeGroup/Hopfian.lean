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
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
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
the right cardinality is a free basis. Together with the Nielsen–Schreier theorem, it shows that a
homomorphism from `FreeGroup α` to a free group is injective as soon as every homomorphism
`FreeGroup α →* ℤ/2` factors through it.

## Main results

* `FreeGroupBasis.injective_of_surjective_of_card_le`: a surjection from `FreeGroup α` onto a group
  with a free basis `ι`, where `#α ≤ #ι`, is injective.
* `IsFreeGroup.injective_of_forall_exists_comp_eq`: a homomorphism from `FreeGroup α` to a free
  group is injective if every homomorphism `FreeGroup α →* ℤ/2` factors through it.
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

end FreeGroupBasis

namespace IsFreeGroup

variable {α H : Type*} [Group H] [IsFreeGroup H] {f : FreeGroup α →* H}

/-- A homomorphism from the free group on a finite type `α` to a free group is injective as soon
as every homomorphism `FreeGroup α →* ℤ/2` factors through it. -/
theorem injective_of_forall_exists_comp_eq [Finite α]
    (h : ∀ v : α → Multiplicative (ZMod 2),
      ∃ φ : H →* Multiplicative (ZMod 2), φ.comp f = FreeGroup.lift v) :
    Function.Injective f := by
  -- The range of `f` is free by the Nielsen–Schreier theorem, and `f` surjects onto it.
  let b := basis f.range
  have hf := f.rangeRestrict_surjective
  have := b.finite_of_surjective hf
  refine MonoidHom.rangeRestrict_injective_iff.mp <| b.injective_of_surjective_of_card_le hf <|
    b.card_le_of_forall_exists_comp_eq (f := f.rangeRestrict) fun v ↦ ?_
  obtain ⟨φ, hφ⟩ := h v
  exact ⟨φ.comp f.range.subtype, by rw [MonoidHom.comp_assoc, f.subtype_comp_rangeRestrict, hφ]⟩

end IsFreeGroup

namespace PresentedGroup

variable {α : Type*} [Finite α] {rels : Set (FreeGroup α)}

/-- If a group presented on finitely many generators is free, and every assignment of elements of
`ℤ/2` to the generators kills the relators, then the presentation map from the free group on the
generators is injective. -/
theorem injective_mk_of_isFreeGroup [IsFreeGroup (PresentedGroup rels)]
    (h : ∀ v : α → Multiplicative (ZMod 2), ∀ r ∈ rels, FreeGroup.lift v r = 1) :
    Function.Injective (mk rels) :=
  IsFreeGroup.injective_of_forall_exists_comp_eq fun v ↦ ⟨toGroup (h v), FreeGroup.ext_hom _ _
    fun _ ↦ (toGroup.of (h v)).trans FreeGroup.lift_apply_of.symm⟩

/-- A group presented on finitely many generators is not free if it has a nontrivial relator and
every assignment of elements of `ℤ/2` to the generators kills the relators. -/
theorem not_isFreeGroup
    (h : ∀ v : α → Multiplicative (ZMod 2), ∀ r ∈ rels, FreeGroup.lift v r = 1)
    {r : FreeGroup α} (hr : r ∈ rels) (hr1 : r ≠ 1) : ¬IsFreeGroup (PresentedGroup rels) :=
  fun _ ↦ hr1 <| injective_mk_of_isFreeGroup h <| by rw [one_of_mem hr, map_one]

end PresentedGroup
