/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.ULift

/-!
# Amalgamated products: non-injective maps, centralizers, and the amalgamation of groups

Mathlib's `Monoid.PushoutI φ` is defined for an arbitrary family of homomorphisms
`φ i : H →* G i`, and `Monoid.PushoutI.of_injective` shows that the factors `G i` embed in it when
every `φ i` is injective. This file records the converse obstruction: two elements of `H`
identified by one map `φ j` have the same image in the pushout, so a factor `G i` that embeds
forces `φ i` to identify them as well. In particular, if `φ i` is injective and some `φ j` is
not, then `G i` does not embed in the pushout.

This is the reason the boundary maps of a graph of groups are required to be injective: for the
data of an amalgam `A ∗_C B` with a non-injective map `C →* B` and an injective map `C →* A`, the
vertex group `A` does not embed in the amalgam, and the normal form theorem fails.

For a pushout of groups along `φ i : C →* G i`, an element of a factor `G i` that centralizes the
image of `C` in `G i` commutes in the pushout with every element of the image `base φ c` of `C`,
since that image is also the image of `φ i c` under the inclusion of `G i`.

Conversely, two injective homomorphisms `φ : C →* A` and `ψ : C →* B` of groups are completed to
a commutative square of injective homomorphisms into a group: the amalgamated product
`A ∗_C B`, in which both factors embed by the normal form theorem. This is the amalgamation
property of the class of groups.

## Main results

* `Monoid.PushoutI.apply_eq_apply_of_injective_of`: if `G i` embeds in the pushout, then `φ i`
  identifies every pair of elements identified by some `φ j`.
* `Monoid.PushoutI.not_injective_of`: if `φ i` is injective and `φ j` is not, then `G i` does not
  embed in the pushout.
* `Monoid.PushoutI.commute_of_base_of_mem_centralizer`: an element of a factor centralizing the
  image of `C` commutes with the image of `C` in the pushout.
* `Monoid.PushoutI.exists_injective_comp_eq_comp`: two injective homomorphisms out of a group `C`
  are completed to a commutative square of injective homomorphisms.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 and §1.2, Theorem 1 (the factors embed in the amalgam).
-/

public section

namespace Monoid.PushoutI

section Monoid

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Monoid (G i)] [Monoid H]
  {φ : ∀ i, H →* G i} {i : ι}

/-- If the factor `G i` embeds in the pushout of the maps `φ k : H →* G k`, then `φ i` identifies
any two elements of `H` that some map `φ j` identifies: both pairs of images are the images of
the same two elements of `H` in the pushout. -/
theorem apply_eq_apply_of_injective_of (hi : Function.Injective (of (φ := φ) i)) {j : ι}
    {x y : H} (hxy : φ j x = φ j y) : φ i x = φ i y :=
  hi <| by rw [of_apply_eq_base, of_apply_eq_base, ← of_apply_eq_base φ j, hxy, of_apply_eq_base]

/-- If `φ i` is injective and some `φ j` is not, then the factor `G i` does not embed in the
pushout of the maps `φ k : H →* G k`. -/
theorem not_injective_of (hi : Function.Injective (φ i)) {j : ι}
    (hj : ¬ Function.Injective (φ j)) : ¬ Function.Injective (of (φ := φ) i) :=
  fun h => hj fun _ _ hxy => hi (apply_eq_apply_of_injective_of h hxy)

end Monoid

section Group

variable {ι : Type*} {G : ι → Type*} {C : Type*} [∀ i, Group (G i)] [Group C]
  {φ : ∀ i, C →* G i}

/-- An element of a factor centralizing the image of the amalgamating group commutes in the
pushout with every element of the image of the amalgamating group. -/
theorem commute_of_base_of_mem_centralizer {i : ι} {z : G i}
    (hz : z ∈ Subgroup.centralizer (Set.range (φ i))) (c : C) :
    Commute (of (φ := φ) i z) (base φ c) := by
  rw [← of_apply_eq_base φ i]
  exact (Commute.map (Subgroup.mem_centralizer_iff.mp hz (φ i c) ⟨c, rfl⟩) (of i)).symm

end Group

section Amalgamation

universe u v w

/-- The two factors `A` and `B` of an amalgamated product as a `Bool`-indexed family of a common
universe: `A` at `false` and `B` at `true`. -/
private abbrev PairFactor (A : Type u) (B : Type v) (i : Bool) : Type (max u v) :=
  cond i (ULift.{u} B) (ULift.{v} A)

private instance (A : Type u) (B : Type v) [Group A] [Group B] (i : Bool) :
    Group (PairFactor A B i) :=
  Bool.rec (motive := fun i => Group (PairFactor A B i))
    (inferInstanceAs (Group (ULift.{v} A))) (inferInstanceAs (Group (ULift.{u} B))) i

/-- **Amalgamation of groups.** Two injective homomorphisms `φ : C →* A` and `ψ : C →* B` of groups
are completed to a commutative square by two injective homomorphisms `α : A →* P` and
`β : B →* P` into a group `P`, the amalgamated product `A ∗_C B`. -/
theorem exists_injective_comp_eq_comp {A : Type u} {B : Type v} {C : Type w} [Group A] [Group B]
    [Group C] {φ : C →* A} {ψ : C →* B} (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ∃ (P : Type (max u v w)) (_ : Group P) (α : A →* P) (β : B →* P),
      Function.Injective α ∧ Function.Injective β ∧ α.comp φ = β.comp ψ := by
  let χ (i : Bool) : C →* PairFactor A B i := Bool.rec (motive := fun i => C →* PairFactor A B i)
    ((MulEquiv.ulift.symm : A ≃* ULift.{v} A).toMonoidHom.comp φ)
    ((MulEquiv.ulift.symm : B ≃* ULift.{u} B).toMonoidHom.comp ψ) i
  have hχ (i : Bool) : Function.Injective (χ i) := by
    cases i
    · exact MulEquiv.ulift.symm.injective.comp hφ
    · exact MulEquiv.ulift.symm.injective.comp hψ
  refine ⟨PushoutI χ, inferInstance,
    (of (φ := χ) false).comp (MulEquiv.ulift.symm : A ≃* ULift.{v} A).toMonoidHom,
    (of (φ := χ) true).comp (MulEquiv.ulift.symm : B ≃* ULift.{u} B).toMonoidHom,
    (of_injective hχ false).comp MulEquiv.ulift.symm.injective,
    (of_injective hχ true).comp MulEquiv.ulift.symm.injective, ?_⟩
  ext c
  exact (of_apply_eq_base χ false c).trans (of_apply_eq_base χ true c).symm

end Amalgamation

end Monoid.PushoutI
