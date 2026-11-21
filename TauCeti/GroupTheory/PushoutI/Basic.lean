/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import TauCeti.Algebra.Group.Subgroup.ZPowers

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
property of the class of groups. For instance, for `n ≠ 0` every element `g` of a group `G` becomes
an `n`-th power in some group containing `G`: in the dihedral group of order `2 · n · orderOf g`,
the power `rⁿ` of the rotation `r` of order `n · orderOf g` has the order of `g`, and `G` embeds in
its amalgam with that dihedral group along `g = rⁿ`. For `n = 2`, `r² = ⁅r, s⁆` with a reflection
`s`, so `g` also becomes a commutator.

## Main results

* `Monoid.PushoutI.apply_eq_apply_of_injective_of`: if `G i` embeds in the pushout, then `φ i`
  identifies every pair of elements identified by some `φ j`.
* `Monoid.PushoutI.not_injective_of`: if `φ i` is injective and `φ j` is not, then `G i` does not
  embed in the pushout.
* `Monoid.PushoutI.commute_of_base_of_mem_centralizer`: an element of a factor centralizing the
  image of `C` commutes with the image of `C` in the pushout.
* `Monoid.PushoutI.exists_injective_comp_eq_comp`: two injective homomorphisms out of a group `C`
  are completed to a commutative square of injective homomorphisms.
* `Monoid.PushoutI.exists_injective_pow_eq`: for `n ≠ 0`, every element of a group is an `n`-th
  power in some group containing it.
* `Monoid.PushoutI.exists_injective_commutatorElement_eq`: every element of a group is a
  commutator in some group containing it.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 and §1.2, Theorem 1 (the factors embed in the amalgam).
* B. H. Neumann, *Adjunction of elements to groups*, J. London Math. Soc. 18 (1943), 4–11
  (adjoining roots of elements by amalgamated products).
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

open DihedralGroup Subgroup

open scoped commutatorElement

/-- For `n ≠ 0`, a group `G` embeds in a group `P` that receives the dihedral group of order
`2 · n · orderOf g` by a homomorphism sending `rⁿ` to `g`, where `r` is the rotation `r 1`, of
order `n · orderOf g`: the amalgamated product of `G` and the dihedral group along `g = rⁿ`. -/
private theorem exists_injective_dihedral {G : Type u} [Group G] {n : ℕ} (hn : n ≠ 0) (g : G) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P) (β : DihedralGroup (n * orderOf g) →* P),
      Function.Injective ι ∧ β (r 1 ^ n) = ι g := by
  have hord : orderOf g = orderOf (r 1 ^ n : DihedralGroup (n * orderOf g)) := by
    rw [orderOf_pow' _ hn, orderOf_r_one, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  -- the embedding `⟨g⟩ →* D`, `g ↦ rⁿ`
  let ψ := (zpowers _).subtype.comp (zpowersMulEquivOfOrderOfEq hord).toMonoidHom
  have hψ : Function.Injective ψ := (zpowers _).subtype_injective.comp (MulEquiv.injective _)
  obtain ⟨P, _, α, β, hα, -, h⟩ := exists_injective_comp_eq_comp (zpowers g).subtype_injective hψ
  exact ⟨P, _, α, β, hα, by simpa [ψ] using (DFunLike.congr_fun h ⟨g, mem_zpowers g⟩).symm⟩

/-- For `n ≠ 0`, every element of a group `G` is an `n`-th power in a group containing `G`:
`g = rⁿ` in the amalgamated product of `G` and a dihedral group along `g = rⁿ`. -/
theorem exists_injective_pow_eq {G : Type u} [Group G] {n : ℕ} (hn : n ≠ 0) (g : G) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Function.Injective ι ∧ ∃ a : P, a ^ n = ι g := by
  obtain ⟨P, _, ι, β, hι, h⟩ := exists_injective_dihedral hn g
  exact ⟨P, _, ι, hι, β (r 1), by rw [← map_pow, h]⟩

/-- Every element of a group `G` is a commutator in a group containing `G`: `g = r² = ⁅r, s⁆` in
the amalgamated product of `G` and a dihedral group along `g = r²`, where `s` is a reflection. -/
theorem exists_injective_commutatorElement_eq {G : Type u} [Group G] (g : G) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Function.Injective ι ∧ ∃ a b : P, ⁅a, b⁆ = ι g := by
  obtain ⟨P, _, ι, β, hι, h⟩ := exists_injective_dihedral two_ne_zero g
  have hrs : ⁅(r 1 : DihedralGroup (2 * orderOf g)), (sr 0 : DihedralGroup (2 * orderOf g))⁆ =
      r 1 ^ 2 := by
    simp only [commutatorElement_def, inv_r, inv_sr, r_mul_sr, sr_mul_r, sr_mul_sr, sq, r_mul_r]
    congr 1
    ring
  exact ⟨P, _, ι, hι, β (r 1), β (sr 0), by rw [← map_commutatorElement, hrs, h]⟩

end Amalgamation

end Monoid.PushoutI
