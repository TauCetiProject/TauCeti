/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Rat
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Sums.Basic
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.CategoryTheory.Aut.Basic
import TauCeti.CategoryTheory.IsomorphismClasses
import TauCeti.CategoryTheory.Products.Basic

/-!
# The mass of a groupoid

The **mass** of a category `C` (the groupoid cardinality of its core) is the rational number

  `mass C = ∑_{[x]} 1 / #Aut x`,

the sum running over the isomorphism classes of objects. It is the weighted count of a groupoid in
which every object is counted with the inverse of the order of its automorphism group. The weighted
number of rational points of a stack over a finite field is the mass of its groupoid of points.

The summand is a function of the isomorphism class because an isomorphism `x ≅ y` conjugates
`Aut x` onto `Aut y` (`CategoryTheory.Aut.autMulEquivOfIso`). The definition uses `finsum` and
`Nat.card`, so no finiteness is required to state it: an object with infinitely many
automorphisms contributes `0`, and when infinitely many classes have finite automorphism groups
(so the sum has infinite support) the mass is `0` by convention. Theorems that need finiteness take
it as a hypothesis.

## Main declarations

* `TauCeti.groupoidMass`: the mass of a category.
* `TauCeti.groupoidMass_eq_finsum`: the mass is the sum of `1 / #Aut (s i)` over any family `s`
  of objects meeting every isomorphism class exactly once.
* `CategoryTheory.Equivalence.groupoidMass_eq`: equivalent categories have the same mass.
* `TauCeti.groupoidMass_discrete`: a discrete category has mass equal to its number of objects.
* `TauCeti.groupoidMass_singleObj`: the single-object groupoid of a group `G` has mass `1 / #G`.
* `TauCeti.groupoidMass_prod`: masses multiply under products, with no finiteness hypotheses.
* `TauCeti.groupoidMass_sum`: masses add under disjoint unions of categories with finitely many
  isomorphism classes.
* `TauCeti.groupoidMass_actionCategory`: for a finite group `G` acting on a type `Y`,
  the action groupoid has mass `#Y / #G`, whether or not the action is free.
* `TauCeti.groupoidMass_nonneg`: masses are nonnegative.

## References

* J. Bergström, C. Faber, S. Payne, *Polynomial point counts and odd cohomology vanishing on
  moduli spaces of stable curves*, Ann. of Math. (2) 199 (2024), §1, the weighted count
  preceding Proposition 1.3.
* J. C. Baez, J. Dolan, *From finite sets to Feynman diagrams*, in Mathematics Unlimited — 2001
  and Beyond, Springer (2001), for groupoid cardinality.
-/

public section

open CategoryTheory Function

universe v₁ v₂ u₁ u₂

namespace TauCeti

variable (C : Type u₁) [Category.{v₁} C]

/-- The **mass** of a category: the sum, over the isomorphism classes of objects, of the inverse
of the order of the automorphism group of a representative.

When `C` has finitely many isomorphism classes and finite automorphism groups this is the
groupoid cardinality `∑_{[x]} 1 / #Aut x`. Without these finiteness conditions it is a junk value:
an object with an infinite automorphism group contributes `0`, and the mass is `0` when infinitely
many isomorphism classes have finite automorphism groups (the sum has infinite support). -/
noncomputable def groupoidMass : ℚ :=
  ∑ᶠ c : _root_.Quotient (isIsomorphicSetoid C),
    Quotient.lift (s := isIsomorphicSetoid C) (fun x => ((Nat.card (Aut x) : ℚ))⁻¹)
      (fun _ _ h => by rw [h.some.natCard_aut_eq]) c

variable {C}

/-- The mass is the sum of `1 / #Aut (s i)` over any family `s` of objects which meets every
isomorphism class exactly once. -/
theorem groupoidMass_eq_finsum {ι : Type*} (s : ι → C)
    (hs : Bijective fun i => (⟦s i⟧ : _root_.Quotient (isIsomorphicSetoid C))) :
    groupoidMass C = ∑ᶠ i, ((Nat.card (Aut (s i)) : ℚ))⁻¹ := by
  rw [groupoidMass, ← finsum_comp_equiv (Equiv.ofBijective _ hs)]
  simp only [Equiv.ofBijective_apply, Quotient.lift_mk]

/-- The mass is the sum of `1 / #Aut x` over chosen representatives `x` of the isomorphism
classes. -/
theorem groupoidMass_eq_finsum_out :
    groupoidMass C = ∑ᶠ c : _root_.Quotient (isIsomorphicSetoid C),
      ((Nat.card (Aut c.out) : ℚ))⁻¹ :=
  groupoidMass_eq_finsum Quotient.out (by convert bijective_id; exact Quotient.out_eq _)

variable (C) in
/-- The mass of a category is nonnegative. -/
theorem groupoidMass_nonneg : 0 ≤ groupoidMass C := by
  rw [groupoidMass_eq_finsum_out]
  exact finsum_nonneg fun _ => by positivity

end TauCeti

namespace CategoryTheory.Equivalence

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Equivalent categories have the same mass: an equivalence induces a bijection on isomorphism
classes and isomorphisms of automorphism groups. -/
theorem groupoidMass_eq (e : C ≌ D) : groupoidMass C = groupoidMass D := by
  have hs : Bijective fun c : _root_.Quotient (isIsomorphicSetoid C) =>
      (⟦e.functor.obj c.out⟧ : _root_.Quotient (isIsomorphicSetoid D)) := by
    convert e.isomorphismClassesEquiv.bijective with c
    rw [← isomorphismClassesEquiv_mk, Quotient.out_eq]
  rw [groupoidMass_eq_finsum _ hs, groupoidMass_eq_finsum_out]
  exact finsum_congr fun c => by rw [e.fullyFaithfulFunctor.natCard_aut_obj]

end CategoryTheory.Equivalence

namespace TauCeti

/-- A discrete category has mass equal to its number of objects. With the junk value conventions
of `groupoidMass` and `Nat.card`, both sides vanish for an infinite type. -/
@[simp]
theorem groupoidMass_discrete (α : Type u₁) : groupoidMass (Discrete α) = Nat.card α := by
  have hs : Bijective fun a : α =>
      (⟦Discrete.mk a⟧ : _root_.Quotient (isIsomorphicSetoid (Discrete α))) :=
    ⟨fun a b h => Discrete.eq_of_hom (Quotient.exact h).some.hom,
      fun c => Quotient.inductionOn c fun x => ⟨x.as, rfl⟩⟩
  have haut (a : α) : Nat.card (Aut (Discrete.mk a)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨Aut.isoEquiv.subsingleton, ⟨1⟩⟩
  rw [groupoidMass_eq_finsum _ hs]
  simp only [haut, Nat.cast_one, inv_one]
  cases finite_or_infinite α
  · have := Fintype.ofFinite α
    simp [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  · rw [finsum_of_infinite_support (by rw [support_const one_ne_zero]; exact Set.infinite_univ),
      Nat.card_eq_zero_of_infinite (α := α), Nat.cast_zero]

/-- The single-object category of a monoid `M` has mass `1 / #Mˣ`: its one object has
automorphism group the units of `M`. -/
theorem groupoidMass_singleObj_units (M : Type u₁) [Monoid M] :
    groupoidMass (SingleObj M) = ((Nat.card Mˣ : ℚ))⁻¹ := by
  have hs : Bijective fun _ : Unit =>
      (⟦SingleObj.star M⟧ : _root_.Quotient (isIsomorphicSetoid (SingleObj M))) :=
    ⟨fun _ _ _ => rfl, fun c => Quotient.inductionOn c fun _ => ⟨(), rfl⟩⟩
  rw [groupoidMass_eq_finsum _ hs, finsum_unique, Nat.card_congr (Units.toAut M).toEquiv.symm]

/-- The single-object groupoid of a group `G` has mass `1 / #G`. -/
@[simp]
theorem groupoidMass_singleObj (G : Type u₁) [Group G] :
    groupoidMass (SingleObj G) = ((Nat.card G : ℚ))⁻¹ := by
  rw [groupoidMass_singleObj_units, Nat.card_congr toUnits.toEquiv.symm]

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The mass of a product of two categories is the product of their masses. No finiteness is
needed: when one factor's sum has infinite support and the other's is nonempty, so does the sum
for the product, and both sides are `0`. -/
@[simp]
theorem groupoidMass_prod : groupoidMass (C × D) = groupoidMass C * groupoidMass D := by
  have hs : Bijective fun p : _root_.Quotient (isIsomorphicSetoid C) ×
      _root_.Quotient (isIsomorphicSetoid D) =>
      (⟦(p.1.out, p.2.out)⟧ : _root_.Quotient (isIsomorphicSetoid (C × D))) := by
    convert (CategoryTheory.Prod.isomorphismClassesEquiv C D).symm.bijective with p
    rw [CategoryTheory.Prod.isomorphismClassesEquiv_symm_apply]
  rw [groupoidMass_eq_finsum _ hs, groupoidMass_eq_finsum_out, groupoidMass_eq_finsum_out,
    finsum_mul_finsum]
  simp_rw [natCard_aut_prod, Nat.cast_mul, mul_inv]

/-- The mass of a disjoint union of two categories with finitely many isomorphism classes is the
sum of their masses. -/
theorem groupoidMass_sum [Finite (_root_.Quotient (isIsomorphicSetoid C))]
    [Finite (_root_.Quotient (isIsomorphicSetoid D))] :
    groupoidMass (C ⊕ D) = groupoidMass C + groupoidMass D := by
  have hs : Bijective fun p : _root_.Quotient (isIsomorphicSetoid C) ⊕
      _root_.Quotient (isIsomorphicSetoid D) =>
      (⟦p.elim (fun a => _root_.Sum.inl a.out) (fun b => _root_.Sum.inr b.out)⟧ :
        _root_.Quotient (isIsomorphicSetoid (C ⊕ D))) := by
    convert (CategoryTheory.Sum.isomorphismClassesEquiv C D).symm.bijective with p
    rcases p with a | b <;> simp
  rw [groupoidMass_eq_finsum _ hs, finsum_sum_type _ (Set.toFinite _) (Set.toFinite _),
    groupoidMass_eq_finsum_out, groupoidMass_eq_finsum_out]
  congr 1
  · exact finsum_congr fun a => congrArg (fun n : ℕ => (n : ℚ)⁻¹)
      ((Sum.fullyFaithfulInl C D).natCard_aut_obj a.out)
  · exact finsum_congr fun b => congrArg (fun n : ℕ => (n : ℚ)⁻¹)
      ((Sum.fullyFaithfulInr C D).natCard_aut_obj b.out)

/-- **Orbit–stabilizer for masses.** For a finite group `G` acting on a type `Y`, the action
groupoid `G ⋉ Y` has mass `#Y / #G`. The action need not be free: the orbit of a point
with stabilizer `H` is one isomorphism class, contributing `1 / #H`, and it has `#G / #H` points.
When `Y` is infinite there are infinitely many orbits, and both sides are `0` by the junk value
conventions of `groupoidMass` and `Nat.card`. -/
theorem groupoidMass_actionCategory (G : Type u₁) (Y : Type u₂) [Group G] [MulAction G Y]
    [Finite G] : groupoidMass (ActionCategory G Y) = Nat.card Y / Nat.card G := by
  have hs : Bijective fun ω : MulAction.orbitRel.Quotient G Y =>
      (⟦ActionCategory.objEquiv G Y ω.out⟧ :
        _root_.Quotient (isIsomorphicSetoid (ActionCategory G Y))) := by
    convert (ActionCategory.orbitQuotientEquivIsomorphismClasses G Y).bijective with ω
    rw [← ActionCategory.orbitQuotientEquivIsomorphismClasses_mk]
    exact congrArg _ ω.out_eq
  have (y : Y) : Finite (MulAction.orbit G y) := (Finite.finite_mulAction_orbit y).to_subtype
  have (y : Y) : Nonempty (MulAction.orbit G y) := ⟨⟨y, MulAction.mem_orbit_self y⟩⟩
  -- Orbit–stabilizer: `1 / #Stab(y) = #(G • y) / #G`.
  have hstab (y : Y) : ((Nat.card (Aut (ActionCategory.objEquiv G Y y)) : ℚ))⁻¹ =
      Nat.card (MulAction.orbit G y) / Nat.card G := by
    rw [← Nat.card_congr (ActionCategory.stabilizerMulEquivAut G y).toEquiv,
      ← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G y), Nat.card_prod, Nat.cast_mul,
      div_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
  rw [groupoidMass_eq_finsum _ hs]
  simp_rw [hstab]
  -- With finitely many orbits, `Y` is their disjoint union; otherwise `Y` is infinite.
  cases finite_or_infinite (MulAction.orbitRel.Quotient G Y)
  · have := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_div,
      Nat.card_congr (MulAction.selfEquivSigmaOrbits G Y), Nat.card_sigma, Nat.cast_sum]
  · have : Infinite Y :=
      Infinite.of_surjective _ (Quotient.mk_surjective (s := MulAction.orbitRel G Y))
    rw [finsum_of_infinite_support, Nat.card_eq_zero_of_infinite (α := Y), Nat.cast_zero,
      zero_div]
    convert Set.infinite_univ (α := MulAction.orbitRel.Quotient G Y)
    exact Set.eq_univ_of_forall fun ω => div_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end TauCeti
