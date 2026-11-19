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

/-!
# The mass of a groupoid

The **mass** of a category `C` (the groupoid cardinality of its core) is the rational number

  `mass C = ∑_{[x]} 1 / #Aut x`,

the sum running over the isomorphism classes of objects. It is the weighted count of a groupoid in
which every object is counted with the inverse of the order of its automorphism group. The weighted
number of rational points of a stack over a finite field is the mass of its groupoid of points.

The summand is a function of the isomorphism class because an isomorphism `x ≅ y` conjugates
`Aut x` onto `Aut y` (`CategoryTheory.Aut.autMulEquivOfIso`). The definition uses `finsum` and
`Nat.card`, so no finiteness is required to state it: when there are infinitely many classes the
mass is `0` by convention, and an object with infinitely many automorphisms contributes `0`.
Theorems that need finiteness take it as a hypothesis.

## Main declarations

* `TauCeti.groupoidMass`: the mass of a category.
* `TauCeti.groupoidMass_eq_finsum`: the mass is the sum of `1 / #Aut (s i)` over any family `s`
  of objects meeting every isomorphism class exactly once.
* `CategoryTheory.Equivalence.groupoidMass_eq`: equivalent categories have the same mass.
* `TauCeti.groupoidMass_discrete`: a discrete category has mass equal to its number of objects.
* `TauCeti.groupoidMass_singleObj`: the single-object groupoid of a group `G` has mass `1 / #G`.
* `TauCeti.groupoidMass_prod` and `TauCeti.groupoidMass_sum`: masses multiply under products
  and add under disjoint unions.
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
`0` when there are infinitely many classes, and an object with an infinite automorphism group
contributes `0`. -/
noncomputable def groupoidMass : ℚ :=
  ∑ᶠ c : _root_.Quotient (isIsomorphicSetoid C),
    Quotient.lift (s := isIsomorphicSetoid C) (fun x => ((Nat.card (Aut x) : ℚ))⁻¹)
      -- Isomorphic objects have isomorphic automorphism groups.
      (fun _ _ h => by rw [Nat.card_congr (Aut.autMulEquivOfIso h.some).toEquiv]) c

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
    refine ⟨fun a b h => ?_, fun d => _root_.Quotient.inductionOn d fun d => ?_⟩
    · rw [← _root_.Quotient.out_eq a, ← _root_.Quotient.out_eq b]
      exact _root_.Quotient.sound
        ⟨e.fullyFaithfulFunctor.preimageIso (_root_.Quotient.exact h).some⟩
    · exact ⟨⟦e.inverse.obj d⟧, _root_.Quotient.sound ⟨e.functor.mapIso
        (_root_.Quotient.mk_out (s := isIsomorphicSetoid C) _).some ≪≫ e.counitIso.app d⟩⟩
  rw [groupoidMass_eq_finsum _ hs, groupoidMass_eq_finsum_out]
  exact finsum_congr fun c => by
    rw [Nat.card_congr (e.fullyFaithfulFunctor.autMulEquivOfFullyFaithful c.out).toEquiv]

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
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
      nsmul_one]
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

/-- The mass of a product of two categories with finitely many isomorphism classes is the product
of their masses. -/
theorem groupoidMass_prod [Finite (_root_.Quotient (isIsomorphicSetoid C))]
    [Finite (_root_.Quotient (isIsomorphicSetoid D))] :
    groupoidMass (C × D) = groupoidMass C * groupoidMass D := by
  have hs : Bijective fun p : _root_.Quotient (isIsomorphicSetoid C) ×
      _root_.Quotient (isIsomorphicSetoid D) =>
      (⟦(p.1.out, p.2.out)⟧ : _root_.Quotient (isIsomorphicSetoid (C × D))) := by
    refine ⟨fun p q h => ?_, fun z => Quotient.inductionOn z fun z =>
      ⟨(⟦z.1⟧, ⟦z.2⟧), Quotient.sound ⟨?_⟩⟩⟩
    · obtain ⟨e⟩ := Quotient.exact h
      refine Prod.ext ?_ ?_
      · rw [← Quotient.out_eq p.1, ← Quotient.out_eq q.1]
        exact Quotient.sound ⟨(CategoryTheory.Prod.fst C D).mapIso e⟩
      · rw [← Quotient.out_eq p.2, ← Quotient.out_eq q.2]
        exact Quotient.sound ⟨(CategoryTheory.Prod.snd C D).mapIso e⟩
    · exact Iso.prod (Quotient.mk_out (s := isIsomorphicSetoid C) _).some
        (Quotient.mk_out (s := isIsomorphicSetoid D) _).some
  -- An automorphism of a pair is a pair of automorphisms.
  have haut (x : C) (y : D) : Nat.card (Aut (x, y)) = Nat.card (Aut x) * Nat.card (Aut y) := by
    rw [← Nat.card_prod]
    let e : ((x, y) ≅ (x, y)) ≃ (x ≅ x) × (y ≅ y) :=
      { toFun e := ((CategoryTheory.Prod.fst C D).mapIso e, (CategoryTheory.Prod.snd C D).mapIso e)
        invFun p := Iso.prod p.1 p.2
        left_inv _ := by ext <;> rfl
        right_inv _ := by ext <;> rfl }
    exact Nat.card_congr <| Aut.isoEquiv.trans <| e.trans (Aut.isoEquiv.prodCongr Aut.isoEquiv).symm
  rw [groupoidMass_eq_finsum _ hs, groupoidMass_eq_finsum_out, groupoidMass_eq_finsum_out]
  simp_rw [haut, Nat.cast_mul, mul_inv]
  rw [finsum_curry _ (Set.toFinite _), finsum_mul]
  refine finsum_congr fun a => ?_
  rw [mul_finsum]

/-- The mass of a disjoint union of two categories with finitely many isomorphism classes is the
sum of their masses. -/
theorem groupoidMass_sum [Finite (_root_.Quotient (isIsomorphicSetoid C))]
    [Finite (_root_.Quotient (isIsomorphicSetoid D))] :
    groupoidMass (C ⊕ D) = groupoidMass C + groupoidMass D := by
  -- The inclusions of the summands are fully faithful.
  let hl : (Sum.inl_ C D).FullyFaithful := { preimage f := f.down }
  let hr : (Sum.inr_ C D).FullyFaithful := { preimage f := f.down }
  have hs : Bijective fun p : _root_.Quotient (isIsomorphicSetoid C) ⊕
      _root_.Quotient (isIsomorphicSetoid D) =>
      (⟦Sum.elim (fun a => Sum.inl a.out) (fun b => Sum.inr b.out) p⟧ :
        _root_.Quotient (isIsomorphicSetoid (C ⊕ D))) := by
    refine ⟨?_, ?_⟩
    · rintro (a | b) (a' | b') h <;> obtain ⟨e⟩ := Quotient.exact h
      · rw [← Quotient.out_eq a, ← Quotient.out_eq a',
          Quotient.sound (s := isIsomorphicSetoid C)
            ⟨hl.preimageIso (X := a.out) (Y := a'.out) e⟩]
      · exact (hom_inl_inr_false C D (X := a.out) (Y := b'.out) e.hom).elim
      · exact (hom_inr_inl_false D C (X := b.out) (Y := a'.out) e.hom).elim
      · rw [← Quotient.out_eq b, ← Quotient.out_eq b',
          Quotient.sound (s := isIsomorphicSetoid D)
            ⟨hr.preimageIso (X := b.out) (Y := b'.out) e⟩]
    · rintro ⟨x | y⟩
      · exact ⟨Sum.inl ⟦x⟧, Quotient.sound
          ⟨(Sum.inl_ C D).mapIso (Quotient.mk_out (s := isIsomorphicSetoid C) x).some⟩⟩
      · exact ⟨Sum.inr ⟦y⟧, Quotient.sound
          ⟨(Sum.inr_ C D).mapIso (Quotient.mk_out (s := isIsomorphicSetoid D) y).some⟩⟩
  rw [groupoidMass_eq_finsum _ hs, finsum_sum_type _ (Set.toFinite _) (Set.toFinite _),
    groupoidMass_eq_finsum_out, groupoidMass_eq_finsum_out]
  congr 1
  · exact finsum_congr fun a => by
      rw [Sum.elim_inl, Nat.card_congr (hl.autMulEquivOfFullyFaithful a.out).toEquiv,
        Sum.inl__obj]
  · exact finsum_congr fun b => by
      rw [Sum.elim_inr, Nat.card_congr (hr.autMulEquivOfFullyFaithful b.out).toEquiv,
        Sum.inr__obj]

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
