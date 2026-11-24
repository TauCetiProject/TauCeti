/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Hom.Monoid
public import TauCeti.Algebra.Order.Group.DimensionGroup.Scale
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Pi

/-!
# Order units of preordered additive monoids and groups

An *order unit* (with respect to natural-number multiples) of a preordered additive monoid `G` is a
nonnegative element `u` such that every element `g : G` satisfies `g ≤ n • u` for some `n : ℕ`.
In a preordered abelian group `G`, an element `u ≥ 0` is an order unit iff `-(n • u) ≤ g ≤ n • u`
holds for every `g : G` (for some `n : ℕ`); admitting an order unit forces `G` to be upward
directed, and in a directed interpolation group `[0, u]` is a scale iff `u` is an order unit
(`isScale_Icc_iff_isNatOrderUnit`).

## Main definitions

* `TauCeti.IsNatOrderUnit u`: `0 ≤ u` and every element `g` lies below `n • u` for some
  `n : ℕ`.

## Main results

* `TauCeti.IsNatOrderUnit.exists_neg_nsmul_le_le_nsmul`: symmetric intervals `[-n • u, n • u]`.
* `TauCeti.IsNatOrderUnit.isDirectedOrder`: a preordered commutative ordered monoid with an
  order unit is upward directed.
* `TauCeti.isNatOrderUnit_iff_forall_nonneg_exists_le_nsmul`: in a directed group or monoid, it
  suffices to dominate nonnegative elements.
* `TauCeti.isNatOrderUnit_iff_pos`: in a nontrivial Archimedean partially ordered abelian group,
  `IsNatOrderUnit u ↔ 0 < u`.
* `TauCeti.IsNatOrderUnit.map`: surjective monotone homomorphisms preserve order units.
* `TauCeti.isNatOrderUnit_int_iff` and `TauCeti.isNatOrderUnit_pi_iff`: characterizations on `ℤ`
  and finite products.
* `TauCeti.isScale_Icc_iff_isNatOrderUnit`: `[0, u]` is a scale iff `u` is an order unit, under
  Riesz interpolation and directedness.

## References

* K. R. Goodearl, *Partially ordered abelian groups with interpolation*, Mathematical Surveys
  and Monographs 20, AMS, 1986, Chapter 1, §1.
* M. Rørdam, *Classification of nuclear C⋆-algebras*, Encyclopaedia of Mathematical Sciences
  126, Springer, 2002, §1.4.
-/

public section

namespace TauCeti

section Defs

variable {G : Type*} [AddMonoid G] [LE G]

/-- An *order unit* (by `ℕ`-multiples) of a preordered additive monoid `G` is a nonnegative
element `u` such that every `g : G` satisfies `g ≤ n • u` for some `n : ℕ`. -/
structure IsNatOrderUnit (u : G) : Prop where
  /-- An order unit is nonnegative. -/
  nonneg : 0 ≤ u
  /-- Every element lies below a natural multiple of the order unit. -/
  exists_le_nsmul (g : G) : ∃ n : ℕ, g ≤ n • u

/-- Unfolding lemma for `IsNatOrderUnit`. -/
theorem isNatOrderUnit_iff {u : G} :
    IsNatOrderUnit u ↔ 0 ≤ u ∧ ∀ g : G, ∃ n : ℕ, g ≤ n • u :=
  ⟨fun h ↦ ⟨h.nonneg, h.exists_le_nsmul⟩, fun ⟨h0, h⟩ ↦ ⟨h0, h⟩⟩

end Defs

namespace IsNatOrderUnit

section AddCommMonoid

variable {G : Type*} [AddCommMonoid G] [Preorder G] [IsOrderedAddMonoid G] {u v : G}

/-- A preordered commutative ordered monoid admitting an order unit is upward directed. -/
theorem isDirectedOrder (hu : IsNatOrderUnit u) : IsDirectedOrder G where
  directed a b := by
    obtain ⟨m, hm⟩ := hu.exists_le_nsmul a
    obtain ⟨n, hn⟩ := hu.exists_le_nsmul b
    exact ⟨(max m n) • u,
      hm.trans (nsmul_le_nsmul_left hu.nonneg (le_max_left m n)),
      hn.trans (nsmul_le_nsmul_left hu.nonneg (le_max_right m n))⟩

/-- Any element above an order unit is an order unit. -/
theorem of_le (hu : IsNatOrderUnit u) (huv : u ≤ v) : IsNatOrderUnit v where
  nonneg := hu.nonneg.trans huv
  exists_le_nsmul g := by
    obtain ⟨n, hn⟩ := hu.exists_le_nsmul g
    exact ⟨n, hn.trans (nsmul_le_nsmul_right huv n)⟩

/-- Any nonnegative element some multiple of which dominates an order unit is itself an order
unit. -/
theorem of_le_nsmul (hv : IsNatOrderUnit v) (hu0 : 0 ≤ u) {n : ℕ} (hvn : v ≤ n • u) :
    IsNatOrderUnit u where
  nonneg := hu0
  exists_le_nsmul g := by
    obtain ⟨m, hm⟩ := hv.exists_le_nsmul g
    refine ⟨m * n, hm.trans ?_⟩
    rw [mul_comm, mul_nsmul]
    exact nsmul_le_nsmul_right hvn m

/-- A positive natural multiple of an order unit is an order unit. -/
theorem nsmul (hu : IsNatOrderUnit u) {n : ℕ} (hn : n ≠ 0) : IsNatOrderUnit (n • u) :=
  hu.of_le (le_self_nsmul hu.nonneg hn)

/-- Adding a nonnegative element on the left preserves order units. -/
theorem add_left (hu : IsNatOrderUnit u) (hv : 0 ≤ v) : IsNatOrderUnit (v + u) :=
  hu.of_le (le_add_of_nonneg_left hv)

/-- Adding a nonnegative element on the right preserves order units. -/
theorem add_right (hu : IsNatOrderUnit u) (hv : 0 ≤ v) : IsNatOrderUnit (u + v) :=
  hu.of_le (le_add_of_nonneg_right hv)

end AddCommMonoid

section Directed

variable {G : Type*} [AddMonoid G] [Preorder G] [IsDirectedOrder G]

/-- In an upward-directed preordered additive monoid, a nonnegative element is an order unit
exactly when it dominates every nonnegative element up to a natural multiple. -/
theorem _root_.TauCeti.isNatOrderUnit_iff_forall_nonneg_exists_le_nsmul {u : G} :
    IsNatOrderUnit u ↔ 0 ≤ u ∧ ∀ ⦃g : G⦄, 0 ≤ g → ∃ n : ℕ, g ≤ n • u := by
  refine ⟨fun hu ↦ ⟨hu.nonneg, fun g _ ↦ hu.exists_le_nsmul g⟩,
    fun ⟨hu0, hdom⟩ ↦ ⟨hu0, fun g ↦ ?_⟩⟩
  obtain ⟨c, hc0, hgc⟩ := exists_ge_ge (0 : G) g
  obtain ⟨n, hn⟩ := hdom hc0
  exact ⟨n, hgc.trans hn⟩

end Directed

section AddCommGroup

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G] {u : G}

/-- In a preordered abelian group, an order unit `u` bounds every element from both sides:
`-(n • u) ≤ g ≤ n • u` for some `n : ℕ`. -/
theorem exists_neg_nsmul_le_le_nsmul (hu : IsNatOrderUnit u) (g : G) :
    ∃ n : ℕ, -(n • u) ≤ g ∧ g ≤ n • u := by
  obtain ⟨m, hm⟩ := hu.exists_le_nsmul (-g)
  obtain ⟨n, hn⟩ := hu.exists_le_nsmul g
  refine ⟨max m n, ?_, hn.trans (nsmul_le_nsmul_left hu.nonneg (le_max_right m n))⟩
  have hm' : -(m • u) ≤ g := neg_le.1 hm
  have hmax : -((max m n) • u) ≤ -(m • u) :=
    neg_le_neg_iff.2 (nsmul_le_nsmul_left hu.nonneg (le_max_left m n))
  exact hmax.trans hm'

/-- Characterization of order units in a preordered abelian group via symmetric intervals. -/
theorem _root_.TauCeti.isNatOrderUnit_iff_exists_neg_nsmul_le_le_nsmul {u : G} :
    IsNatOrderUnit u ↔ 0 ≤ u ∧ ∀ g : G, ∃ n : ℕ, -(n • u) ≤ g ∧ g ≤ n • u :=
  ⟨fun hu ↦ ⟨hu.nonneg, hu.exists_neg_nsmul_le_le_nsmul⟩,
    fun ⟨hu0, h⟩ ↦ ⟨hu0, fun g ↦ (h g).imp fun _ hn ↦ hn.2⟩⟩

end AddCommGroup

section PartialOrder

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- `0` is an order unit of a partially ordered abelian group iff the group is trivial. -/
theorem _root_.TauCeti.isNatOrderUnit_zero_iff :
    IsNatOrderUnit (0 : G) ↔ Subsingleton G := by
  refine ⟨fun h0 ↦ ⟨fun a b ↦ ?_⟩, fun _ ↦ ⟨le_rfl, fun _ ↦ ⟨0, by simp⟩⟩⟩
  have hle : ∀ g : G, g ≤ 0 := fun g ↦ by
    obtain ⟨n, hn⟩ := h0.exists_le_nsmul g
    simpa using hn
  have hzero : ∀ g : G, g = 0 := fun g ↦ le_antisymm (hle g) (neg_nonpos.1 (hle (-g)))
  rw [hzero a, hzero b]

/-- In a nontrivial partially ordered abelian group, every order unit is strictly positive. -/
theorem pos [Nontrivial G] {u : G} (hu : IsNatOrderUnit u) : 0 < u :=
  lt_of_le_of_ne hu.nonneg fun h ↦ not_subsingleton G <|
    isNatOrderUnit_zero_iff.1 (h ▸ hu)

/-- In a nontrivial Archimedean partially ordered abelian group, an element is an order unit iff
it is strictly positive. -/
theorem _root_.TauCeti.isNatOrderUnit_iff_pos [Archimedean G] [Nontrivial G] {u : G} :
    IsNatOrderUnit u ↔ 0 < u :=
  ⟨IsNatOrderUnit.pos, fun h ↦ ⟨h.le, fun g ↦ Archimedean.arch g h⟩⟩

end PartialOrder

section Hom

variable {G H : Type*} [AddMonoid G] [Preorder G] [AddMonoid H] [Preorder H]

/-- A surjective monotone additive homomorphism sends order units to order units. -/
theorem map {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] [OrderHomClass F G H]
    {u : G} (hu : IsNatOrderUnit u) (f : F) (hf : Function.Surjective f) :
    IsNatOrderUnit (f u) where
  nonneg := map_zero f ▸ OrderHomClass.mono f hu.nonneg
  exists_le_nsmul h := by
    obtain ⟨g, rfl⟩ := hf h
    obtain ⟨n, hn⟩ := hu.exists_le_nsmul g
    exact ⟨n, (OrderHomClass.mono f hn).trans_eq (map_nsmul f n u)⟩

end Hom

end IsNatOrderUnit

end TauCeti

section Iso

variable {G H : Type*} [AddMonoid G] [Preorder G] [AddMonoid H] [Preorder H]

/-- An ordered additive isomorphism preserves and reflects order units. -/
@[simp]
theorem OrderAddMonoidIso.isNatOrderUnit_map_iff (e : G ≃+o H) {u : G} :
    TauCeti.IsNatOrderUnit (e u) ↔ TauCeti.IsNatOrderUnit u :=
  ⟨fun he ↦ by simpa using he.map e.symm e.symm.surjective,
    fun hu ↦ hu.map e e.surjective⟩

end Iso

namespace TauCeti

section Examples

/-- In `ℤ`, an integer is an order unit iff it is strictly positive. -/
@[simp]
theorem isNatOrderUnit_int_iff {u : ℤ} : IsNatOrderUnit u ↔ 0 < u :=
  isNatOrderUnit_iff_pos

/-- In a finite product of ordered additive monoids, a family is an order unit iff each
component is an order unit. -/
theorem isNatOrderUnit_pi_iff {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, AddCommMonoid (G i)] [∀ i, Preorder (G i)] [∀ i, IsOrderedAddMonoid (G i)]
    {u : ∀ i, G i} : IsNatOrderUnit u ↔ ∀ i, IsNatOrderUnit (u i) := by
  refine ⟨fun hu i ↦ ⟨hu.nonneg i, fun x ↦ ?_⟩,
    fun hu ↦ ⟨fun i ↦ (hu i).nonneg, fun g ↦ ?_⟩⟩
  · classical
    obtain ⟨n, hn⟩ := hu.exists_le_nsmul (Pi.single i x)
    exact ⟨n, by simpa using hn i⟩
  · cases nonempty_fintype ι
    choose n hn using fun i ↦ (hu i).exists_le_nsmul (g i)
    refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
    exact (hn i).trans (nsmul_le_nsmul_left (hu i).nonneg (Finset.le_sup (Finset.mem_univ i)))

/-- In an interpolation group, `[0, u]` is a scale for every order unit `u`. -/
theorem IsNatOrderUnit.isScale_Icc {G : Type*} [AddCommGroup G] [Preorder G]
    [IsOrderedAddMonoid G] (h : HasRieszInterpolation G) {u : G} (hu : IsNatOrderUnit u) :
    IsScale (Set.Icc 0 u) :=
  (isScale_Icc_iff h).2 ⟨hu.nonneg, fun _ _ ↦ hu.exists_le_nsmul _⟩

/-- In a directed interpolation group, `[0, u]` is a scale iff `u` is an order unit. -/
theorem isScale_Icc_iff_isNatOrderUnit {G : Type*} [AddCommGroup G] [Preorder G]
    [IsOrderedAddMonoid G] (h : HasRieszInterpolation G) [IsDirectedOrder G] {u : G} :
    IsScale (Set.Icc 0 u) ↔ IsNatOrderUnit u :=
  (isScale_Icc_iff h).trans isNatOrderUnit_iff_forall_nonneg_exists_le_nsmul.symm

end Examples

end TauCeti
