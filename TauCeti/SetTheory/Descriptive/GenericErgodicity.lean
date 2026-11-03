/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Transitive
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Baire.BaireMeasurable

/-!
# Generic ergodicity

An equivalence relation on a topological space is *generically ergodic* when every invariant set
with the Baire property is meagre or comeagre. This file proves the standard source of generic
ergodicity and its main consequence.

* **Topologically transitive actions.** If a countable group acts by homeomorphisms and
  topologically transitively, every invariant set with the Baire property is meagre or comeagre.
  Such a set agrees with an open set `U` up to a meagre set. If `U` is nonempty, the translates
  of `U` cover a dense open set, and since the set is invariant, it agrees with each translate of
  `U` up to a meagre set; so its complement is meagre. In particular, the cosets of a countable
  dense subgroup of a group with continuous multiplication (for the Vitali relation, the cosets
  of `ℚ` in `ℝ`) form a generically ergodic equivalence relation.
* **Non-smoothness.** On a nonempty Baire space, an equivalence relation with meagre classes for
  which the preimages of the measurable sets of the quotient σ-algebra are meagre or comeagre has a
  quotient that is not countably separated: no countable family of invariant measurable sets
  separates its classes. Countably many such sets are simultaneously constant on one comeagre
  set, which then lies in a single class, while classes are meagre.

## Main results

* `MulAction.isMeagre_or_mem_residual_of_orbitRel_invariant`: generic ergodicity of the orbit
  relation of a countable group acting topologically transitively by homeomorphisms.
* `QuotientGroup.isMeagre_or_mem_residual_of_leftRel_invariant`: generic ergodicity of the
  relation of lying in the same left coset of a countable dense subgroup.
* `Setoid.not_countablySeparated_quotient_of_isMeagre_or_mem_residual`: an equivalence relation
  with meagre classes on a nonempty Baire space, for which the preimage of every measurable set of
  the quotient σ-algebra is meagre or comeagre, has a quotient that is not countably separated.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 8.46 (generic ergodicity of topologically transitive actions).
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Section 6.1 (generically
  ergodic relations with meagre classes are not smooth).
-/

public section

open Filter MeasurableSpace Set Topology
open scoped Pointwise

variable {X : Type*} [TopologicalSpace X]

namespace MulAction

variable {G : Type*} [Group G] [Countable G] [MulAction G X] [ContinuousConstSMul G X]
  [IsTopologicallyTransitive G X] {B : Set X}

/-- **Generic ergodicity of topologically transitive actions.** If a countable group acts by
homeomorphisms and topologically transitively, every invariant set with the Baire property is
meagre or comeagre. -/
@[to_additive /-- **Generic ergodicity of topologically transitive actions.** If a countable
additive group acts by homeomorphisms and topologically transitively, every invariant set with the
Baire property is meagre or comeagre. -/]
theorem isMeagre_or_mem_residual_of_orbitRel_invariant (hB : BaireMeasurableSet B)
    (hinv : Quotient.mk (orbitRel G X) ⁻¹' (Quotient.mk (orbitRel G X) '' B) = B) :
    IsMeagre B ∨ B ∈ residual X := by
  obtain ⟨U, hUo, hBU⟩ := hB.residualEq_isOpen
  have hUB : IsMeagre (U \ B) :=
    mem_of_superset hBU.mem_iff fun x hx hxUB => hxUB.2 (hx.2 hxUB.1)
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · exact .inl <| mem_of_superset hBU.mem_iff fun x hx hxB => hx.1 hxB
  refine .inr ?_
  -- The translates of `U` cover a dense open set, and `B` contains each of them up to the meagre
  -- translate of `U \ B`.
  have hV : ⋃ g : G, g • U ∈ residual X :=
    residual_of_dense_open (isOpen_iUnion fun g => hUo.smul g) (hUo.dense_iUnion_smul G hUne)
  have htr : ∀ g : G, IsMeagre (g • (U \ B)) := fun g => by
    rw [← preimage_smul_inv]
    exact hUB.preimage_of_isOpenMap (continuous_const_smul _) (isOpenMap_smul _)
  refine mem_of_superset (inter_mem hV (countable_iInter_mem.2 htr)) ?_
  rintro y ⟨hyV, hy⟩
  obtain ⟨g, u, hu, rfl⟩ := mem_iUnion.1 hyV
  by_contra hyB
  refine mem_iInter.1 hy g (smul_mem_smul_set ⟨hu, fun huB => hyB ?_⟩)
  rw [← hinv]
  exact ⟨u, huB, (Quotient.sound (mem_orbit u g)).symm⟩

end MulAction

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {H : Subgroup G}
  [Countable H] {B : Set G}

/-- **Generic ergodicity of the cosets of a countable dense subgroup.** If `H` is a countable
dense subgroup of a group `G` with continuous multiplication, every set with the Baire property
that is a union of left cosets of `H` is meagre or comeagre. -/
@[to_additive /-- **Generic ergodicity of the cosets of a countable dense subgroup.** If `H` is a
countable dense subgroup of an additive group `G` with continuous addition, every set with the
Baire property that is a union of left cosets of `H` is meagre or comeagre. -/]
theorem isMeagre_or_mem_residual_of_leftRel_invariant (hH : Dense (H : Set G))
    (hB : BaireMeasurableSet B)
    (hinv : Quotient.mk (leftRel H) ⁻¹' (Quotient.mk (leftRel H) '' B) = B) :
    IsMeagre B ∨ B ∈ residual G := by
  -- `H` acts on `G` by right multiplication, and the orbit relation is `leftRel H`. This action
  -- is topologically transitive: a nonempty open set `U` meets `V` after right multiplication by
  -- any point of `H` in the nonempty open set `u⁻¹ V`, for `u ∈ U`.
  have : MulAction.IsTopologicallyTransitive H.op G := by
    refine ⟨fun {U V} _ ⟨u, hu⟩ hVo ⟨v, hv⟩ => ?_⟩
    obtain ⟨h, hhV, hhH⟩ := hH.inter_open_nonempty ((u * ·) ⁻¹' V)
      (hVo.preimage (continuous_const.mul continuous_id)) ⟨u⁻¹ * v, by simpa using hv⟩
    exact ⟨⟨MulOpposite.op h, hhH⟩, u * h, ⟨u, hu, rfl⟩, hhV⟩
  have : Countable H.op := (Subgroup.equivOp H).symm.injective.countable
  exact MulAction.isMeagre_or_mem_residual_of_orbitRel_invariant hB hinv

end QuotientGroup

namespace Setoid

/-- A **generically ergodic** equivalence relation with meagre classes on a nonempty Baire space
has a quotient that is not countably separated: if every class of `E` is meagre and the preimage
of every measurable set of the quotient σ-algebra is meagre or comeagre, then no countable family
of `E`-invariant measurable sets separates the classes of `E`. -/
theorem not_countablySeparated_quotient_of_isMeagre_or_mem_residual [BaireSpace X] [Nonempty X]
    [MeasurableSpace X] (E : Setoid X) (hclass : ∀ x, IsMeagre {y | E x y})
    (herg : ∀ s : Set (Quotient E), MeasurableSet s →
      IsMeagre (Quotient.mk E ⁻¹' s) ∨ Quotient.mk E ⁻¹' s ∈ residual X) :
    ¬ CountablySeparated (Quotient E) := by
  intro h
  obtain ⟨S, hSc, hSm, hS⟩ := exists_countable_separating (Quotient E) MeasurableSet univ
  -- Membership in each set of `S` is constant on a comeagre set.
  have hconst : ∀ s ∈ S, ∃ c : Prop, ∀ᶠ x in residual X, (Quotient.mk E x ∈ s ↔ c) := by
    intro s hs
    rcases herg s (hSm s hs) with hm | hr
    · exact ⟨False, mem_of_superset hm fun x hx => iff_false_intro hx⟩
    · exact ⟨True, mem_of_superset hr fun x hx => iff_true_intro hx⟩
  choose! c hc using hconst
  have hall := (eventually_countable_ball hSc).2 hc
  obtain ⟨x₀, hx₀⟩ := (dense_of_mem_residual hall).nonempty
  -- That comeagre set lies in the class of `x₀`, which is meagre.
  refine not_isMeagre_of_mem_residual hall ((hclass x₀).mono fun x hx => ?_)
  exact Quotient.exact <| hS _ (mem_univ _) _ (mem_univ _) fun s hs =>
    (hx₀ s hs).trans (hx s hs).symm

end Setoid
