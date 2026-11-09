/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.MoveHorizontal
import TauCeti.Data.Finset.Basic

/-!
# The algebra of a matching

Let `Z` be a pointed matched circle with `4k` points, matched in pairs. Lipshitz, Ozsváth and
Thurston define the algebra `A(Z)` as a subalgebra of the strands algebra `A(4k)`: its elements
are the sums of strand diagrams over all ways of placing horizontal strands on given matched pairs,
each horizontal strand sitting at either point of its pair, and restricted to diagrams in which no
two starting points and no two ending points are matched. This file constructs this subalgebra for
an arbitrary matching `m : α → β` of a finite linear order `α`, two points being matched when they
have the same image, and over any commutative semiring.

The subalgebra `TauCeti.StrandsAlgebra.matchedSubalgebra R m` consists of the elements whose
coefficients vanish off the diagrams with pairwise unmatched starting points and pairwise unmatched
ending points, and are unchanged by moving a horizontal strand to a point matched with it
(`TauCeti.StrandDiagram.moveHorizontal`). It is closed under products and under the differential:
in the coefficient of a diagram `χ` with a horizontal strand at `p`, every term comes from a
factorization of `χ`, or a resolution giving `χ`, in which that strand is horizontal throughout.
Moving it to a point `q` matched with `p` in each piece matches these terms bijectively with those
of the moved diagram, and preserves the conditions for a nonzero product and for a term of the
differential.

Two diagrams are related by `TauCeti.StrandDiagram.matchedSetoid m` when they differ only in the
positions of their horizontal strands within matched classes. The coefficients of an element of
the subalgebra are constant on these classes, so the subalgebra is spanned by the matched
completion sums `TauCeti.StrandsAlgebra.matchedSum`, the sums over the classes of diagrams with
pairwise unmatched starting points and pairwise unmatched ending points; these are the generators
of `A(Z)` in Lipshitz, Ozsváth and Thurston.

The subalgebra has its own unit `TauCeti.StrandsAlgebra.matchedOne`, the sum of the idempotents
`I(s)` of the sets `s` with pairwise unmatched points. When `m` identifies two points it differs
from the unit of the strands algebra. It splits into the orthogonal idempotents `I(t)`
(`TauCeti.StrandsAlgebra.matchedIdem`) indexed by the sets `t` of occupied matched classes, each
the sum of the `I(s)` over the sets `s` containing exactly one point of each class in `t` and no
other points. With this unit the subalgebra is an `R`-algebra, and over a ring of characteristic
two the restricted differential makes it an ungraded differential algebra, over which type `D`
structures are defined.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebra R m`: the algebra `A(m)` of the matching `m`.
* `TauCeti.StrandDiagram.matchedSetoid m`: diagrams differing by moving horizontal strands within
  matched classes.
* `TauCeti.StrandsAlgebra.matchedSum R m φ`: the matched completion sum of a diagram.
* `TauCeti.StrandsAlgebra.matchedIdem R m t`, `TauCeti.StrandsAlgebra.matchedOne R m`: the
  idempotents `I(t)` of `A(m)` and its unit.
* `TauCeti.StrandsAlgebra.matchedDifferential R m`: the differential restricted to `A(m)`.

## Main results

* `TauCeti.StrandsAlgebra.mem_matchedSubalgebra`: membership in `A(m)`.
* `TauCeti.StrandsAlgebra.differential_mem_matchedSubalgebra`: `A(m)` is closed under the
  differential.
* `TauCeti.StrandsAlgebra.matchedSum_mem`, `TauCeti.StrandsAlgebra.span_matchedSum`: the matched
  completion sums lie in `A(m)` and span it.
* `TauCeti.StrandsAlgebra.matchedOne_mul`, `TauCeti.StrandsAlgebra.mul_matchedOne`: the unit.
* `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`, `TauCeti.StrandsAlgebra.sum_matchedIdem`:
  the `I(t)` are orthogonal idempotents of `A(m)` summing to its unit.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_matchedDifferential`: over a ring of characteristic
  two, `A(m)` is an ungraded differential algebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (pointed matched circles, the idempotents `I(s)` and the algebra `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α β : Type*} [LinearOrder α] [Fintype α]

variable (m : α → β) in
/-- Two strand diagrams are related for a matching `m : α → β` when one is obtained from the other
by moving horizontal strands to points with the same image under `m`, so that they differ only in
the positions of their horizontal strands within matched classes. -/
def matchedSetoid : Setoid (StrandDiagram α) :=
  Relation.EqvGen.setoid fun φ ψ ↦ ∃ p q, m p = m q ∧ φ.moveHorizontal p q = ψ

variable {m : α → β} {φ ψ : StrandDiagram α}

/-- A diagram moved by horizontal strands along a matching `m` has pairwise unmatched starting
points and pairwise unmatched ending points exactly when the original diagram has. -/
theorem injOn_source_and_target_iff_of_matchedSetoid (h : matchedSetoid m φ ψ) :
    Set.InjOn m φ.source ∧ Set.InjOn m φ.target ↔ Set.InjOn m ψ.source ∧ Set.InjOn m ψ.target := by
  induction h with
  | rel φ ψ h =>
    obtain ⟨p, q, hm, rfl⟩ := h
    rw [injOn_source_moveHorizontal_iff hm, injOn_target_moveHorizontal_iff hm]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- The defining property of the elements of the matched subalgebra: their coefficients vanish
off the diagrams whose starting and ending points are pairwise unmatched, and are unchanged by
moving a horizontal strand to a point matched with it. -/
private def IsMatched (m : α → β) (x : StrandsAlgebra R α) : Prop :=
  (∀ φ, (basis R α).repr x φ ≠ 0 → Set.InjOn m φ.source ∧ Set.InjOn m φ.target) ∧
    ∀ φ : StrandDiagram α, Set.InjOn m φ.source → Set.InjOn m φ.target → ∀ ⦃p q : α⦄,
      p ∈ φ p → p ≠ q → m p = m q →
        (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ

variable {m : α → β}

/-- A point matched with a horizontal strand of a diagram with pairwise unmatched starting points
and pairwise unmatched ending points is free in that diagram. -/
private theorem notMem_source_and_notMem_target {φ : StrandDiagram α}
    (hS : Set.InjOn m φ.source) (hT : Set.InjOn m φ.target) {p q : α} (hp : p ∈ φ p)
    (hpq : p ≠ q) (hm : m p = m q) : q ∉ φ.source ∧ q ∉ φ.target :=
  ⟨fun hq ↦ hS.ne (mem_source.2 ⟨p, hp⟩) hq hpq hm, fun hq ↦ hT.ne (mem_target.2 ⟨p, hp⟩) hq hpq hm⟩

/-- The bijection behind the closure of the matched subalgebra. Let the terms `f i` of the
coefficient of a diagram `χ` be indexed by the `i` with `P i χ`, and let `mv p q` move the
horizontal strand at `p` to `q` in the pieces `i`. If `mv p q` carries every nonzero term for a
diagram to a term for the moved diagram with the same value, and moving back undoes it, then the
coefficients of `χ` and of the moved diagram agree. -/
private theorem sum_moveHorizontal_eq {ι : Type*} [Fintype ι] (P : ι → StrandDiagram α → Prop)
    [∀ i χ, Decidable (P i χ)] (f : ι → R) (mv : α → α → ι → ι)
    (h : ∀ ⦃χ : StrandDiagram α⦄ ⦃p q : α⦄, p ∈ χ p → p ≠ q → m p = m q → ∀ i, P i χ →
      f i ≠ 0 → P (mv p q i) (χ.moveHorizontal p q) ∧ f (mv p q i) = f i ∧ mv q p (mv p q i) = i)
    {χ : StrandDiagram α} (hS : Set.InjOn m χ.source) (hT : Set.InjOn m χ.target) {p q : α}
    (hp : p ∈ χ p) (hpq : p ≠ q) (hm : m p = m q) :
    ∑ i ∈ univ.filter (P · (χ.moveHorizontal p q)), f i = ∑ i ∈ univ.filter (P · χ), f i := by
  obtain ⟨hs, ht⟩ := notMem_source_and_notMem_target hS hT hp hpq hm
  have hq := mem_moveHorizontal_self hp hs ht
  have hback := moveHorizontal_moveHorizontal hp hs ht
  -- Moving the horizontal strand back from `q` to `p` matches the nonzero terms.
  refine Finset.sum_bij_ne_zero (fun i _ _ ↦ mv q p i) ?_ ?_ ?_ ?_
  · intro i hi hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa only [hback] using (h hq hpq.symm hm.symm i hi hne).1
  · intro i hi hne j hj hne' he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [← (h hq hpq.symm hm.symm i hi hne).2.2, he, (h hq hpq.symm hm.symm j hj hne').2.2]
  · intro j hj hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨h₁, h₂, h₃⟩ := h hp hpq hm j hj hne
    exact ⟨mv p q j, Finset.mem_filter.2 ⟨Finset.mem_univ _, h₁⟩, by rwa [h₂], h₃⟩
  · intro i hi hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact (h hq hpq.symm hm.symm i hi hne).2.1.symm

/-- Moving a horizontal strand of `χ` to a matched point, in both factors of a factorization of
`χ` with nonzero coefficients, gives a factorization of the moved diagram with the same
coefficients, and moving back recovers the factorization. -/
private theorem isMatched_factor {x y : StrandsAlgebra R α} (hx : IsMatched m x)
    (hy : IsMatched m y) {φ ψ χ : StrandDiagram α} (h : φ.Composable ψ) (hχ : φ.trans ψ = χ)
    (hφ : (basis R α).repr x φ ≠ 0) (hψ : (basis R α).repr y ψ ≠ 0) {p q : α} (hp : p ∈ χ p)
    (hpq : p ≠ q) (hm : m p = m q) :
    ((φ.moveHorizontal p q).Composable (ψ.moveHorizontal p q) ∧
      (φ.moveHorizontal p q).trans (ψ.moveHorizontal p q) = χ.moveHorizontal p q) ∧
      (basis R α).repr x (φ.moveHorizontal p q) * (basis R α).repr y (ψ.moveHorizontal p q) =
        (basis R α).repr x φ * (basis R α).repr y ψ ∧
      (φ.moveHorizontal p q).moveHorizontal q p = φ ∧
      (ψ.moveHorizontal p q).moveHorizontal q p = ψ := by
  subst hχ
  obtain ⟨hφS, hφT⟩ := hx.1 φ hφ
  obtain ⟨hψS, hψT⟩ := hy.1 ψ hψ
  obtain ⟨hpφ, hpψ⟩ := mem_trans_self_iff.1 hp
  obtain ⟨hsφ, htφ⟩ := notMem_source_and_notMem_target hφS hφT hpφ hpq hm
  obtain ⟨hsψ, htψ⟩ := notMem_source_and_notMem_target hψS hψT hpψ hpq hm
  refine ⟨⟨h.moveHorizontal hpφ hsφ htφ hpψ hsψ htψ, moveHorizontal_trans hpφ hsφ htφ hpψ hsψ htψ⟩,
    ?_, moveHorizontal_moveHorizontal hpφ hsφ htφ, moveHorizontal_moveHorizontal hpψ hsψ htψ⟩
  rw [hx.2 φ hφS hφT hpφ hpq hm, hy.2 ψ hψS hψT hpψ hpq hm]

/-- **The matched subalgebra is closed under products.** -/
private theorem isMatched_mul {x y : StrandsAlgebra R α} (hx : IsMatched m x)
    (hy : IsMatched m y) : IsMatched m (x * y) := by
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  refine ⟨fun χ hχ ↦ ?_, fun χ hS hT p q hp hpq hm ↦ ?_⟩
  · rw [repr_mul_apply] at hχ
    obtain ⟨π, hπ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    obtain ⟨h, rfl⟩ := hπ
    rw [source_trans_of_target_eq h.target_eq, target_trans_of_target_eq h.target_eq]
    exact ⟨(hx.1 _ (left_ne_zero_of_mul hne)).1, (hy.1 _ (right_ne_zero_of_mul hne)).2⟩
  rw [repr_mul_apply, repr_mul_apply]
  refine sum_moveHorizontal_eq
    (fun (π : StrandDiagram α × StrandDiagram α) χ ↦ π.1.Composable π.2 ∧ π.1.trans π.2 = χ) _
    (fun p q π ↦ (π.1.moveHorizontal p q, π.2.moveHorizontal p q))
    (fun χ p q hp hpq hm π hπ hne ↦ ?_) hS hT hp hpq hm
  obtain ⟨h₁, h₂, h₃, h₄⟩ := isMatched_factor hx hy hπ.1 hπ.2 (left_ne_zero_of_mul hne)
    (right_ne_zero_of_mul hne) hp hpq hm
  exact ⟨h₁, h₂, Prod.ext h₃ h₄⟩

/-- Moving a horizontal strand of a resolution `χ` of `φ`, where `φ` has a nonzero coefficient, to
a matched point: the moved diagram is the resolution of the moved `φ` at the same crossing, the
coefficient is unchanged, and moving back recovers `φ`. -/
private theorem isMatched_resolve {x : StrandsAlgebra R α} (hx : IsMatched m x)
    {φ χ : StrandDiagram α} {r : α × α} (hr : r ∈ φ.resolvableInversions) (hχ : φ.resolve r = χ)
    (hφ : (basis R α).repr x φ ≠ 0) {p q : α} (hp : p ∈ χ p) (hpq : p ≠ q) (hm : m p = m q) :
    (r ∈ (φ.moveHorizontal p q).resolvableInversions ∧
      (φ.moveHorizontal p q).resolve r = χ.moveHorizontal p q) ∧
      (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ ∧
      (φ.moveHorizontal p q).moveHorizontal q p = φ := by
  subst hχ
  obtain ⟨hS, hT⟩ := hx.1 φ hφ
  have hr' := (mem_resolvableInversions.1 hr).1
  obtain ⟨hpφ, h₁, h₂⟩ := mem_self_and_ne_of_mem_resolve_self hr' hp
  obtain ⟨hs, ht⟩ := notMem_source_and_notMem_target hS hT hpφ hpq hm
  exact ⟨⟨mem_resolvableInversions_moveHorizontal hr hp hs ht,
    (moveHorizontal_resolve hpφ hs ht hr' h₁ h₂).symm⟩, hx.2 φ hS hT hpφ hpq hm,
    moveHorizontal_moveHorizontal hpφ hs ht⟩

/-- **The matched subalgebra is closed under the differential.** -/
private theorem isMatched_differential {x : StrandsAlgebra R α} (hx : IsMatched m x) :
    IsMatched m (differential R α x) := by
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  refine ⟨fun χ hχ ↦ ?_, fun χ hS hT p q hp hpq hm ↦ ?_⟩
  · rw [repr_differential_apply] at hχ
    obtain ⟨π, hπ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    obtain ⟨-, rfl⟩ := hπ
    rw [source_resolve, target_resolve]
    exact hx.1 _ hne
  rw [repr_differential_apply, repr_differential_apply]
  refine sum_moveHorizontal_eq
    (fun (π : StrandDiagram α × (α × α)) χ ↦ π.2 ∈ π.1.resolvableInversions ∧ π.1.resolve π.2 = χ)
    _ (fun p q π ↦ (π.1.moveHorizontal p q, π.2)) (fun χ p q hp hpq hm π hπ hne ↦ ?_) hS hT hp
    hpq hm
  obtain ⟨h₁, h₂, h₃⟩ := isMatched_resolve hx hπ.1 hπ.2 hne hp hpq hm
  exact ⟨h₁, h₂, Prod.ext h₃ rfl⟩

/-- A sum of idempotents `I(s)` over a family of sets on which the matching is injective, closed
under moving a point to a point matched with it, lies in the matched subalgebra. -/
private theorem isMatched_sum_idem (F : Finset (Finset α)) (hF : ∀ s ∈ F, Set.InjOn m s)
    (hmove : ∀ s ∈ F, ∀ ⦃p q⦄, p ∈ s → q ∉ s → m p = m q → insert q (s.erase p) ∈ F) :
    IsMatched m (∑ s ∈ F, idem s : StrandsAlgebra R α) := by
  classical
  refine ⟨fun ψ hψ ↦ ?_, fun φ hS hT p q hp hpq hm ↦ ?_⟩
  · rw [repr_sum_idem_apply] at hψ
    obtain ⟨h₁, h₂⟩ := (ite_ne_right_iff.1 hψ).1
    rw [h₁, source_idOn, target_idOn]
    exact ⟨hF _ h₂, hF _ h₂⟩
  obtain ⟨hs, ht⟩ := notMem_source_and_notMem_target hS hT hp hpq hm
  have hpS : p ∈ φ.source := mem_source.2 ⟨p, hp⟩
  rw [repr_sum_idem_apply, repr_sum_idem_apply, source_moveHorizontal hp hs ht]
  congr 1
  refine propext ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · have hq' : q ∈ insert q (φ.source.erase p) := mem_insert_self q _
    have hp' : p ∉ insert q (φ.source.erase p) := by simp [hpq]
    have he : insert p ((insert q (φ.source.erase p)).erase q) = φ.source := by
      rw [erase_insert (by simp [hs]), insert_erase hpS]
    refine ⟨?_, he ▸ hmove _ h₂ hq' hp' hm.symm⟩
    rw [← moveHorizontal_moveHorizontal hp hs ht, h₁, moveHorizontal_idOn hq' hp', he, source_idOn]
  · refine ⟨?_, hmove _ h₂ hpS hs hm⟩
    conv_lhs => rw [h₁]
    rw [moveHorizontal_idOn hpS hs]

variable (R m) in
/-- The **matched subalgebra** `A(m)` of the strands algebra for a matching `m : α → β`, two points
being matched when they have the same image. It consists of the elements whose coefficients vanish
off the diagrams with pairwise unmatched starting points and pairwise unmatched ending points, and
are unchanged by moving a horizontal strand to a point matched with it. Equivalently it is spanned
by the matched completion sums `TauCeti.StrandsAlgebra.matchedSum` of the diagrams with pairwise
unmatched starting points and pairwise unmatched ending points
(`TauCeti.StrandsAlgebra.span_matchedSum`). For the matching of the `4k` points of a pointed
matched circle `Z` this is the algebra `A(Z)` of Lipshitz, Ozsváth and Thurston. -/
def matchedSubalgebra : NonUnitalSubalgebra R (StrandsAlgebra R α) where
  carrier := {x | IsMatched m x}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {x y} hx hy := by
    refine ⟨fun φ hφ ↦ ?_, fun φ hS hT p q hp hpq hm ↦ ?_⟩
    · rw [map_add, Finsupp.add_apply] at hφ
      by_cases h : (basis R α).repr x φ = 0
      · exact hy.1 φ (by simpa [h] using hφ)
      · exact hx.1 φ h
    · simp [hx.2 φ hS hT hp hpq hm, hy.2 φ hS hT hp hpq hm]
  smul_mem' r x hx := by
    refine ⟨fun φ hφ ↦ hx.1 φ fun h ↦ hφ (by simp [h]), fun φ hS hT p q hp hpq hm ↦ ?_⟩
    simp [hx.2 φ hS hT hp hpq hm]
  mul_mem' := isMatched_mul

/-- Membership in the matched subalgebra. -/
theorem mem_matchedSubalgebra {x : StrandsAlgebra R α} :
    x ∈ matchedSubalgebra R m ↔
      (∀ φ, (basis R α).repr x φ ≠ 0 → Set.InjOn m φ.source ∧ Set.InjOn m φ.target) ∧
        ∀ φ : StrandDiagram α, Set.InjOn m φ.source → Set.InjOn m φ.target → ∀ ⦃p q : α⦄,
          p ∈ φ p → p ≠ q → m p = m q →
            (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ :=
  Iff.rfl

/-- Membership in the matched subalgebra is the defining property `IsMatched`. -/
private theorem mem_matchedSubalgebra_iff_isMatched {x : StrandsAlgebra R α} :
    x ∈ matchedSubalgebra R m ↔ IsMatched m x :=
  Iff.rfl

/-- **The matched subalgebra is closed under the differential.** -/
theorem differential_mem_matchedSubalgebra {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R m) : differential R α x ∈ matchedSubalgebra R m :=
  mem_matchedSubalgebra_iff_isMatched.2
    (isMatched_differential (mem_matchedSubalgebra_iff_isMatched.1 hx))

/-- The coefficients of an element of the matched subalgebra agree on diagrams related by moving
horizontal strands to matched points. -/
theorem repr_eq_of_matchedSetoid {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R m)
    {φ ψ : StrandDiagram α} (h : matchedSetoid m φ ψ) :
    (basis R α).repr x φ = (basis R α).repr x ψ := by
  obtain ⟨hx₁, hx₂⟩ := mem_matchedSubalgebra.1 hx
  induction h with
  | rel φ ψ h =>
    obtain ⟨p, q, hm, rfl⟩ := h
    by_cases hinj : Set.InjOn m φ.source ∧ Set.InjOn m φ.target
    · by_cases hc : p ∈ φ p ∧ p ≠ q
      · exact (hx₂ φ hinj.1 hinj.2 hc.1 hc.2 hm).symm
      · rw [moveHorizontal_of_not fun h ↦ hc ⟨h.1, fun hpq ↦ h.2.1 (hpq ▸ mem_source.2 ⟨p, h.1⟩)⟩]
    · -- Neither diagram has pairwise unmatched endpoints, so both coefficients vanish.
      have hinj' : ¬(Set.InjOn m (φ.moveHorizontal p q).source ∧
          Set.InjOn m (φ.moveHorizontal p q).target) := by
        rwa [injOn_source_moveHorizontal_iff hm, injOn_target_moveHorizontal_iff hm]
      rw [not_not.1 (mt (hx₁ φ) hinj), not_not.1 (mt (hx₁ _) hinj')]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable (R m) in
/-- The **matched completion sum** of a strand diagram `φ`: the sum of the diagrams obtained from
`φ` by moving horizontal strands to points matched with them. When the starting points and the
ending points of `φ` are pairwise unmatched, it is the sum over all ways of placing each horizontal
strand of `φ` at any point of its matched class, keeping the other strands; these sums span the
matched subalgebra. -/
def matchedSum (φ : StrandDiagram α) : StrandsAlgebra R α :=
  ∑ ψ ∈ (Set.toFinite {ψ | matchedSetoid m φ ψ}).toFinset, of ψ

open scoped Classical in
/-- The coefficients of a matched completion sum: `1` on the diagrams related to `φ` and `0`
elsewhere. -/
theorem repr_matchedSum_apply (φ ψ : StrandDiagram α) :
    (basis R α).repr (matchedSum R m φ) ψ = if matchedSetoid m φ ψ then 1 else 0 := by
  rw [matchedSum, repr_sum_of_apply]
  simp

/-- The matched completion sum of a diagram with pairwise unmatched starting points and pairwise
unmatched ending points lies in the matched subalgebra. -/
theorem matchedSum_mem {φ : StrandDiagram α} (hS : Set.InjOn m φ.source)
    (hT : Set.InjOn m φ.target) : matchedSum R m φ ∈ matchedSubalgebra R m := by
  classical
  refine mem_matchedSubalgebra.2 ⟨fun ψ hψ ↦ ?_, fun ψ _ _ p q _ _ hm ↦ ?_⟩
  · rw [repr_matchedSum_apply] at hψ
    exact (injOn_source_and_target_iff_of_matchedSetoid (ite_ne_right_iff.1 hψ).1).1 ⟨hS, hT⟩
  · have h : matchedSetoid m ψ (ψ.moveHorizontal p q) := Relation.EqvGen.rel _ _ ⟨p, q, hm, rfl⟩
    have h' : matchedSetoid m φ (ψ.moveHorizontal p q) ↔ matchedSetoid m φ ψ :=
      ⟨fun h' ↦ (matchedSetoid m).iseqv.trans h' ((matchedSetoid m).iseqv.symm h),
        fun h' ↦ (matchedSetoid m).iseqv.trans h' h⟩
    simp only [repr_matchedSum_apply, h']

/-- **The matched completion sums span the matched subalgebra.** The sums
`TauCeti.StrandsAlgebra.matchedSum` of the diagrams with pairwise unmatched starting points and
pairwise unmatched ending points span `A(m)` as an `R`-module. -/
theorem span_matchedSum :
    Submodule.span R (matchedSum R m '' {φ | Set.InjOn m φ.source ∧ Set.InjOn m φ.target}) =
      (matchedSubalgebra R m).toSubmodule := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
  · rintro _ ⟨φ, ⟨hS, hT⟩, rfl⟩
    exact matchedSum_mem hS hT
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  let := Fintype.ofFinite (Quotient (matchedSetoid m))
  rw [NonUnitalSubalgebra.mem_toSubmodule] at hx
  -- Grouping the basis expansion of `x` by classes of diagrams writes `x` as a combination of
  -- the matched completion sums of class representatives.
  have key : x = ∑ C : Quotient (matchedSetoid m),
      (basis R α).repr x C.out • matchedSum R m C.out := by
    conv_lhs => rw [← (basis R α).sum_repr x]
    rw [← Finset.sum_fiberwise univ fun φ ↦ (⟦φ⟧ : Quotient (matchedSetoid m))]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [matchedSum, Finset.smul_sum]
    refine Finset.sum_congr ?_ fun φ hφ ↦ ?_
    · ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq, Quotient.mk_eq_iff_out]
      exact ⟨(matchedSetoid m).iseqv.symm, (matchedSetoid m).iseqv.symm⟩
    · rw [Set.Finite.mem_toFinset] at hφ
      rw [basis_apply, repr_eq_of_matchedSetoid hx hφ]
  rw [key]
  refine Submodule.sum_mem _ fun C _ ↦ ?_
  by_cases h : (basis R α).repr x C.out = 0
  · simp [h]
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨C.out, (mem_matchedSubalgebra.1 hx).1 _ h, rfl⟩)

open scoped Classical in
variable (R m) in
/-- The unit of the matched subalgebra: the sum of the idempotents `I(s)` over the sets `s` on
which the matching is injective. -/
def matchedOne : StrandsAlgebra R α :=
  ∑ s ∈ univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α), idem s

open scoped Classical in
/-- The unit of the matched subalgebra as a sum of idempotents `I(s)`. -/
theorem matchedOne_def :
    matchedOne R m = ∑ s ∈ univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α), idem s :=
  (rfl)

theorem matchedOne_mem : matchedOne R m ∈ matchedSubalgebra R m := by
  classical
  rw [matchedOne_def]
  refine isMatched_sum_idem _ (fun s hs ↦ (Finset.mem_filter.1 hs).2) fun s hs p q hp _ hm ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact Finset.injOn_insert_erase hs hp hm

/-- The unit of the matched subalgebra fixes a diagram whose starting points are pairwise
unmatched. -/
theorem matchedOne_mul_of {φ : StrandDiagram α} (h : Set.InjOn m φ.source) :
    matchedOne R m * of φ = of φ := by
  classical
  simp [matchedOne_def, Finset.sum_mul, idem_mul_of, h]

/-- The unit of the matched subalgebra fixes a diagram whose ending points are pairwise
unmatched. -/
theorem of_mul_matchedOne {φ : StrandDiagram α} (h : Set.InjOn m φ.target) :
    of φ * matchedOne R m = of φ := by
  classical
  simp [matchedOne_def, Finset.mul_sum, of_mul_idem, h]

/-- `TauCeti.StrandsAlgebra.matchedOne` is a left identity on the elements of the matched
subalgebra. -/
theorem matchedOne_mul {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R m) :
    matchedOne R m * x = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [mul_smul_comm, basis_apply, matchedOne_mul_of ((mem_matchedSubalgebra.1 hx).1 φ hφ).1]

/-- `TauCeti.StrandsAlgebra.matchedOne` is a right identity on the elements of the matched
subalgebra. -/
theorem mul_matchedOne {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R m) :
    x * matchedOne R m = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [smul_mul_assoc, basis_apply, of_mul_matchedOne ((mem_matchedSubalgebra.1 hx).1 φ hφ).2]

/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem differential_matchedOne : differential R α (matchedOne R m) = 0 := by
  simp [matchedOne_def]

instance : One (matchedSubalgebra R m) :=
  ⟨⟨matchedOne R m, matchedOne_mem⟩⟩

/-- The unit of the matched subalgebra is `TauCeti.StrandsAlgebra.matchedOne`, which differs from
the unit of the strands algebra when `m` identifies two points. -/
@[simp]
theorem coe_matchedSubalgebra_one :
    ((1 : matchedSubalgebra R m) : StrandsAlgebra R α) = matchedOne R m :=
  (rfl)

/-- The matched subalgebra is a unital algebra, with unit `TauCeti.StrandsAlgebra.matchedOne`. -/
instance : Semiring (matchedSubalgebra R m) where
  __ := (matchedSubalgebra R m).toNonUnitalSemiring
  one_mul x := Subtype.ext (matchedOne_mul x.2)
  mul_one x := Subtype.ext (mul_matchedOne x.2)

instance {R : Type*} [CommRing R] : Ring (matchedSubalgebra R m) where
  __ := (inferInstance : Semiring (matchedSubalgebra R m))
  __ := (matchedSubalgebra R m).toNonUnitalRing

instance : Algebra R (matchedSubalgebra R m) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

open scoped Classical in
variable (R m) in
/-- The idempotent `I(t)` of the matched subalgebra for a set `t` of matched classes: the sum of
the idempotents `I(s)` over the sets `s` containing exactly one point of each class in `t` and no
other points, that is, the sets on which `m` is injective with image `t`. -/
def matchedIdem (t : Finset β) : matchedSubalgebra R m :=
  ⟨∑ s ∈ univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α) ∧ s.image m = t, idem s, by
    refine isMatched_sum_idem _ (fun s hs ↦ (Finset.mem_filter.1 hs).2.1)
      fun s hs p q hp _ hm ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    refine ⟨Finset.injOn_insert_erase hs.1 hp hm, ?_⟩
    rw [Finset.image_insert, ← hm, ← Finset.image_insert, Finset.insert_erase hp, hs.2]⟩

open scoped Classical in
/-- The idempotent `I(t)` as an element of the strands algebra: a sum of idempotents `I(s)`. -/
@[simp]
theorem coe_matchedIdem (t : Finset β) :
    (matchedIdem R m t : StrandsAlgebra R α) =
      ∑ s ∈ univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α) ∧ s.image m = t, idem s :=
  (rfl)

/-- The idempotents `I(t)` are orthogonal: `I(t) I(t')` is `I(t)` when `t = t'` and zero
otherwise. -/
@[simp]
theorem matchedIdem_mul_matchedIdem [DecidableEq β] (t t' : Finset β) :
    matchedIdem R m t * matchedIdem R m t' = if t = t' then matchedIdem R m t else 0 := by
  classical
  refine Subtype.ext ?_
  rw [NonUnitalSubalgebra.coe_mul, apply_ite Subtype.val, coe_matchedIdem, coe_matchedIdem,
    Finset.sum_mul_sum]
  simp only [idem_mul_idem, Finset.sum_ite_eq]
  split_ifs with h
  · subst h
    exact Finset.sum_congr rfl fun s hs ↦ ite_eq_left hs
  · refine Finset.sum_eq_zero fun s hs ↦ ite_eq_right fun hs' ↦ ?_
    simp only [Finset.mem_filter] at hs hs'
    exact absurd (hs.2.2.symm.trans hs'.2.2) h

theorem isIdempotentElem_matchedIdem (t : Finset β) :
    IsIdempotentElem (matchedIdem R m t) := by
  classical
  rw [IsIdempotentElem, matchedIdem_mul_matchedIdem, ite_eq_left rfl]

/-- Multiplying a diagram with pairwise unmatched starting points on the left by `I(t)` keeps it
when its starting points occupy the classes `t`, and gives zero otherwise. -/
theorem matchedIdem_mul_of [DecidableEq β] (t : Finset β) {φ : StrandDiagram α}
    (h : Set.InjOn m φ.source) :
    (matchedIdem R m t : StrandsAlgebra R α) * of φ =
      if φ.source.image m = t then of φ else 0 := by
  classical
  simp only [coe_matchedIdem, Finset.sum_mul, idem_mul_of, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, h, true_and]
  -- The two sides decide equality of images with different instances.
  congr
  exact Subsingleton.elim _ _

/-- Multiplying a diagram with pairwise unmatched ending points on the right by `I(t)` keeps it
when its ending points occupy the classes `t`, and gives zero otherwise. -/
theorem of_mul_matchedIdem [DecidableEq β] (t : Finset β) {φ : StrandDiagram α}
    (h : Set.InjOn m φ.target) :
    of φ * (matchedIdem R m t : StrandsAlgebra R α) =
      if φ.target.image m = t then of φ else 0 := by
  classical
  simp only [coe_matchedIdem, Finset.mul_sum, of_mul_idem, Finset.sum_ite_eq, Finset.mem_filter,
    Finset.mem_univ, h, true_and]
  -- The two sides decide equality of images with different instances.
  congr
  exact Subsingleton.elim _ _

/-- The idempotents `I(t)` sum to the unit of the matched subalgebra. -/
theorem sum_matchedIdem [Fintype β] : ∑ t : Finset β, matchedIdem R m t = 1 := by
  classical
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum, coe_matchedSubalgebra_one, matchedOne_def]
  simp only [coe_matchedIdem]
  rw [← Finset.sum_fiberwise (univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α))
    (fun s ↦ s.image m)]
  simp only [Finset.filter_filter]

variable (R m) in
/-- The differential of the strands algebra restricted to the matched subalgebra. -/
def matchedDifferential : matchedSubalgebra R m →ₗ[R] matchedSubalgebra R m where
  toFun x := ⟨differential R α x, differential_mem_matchedSubalgebra x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp]
theorem coe_matchedDifferential (x : matchedSubalgebra R m) :
    (matchedDifferential R m x : StrandsAlgebra R α) = differential R α x :=
  (rfl)

/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem matchedDifferential_one : matchedDifferential R m 1 = 0 :=
  Subtype.ext (by simp)

/-- The idempotents `I(t)` are cycles. -/
@[simp]
theorem matchedDifferential_matchedIdem (t : Finset β) :
    matchedDifferential R m (matchedIdem R m t) = 0 :=
  Subtype.ext (by simp)

/-- Over a ring of characteristic two, such as `𝔽₂`, the matched subalgebra with the restricted
differential is an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_matchedDifferential {R : Type*} [CommRing R] [CharP R 2] :
    IsUngradedDGAlgebra (matchedDifferential R m) where
  map_mul a b := Subtype.ext (by simp [differential_mul])
  map_map a := Subtype.ext (by simp [differential_differential])

end StrandsAlgebra

end TauCeti
