/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.DeleteItems
public import TauCeti.GroupTheory.FreeGroup.GenEq.Surgery
public import TauCeti.GroupTheory.FreeGroup.GenEq.Tied
import TauCeti.Algebra.Group.Basic
import TauCeti.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Removal of a lonely base

A variable base `μ` of a generalised equation `Ω` is *lonely* when no other variable base
contains an item of `μ` and every boundary inside `μ` is `μ`-tied (Kharlampovich–Myasnikov, §5.1,
ET4). The ties match the items of `μ` with consecutive segments of `Δ(μ)`: writing `b(i)` for the
boundary to which `i` is tied, in a formally consistent `Ω` the equations of `μ` and `Δ(μ)` say
that the item `hᵢ` of `μ` equals `h[b(i), b(i + 1)]` when `ε(μ) = ε(Δμ)` and `h[b(i + 1), b(i)]⁻¹`
otherwise. The transformation
ET4 removes the bases `μ` and `Δ(μ)` together with the section `σ(μ)` and its items, and moves
each constant base of an item of `μ` to the matching item of `Δ(μ)`, with the same letter when
`ε(μ) = ε(Δμ)` and with the inverse letter otherwise.

Writing `Ω′ = Ω.removeLonely μ h`, the substitution `π` sending an item of `μ` to the word of its
segment of `Δ(μ)` and every other item to itself maps the points of `Ω′*` bijectively onto the
points of `Ω*`, in every `F(A)`-group (`TauCeti.GenEq.bijOn_wordMap_removeLonely`); hence it
induces an `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}` (`TauCeti.GenEq.removeLonelyHom`,
`TauCeti.GenEq.removeLonelyHom_bijective`).

The source deletes "the boundaries `α(μ) + 1, …, β(μ) - 1`", which would leave one free item in
place of `σ(μ)`, gives `π` only for the items after the first, with a misprinted last index and
without the inverse, and keeps the letter of a moved constant base. With one item left, `π` is
not surjective; the uses of ET4 in the source remove the whole section `σ(μ)`, as is done here.
We also require `Δ(μ) ≠ μ`: a base which is its own dual has no segment of another base to which
its items could be sent. Finally the source moves a constant base of an item of `μ` to the
matching place of `Δ(μ)` without asking that this place be a single item; formal consistency
guarantees it only for items strictly inside `μ`, so it is part of `TauCeti.GenEq.IsLonely`.

## Main definitions

* `TauCeti.GenEq.IsLonely`: a lonely base.
* `TauCeti.GenEq.dualItem`, `TauCeti.GenEq.moveConstBases`: the item of `Δ(μ)` matched with an
  item of `μ`, and the generalised equation with the constant bases of `μ` moved there.
* `TauCeti.GenEq.removeLonely`: the generalised equation obtained by removing a lonely base.
* `TauCeti.GenEq.removeLonelyWord`: the substitution `π` of the items.
* `TauCeti.GenEq.removeLonelyHom`: the `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` it induces.

## Main results

* `TauCeti.GenEq.equations_subset_union_moveConstBases`,
  `TauCeti.GenEq.equations_moveConstBases_subset_union`: moving constant bases changes only the
  coefficient equations of the moved bases.
* `TauCeti.GenEq.mapsTo_wordMap_removeLonely`, `TauCeti.GenEq.bijOn_wordMap_removeLonely`: `π`
  maps the points of `Ω′*` bijectively onto the points of `Ω*`, in every `F(A)`-group.
* `TauCeti.GenEq.removeLonelyHom_bijective`: `π` induces an `F(A)`-isomorphism of coordinate
  groups.

The examples at the end of the file treat the equation `h₀ = h₁`: removing its lonely base leaves
one item without equations, whose coordinate group is not that of a point. They also show that
formal consistency does not imply the condition on constant items in `TauCeti.GenEq.IsLonely`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, ET4.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §5.1, ET4.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod

variable {A : Type*} (Ω : GenEq A)

/-- A variable base `μ` is lonely (ET4) when it is not its own dual, no other variable base
contains an item of `μ`, every boundary inside `μ` is `μ`-tied, and the two end-points of every
item of `μ` carrying a constant base are tied to adjacent boundaries, so that the item is matched
with a single item of `Δ(μ)`. For an item strictly inside `μ` the last condition is part of formal
consistency; for the first and the last item of `μ` it is not. -/
structure IsLonely (μ : Fin Ω.numBases) : Prop where
  dual_ne : Ω.dual μ ≠ μ
  disjoint : ∀ ν, ν ≠ μ → Disjoint (Ω.baseItems ν) (Ω.baseItems μ)
  tied : ∀ p, Ω.Crosses p μ → ∃ q, (p, μ, q) ∈ Ω.connections
  adjacent_of_mem_constBases : ∀ b ∈ Ω.constBases, b.1 ∈ Ω.baseItems μ → ∀ q q',
    Ω.IsTiedTo μ b.1.castSucc q → Ω.IsTiedTo μ b.1.succ q' →
      (q : ℕ) + 1 = q' ∨ (q' : ℕ) + 1 = q

/-- Loneliness as a conjunction of its four conditions. -/
theorem isLonely_iff {μ : Fin Ω.numBases} : Ω.IsLonely μ ↔ Ω.dual μ ≠ μ ∧
    (∀ ν, ν ≠ μ → Disjoint (Ω.baseItems ν) (Ω.baseItems μ)) ∧
      (∀ p, Ω.Crosses p μ → ∃ q, (p, μ, q) ∈ Ω.connections) ∧
      ∀ b ∈ Ω.constBases, b.1 ∈ Ω.baseItems μ → ∀ q q',
        Ω.IsTiedTo μ b.1.castSucc q → Ω.IsTiedTo μ b.1.succ q' →
          (q : ℕ) + 1 = q' ∨ (q' : ℕ) + 1 = q :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- The item of `Δ(μ)` matched with the item `k` of a base `μ` all of whose boundaries are tied:
the first item of the segment of `Δ(μ)` between the boundaries tied to the end-points of `k`,
which is the whole segment when these boundaries are adjacent (as for a constant item of a lonely
base). If the smaller of the two boundaries is the last boundary, which never happens for an item
of a lonely base, the value is `k`. -/
def dualItem (μ : Fin Ω.numBases) (k : Fin Ω.numItems) : Fin Ω.numItems :=
  if h : min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) < Ω.numItems then
    ⟨min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ), h⟩
  else k

variable {Ω} in
/-- The item matched with `k` starts at the smaller of the boundaries tied to the end-points of
`k`, when that boundary is the left end-point of an item. -/
theorem val_dualItem {μ : Fin Ω.numBases} {k : Fin Ω.numItems}
    (hlt : min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) < Ω.numItems) :
    (Ω.dualItem μ k : ℕ) = min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) := by
  rw [dualItem, dite_eq_left hlt]

open Classical in
-- Reducible, so that the items, bases and boundary connections of the result are reducibly those
-- of `Ω`.
/-- Move every constant base of an item of `μ` to the matching item of `Δ(μ)`, with the same
letter when `ε(μ) = ε(Δμ)` and the inverse letter otherwise. -/
noncomputable abbrev moveConstBases (μ : Fin Ω.numBases) : GenEq A :=
  { Ω with
    constBases := Ω.constBases.image fun b =>
      if b.1 ∈ Ω.baseItems μ then
        (Ω.dualItem μ b.1, (b.2.1, if Ω.sign μ = Ω.sign (Ω.dual μ) then b.2.2 else !b.2.2))
      else b }

/-! ### Moving the constant bases -/

section MoveConstBases

variable (μ : Fin Ω.numBases)

/-- Moving constant bases keeps the words `h[i, j] ^ ±1`, which only depend on the items. -/
@[simp]
theorem segment_moveConstBases (i j : ℕ) (s : Bool) :
    (Ω.moveConstBases μ).segment i j s = Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- Moving constant bases keeps the basic equations. -/
@[simp]
theorem basicEquation_moveConstBases (ν : Fin Ω.numBases) :
    (Ω.moveConstBases μ).basicEquation ν = Ω.basicEquation ν :=
  Prod.ext (by simp) (by simp)

/-- Moving constant bases keeps the coefficient equation `hₖ = a` of a pair `(k, a)`, which only
depends on the pair. -/
@[simp]
theorem coeffEquation_moveConstBases (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.moveConstBases μ).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- Moving constant bases keeps the boundary equations. -/
@[simp]
theorem boundaryEquation_moveConstBases
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.moveConstBases μ).boundaryEquation c = Ω.boundaryEquation c := by
  refine Prod.ext (by simp) ?_
  by_cases hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) <;>
    simp [boundaryEquation_snd_of_sign_eq, boundaryEquation_snd_of_sign_ne, hs]

/-- The constant bases after moving those of `μ` are the constant bases of `Ω` on items outside
`μ` and the constant bases on items `k` of `μ` moved to `Ω.dualItem μ k`, with their letter
inverted when `ε(μ) ≠ ε(Δμ)`. -/
theorem mem_constBases_moveConstBases {b : Fin Ω.numItems × (A × Bool)} :
    b ∈ (Ω.moveConstBases μ).constBases ↔ (b ∈ Ω.constBases ∧ b.1 ∉ Ω.baseItems μ) ∨
      ∃ b' ∈ Ω.constBases, b'.1 ∈ Ω.baseItems μ ∧ (Ω.dualItem μ b'.1,
        (b'.2.1, if Ω.sign μ = Ω.sign (Ω.dual μ) then b'.2.2 else !b'.2.2)) = b := by
  classical
  grind

/-- A constant base of an item outside `μ` is not moved. -/
theorem mem_constBases_moveConstBases_of_notMem {b : Fin Ω.numItems × (A × Bool)}
    (hb : b ∈ Ω.constBases) (hk : b.1 ∉ Ω.baseItems μ) : b ∈ (Ω.moveConstBases μ).constBases :=
  (Ω.mem_constBases_moveConstBases μ).2 (.inl ⟨hb, hk⟩)

/-- A constant base of an item `k` of `μ` is moved to the item `Ω.dualItem μ k`, with its letter
inverted when `ε(μ) ≠ ε(Δμ)`. -/
theorem mem_constBases_moveConstBases_of_mem {b : Fin Ω.numItems × (A × Bool)}
    (hb : b ∈ Ω.constBases) (hk : b.1 ∈ Ω.baseItems μ) :
    (Ω.dualItem μ b.1, (b.2.1, if Ω.sign μ = Ω.sign (Ω.dual μ) then b.2.2 else !b.2.2)) ∈
      (Ω.moveConstBases μ).constBases :=
  (Ω.mem_constBases_moveConstBases μ).2 (.inr ⟨b, hb, hk, rfl⟩)

/-- Every equation of `Ω` is an equation of `Ω` with the constant bases of `μ` moved, or the
coefficient equation of a constant base of an item of `μ`. -/
theorem equations_subset_union_moveConstBases :
    Ω.equations ⊆ (Ω.moveConstBases μ).equations ∪
      Ω.coeffEquation '' {b | b ∈ Ω.constBases ∧ b.1 ∈ Ω.baseItems μ} := by
  refine (Ω.forall_mem_equations (P := (· ∈ _))).2 ⟨fun ν => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · exact Or.inl (basicEquation_moveConstBases Ω μ ν ▸
      (Ω.moveConstBases μ).basicEquation_mem_equations ν)
  · by_cases hk : b.1 ∈ Ω.baseItems μ
    · exact Or.inr ⟨b, ⟨hb, hk⟩, rfl⟩
    · exact Or.inl (coeffEquation_moveConstBases Ω μ b ▸
        (Ω.moveConstBases μ).coeffEquation_mem_equations
          (Ω.mem_constBases_moveConstBases_of_notMem μ hb hk))
  · exact Or.inl (boundaryEquation_moveConstBases Ω μ c ▸
      (Ω.moveConstBases μ).boundaryEquation_mem_equations hc)

/-- Every equation of `Ω` with the constant bases of `μ` moved is an equation of `Ω`, or the
coefficient equation of a moved constant base. -/
theorem equations_moveConstBases_subset_union :
    (Ω.moveConstBases μ).equations ⊆ Ω.equations ∪ Ω.coeffEquation ''
      ((fun b => (Ω.dualItem μ b.1,
        (b.2.1, if Ω.sign μ = Ω.sign (Ω.dual μ) then b.2.2 else !b.2.2))) ''
          {b | b ∈ Ω.constBases ∧ b.1 ∈ Ω.baseItems μ}) := by
  refine ((Ω.moveConstBases μ).forall_mem_equations (P := (· ∈ _))).2
    ⟨fun ν => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · exact Or.inl ((basicEquation_moveConstBases Ω μ ν).symm ▸ Ω.basicEquation_mem_equations ν)
  · rw [coeffEquation_moveConstBases]
    rcases (Ω.mem_constBases_moveConstBases μ).1 hb with ⟨hb, -⟩ | ⟨b', hb', hk, rfl⟩
    · exact Or.inl (Ω.coeffEquation_mem_equations hb)
    · exact Or.inr ⟨_, ⟨b', ⟨hb', hk⟩, rfl⟩, rfl⟩
  · exact Or.inl ((boundaryEquation_moveConstBases Ω μ c).symm ▸
      Ω.boundaryEquation_mem_equations hc)

end MoveConstBases

variable {Ω} in
/-- After the bases `μ, Δ(μ)` are removed, no variable base meets the items of a lonely base
`μ`. -/
theorem IsLonely.disjoint_baseItems_removePair {μ : Fin Ω.numBases} (h : Ω.IsLonely μ)
    (ν : Fin ((Ω.moveConstBases μ).removePair μ).numBases) :
    Disjoint (((Ω.moveConstBases μ).removePair μ).baseItems ν) (Ω.baseItems μ) := by
  have hν : ({μ, Ω.dual μ} : Finset _)ᶜ.orderEmbOfFin rfl ν ≠ μ := fun hν =>
    Finset.mem_compl.1 (Finset.orderEmbOfFin_mem ({μ, Ω.dual μ} : Finset _)ᶜ rfl ν)
      (Finset.mem_insert.2 (Or.inl hν))
  refine Finset.disjoint_left.2 fun k hk => Finset.disjoint_left.1 (h.disjoint _ hν) ?_
  exact Ω.mem_baseItems.2 (((Ω.moveConstBases μ).removePair μ).mem_baseItems.1 hk)

-- Reducible, so that the items of the result are reducibly those of `Ω` outside `μ`.
/-- Remove a lonely base `μ` (ET4): move the constant bases of the items of `μ` to the matching
items of `Δ(μ)`, remove the bases `μ` and `Δ(μ)` with the connections through them, and delete
the items of `μ`. -/
noncomputable abbrev removeLonely (μ : Fin Ω.numBases) (h : Ω.IsLonely μ) : GenEq A :=
  ((Ω.moveConstBases μ).removePair μ).deleteItems (Ω.baseItems μ) h.disjoint_baseItems_removePair

/-- The word in the items of `Ω.removeLonely μ h` to which ET4 sends the item `k` of `Ω`: the
segment of `Δ(μ)` between the boundaries tied to the end-points of `k`, inverted when
`ε(μ) ≠ ε(Δμ)`, if `k` is an item of `μ`; the item `k` itself otherwise. -/
noncomputable def removeLonelyList (μ : Fin Ω.numBases) (h : Ω.IsLonely μ) (k : Fin Ω.numItems) :
    List ((Fin (Ω.removeLonely μ h).numItems ⊕ A) × Bool) :=
  if k ∈ Ω.baseItems μ then
    (Ω.removeLonely μ h).segment
      ((Ω.baseItems μ).collapse
        (min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ)))
      ((Ω.baseItems μ).collapse
        (max (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ)))
      (decide (Ω.sign μ = Ω.sign (Ω.dual μ)))
  else
    (Ω.removeLonely μ h).segment ((Ω.baseItems μ).collapse k)
      ((Ω.baseItems μ).collapse k + 1) true

/-- The substitution `π` of ET4, as a tuple of elements of `F(A)[h′]`. -/
noncomputable def removeLonelyWord (μ : Fin Ω.numBases) (h : Ω.IsLonely μ) (k : Fin Ω.numItems) :
    GX (FreeGroup A) (Fin (Ω.removeLonely μ h).numItems) :=
  EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.removeLonelyList μ h k))

variable {Ω} {μ : Fin Ω.numBases} (h : Ω.IsLonely μ) (hΩ : Ω.IsFormallyConsistent)

/-- An item outside a lonely base is sent by `π` to the corresponding item of the result. -/
theorem removeLonelyList_of_notMem {k : Fin (Ω.baseItems μ)ᶜ.card} :
    Ω.removeLonelyList μ h ((Ω.baseItems μ)ᶜ.orderEmbOfFin rfl k) = [(Sum.inl k, true)] := by
  rw [removeLonelyList, ite_eq_right (Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ rfl k)),
    Finset.collapse_orderEmbOfFin]
  exact (Ω.removeLonely μ h).segment_succ k true

include h in
/-- Every boundary of a lonely base is tied: the inner boundaries by boundary connections, the
end-points to the corresponding end-points of the dual base. -/
theorem IsLonely.isTiedTo_tiedBoundary {p : Fin (Ω.numItems + 1)} (h₁ : Ω.left μ ≤ p)
    (h₂ : p ≤ Ω.right μ) : Ω.IsTiedTo μ p (Ω.tiedBoundary μ p) := by
  rcases h₁.eq_or_lt with rfl | h₁
  · exact isTiedTo_left.isTiedTo_tiedBoundary
  rcases h₂.eq_or_lt with rfl | h₂
  · exact isTiedTo_right.isTiedTo_tiedBoundary
  obtain ⟨q, hq⟩ := h.tied p (Ω.crosses_iff.2 ⟨h₁, h₂⟩)
  exact (isTiedTo_of_mem_connections hq).isTiedTo_tiedBoundary

/-! ### The segments of `Δ(μ)` matched with the items of `μ` -/

section Segments

variable {k : Fin Ω.numItems}

include h in
private theorem isTiedTo_castSucc (hk : k ∈ Ω.baseItems μ) :
    Ω.IsTiedTo μ k.castSucc (Ω.tiedBoundary μ k.castSucc) :=
  h.isTiedTo_tiedBoundary (left_le_castSucc_of_mem_baseItems hk)
    (k.castSucc_lt_succ.le.trans (succ_le_right_of_mem_baseItems hk))

include h in
private theorem isTiedTo_succ (hk : k ∈ Ω.baseItems μ) :
    Ω.IsTiedTo μ k.succ (Ω.tiedBoundary μ k.succ) :=
  h.isTiedTo_tiedBoundary ((left_le_castSucc_of_mem_baseItems hk).trans k.castSucc_lt_succ.le)
    (succ_le_right_of_mem_baseItems hk)

include h in
/-- The segment of `Δ(μ)` matched with an item of `μ` lies in `Δ(μ)`. -/
private theorem tiedSegment_bounds (hk : k ∈ Ω.baseItems μ) :
    (Ω.left (Ω.dual μ) : ℕ) ≤ min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) ∧
      max (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) ≤
        Ω.right (Ω.dual μ) := by
  have := Fin.le_def.1 (isTiedTo_castSucc h hk).left_dual_le
  have := Fin.le_def.1 (isTiedTo_succ h hk).left_dual_le
  have := Fin.le_def.1 (isTiedTo_castSucc h hk).le_right_dual
  have := Fin.le_def.1 (isTiedTo_succ h hk).le_right_dual
  lia

include h hΩ in
/-- In a formally consistent generalised equation the segment of `Δ(μ)` matched with an item of
`μ` is nonempty. -/
private theorem min_lt_max_tiedBoundary (hk : k ∈ Ω.baseItems μ) :
    min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) <
      max (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ) := by
  have h₁ := isTiedTo_castSucc h hk
  have h₂ := isTiedTo_succ h hk
  rw [min_lt_max, Ne, ← Fin.ext_iff]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · exact (hΩ.lt_of_isTiedTo_of_sign_eq hs h₁ h₂ k.castSucc_lt_succ).ne
  · exact (hΩ.lt_of_isTiedTo_of_sign_ne hs h₁ h₂ k.castSucc_lt_succ).ne'

include h hΩ in
/-- The item of `Δ(μ)` matched with an item of `μ` is an item of `Δ(μ)`, hence not of `μ`. -/
private theorem dualItem_notMem (hk : k ∈ Ω.baseItems μ) : Ω.dualItem μ k ∉ Ω.baseItems μ := by
  obtain ⟨h₁, h₃⟩ := tiedSegment_bounds h hk
  have h₂ := min_lt_max_tiedBoundary h hΩ hk
  refine Finset.disjoint_left.1 (h.disjoint _ h.dual_ne) (Ω.mem_baseItems.2 ?_)
  rw [val_dualItem (by have := Fin.is_le (Ω.right (Ω.dual μ)); lia)]
  exact ⟨h₁, by lia⟩

include h hΩ in
/-- After the constant bases of `μ` are moved, no constant base lies on an item of `μ`. -/
private theorem notMem_baseItems_of_mem_constBases {b : Fin Ω.numItems × (A × Bool)}
    (hb : b ∈ (Ω.moveConstBases μ).constBases) : b.1 ∉ Ω.baseItems μ := by
  rcases (Ω.mem_constBases_moveConstBases μ).1 hb with ⟨-, hk⟩ | ⟨b', -, hk, rfl⟩
  · exact hk
  · exact dualItem_notMem h hΩ hk

variable (Ω μ) in
/-- The word of the segment of `Δ(μ)` matched with the item `k` of `μ`, in the items of `Ω`. -/
private def tiedSegment (k : Fin Ω.numItems) : List ((Fin Ω.numItems ⊕ A) × Bool) :=
  Ω.segment (min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ))
    (max (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ))
    (decide (Ω.sign μ = Ω.sign (Ω.dual μ)))

include h in
/-- The two end-points of a constant item of `μ` are tied to the end-points of a single item:
its matched segment is the item `Ω.dualItem μ k`. -/
private theorem tiedSegment_of_mem_constBases {b : Fin Ω.numItems × (A × Bool)}
    (hb : b ∈ Ω.constBases) (hk : b.1 ∈ Ω.baseItems μ) :
    Ω.tiedSegment μ b.1 =
      [(Sum.inl (Ω.dualItem μ b.1), decide (Ω.sign μ = Ω.sign (Ω.dual μ)))] := by
  have hadj := h.adjacent_of_mem_constBases b hb hk _ _ (isTiedTo_castSucc h hk)
    (isTiedTo_succ h hk)
  have hmax : max (Ω.tiedBoundary μ b.1.castSucc : ℕ) (Ω.tiedBoundary μ b.1.succ) =
      min (Ω.tiedBoundary μ b.1.castSucc : ℕ) (Ω.tiedBoundary μ b.1.succ) + 1 := by
    lia
  have hlt : min (Ω.tiedBoundary μ b.1.castSucc : ℕ) (Ω.tiedBoundary μ b.1.succ) < Ω.numItems := by
    have := Fin.is_le (Ω.tiedBoundary μ b.1.castSucc)
    have := Fin.is_le (Ω.tiedBoundary μ b.1.succ)
    lia
  have hd : Ω.dualItem μ b.1 = ⟨_, hlt⟩ := Fin.ext (val_dualItem hlt)
  rw [tiedSegment, hmax, hd]
  exact Ω.segment_succ ⟨_, hlt⟩ _

/-- An item of a lonely base `μ` is sent by `π` to the segment of `Δ(μ)` between the boundaries
tied to its end-points, inverted when `ε(μ) ≠ ε(Δμ)`; here this word of the result is read in the
items of `Ω`. -/
theorem restoreWord_removeLonelyList_of_mem (hk : k ∈ Ω.baseItems μ) :
    restoreWord (Ω.baseItems μ) (Ω.removeLonelyList μ h k) =
      Ω.segment (min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ))
        (max (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ))
        (decide (Ω.sign μ = Ω.sign (Ω.dual μ))) := by
  obtain ⟨h₁, h₃⟩ := tiedSegment_bounds h hk
  -- The matched segment lies in `Δ(μ)`, which contains no item of `μ`.
  have hS : Disjoint (((Ω.moveConstBases μ).removePair μ).sectionItems
      (min (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ))
      (max (Ω.tiedBoundary μ k.castSucc : ℕ) (Ω.tiedBoundary μ k.succ))) (Ω.baseItems μ) :=
    Finset.disjoint_left.2 fun l hl => Finset.disjoint_left.1 (h.disjoint _ h.dual_ne)
      (Ω.mem_baseItems.2 (by
        have := ((Ω.moveConstBases μ).removePair μ).mem_sectionItems.1 hl
        lia))
  have := restoreWord_segment_deleteItems h.disjoint_baseItems_removePair hS
    (decide (Ω.sign μ = Ω.sign (Ω.dual μ)))
  simp only [segment_removeBases, segment_moveConstBases] at this
  rw [removeLonelyList, ite_eq_left hk, this]

end Segments

/-! ### Evaluating words at an assignment of the items -/

section Eval

variable {H : Type*} [Group H] (ι : FreeGroup A →* H)

/-- The value of a word in the items `Fin n` and the letters of `A` at an assignment `v` of the
items in an `F(A)`-group. -/
private def evalWord {n : ℕ} (v : Fin n → H) (w : List ((Fin n ⊕ A) × Bool)) : H :=
  FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk w)

private theorem evalWord_append {n : ℕ} (v : Fin n → H) (w w' : List ((Fin n ⊕ A) × Bool)) :
    evalWord ι v (w ++ w') = evalWord ι v w * evalWord ι v w' := by
  rw [evalWord, evalWord, evalWord, ← FreeGroup.mul_mk, map_mul]

private theorem evalWord_restoreWord {n : ℕ} (S : Finset (Fin n)) (v : Fin n → H)
    (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    evalWord ι v (restoreWord S w) = evalWord ι (v ∘ Sᶜ.orderEmbOfFin rfl) w := by
  rw [evalWord, evalWord, mk_restoreWord, ← EqIneqSystem.eval_eq_lift,
    EqIneqSystem.eval_map_sumMap, EqIneqSystem.eval_eq_lift]

variable (Ω) in
/-- The value of the prefix `h[0, i]` at `v`. -/
private def prefixVal (v : Fin Ω.numItems → H) (i : ℕ) : H :=
  evalWord ι v (Ω.segment 0 i true)

private theorem evalWord_segment_true (v : Fin Ω.numItems → H) {i j : ℕ} (hij : i ≤ j) :
    evalWord ι v (Ω.segment i j true) = (prefixVal Ω ι v i)⁻¹ * prefixVal Ω ι v j := by
  rw [prefixVal, prefixVal, ← Ω.segment_append (Nat.zero_le i) hij, evalWord_append,
    inv_mul_cancel_left]

private theorem evalWord_segment (v : Fin Ω.numItems → H) {i j : ℕ} (hij : i ≤ j) (s : Bool) :
    evalWord ι v (Ω.segment i j s) = cond s ((prefixVal Ω ι v i)⁻¹ * prefixVal Ω ι v j)
      ((prefixVal Ω ι v i)⁻¹ * prefixVal Ω ι v j)⁻¹ := by
  rw [← evalWord_segment_true ι v hij]
  exact Ω.lift_mk_segment _ i j s

/-- The value of an item is the quotient of the values of the prefixes ending at its two
end-points. -/
private theorem apply_eq_prefixVal (v : Fin Ω.numItems → H) (k : Fin Ω.numItems) :
    v k = (prefixVal Ω ι v k)⁻¹ * prefixVal Ω ι v (k + 1) := by
  rw [← evalWord_segment_true ι v (Nat.le_succ _), Ω.segment_succ, evalWord,
    FreeGroup.lift_mk_singleton]
  rfl

variable (Ω μ) in
/-- The defect of the tie at a boundary `p` of `μ`: the value of `h[0, p]` divided by the value
of `h[0, b(p)]`. The equations of `μ` and `Δ(μ)` say that it is constant on the boundaries of
`μ`. -/
private def tiedDefect (v : Fin Ω.numItems → H) (p : Fin (Ω.numItems + 1)) : H :=
  prefixVal Ω ι v p * (prefixVal Ω ι v (Ω.tiedBoundary μ p))⁻¹

include h hΩ in
private theorem evalWord_tiedSegment (v : Fin Ω.numItems → H) {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) : evalWord ι v (Ω.tiedSegment μ k) =
      (prefixVal Ω ι v (Ω.tiedBoundary μ k.castSucc))⁻¹ *
        prefixVal Ω ι v (Ω.tiedBoundary μ k.succ) := by
  have h₁ := isTiedTo_castSucc h hk
  have h₂ := isTiedTo_succ h hk
  rw [tiedSegment]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · have hlt := Fin.lt_def.1 (hΩ.lt_of_isTiedTo_of_sign_eq hs h₁ h₂ k.castSucc_lt_succ)
    rw [min_eq_left hlt.le, max_eq_right hlt.le, evalWord_segment ι v hlt.le]
    simp [hs]
  · have hlt := Fin.lt_def.1 (hΩ.lt_of_isTiedTo_of_sign_ne hs h₁ h₂ k.castSucc_lt_succ)
    rw [min_eq_right hlt.le, max_eq_left hlt.le, evalWord_segment ι v hlt.le]
    simp [hs]

include h hΩ in
/-- An item of `μ` takes the value of its matched segment exactly when the defect of the tie is
the same at its two end-points. -/
private theorem eq_evalWord_tiedSegment_iff (v : Fin Ω.numItems → H) {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) : v k = evalWord ι v (Ω.tiedSegment μ k) ↔
      tiedDefect Ω μ ι v k.succ = tiedDefect Ω μ ι v k.castSucc := by
  rw [evalWord_tiedSegment h hΩ ι v hk, apply_eq_prefixVal ι v k,
    inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv]
  rfl

include h hΩ in
/-- If every item of `μ` takes the value of its matched segment, the defect of the tie is constant
on the boundaries of `μ`. -/
private theorem tiedDefect_eq_of_forall (v : Fin Ω.numItems → H)
    (hI : ∀ k ∈ Ω.baseItems μ, v k = evalWord ι v (Ω.tiedSegment μ k)) {p : Fin (Ω.numItems + 1)}
    (h₁ : Ω.left μ ≤ p) (h₂ : p ≤ Ω.right μ) :
    tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Fin.le_def.1 h₁)
  induction m generalizing p with
  | zero => rw [Fin.ext (hm.trans (Nat.add_zero _))]
  | succ m ih =>
    have := Fin.le_def.1 h₂
    have := Fin.is_le (Ω.right μ)
    let k : Fin Ω.numItems := ⟨Ω.left μ + m, by lia⟩
    have hk : k ∈ Ω.baseItems μ := Ω.mem_baseItems.2 ⟨by simp [k], by simp only [k]; lia⟩
    have hp : p = k.succ := Fin.ext (by simp [k]; lia)
    rw [hp, (eq_evalWord_tiedSegment_iff h hΩ ι v hk).1 (hI k hk)]
    exact ih (Fin.le_def.2 (by simp [k])) (Fin.le_def.2 (by simp [k]; lia)) (by simp [k])

include h hΩ in
/-- If the defect of the tie is constant on the boundaries of `μ`, every item of `μ` takes the
value of its matched segment. -/
private theorem eq_evalWord_tiedSegment_of_forall (v : Fin Ω.numItems → H)
    (hC : ∀ p : Fin (Ω.numItems + 1), Ω.left μ ≤ p → p ≤ Ω.right μ →
      tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ)) {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) : v k = evalWord ι v (Ω.tiedSegment μ k) := by
  have h₁ := left_le_castSucc_of_mem_baseItems hk
  have h₂ := succ_le_right_of_mem_baseItems hk
  exact (eq_evalWord_tiedSegment_iff h hΩ ι v hk).2 <|
    (hC _ (h₁.trans k.castSucc_lt_succ.le) h₂).trans (hC _ h₁ (k.castSucc_lt_succ.le.trans h₂)).symm

/-- The basic equation of `μ` holds exactly when the defect of the tie is the same at the two
end-points of `μ`. -/
private theorem basicEquation_iff (v : Fin Ω.numItems → H) :
    evalWord ι v (Ω.basicEquation μ).1 = evalWord ι v (Ω.basicEquation μ).2 ↔
      tiedDefect Ω μ ι v (Ω.right μ) = tiedDefect Ω μ ι v (Ω.left μ) := by
  rw [basicEquation_fst, basicEquation_snd,
    evalWord_segment ι v (Fin.le_def.1 (Ω.left_lt_right μ).le),
    evalWord_segment ι v (Fin.le_def.1 (Ω.left_lt_right (Ω.dual μ)).le),
    tiedDefect, tiedDefect, tiedBoundary_left, tiedBoundary_right]
  cases Ω.sign μ <;> cases Ω.sign (Ω.dual μ) <;>
    simp [inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv, eq_comm]

include hΩ in
/-- The boundary equation of a connection `(p, μ, q)` holds exactly when the defect of the tie is
the same at `p` and at the initial boundary of `μ`. -/
private theorem boundaryEquation_iff (v : Fin Ω.numItems → H) {p q : Fin (Ω.numItems + 1)}
    (hc : (p, μ, q) ∈ Ω.connections) :
    evalWord ι v (Ω.boundaryEquation (p, μ, q)).1 = evalWord ι v (Ω.boundaryEquation (p, μ, q)).2 ↔
      tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ) := by
  obtain ⟨hp₁, -, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections _ hc
  have hq := hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections hc)
  rw [boundaryEquation_fst, evalWord_segment ι v (Fin.le_def.1 hp₁.le)]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) Ω hs,
      evalWord_segment ι v (Fin.le_def.1 hq₁.le)]
    simp [tiedDefect, hq, hs, inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv]
  · rw [boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) Ω hs,
      evalWord_segment ι v (Fin.le_def.1 hq₂.le)]
    simp [tiedDefect, hq, hs, inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv]

include hΩ in
/-- The boundary equation of a connection `(q, Δ(μ), p)` holds when the defect of the tie is the
same at `p` and at the two end-points of `μ`. -/
private theorem boundaryEquation_dual_eq (v : Fin Ω.numItems → H) {p q : Fin (Ω.numItems + 1)}
    (hc : (p, μ, q) ∈ Ω.connections) (hp : tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ))
    (hr : tiedDefect Ω μ ι v (Ω.right μ) = tiedDefect Ω μ ι v (Ω.left μ)) :
    evalWord ι v (Ω.boundaryEquation (q, Ω.dual μ, p)).1 =
      evalWord ι v (Ω.boundaryEquation (q, Ω.dual μ, p)).2 := by
  obtain ⟨hp₁, hp₂, hq₁, -⟩ := Ω.bounds_of_mem_connections _ hc
  have hq := hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections hc)
  rw [eq_comm, boundaryEquation_fst, evalWord_segment ι v (Fin.le_def.1 hq₁.le)]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [boundaryEquation_snd_of_sign_eq (c := (q, Ω.dual μ, p)) Ω
      (by rw [Ω.dual_involutive μ]; exact hs.symm), Ω.dual_involutive μ,
      evalWord_segment ι v (Fin.le_def.1 hp₁.le)]
    simpa [tiedDefect, hq, hs, inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv] using hp
  · rw [boundaryEquation_snd_of_sign_ne (c := (q, Ω.dual μ, p)) Ω
      (by rw [Ω.dual_involutive μ]; exact Ne.symm hs), Ω.dual_involutive μ,
      evalWord_segment ι v (Fin.le_def.1 hp₂.le)]
    simpa [tiedDefect, hq, hs, inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv] using hp.trans hr.symm

/-- If the defect of the tie is constant on the boundaries of `μ`, the basic equations of `μ` and
`Δ(μ)` hold. -/
private theorem basicEquation_eq_of_tiedDefect (v : Fin Ω.numItems → H)
    (hC : ∀ p : Fin (Ω.numItems + 1), Ω.left μ ≤ p → p ≤ Ω.right μ →
      tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ)) {ν : Fin Ω.numBases}
    (hν : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) :
    evalWord ι v (Ω.basicEquation ν).1 = evalWord ι v (Ω.basicEquation ν).2 := by
  have hr := (basicEquation_iff ι v).2 (hC _ (Ω.left_lt_right μ).le le_rfl)
  rcases Finset.mem_insert.1 hν with rfl | hν
  · exact hr
  · rw [Finset.mem_singleton.1 hν, basicEquation_dual]
    exact hr.symm

include hΩ in
/-- If the defect of the tie is constant on the boundaries of `μ`, the boundary equations of the
connections through `μ` and `Δ(μ)` hold. -/
private theorem boundaryEquation_eq_of_tiedDefect (v : Fin Ω.numItems → H)
    (hC : ∀ p : Fin (Ω.numItems + 1), Ω.left μ ≤ p → p ≤ Ω.right μ →
      tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ))
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections)
    (hν : c.2.1 ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) :
    evalWord ι v (Ω.boundaryEquation c).1 = evalWord ι v (Ω.boundaryEquation c).2 := by
  obtain ⟨p, ν, q⟩ := c
  rcases Finset.mem_insert.1 hν with rfl | hν
  · obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections _ hc
    exact (boundaryEquation_iff hΩ ι v hc).2 (hC p hp₁.le hp₂.le)
  · obtain rfl := Finset.mem_singleton.1 hν
    have hc' : (q, μ, p) ∈ Ω.connections := by
      simpa [Ω.dual_involutive μ] using Ω.dual_mem_connections _ hc
    obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections _ hc'
    exact boundaryEquation_dual_eq hΩ ι v hc' (hC q hp₁.le hp₂.le)
      (hC _ (Ω.left_lt_right μ).le le_rfl)

include h hΩ in
/-- At a point of `Ω*` the defect of the tie is constant on the boundaries of `μ`. -/
private theorem tiedDefect_eq_of_mem_V {v : Fin Ω.numItems → H} (hv : v ∈ V ι Ω.toSystem)
    {p : Fin (Ω.numItems + 1)} (h₁ : Ω.left μ ≤ p) (h₂ : p ≤ Ω.right μ) :
    tiedDefect Ω μ ι v p = tiedDefect Ω μ ι v (Ω.left μ) := by
  rw [mem_V_toSystem_iff] at hv
  rcases h₁.eq_or_lt with rfl | h₁
  · rfl
  rcases h₂.eq_or_lt with rfl | h₂
  · exact (basicEquation_iff ι v).1 (hv _ (Ω.basicEquation_mem_equations μ))
  obtain ⟨q, hq⟩ := h.tied p (Ω.crosses_iff.2 ⟨h₁, h₂⟩)
  exact (boundaryEquation_iff hΩ ι v hq).1 (hv _ (Ω.boundaryEquation_mem_equations hq))

include h in
/-- If the items of `μ` take the values of their matched segments, the coefficient equation of a
constant base on an item of `μ` holds exactly when the coefficient equation of the moved constant
base holds. -/
private theorem coeffEquation_eq_iff (v : Fin Ω.numItems → H)
    (hI : ∀ k ∈ Ω.baseItems μ, v k = evalWord ι v (Ω.tiedSegment μ k))
    {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ Ω.constBases) (hk : b.1 ∈ Ω.baseItems μ) :
    evalWord ι v (Ω.coeffEquation b).1 = evalWord ι v (Ω.coeffEquation b).2 ↔
      evalWord ι v (Ω.coeffEquation (Ω.dualItem μ b.1,
        (b.2.1, if Ω.sign μ = Ω.sign (Ω.dual μ) then b.2.2 else !b.2.2))).1 =
      evalWord ι v (Ω.coeffEquation (Ω.dualItem μ b.1,
        (b.2.1, if Ω.sign μ = Ω.sign (Ω.dual μ) then b.2.2 else !b.2.2))).2 := by
  simp only [evalWord, coeffEquation_fst, coeffEquation_snd, FreeGroup.lift_mk_singleton,
    Bool.cond_true, Sum.elim_inl, Sum.elim_inr]
  rw [hI _ hk, tiedSegment_of_mem_constBases h hb hk, evalWord, FreeGroup.lift_mk_singleton,
    Sum.elim_inl]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> cases b.2.2 <;> simp [hs, inv_eq_iff_eq_inv]

/-! ### The substitution `π` -/

/-- At an assignment `v` of the items of the result in an `F(A)`-group, `π` sends the item `k` of
`Ω` to the value of the word `Ω.removeLonelyList μ h k` at `v`. -/
theorem wordMap_removeLonelyWord_apply (v : Fin (Ω.removeLonely μ h).numItems → H)
    (k : Fin Ω.numItems) : wordMap ι (Ω.removeLonelyWord μ h) v k =
      FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk (Ω.removeLonelyList μ h k)) := by
  rw [wordMap_apply, removeLonelyWord, EqIneqSystem.eval_toGX, EqIneqSystem.eval_eq_lift]

/-- `π` sends an item outside `μ` to the corresponding item of the result. -/
theorem wordMap_removeLonelyWord_orderEmbOfFin (v : Fin (Ω.removeLonely μ h).numItems → H)
    (j : Fin (Ω.baseItems μ)ᶜ.card) :
    wordMap ι (Ω.removeLonelyWord μ h) v ((Ω.baseItems μ)ᶜ.orderEmbOfFin rfl j) = v j := by
  rw [wordMap_removeLonelyWord_apply, removeLonelyList_of_notMem, FreeGroup.lift_mk_singleton]
  rfl

private theorem wordMap_removeLonelyWord_comp_of_mem (v : Fin Ω.numItems → H) {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) :
    wordMap ι (Ω.removeLonelyWord μ h) (v ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl) k =
      evalWord ι v (Ω.tiedSegment μ k) := by
  rw [wordMap_removeLonelyWord_apply, ← evalWord.eq_1, ← evalWord_restoreWord,
    restoreWord_removeLonelyList_of_mem h hk, tiedSegment]

private theorem wordMap_removeLonelyWord_comp_of_notMem (v : Fin Ω.numItems → H)
    {k : Fin Ω.numItems} (hk : k ∉ Ω.baseItems μ) :
    wordMap ι (Ω.removeLonelyWord μ h) (v ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl) k = v k := by
  have := wordMap_removeLonelyWord_orderEmbOfFin h ι (v ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl)
    ⟨(Ω.baseItems μ).collapse k, Finset.collapse_lt_card hk⟩
  simpa only [Function.comp_apply, Finset.orderEmbOfFin_collapse hk] using this

include hΩ in
/-- Restricting an assignment of the items of `Ω` to the items outside `μ` gives a point of
`Ω′*` exactly when the equations of `Ω` without `μ, Δ(μ)` and with the constant bases moved
hold. -/
private theorem comp_mem_V_iff (v : Fin Ω.numItems → H) :
    v ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl ∈ V ι (Ω.removeLonely μ h).toSystem ↔
      ∀ e ∈ ((Ω.moveConstBases μ).removePair μ).equations,
        evalWord ι v e.1 = evalWord ι v e.2 := by
  rw [mem_V_toSystem_iff]
  constructor
  · intro hv e he
    rcases equations_subset_union_deleteItems h.disjoint_baseItems_removePair he with
      ⟨e', he', rfl⟩ | ⟨b, ⟨hb, hk⟩, rfl⟩
    · simp only [restoreEquation_fst, restoreEquation_snd, evalWord_restoreWord]
      exact hv e' he'
    · exact absurd hk (notMem_baseItems_of_mem_constBases h hΩ hb)
  · intro hv e' he'
    have := hv _ (image_equations_deleteItems_subset h.disjoint_baseItems_removePair ⟨e', he', rfl⟩)
    simp only [restoreEquation_fst, restoreEquation_snd, evalWord_restoreWord] at this
    exact this

end Eval

include hΩ in
/-- **ET4 on group solutions.** The substitution `π` maps the points of `Ω′*` to points of `Ω*`
in every `F(A)`-group, where `Ω′` is `Ω` with a lonely base removed. -/
theorem mapsTo_wordMap_removeLonely {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    Set.MapsTo (wordMap ι (Ω.removeLonelyWord μ h)) (V ι (Ω.removeLonely μ h).toSystem)
      (V ι Ω.toSystem) := by
  intro v' hv'
  set v := wordMap ι (Ω.removeLonelyWord μ h) v'
  have hcomp : v ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl = v' :=
    funext (wordMap_removeLonelyWord_orderEmbOfFin h ι v')
  -- The items of `μ` take the values of their matched segments, by definition of `π`.
  have hI : ∀ k ∈ Ω.baseItems μ, v k = evalWord ι v (Ω.tiedSegment μ k) := fun k hk => by
    have := wordMap_removeLonelyWord_comp_of_mem h ι v hk
    rwa [hcomp] at this
  have hC := fun p => tiedDefect_eq_of_forall h hΩ ι v hI (p := p)
  have hv := (comp_mem_V_iff h hΩ ι v).1 (hcomp ▸ hv')
  refine Ω.mem_V_toSystem_iff.2 fun e he => ?_
  rcases Ω.equations_subset_union_moveConstBases μ he with he | ⟨b, ⟨hb, hk⟩, rfl⟩
  · rcases equations_subset_union_removeBases _ he with he | ⟨ν, hν, rfl⟩ | ⟨c, ⟨hc, hν⟩, rfl⟩
    · exact hv e he
    · rw [basicEquation_moveConstBases]
      exact basicEquation_eq_of_tiedDefect ι v hC hν
    · rw [boundaryEquation_moveConstBases]
      exact boundaryEquation_eq_of_tiedDefect hΩ ι v hC hc hν
  · refine (coeffEquation_eq_iff h ι v hI hb hk).2 ?_
    simpa only [coeffEquation_removeBases, coeffEquation_moveConstBases] using
      hv _ (((Ω.moveConstBases μ).removePair μ).coeffEquation_mem_equations
        (Ω.mem_constBases_moveConstBases_of_mem μ hb hk))

include hΩ in
/-- **ET4 on group solutions.** Every point of `Ω*` in an `F(A)`-group is the image under `π` of
exactly one point of `Ω′*`, where `Ω′` is `Ω` with a lonely base removed. -/
theorem bijOn_wordMap_removeLonely {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    Set.BijOn (wordMap ι (Ω.removeLonelyWord μ h)) (V ι (Ω.removeLonely μ h).toSystem)
      (V ι Ω.toSystem) := by
  refine ⟨mapsTo_wordMap_removeLonely h hΩ ι, fun v₁ _ v₂ _ he => funext fun j => ?_,
    fun v hv => ?_⟩
  · rw [← wordMap_removeLonelyWord_orderEmbOfFin h ι v₁ j, he,
      wordMap_removeLonelyWord_orderEmbOfFin]
  -- A point of `Ω*` is the image of its restriction to the items outside `μ`.
  have hI : ∀ k ∈ Ω.baseItems μ, v k = evalWord ι v (Ω.tiedSegment μ k) := fun k hk =>
    eq_evalWord_tiedSegment_of_forall h hΩ ι v (fun _ => tiedDefect_eq_of_mem_V h hΩ ι hv) hk
  rw [mem_V_toSystem_iff] at hv
  refine ⟨v ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl, (comp_mem_V_iff h hΩ ι v).2 fun e he => ?_,
    funext fun k => ?_⟩
  · rcases Ω.equations_moveConstBases_subset_union μ (equations_removeBases_subset _ he) with
      he | ⟨_, ⟨b, ⟨hb, hk⟩, rfl⟩, rfl⟩
    · exact hv e he
    · exact (coeffEquation_eq_iff h ι v hI hb hk).1 (hv _ (Ω.coeffEquation_mem_equations hb))
  · by_cases hk : k ∈ Ω.baseItems μ
    · rw [wordMap_removeLonelyWord_comp_of_mem h ι v hk, ← hI k hk]
    · exact wordMap_removeLonelyWord_comp_of_notMem h ι v hk

/-- **ET4 on coordinate groups.** The `F(A)`-homomorphism `π : F_{R(Ω)} → F_{R(Ω′)}`, where `Ω′`
is `Ω` with a lonely base removed. -/
noncomputable def removeLonelyHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.removeLonely μ h).toSystem) :=
  CoordGroup.homOfMapsToWordMap _ _ _ _ (mapsTo_wordMap_removeLonely h hΩ _)

/-- The homomorphism of ET4 sends each item to its word. -/
theorem removeLonelyHom_inr_of (k : Fin Ω.numItems) :
    removeLonelyHom h hΩ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) :
      Ω.coordGroup) = (Ω.removeLonelyWord μ h k : (Ω.removeLonely μ h).coordGroup) := by
  rw [removeLonelyHom, CoordGroup.homOfMapsToWordMap_mk, eval_inr_of]

/-- **ET4 on coordinate groups.** The homomorphism `π : F_{R(Ω)} → F_{R(Ω′)}` is an
isomorphism. -/
theorem removeLonelyHom_bijective : Function.Bijective (removeLonelyHom h hΩ) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_, fun y => ?_⟩
  · -- An equation vanishing on `Ω′*` after substituting `π` vanishes on `Ω*`, since every point of
    -- `Ω*` is the image of a point of `Ω′*`.
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    rw [removeLonelyHom, CoordGroup.homOfMapsToWordMap_mk, QuotientGroup.eq_one_iff,
      mem_Rad] at hx
    refine (QuotientGroup.eq_one_iff _).2 (mem_Rad.2 fun v hv => ?_)
    obtain ⟨v', hv', rfl⟩ := (bijOn_wordMap_removeLonely h hΩ _).surjOn hv
    rw [← hx v' hv', ← MonoidHom.comp_apply, eval_comp_eval]
  · -- Every item of `Ω′` is the image under `π` of an item of `Ω` outside `μ`.
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    have hw : wordMap inl (fun j => inr (FreeGroup.of ((Ω.baseItems μ)ᶜ.orderEmbOfFin rfl j)))
        (Ω.removeLonelyWord μ h) = fun j => inr (FreeGroup.of j) := by
      funext j
      rw [wordMap_apply, eval_inr_of, removeLonelyWord, removeLonelyList_of_notMem,
        ← FreeGroup.of.eq_1, EqIneqSystem.toGX_of_inl]
    refine ⟨((eval inl fun j => inr (FreeGroup.of ((Ω.baseItems μ)ᶜ.orderEmbOfFin rfl j))) t :
      GX (FreeGroup A) (Fin Ω.numItems)), ?_⟩
    rw [removeLonelyHom, CoordGroup.homOfMapsToWordMap_mk, ← MonoidHom.comp_apply,
      eval_comp_eval, hw, eval_inl_inr_of, MonoidHom.id_apply]

/-! ### Examples -/

/-- The generalised equation `h₀ = h₁` over `F(a, b)`: two items and the dual bases `μ = [0, 1]`,
`Δ(μ) = [1, 2]`. -/
private abbrev equalItems : GenEq (Fin 2) where
  numItems := 2
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- The base `μ = [0, 1]` of `h₀ = h₁` is lonely. -/
private theorem isLonely_equalItems : equalItems.IsLonely 0 where
  dual_ne := by decide
  disjoint ν hν := Finset.disjoint_left.2 fun k hk hk' => by
    rw [mem_baseItems] at hk hk'
    revert ν k
    decide
  tied p hp := absurd (equalItems.crosses_iff.1 hp) (by revert p; decide)
  adjacent_of_mem_constBases b hb := absurd hb (Finset.notMem_empty b)

/-- Removing the lonely base `μ` of `h₀ = h₁` together with its item leaves one item. -/
private theorem numItems_removeLonely_equalItems :
    (equalItems.removeLonely 0 isLonely_equalItems).numItems = 1 := by
  have h : equalItems.baseItems 0 = {0} := by
    ext k
    rw [mem_baseItems, Finset.mem_singleton]
    revert k
    decide
  simp [h, Finset.card_compl]

/-- Removing the lonely base `μ` of `h₀ = h₁` leaves no variable base. -/
example : (equalItems.removeLonely 0 isLonely_equalItems).numBases = 0 := by decide

/-- Removing the lonely base of `h₀ = h₁` retains the free assignment of the remaining item: the
result imposes no equation, so every assignment is a point, in every `F(a, b)`-group. By
`TauCeti.GenEq.bijOn_wordMap_removeLonely` the points of `h₀ = h₁` are then the pairs `(x, x)`. -/
private theorem V_removeLonely_equalItems {H : Type*} [Group H] (ι : FreeGroup (Fin 2) →* H) :
    V ι (equalItems.removeLonely 0 isLonely_equalItems).toSystem = Set.univ := by
  refine Set.eq_univ_of_forall fun v => (mem_V_toSystem_iff _).2 ?_
  refine (forall_mem_equations _).2 ⟨fun ν => absurd ν.is_lt (by decide +revert), fun b hb => ?_,
    fun c hc => ?_⟩
  · rw [mem_constBases_deleteItems] at hb
    simp at hb
  · obtain ⟨c', hc', -⟩ := (mem_connections_deleteItems _).1 hc
    exact absurd ((mem_connections_removeBases _).1 hc') (Finset.notMem_empty _)

/-- The coordinate group of `h₀ = h₁` with its lonely base removed is not the coordinate group of
a point: its item is not a constant. -/
example (g : FreeGroup (Fin 2)) :
    ((inr (FreeGroup.of ⟨0, numItems_removeLonely_equalItems.symm ▸ one_pos⟩) :
      GX (FreeGroup (Fin 2)) (Fin (equalItems.removeLonely 0 isLonely_equalItems).numItems)) :
        (equalItems.removeLonely 0 isLonely_equalItems).coordGroup) ≠
      CoordGroup.coeff _ _ g := by
  intro hg
  have hV := V_removeLonely_equalItems (MonoidHom.id (FreeGroup (Fin 2)))
  have h₁ := congrArg (CoordGroup.evalGHom (fun _ => 1) (hV ▸ Set.mem_univ _)) hg
  have h₂ := congrArg (CoordGroup.evalGHom (fun _ => FreeGroup.of 0) (hV ▸ Set.mem_univ _)) hg
  simp only [CoordGroup.coeff_apply, CoordGroup.evalGHom_mk, eval_inr_of, eval_inl] at h₁ h₂
  exact FreeGroup.of_ne_one (0 : Fin 2) (h₂.trans h₁.symm)

/-- The generalised equation `h₀ = h₁h₂`, `h₀ = a` over `F(a, b)`: the dual bases `μ = [0, 1]` and
`Δ(μ) = [1, 3]` and a constant base on the item of `μ`. -/
private abbrev constEndItem : GenEq (Fin 2) where
  numItems := 3
  numBases := 2
  left := ![0, 1]
  right := ![1, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := {(0, (0, true))}
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- `h₀ = h₁h₂`, `h₀ = a` is formally consistent, and `μ = [0, 1]` meets no other variable base and
has no inner boundary: formal consistency only constrains constant items between two boundary
connections. -/
example : constEndItem.IsFormallyConsistent ∧ constEndItem.dual 0 ≠ 0 ∧
    Disjoint (constEndItem.baseItems 1) (constEndItem.baseItems 0) ∧
    ∀ p, ¬ constEndItem.Crosses p 0 := by
  refine ⟨by decide, by decide, Finset.disjoint_left.2 fun k hk hk' => ?_,
    fun p hp => absurd (constEndItem.crosses_iff.1 hp) (by revert p; decide)⟩
  rw [mem_baseItems] at hk hk'
  revert k
  decide

/-- The base `μ = [0, 1]` of `h₀ = h₁h₂`, `h₀ = a` is not lonely: its constant item is matched with
the two items `h₁h₂`, on which the constant base cannot be moved. -/
example : ¬ constEndItem.IsLonely 0 := fun h => by
  have := h.adjacent_of_mem_constBases (0, (0, true)) (Finset.mem_singleton_self _)
    (by rw [mem_baseItems]; decide) 1 3 (isTiedTo_left_iff.2 (by decide))
    (isTiedTo_right_iff.2 (by decide))
  revert this
  decide

end GenEq

end TauCeti
