/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import TauCeti.Data.List.Count
import TauCeti.Data.List.Flatten
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Reduced and cyclically reduced words in the free `G`-group `G[X]`

An element of the free `G`-group `G[X] = G ∗ F(X)` is a product of letters: coefficients `g ∈ G`
and variable letters `x` and `x⁻¹`. Following [IFT, §2.2], a word in these letters is *reduced*
when its coefficients are nontrivial, no two coefficients are adjacent and no variable letter is
adjacent to its inverse. Its maximal runs of variable letters are then reduced words of `F(X)`,
separated by single nontrivial coefficients, so that it is the reduced form of a free-product
element in which every syllable from `F(X)` is written out letter by letter.

The normal form theorem for the free product `G ∗ F(X)` says that every element of `G[X]` is the
product of exactly one reduced word, `reducedWord w`. It is proved here by letting `G[X]` act on
reduced words: a coefficient multiplies into the first letter or is prepended, and a variable
letter cancels against the first letter or is prepended.

A reduced word is *cyclically reduced* when moreover, if it has at least two letters, its last and
first letters do not combine: they are not both coefficients, and they are not a variable letter
and its inverse. Cyclic reduction relative to `G` writes the product of a reduced word `l` as the
conjugate of the product of a cyclically reduced word `m` by the product of an initial segment `u`
of `l`, and for every variable `x` the word `l` has as many letters `x^{±1}` as `m` plus twice as
many as `u`. When the first and last letters of `l` combine, they are removed into the conjugator:
a variable letter at the start cancels against its inverse at the end, as do coefficients `g` at
the start and `h` at the end with `h * g = 1`; if `h * g ≠ 1`, then `g m' h` is the conjugate of
`m' (h * g)` by `g`, so `g` merges into the coefficient at the end.

Counting the letters `x^{±1}` of the reduced word gives the number of occurrences
`GX.occurrences x w` of a variable `x` in an element `w ∈ G[X]`, and its finite set of occurring
variables `GX.occVars w`; a word without letters `x^{±1}` spells an element of the subgroup
`GX.avoiding x` of the words in which `x` does not occur. Cyclic reduction replaces an equation
`w = 1` over `G` by an equation with the same solutions whose left side is cyclically reduced; in a
quadratic equation, the variables of the conjugator disappear from it. This is a step towards the
standard form of strictly quadratic words [IFT, §2.7, Lemma 1].

Mathlib has no normal form for the binary free product `Monoid.Coprod`, and the source's reduced
forms write each syllable from `F(X)` as a reduced word of `F(X)`, so the normal form is proved
directly for words in letters.

## Main definitions

* `TauCeti.GroupAlgGeom.GX.letter`: the element of `G[X]` spelled by a letter.
* `TauCeti.GroupAlgGeom.GX.countVar x l`: the number of letters `x^{±1}` in a word.
* `TauCeti.GroupAlgGeom.GX.Combines`: adjacent letters that combine: two coefficients, or a
  variable letter and its inverse.
* `TauCeti.GroupAlgGeom.GX.IsReduced`, `TauCeti.GroupAlgGeom.GX.IsCyclicallyReduced`: reduced and
  cyclically reduced words.
* `TauCeti.GroupAlgGeom.GX.invRev`: the formal inverse of a word.
* `TauCeti.GroupAlgGeom.GX.reducedWord w`: the reduced word of `w ∈ G[X]`.
* `TauCeti.GroupAlgGeom.GX.occurrences x w`, `TauCeti.GroupAlgGeom.GX.occVars w`: the number of
  occurrences of `x` in `w`, and the finite set of variables occurring in `w`.

## Main results

* `TauCeti.GroupAlgGeom.GX.prod_reducedWord`, `TauCeti.GroupAlgGeom.GX.reducedWord_eq_iff`: the
  normal form theorem: `w` is the product of `reducedWord w`, which is the only reduced word with
  product `w`.
* `TauCeti.GroupAlgGeom.GX.reducedWord_inv`, `TauCeti.GroupAlgGeom.GX.reducedWord_inr`: the
  reduced words of `w⁻¹` and of the elements of `F(X)`.
* `TauCeti.GroupAlgGeom.GX.mem_range_inl_iff`, `TauCeti.GroupAlgGeom.GX.mem_range_inr_iff`: the
  elements of `G` and of `F(X)` are those whose reduced word has no variable letter, respectively
  no coefficient.
* `TauCeti.GroupAlgGeom.GX.exists_countVar_eq_add_two_mul`,
  `TauCeti.GroupAlgGeom.GX.countVar_reducedWord_le`: reduction removes letters `x^{±1}` in pairs,
  so it does not increase their number.
* `TauCeti.GroupAlgGeom.GX.isCyclicallyReduced_append_comm`,
  `TauCeti.GroupAlgGeom.GX.isCyclicallyReduced_flatten_iff`,
  `TauCeti.GroupAlgGeom.GX.isCyclicallyReduced_invRev`: cyclically reduced words are closed under
  cyclic permutation and formal inversion, and a block-level characterization of cyclic
  reducedness.
* `TauCeti.GroupAlgGeom.GX.IsReduced.exists_isCyclicallyReduced`: cyclic reduction relative to
  `G` of reduced words.
* `TauCeti.GroupAlgGeom.GX.le_occurrences`,
  `TauCeti.GroupAlgGeom.GX.exists_occurrences_add_occurrences_eq_add_two_mul`,
  `TauCeti.GroupAlgGeom.GX.occurrences_map_le`,
  `TauCeti.GroupAlgGeom.GX.occurrences_map_eq_zero`,
  `TauCeti.GroupAlgGeom.GX.mem_avoiding_iff_occurrences_eq_zero`: the extremal characterization,
  pair cancellation, homomorphism bounds, and `GX.avoiding` characterization for variable
  occurrences.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.2 and §2.7.
* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §1.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.GX

variable {G X : Type*}

/-! ### Letters -/

section Letter

variable [Group G]

/-- The element of `G[X]` spelled by a letter: a coefficient `g`, or a variable letter `(y, true)`
standing for `y` or `(y, false)` standing for `y⁻¹`. -/
def letter : G ⊕ X × Bool → GX G X
  | .inl g => inl g
  | .inr (y, true) => inr (FreeGroup.of y)
  | .inr (y, false) => (inr (FreeGroup.of y))⁻¹

@[simp]
theorem letter_inl (g : G) : letter (.inl g : G ⊕ X × Bool) = inl g := (rfl)

@[simp]
theorem letter_inr_true (y : X) : letter (.inr (y, true) : G ⊕ X × Bool) = inr (FreeGroup.of y) :=
  (rfl)

@[simp]
theorem letter_inr_false (y : X) :
    letter (.inr (y, false) : G ⊕ X × Bool) = (inr (FreeGroup.of y))⁻¹ := (rfl)

/-- Flipping the sign of a variable letter inverts the element of `G[X]` it spells. -/
@[simp]
theorem letter_inr_not (x : X) (b : Bool) :
    (letter (.inr (x, !b)) : GX G X) = (letter (.inr (x, b)))⁻¹ := by
  cases b <;> simp

/-- The product of a word in variable letters is the image in `G[X]` of the element of the free
group `F(X)` that the word spells. -/
theorem prod_map_letter_map_inr (L : List (X × Bool)) :
    ((L.map Sum.inr).map (letter (G := G))).prod = inr (FreeGroup.mk L) := by
  rw [MonoidHom.apply_freeGroup_mk (inr : FreeGroup X →* GX G X), List.map_map]
  exact congrArg List.prod <| List.map_congr_left fun ⟨_, b⟩ _ => by cases b <;> rfl

/-- The product of a word in coefficients is the image in `G[X]` of the product of the
coefficients. -/
theorem prod_map_letter_map_inl (L : List G) :
    ((L.map Sum.inl : List (G ⊕ X × Bool)).map letter).prod = inl L.prod := by
  simp [Function.comp_def, map_list_prod]

theorem letter_inr (p : X × Bool) : letter (.inr p : G ⊕ X × Bool) = inr (FreeGroup.mk [p]) := by
  simpa using prod_map_letter_map_inr (G := G) [p]

/- Every element of `G[X]` is a product of letters. -/
private theorem exists_map_letter_prod_eq (w : GX G X) :
    ∃ l : List (G ⊕ X × Bool), (l.map letter).prod = w := by
  classical
  induction w using Monoid.Coprod.induction_on with
  | inl g => exact ⟨[.inl g], by simp⟩
  | inr f => exact ⟨f.toWord.map Sum.inr, by rw [prod_map_letter_map_inr, FreeGroup.mk_toWord]⟩
  | mul u v hu hv =>
    obtain ⟨l₁, hl₁⟩ := hu
    obtain ⟨l₂, hl₂⟩ := hv
    exact ⟨l₁ ++ l₂, by simp [hl₁, hl₂]⟩

end Letter

/-! ### Counting variable letters -/

section CountVar

open Classical in
/-- The number of letters `x` and `x⁻¹` in a word in coefficients and variable letters. -/
noncomputable def countVar (x : X) (l : List (G ⊕ X × Bool)) : ℕ :=
  l.countP fun a => a.elim (fun _ => false) (fun p => p.1 = x)

@[simp]
theorem countVar_nil (x : X) : countVar x ([] : List (G ⊕ X × Bool)) = 0 := by
  simp [countVar]

@[simp]
theorem countVar_cons_inl (x : X) (g : G) (l : List (G ⊕ X × Bool)) :
    countVar x (.inl g :: l) = countVar x l := by
  simp [countVar]

@[simp]
theorem countVar_cons_inr_self (x : X) (b : Bool) (l : List (G ⊕ X × Bool)) :
    countVar x (.inr (x, b) :: l) = countVar x l + 1 := by
  simp [countVar]

@[simp]
theorem countVar_cons_inr_of_ne {x y : X} (h : y ≠ x) (b : Bool) (l : List (G ⊕ X × Bool)) :
    countVar x (.inr (y, b) :: l) = countVar x l := by
  simp [countVar, h]

@[simp]
theorem countVar_append (x : X) (l₁ l₂ : List (G ⊕ X × Bool)) :
    countVar x (l₁ ++ l₂) = countVar x l₁ + countVar x l₂ := by
  simp [countVar]

theorem countVar_eq_countP [DecidableEq X] (x : X) (l : List (G ⊕ X × Bool)) :
    countVar x l = l.countP fun a => a.elim (fun _ => false) (fun p => p.1 = x) := by
  unfold countVar
  congr!

theorem countVar_eq_zero {x : X} {l : List (G ⊕ X × Bool)} :
    countVar x l = 0 ↔ ∀ b, .inr (x, b) ∉ l := by
  classical
  rw [countVar_eq_countP, List.countP_eq_zero]
  refine ⟨fun h b hb => by simpa using h _ hb, ?_⟩
  rintro h (_ | ⟨y, b⟩) hm
  · simp
  · simpa using fun hy : y = x => h b (hy ▸ hm)

@[simp]
theorem countVar_map_inl (x : X) (L : List G) :
    countVar x (L.map Sum.inl : List (G ⊕ X × Bool)) = 0 := by
  simp [countVar, Function.comp_def]

@[simp]
theorem countVar_map_inr [DecidableEq X] (x : X) (L : List (X × Bool)) :
    countVar x (L.map Sum.inr : List (G ⊕ X × Bool)) = L.countP fun p => p.1 = x := by
  simp [countVar_eq_countP, Function.comp_def]

@[simp]
theorem countVar_flatten (x : X) (L : List (List (G ⊕ X × Bool))) :
    countVar x L.flatten = (L.map (countVar x)).sum := by
  classical
  rw [countVar_eq_countP, List.countP_flatten]
  exact congrArg List.sum (List.map_congr_left fun l _ => (countVar_eq_countP x l).symm)

/-- A word in which `x` occurs splits at its first letter `x^{±1}`. -/
theorem exists_split_of_countVar_pos {x : X} {l : List (G ⊕ X × Bool)} (h : 0 < countVar x l) :
    ∃ l₁ b l₂, l = l₁ ++ .inr (x, b) :: l₂ ∧ countVar x l₁ = 0 := by
  classical
  rw [countVar_eq_countP] at h
  obtain ⟨l₁, a, l₂, rfl, ha, h₁⟩ := List.exists_split_of_countP_pos h
  rcases a with g | ⟨y, b⟩
  · simp at ha
  · obtain rfl : y = x := by simpa using ha
    exact ⟨l₁, b, l₂, rfl, by simpa [countVar_eq_countP] using h₁⟩

/-- A word in which `x` occurs at least twice splits at its first two letters `x^{±1}`. -/
theorem exists_two_split_of_two_le_countVar {x : X} {l : List (G ⊕ X × Bool)}
    (h : 2 ≤ countVar x l) :
    ∃ l₁ b₁ l₂ b₂ l₃, l = l₁ ++ .inr (x, b₁) :: (l₂ ++ .inr (x, b₂) :: l₃) ∧
      countVar x l₁ = 0 ∧ countVar x l₂ = 0 := by
  classical
  rw [countVar_eq_countP] at h
  obtain ⟨l₁, a₁, l₂, a₂, l₃, rfl, ha₁, ha₂, h₁, h₂⟩ := List.exists_two_split_of_two_le_countP h
  rcases a₁ with g | ⟨y₁, b₁⟩; · simp at ha₁
  rcases a₂ with g | ⟨y₂, b₂⟩; · simp at ha₂
  have hy₁ : y₁ = x := by simpa using ha₁
  have hy₂ : y₂ = x := by simpa using ha₂
  subst y₁ y₂
  exact ⟨l₁, b₁, l₂, b₂, l₃, rfl,
    by simpa [countVar_eq_countP] using h₁, by simpa [countVar_eq_countP] using h₂⟩

/-- A word without variable letters is a word in coefficients. -/
theorem exists_eq_map_inl {l : List (G ⊕ X × Bool)} (h : ∀ x, countVar x l = 0) :
    ∃ L : List G, l = L.map Sum.inl := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    rcases a with g | ⟨x, b⟩
    · obtain ⟨L, rfl⟩ := ih fun x => by simpa using h x
      exact ⟨g :: L, rfl⟩
    · simpa using h x

/-- A signed variable letter `y^{±1}` does not involve `x` if and only if `y ≠ x`. -/
@[simp]
theorem letter_inr_mem_avoiding_iff [Group G] [DecidableEq X] {x y : X} {b : Bool} :
    letter (G := G) (.inr (y, b)) ∈ avoiding x ↔ y ≠ x := by
  cases b <;> simp

/-- A variable that is not spelled in a word does not occur in its product. -/
theorem prod_map_letter_mem_avoiding [Group G] [DecidableEq X] {x : X} {l : List (G ⊕ X × Bool)}
    (h : countVar x l = 0) : (l.map letter).prod ∈ avoiding x :=
  list_prod_mem <| List.forall_mem_map.2 fun
    | .inl g, _ => by simp
    | .inr (y, b), hm =>
      letter_inr_mem_avoiding_iff.2 (by rintro rfl; exact countVar_eq_zero.1 h b hm)

end CountVar

/-! ### Reduced words -/

section Reduced

/-- Two adjacent letters combine when they are both coefficients, or a variable letter `x^ε` and its
inverse `x^{-ε}`. A reduced word has no two adjacent letters that combine. -/
def Combines : G ⊕ X × Bool → G ⊕ X × Bool → Prop
  | .inl _, .inl _ => True
  | .inr p, .inr q => p.1 = q.1 ∧ p.2 ≠ q.2
  | .inl _, .inr _ => False
  | .inr _, .inl _ => False

@[simp]
theorem combines_inl_inl (g h : G) : Combines (.inl g : G ⊕ X × Bool) (.inl h) := trivial

@[simp]
theorem combines_inr_inr (p q : X × Bool) :
    Combines (.inr p : G ⊕ X × Bool) (.inr q) ↔ p.1 = q.1 ∧ p.2 ≠ q.2 := Iff.rfl

@[simp]
theorem not_combines_inl_inr (g : G) (p : X × Bool) : ¬Combines (.inl g) (.inr p) := id

@[simp]
theorem not_combines_inr_inl (p : X × Bool) (g : G) : ¬Combines (.inr p) (.inl g) := id

theorem combines_comm {a b : G ⊕ X × Bool} : Combines a b ↔ Combines b a := by
  rcases a with _ | ⟨y, e⟩ <;> rcases b with _ | ⟨z, f⟩ <;> simp [eq_comm]

theorem Combines.symm {a b : G ⊕ X × Bool} (h : Combines a b) : Combines b a :=
  combines_comm.1 h

/- Combining with a coefficient only depends on the other letter being a coefficient. -/
private theorem combines_inl_iff {g h : G} {c : G ⊕ X × Bool} :
    Combines (.inl g) c ↔ Combines (.inl h) c := by
  cases c <;> simp

private theorem combines_inl_right_iff {g h : G} {c : G ⊕ X × Bool} :
    Combines c (.inl g) ↔ Combines c (.inl h) := by
  cases c <;> simp

variable [One G]

/-- A word in coefficients and variable letters is reduced (as written) when its coefficients are
nontrivial and no two adjacent letters combine: no two coefficients are adjacent and no variable
letter is adjacent to its inverse. -/
def IsReduced (l : List (G ⊕ X × Bool)) : Prop :=
  (∀ g, .inl g ∈ l → g ≠ 1) ∧ l.IsChain fun a b => ¬Combines a b

theorem isReduced_iff {l : List (G ⊕ X × Bool)} :
    IsReduced l ↔ (∀ g, .inl g ∈ l → g ≠ 1) ∧ l.IsChain fun a b => ¬Combines a b := Iff.rfl

@[simp]
theorem isReduced_nil : IsReduced ([] : List (G ⊕ X × Bool)) :=
  ⟨by simp, List.isChain_nil⟩

@[simp]
theorem isReduced_singleton_inl {g : G} : IsReduced ([.inl g] : List (G ⊕ X × Bool)) ↔ g ≠ 1 := by
  simp [IsReduced]

@[simp]
theorem isReduced_singleton_inr (p : X × Bool) : IsReduced ([.inr p] : List (G ⊕ X × Bool)) := by
  simp [IsReduced]

theorem isReduced_cons {a : G ⊕ X × Bool} {l : List (G ⊕ X × Bool)} :
    IsReduced (a :: l) ↔ IsReduced [a] ∧ (∀ b ∈ l.head?, ¬Combines a b) ∧ IsReduced l := by
  simp only [IsReduced, List.mem_cons, List.isChain_cons, List.not_mem_nil, or_false,
    List.isChain_nil, and_true, or_imp, forall_and]
  tauto

@[simp]
theorem isReduced_cons_cons {a b : G ⊕ X × Bool} {l : List (G ⊕ X × Bool)} :
    IsReduced (a :: b :: l) ↔ IsReduced [a] ∧ ¬Combines a b ∧ IsReduced (b :: l) := by
  simp [isReduced_cons (l := b :: l)]

theorem isReduced_append {l₁ l₂ : List (G ⊕ X × Bool)} :
    IsReduced (l₁ ++ l₂) ↔ IsReduced l₁ ∧ IsReduced l₂ ∧
      ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, ¬Combines a b := by
  simp only [IsReduced, List.mem_append, List.isChain_append, or_imp, forall_and]
  tauto

theorem IsReduced.infix {l₁ l₂ : List (G ⊕ X × Bool)} (h : IsReduced l₂) (h' : l₁ <:+: l₂) :
    IsReduced l₁ :=
  ⟨fun g hg => h.1 g (h'.subset hg), h.2.infix h'⟩

/-- A reduced word consisting of a sequence of coefficients between two mutually inverse variable
letters contains a single coefficient. -/
theorem IsReduced.exists_eq_singleton_of_inr_map_inl {z : X} {b : Bool} {L : List G}
    (h : IsReduced (.inr (z, b) :: (L.map Sum.inl ++ [.inr (z, !b)]))) : ∃ c : G, L = [c] := by
  rcases L with _ | ⟨c, _ | ⟨c', L'⟩⟩
  · simp at h
  · exact ⟨c, rfl⟩
  · simp at h

/-- A word in variable letters is reduced exactly when it is a reduced word of the free group
`F(X)`. -/
@[simp]
theorem isReduced_map_inr {L : List (X × Bool)} :
    IsReduced (L.map Sum.inr : List (G ⊕ X × Bool)) ↔ FreeGroup.IsReduced L := by
  simp [IsReduced, FreeGroup.IsReduced, List.isChain_map]

/-- A flatten of nonempty words is reduced if and only if each word is reduced and consecutive
words do not combine across boundaries. -/
theorem isReduced_flatten_iff {L : List (List (G ⊕ X × Bool))} (hne : ∀ l ∈ L, l ≠ []) :
    IsReduced L.flatten ↔ (∀ l ∈ L, IsReduced l) ∧
      L.IsChain fun l₁ l₂ => ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, ¬Combines a b := by
  simp only [isReduced_iff, List.mem_flatten, List.isChain_flatten fun h => hne [] h rfl,
    forall_exists_index, and_imp]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun l hl => ⟨fun g hg => h1 g l hl hg, h2 l hl⟩, h3⟩,
    fun ⟨h, h3⟩ => ⟨fun g l hl hg => (h l hl).1 g hg, fun l hl => (h l hl).2, h3⟩⟩

end Reduced

/-! ### Inverse words -/

section InvRev

/-- The formal inverse of a word in coefficients and variable letters: the inverse letters `g⁻¹`
and `x^{-ε}` in reverse order. On words in variable letters it is `FreeGroup.invRev`
(`invRev_map_inr`). -/
def invRev [Inv G] (l : List (G ⊕ X × Bool)) : List (G ⊕ X × Bool) :=
  (l.map (Sum.map (·⁻¹) fun p => (p.1, !p.2))).reverse

theorem invRev_def [Inv G] (l : List (G ⊕ X × Bool)) :
    invRev l = (l.map (Sum.map (·⁻¹) fun p => (p.1, !p.2))).reverse :=
  (rfl)

@[simp]
theorem invRev_nil [Inv G] : invRev ([] : List (G ⊕ X × Bool)) = [] := (rfl)

@[simp]
theorem invRev_singleton_inl [Inv G] (g : G) :
    invRev ([.inl g] : List (G ⊕ X × Bool)) = [.inl g⁻¹] := (rfl)

@[simp]
theorem invRev_singleton_inr [Inv G] (p : X × Bool) :
    invRev ([.inr p] : List (G ⊕ X × Bool)) = [.inr (p.1, !p.2)] := (rfl)

@[simp]
theorem invRev_append [Inv G] (l₁ l₂ : List (G ⊕ X × Bool)) :
    invRev (l₁ ++ l₂) = invRev l₂ ++ invRev l₁ := by
  simp [invRev]

theorem invRev_cons [Inv G] (a : G ⊕ X × Bool) (l : List (G ⊕ X × Bool)) :
    invRev (a :: l) = invRev l ++ invRev [a] := by
  rw [← List.singleton_append, invRev_append]

@[simp]
theorem length_invRev [Inv G] (l : List (G ⊕ X × Bool)) : (invRev l).length = l.length := by
  simp [invRev]

@[simp]
theorem invRev_eq_nil_iff [Inv G] {l : List (G ⊕ X × Bool)} : invRev l = [] ↔ l = [] := by
  simp [invRev]

@[simp]
theorem invRev_invRev [InvolutiveInv G] (l : List (G ⊕ X × Bool)) : invRev (invRev l) = l := by
  simp only [invRev, List.map_reverse, List.reverse_reverse, List.map_map]
  exact List.map_id'' (fun a => by rcases a with _ | _ <;> simp) l

theorem invRev_injective [InvolutiveInv G] :
    Function.Injective (invRev : List (G ⊕ X × Bool) → List (G ⊕ X × Bool)) :=
  Function.LeftInverse.injective invRev_invRev

@[simp]
theorem invRev_inj [InvolutiveInv G] {l₁ l₂ : List (G ⊕ X × Bool)} :
    invRev l₁ = invRev l₂ ↔ l₁ = l₂ :=
  invRev_injective.eq_iff

@[simp]
theorem invRev_map_inr [Inv G] (L : List (X × Bool)) :
    invRev (L.map Sum.inr : List (G ⊕ X × Bool)) = (FreeGroup.invRev L).map Sum.inr := by
  simp [invRev, FreeGroup.invRev, Function.comp_def]

@[simp]
theorem getLast?_invRev [Inv G] (l : List (G ⊕ X × Bool)) :
    (invRev l).getLast? = l.head?.map (Sum.map (·⁻¹) fun p => (p.1, !p.2)) := by
  simp [invRev, List.getLast?_reverse]

@[simp]
theorem countVar_invRev [Inv G] (x : X) (l : List (G ⊕ X × Bool)) :
    countVar x (invRev l) = countVar x l := by
  classical
  simp only [countVar_eq_countP, invRev, List.countP_reverse, List.countP_map]
  congr 1 with (_ | _) <;> rfl

/- Inverting two letters does not change whether they combine. -/
private theorem combines_map_inv [Inv G] {a b : G ⊕ X × Bool} :
    Combines (Sum.map (·⁻¹) (fun p => (p.1, !p.2)) a) (Sum.map (·⁻¹) (fun p => (p.1, !p.2)) b) ↔
      Combines a b := by
  rcases a with _ | ⟨y, e⟩ <;> rcases b with _ | ⟨z, f⟩ <;> simp

@[simp]
theorem isReduced_invRev [DivisionMonoid G] {l : List (G ⊕ X × Bool)} :
    IsReduced (invRev l) ↔ IsReduced l := by
  rw [isReduced_iff, isReduced_iff, invRev, List.isChain_reverse, List.isChain_map]
  refine and_congr ?_ ⟨fun h => h.imp fun a b h' hab => h' (combines_map_inv.2 hab.symm),
    fun h => h.imp fun a b h' hab => h' (combines_map_inv.1 hab).symm⟩
  simp [Sum.exists]

@[simp]
theorem prod_map_letter_invRev [Group G] (l : List (G ⊕ X × Bool)) :
    ((invRev l).map letter).prod = ((l.map letter).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [invRev_cons, List.map_append, List.prod_append, ih]
    rcases a with g | ⟨y, _ | _⟩ <;> simp

end InvRev

/-! ### The normal form theorem -/

section NormalForm

variable [Group G]

open Classical in
/-- The reduced word of `a * w` from the reduced word of `w`, for a letter `a`. -/
private noncomputable def letterMul : G ⊕ X × Bool → List (G ⊕ X × Bool) → List (G ⊕ X × Bool)
  | .inl g, [] => if g = 1 then [] else [.inl g]
  | .inl g, .inl h :: l => if g * h = 1 then l else .inl (g * h) :: l
  | .inl g, .inr q :: l => if g = 1 then .inr q :: l else .inl g :: .inr q :: l
  | .inr p, [] => [.inr p]
  | .inr p, .inl h :: l => .inr p :: .inl h :: l
  | .inr p, .inr q :: l => if p.1 = q.1 ∧ p.2 ≠ q.2 then l else .inr p :: .inr q :: l

private theorem isReduced_letterMul {l : List (G ⊕ X × Bool)} (hl : IsReduced l)
    (a : G ⊕ X × Bool) : IsReduced (letterMul a l) := by
  rcases a with g | p <;> rcases l with _ | ⟨h | q, l⟩ <;> simp only [letterMul]
  · split_ifs with hg <;> simp [hg]
  · rw [isReduced_cons] at hl
    split_ifs with hgh
    · exact hl.2.2
    · exact isReduced_cons.2 ⟨by simpa using hgh,
        fun c hc => combines_inl_iff.not.2 (hl.2.1 c hc), hl.2.2⟩
  · split_ifs with hg
    · exact hl
    · exact isReduced_cons_cons.2 ⟨by simpa using hg, by simp, hl⟩
  · simp
  · exact isReduced_cons_cons.2 ⟨by simp, by simp, hl⟩
  · split_ifs with hpq
    · exact (isReduced_cons.1 hl).2.2
    · exact isReduced_cons_cons.2 ⟨by simp, by simpa using hpq, hl⟩

private theorem letterMul_inl_mul {l : List (G ⊕ X × Bool)} (hl : IsReduced l) (g h : G) :
    letterMul (.inl g) (letterMul (.inl h) l) = letterMul (.inl (g * h)) l := by
  rcases l with _ | ⟨k | q, _ | ⟨k' | q', l⟩⟩
  · simp only [letterMul]; split_ifs <;> simp_all
  -- a leading coefficient `k` absorbs `h`; the letter after it is not a coefficient
  all_goals first
    | simp at hl; done
    | simp only [letterMul]; split_ifs <;> simp_all [mul_assoc]

private theorem letterMul_inl_one {l : List (G ⊕ X × Bool)} (hl : IsReduced l) :
    letterMul (.inl 1) l = l := by
  rcases l with _ | ⟨k | q, l⟩
  · simp [letterMul]
  · have hk : k ≠ 1 := by simpa using (isReduced_cons.1 hl).1
    simp [letterMul, hk]
  · simp [letterMul]

private theorem letterMul_inr_letterMul_inr {l : List (G ⊕ X × Bool)} (hl : IsReduced l)
    (p : X × Bool) : letterMul (.inr (p.1, !p.2)) (letterMul (.inr p) l) = l := by
  rcases p with ⟨y, b⟩
  rcases l with _ | ⟨k | ⟨z, c⟩, l⟩
  · simp [letterMul]
  · simp [letterMul]
  · by_cases hz : y = z ∧ b ≠ c
    · obtain ⟨rfl, hbc⟩ := hz
      obtain rfl : c = !b := by cases b <;> cases c <;> simp_all
      rcases l with _ | ⟨k | ⟨z', c'⟩, l⟩
      · simp [letterMul]
      · simp [letterMul]
      · have := (isReduced_cons_cons.1 hl).2.1
        simp only [combines_inr_inr, not_and] at this
        simp only [letterMul]
        split_ifs <;> simp_all
    · simp [letterMul, hz]

/-- The action of a coefficient on reduced words. -/
private noncomputable def coeffPerm : G →* Equiv.Perm {l : List (G ⊕ X × Bool) // IsReduced l} where
  toFun g :=
    { toFun l := ⟨letterMul (.inl g) l, isReduced_letterMul l.property _⟩
      invFun l := ⟨letterMul (.inl g⁻¹) l, isReduced_letterMul l.property _⟩
      left_inv l := Subtype.ext <| by
        dsimp only
        rw [letterMul_inl_mul l.property, inv_mul_cancel, letterMul_inl_one l.property]
      right_inv l := Subtype.ext <| by
        dsimp only
        rw [letterMul_inl_mul l.property, mul_inv_cancel, letterMul_inl_one l.property] }
  map_one' := Equiv.ext fun l => Subtype.ext (letterMul_inl_one l.property)
  map_mul' g h := Equiv.ext fun l => Subtype.ext (letterMul_inl_mul l.property g h).symm

/-- The action of a variable on reduced words. -/
private noncomputable def varPerm (x : X) :
    Equiv.Perm {l : List (G ⊕ X × Bool) // IsReduced l} where
  toFun l := ⟨letterMul (.inr (x, true)) l, isReduced_letterMul l.property _⟩
  invFun l := ⟨letterMul (.inr (x, false)) l, isReduced_letterMul l.property _⟩
  left_inv l := Subtype.ext (letterMul_inr_letterMul_inr l.property (x, true))
  right_inv l := Subtype.ext (letterMul_inr_letterMul_inr l.property (x, false))

/-- The action of `G[X]` on reduced words, by left multiplication followed by reduction. -/
private noncomputable def act : GX G X →* Equiv.Perm {l : List (G ⊕ X × Bool) // IsReduced l} :=
  Monoid.Coprod.lift coeffPerm (FreeGroup.lift varPerm)

/-- The reduced word of an element `w` of `G[X]`: the unique reduced word in coefficients and
variable letters whose product is `w` (`reducedWord_eq_iff`). -/
noncomputable def reducedWord (w : GX G X) : List (G ⊕ X × Bool) :=
  (act w ⟨[], by simp⟩).val

private theorem act_letter (a : G ⊕ X × Bool) (l : {l : List (G ⊕ X × Bool) // IsReduced l}) :
    (act (letter a) l).val = letterMul a l.val := by
  rcases a with g | ⟨y, _ | _⟩ <;> simp [act, coeffPerm, varPerm, Equiv.Perm.inv_def]

private theorem act_prod (l : List (G ⊕ X × Bool)) (m : {l : List (G ⊕ X × Bool) // IsReduced l}) :
    (act (l.map letter).prod m).val = l.foldr letterMul m.val := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Equiv.Perm.mul_apply, act_letter, ih]

private theorem prod_letterMul (a : G ⊕ X × Bool) (l : List (G ⊕ X × Bool)) :
    ((letterMul a l).map letter).prod = letter a * (l.map letter).prod := by
  rcases a with g | ⟨y, b⟩ <;> rcases l with _ | ⟨h | ⟨z, c⟩, l⟩ <;> simp only [letterMul]
  · split_ifs with hg <;> simp [hg]
  · split_ifs with hgh
    · rw [List.map_cons, List.prod_cons, letter_inl, letter_inl, ← mul_assoc, ← map_mul, hgh,
        map_one, one_mul]
    · simp [mul_assoc]
  · split_ifs with hg <;> simp [hg]
  · simp
  · simp
  · split_ifs with H
    · obtain ⟨rfl, H⟩ := H
      cases b <;> cases c <;> simp_all
    · simp

/- Multiplying by a letter removes no letter `x^{±1}` or cancels a pair `x^{±1}`, `x^{∓1}`. -/
private theorem countVar_letterMul (x : X) (a : G ⊕ X × Bool) (l : List (G ⊕ X × Bool)) :
    countVar x [a] + countVar x l = countVar x (letterMul a l) ∨
      countVar x [a] + countVar x l = countVar x (letterMul a l) + 2 := by
  rcases a with g | ⟨y, b⟩ <;> rcases l with _ | ⟨h | ⟨z, c⟩, l⟩ <;> simp only [letterMul] <;>
    (try split_ifs) <;> (try by_cases hz : z = x) <;> (try by_cases hy : y = x) <;> simp_all <;>
    omega

private theorem reducedWord_prod_eq_foldr (l : List (G ⊕ X × Bool)) :
    reducedWord (l.map letter).prod = l.foldr letterMul [] :=
  act_prod l _

private theorem prod_foldr_letterMul (l m : List (G ⊕ X × Bool)) :
    ((l.foldr letterMul m).map letter).prod = (l.map letter).prod * (m.map letter).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [prod_letterMul, ih, mul_assoc]

private theorem letterMul_of_isReduced_cons {a : G ⊕ X × Bool} {l : List (G ⊕ X × Bool)}
    (h : IsReduced (a :: l)) : letterMul a l = a :: l := by
  rcases a with g | p <;> rcases l with _ | ⟨h' | q, l⟩ <;> simp only [letterMul]
  · simp_all
  · simp at h
  · simp_all
  · have := (isReduced_cons_cons.1 h).2.1
    simp only [combines_inr_inr] at this
    simp [this]

/-- The reduced word of `w` is reduced. -/
@[simp]
theorem isReduced_reducedWord (w : GX G X) : IsReduced (reducedWord w) :=
  (act w _).property

/-- The product of the letters of the reduced word of `w` is `w`. -/
@[simp]
theorem prod_reducedWord (w : GX G X) : ((reducedWord w).map letter).prod = w := by
  obtain ⟨l, rfl⟩ := exists_map_letter_prod_eq w
  rw [reducedWord_prod_eq_foldr, prod_foldr_letterMul]
  simp

/-- A reduced word is the reduced word of its product. -/
theorem IsReduced.reducedWord_prod {l : List (G ⊕ X × Bool)} (hl : IsReduced l) :
    reducedWord (l.map letter).prod = l := by
  rw [reducedWord_prod_eq_foldr]
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih (isReduced_cons.1 hl).2.2, letterMul_of_isReduced_cons hl]

/-- The normal form theorem: the reduced word of `w` is the only reduced word with product `w`. -/
theorem reducedWord_eq_iff {w : GX G X} {l : List (G ⊕ X × Bool)} (hl : IsReduced l) :
    reducedWord w = l ↔ (l.map letter).prod = w :=
  ⟨fun h => h ▸ prod_reducedWord w, fun h => h ▸ hl.reducedWord_prod⟩

theorem reducedWord_injective : Function.Injective (reducedWord : GX G X → _) :=
  fun u v h => by simpa using congrArg (fun l => (l.map letter).prod) h

@[simp]
theorem reducedWord_inj {u v : GX G X} : reducedWord u = reducedWord v ↔ u = v :=
  reducedWord_injective.eq_iff

@[simp]
theorem reducedWord_eq_nil_iff {w : GX G X} : reducedWord w = [] ↔ w = 1 := by
  simp [reducedWord_eq_iff isReduced_nil, eq_comm]

@[simp]
theorem reducedWord_one : reducedWord (1 : GX G X) = [] :=
  reducedWord_eq_nil_iff.2 rfl

@[simp]
theorem reducedWord_inl_of_ne_one {g : G} (hg : g ≠ 1) : reducedWord (inl g : GX G X) = [.inl g] :=
  (reducedWord_eq_iff (by simpa using hg)).2 (by simp)

/-- The reduced word of a variable word `inr f` consists of the letters of the reduced word of `f`
in the free group `F(X)`. -/
theorem reducedWord_inr [DecidableEq X] (f : FreeGroup X) :
    reducedWord (inr f : GX G X) = f.toWord.map Sum.inr :=
  (reducedWord_eq_iff (isReduced_map_inr.2 FreeGroup.isReduced_toWord)).2 <| by
    rw [prod_map_letter_map_inr, FreeGroup.mk_toWord]

@[simp]
theorem reducedWord_inr_of (y : X) :
    reducedWord (inr (FreeGroup.of y) : GX G X) = [.inr (y, true)] :=
  (reducedWord_eq_iff (isReduced_singleton_inr _)).2 (by simp)

/-- The coefficients are the elements of `G[X]` whose reduced word has no variable letter. -/
theorem mem_range_inl_iff {w : GX G X} :
    w ∈ Set.range (inl : G →* GX G X) ↔ ∀ x, countVar x (reducedWord w) = 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨g, rfl⟩ x
    by_cases hg : g = 1 <;> simp [hg]
  · have hr := isReduced_reducedWord w
    rw [← prod_reducedWord w]
    generalize reducedWord w = l at h hr
    -- a reduced word without variable letters has at most one letter
    rcases l with _ | ⟨g | ⟨y, b⟩, _ | ⟨_ | ⟨z, c⟩, l⟩⟩
    · exact ⟨1, by simp⟩
    · exact ⟨g, by simp⟩
    · simp at hr
    · simpa using h z
    all_goals simpa using h y

/-- The elements of `F(X)` are the elements of `G[X]` whose reduced word has no coefficient. -/
theorem mem_range_inr_iff {w : GX G X} :
    w ∈ Set.range (inr : FreeGroup X →* GX G X) ↔ ∀ g, .inl g ∉ reducedWord w := by
  classical
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, rfl⟩ g
    simp [reducedWord_inr]
  · rw [← prod_reducedWord w]
    generalize reducedWord w = l at h
    induction l with
    | nil => exact ⟨1, by simp⟩
    | cons a l ih =>
      obtain ⟨f, hf⟩ := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
      rcases a with g | p
      · exact absurd List.mem_cons_self (h g)
      · exact ⟨FreeGroup.mk [p] * f, by simp [hf, letter_inr]⟩

/-- The reduced word of `w⁻¹` is the formal inverse of the reduced word of `w`. -/
@[simp]
theorem reducedWord_inv (w : GX G X) : reducedWord w⁻¹ = invRev (reducedWord w) :=
  (reducedWord_eq_iff (isReduced_invRev.2 (isReduced_reducedWord w))).2 <| by
    rw [prod_map_letter_invRev, prod_reducedWord]

/-- Reduction removes letters `x^{±1}` in pairs: a word `l` has as many letters `x^{±1}` as the
reduced word of its product plus an even number. -/
theorem exists_countVar_eq_add_two_mul (x : X) (l : List (G ⊕ X × Bool)) :
    ∃ k, countVar x l = countVar x (reducedWord (l.map letter).prod) + 2 * k := by
  rw [reducedWord_prod_eq_foldr]
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨k, hk⟩ := ih
    rw [List.foldr_cons, ← List.singleton_append, countVar_append]
    rcases countVar_letterMul x a (l.foldr letterMul []) with h | h
    exacts [⟨k, by omega⟩, ⟨k + 1, by omega⟩]

/-- Reduction does not increase the number of letters `x^{±1}`: the reduced word of the product of
a word `l` has at most as many letters `x^{±1}` as `l`. -/
theorem countVar_reducedWord_le (x : X) (l : List (G ⊕ X × Bool)) :
    countVar x (reducedWord (l.map letter).prod) ≤ countVar x l := by
  obtain ⟨k, hk⟩ := exists_countVar_eq_add_two_mul x l
  omega

end NormalForm

/-! ### Cyclically reduced words -/

section Cyclic

variable [One G]

/-- A word is cyclically reduced when it is reduced and, if it has at least two letters, its last
and first letters do not combine: no letter of the cyclic word it spells combines with the next
one. This condition is on letters: on words without coefficients it is
`FreeGroup.IsCyclicallyReduced` (`isCyclicallyReduced_map_inr`). It differs from the condition of
[IFT, §2.2] on syllables, that the first and last syllables lie in different factors of
`G ∗ F(X)`: `x g y` is cyclically reduced here but not there, and `z⁻¹ y z` (one syllable of
`F(X)`) is not cyclically reduced here. -/
def IsCyclicallyReduced (l : List (G ⊕ X × Bool)) : Prop :=
  IsReduced l ∧ ∀ a b m, l = a :: (m ++ [b]) → ¬Combines b a

theorem isCyclicallyReduced_iff {l : List (G ⊕ X × Bool)} :
    IsCyclicallyReduced l ↔ IsReduced l ∧ ∀ a b m, l = a :: (m ++ [b]) → ¬Combines b a :=
  Iff.rfl

theorem IsCyclicallyReduced.isReduced {l : List (G ⊕ X × Bool)} (h : IsCyclicallyReduced l) :
    IsReduced l :=
  h.1

@[simp]
theorem isCyclicallyReduced_nil : IsCyclicallyReduced ([] : List (G ⊕ X × Bool)) :=
  ⟨isReduced_nil, by simp⟩

@[simp]
theorem isCyclicallyReduced_singleton {a : G ⊕ X × Bool} :
    IsCyclicallyReduced [a] ↔ IsReduced [a] :=
  ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩

theorem isCyclicallyReduced_cons_append {a b : G ⊕ X × Bool} {m : List (G ⊕ X × Bool)} :
    IsCyclicallyReduced (a :: (m ++ [b])) ↔ IsReduced (a :: (m ++ [b])) ∧ ¬Combines b a := by
  refine ⟨fun h => ⟨h.1, h.2 a b m rfl⟩, fun h => ⟨h.1, fun a' b' m' he => ?_⟩⟩
  simp only [List.cons.injEq, List.append_singleton_inj] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact h.2

@[simp]
theorem isCyclicallyReduced_cons_cons {a b : G ⊕ X × Bool} {l : List (G ⊕ X × Bool)} :
    IsCyclicallyReduced (a :: b :: l) ↔
      IsReduced (a :: b :: l) ∧ ¬Combines ((b :: l).getLast (List.cons_ne_nil b l)) a := by
  conv_lhs => rw [← List.dropLast_append_getLast (List.cons_ne_nil b l)]
  rw [isCyclicallyReduced_cons_append, List.dropLast_append_getLast]

/-- A word in variable letters is cyclically reduced exactly when it is a cyclically reduced word of
the free group `F(X)`. -/
@[simp]
theorem isCyclicallyReduced_map_inr {L : List (X × Bool)} :
    IsCyclicallyReduced (L.map Sum.inr : List (G ⊕ X × Bool)) ↔
      FreeGroup.IsCyclicallyReduced L := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton a => simp
  | cons_append a m b =>
    rw [← List.cons_append, FreeGroup.isCyclicallyReduced_cons_append_iff,
      ← isReduced_map_inr (G := G)]
    simp [isCyclicallyReduced_cons_append]

/-- The word `z⁻¹ a z` is not cyclically reduced: its last letter `z` cancels against its first
letter `z⁻¹`. -/
theorem not_isCyclicallyReduced_inv_inl_self {a : G} {z : X} :
    ¬IsCyclicallyReduced ([.inr (z, false), .inl a, .inr (z, true)] : List (G ⊕ X × Bool)) := by
  simp

/- Moving the first letter of a cyclically reduced word to its end keeps it cyclically reduced. -/
private theorem IsCyclicallyReduced.append_singleton {a : G ⊕ X × Bool}
    {l : List (G ⊕ X × Bool)} (h : IsCyclicallyReduced (a :: l)) :
    IsCyclicallyReduced (l ++ [a]) := by
  rcases l with _ | ⟨b, l⟩
  · simpa using h
  obtain ⟨hr, hba⟩ := isCyclicallyReduced_cons_cons.1 h
  obtain ⟨ha, hab, hl⟩ := isReduced_cons_cons.1 hr
  rw [List.cons_append, isCyclicallyReduced_cons_append, ← List.cons_append, isReduced_append]
  exact ⟨⟨hl, ha, by simpa [List.getLast?_eq_some_getLast (List.cons_ne_nil b l)] using hba⟩, hab⟩

/-- Being cyclically reduced is invariant under cyclic permutations. -/
theorem isCyclicallyReduced_append_comm {l₁ l₂ : List (G ⊕ X × Bool)} :
    IsCyclicallyReduced (l₁ ++ l₂) ↔ IsCyclicallyReduced (l₂ ++ l₁) := by
  suffices ∀ l₁ l₂ : List (G ⊕ X × Bool), IsCyclicallyReduced (l₁ ++ l₂) →
      IsCyclicallyReduced (l₂ ++ l₁) from ⟨this _ _, this _ _⟩
  intro l₁
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    intro l₂ h
    simpa using ih (l₂ ++ [a]) (by simpa using h.append_singleton)

/-- A word is cyclically reduced if and only if it is reduced and, whenever it has at least two
letters, its last and first letters do not combine. -/
theorem isCyclicallyReduced_iff_head?_getLast? {l : List (G ⊕ X × Bool)} :
    IsCyclicallyReduced l ↔
      IsReduced l ∧ (2 ≤ l.length → ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, ¬Combines a b) := by
  induction l using List.bidirectionalRec with
  | nil => simp
  | singleton a => simp
  | cons_append b m a =>
    rw [isCyclicallyReduced_cons_append, List.getLast?_cons, List.getLast?_concat, List.head?_cons]
    simp

/-- A flatten of nonempty words is cyclically reduced if and only if each word is reduced,
consecutive words do not combine across boundaries, and when the flattened word has at least two
letters, the last letter of the last word and the first letter of the first word do not combine. -/
theorem isCyclicallyReduced_flatten_iff {blocks : List (List (G ⊕ X × Bool))}
    (hne : ∀ l ∈ blocks, l ≠ []) :
    IsCyclicallyReduced blocks.flatten ↔
      (∀ l ∈ blocks, IsReduced l) ∧
      (blocks.IsChain fun l₁ l₂ => ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, ¬Combines a b) ∧
      (2 ≤ blocks.flatten.length →
        ∀ l₁ ∈ blocks.getLast?, ∀ l₂ ∈ blocks.head?,
          ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, ¬Combines a b) := by
  rw [isCyclicallyReduced_iff_head?_getLast?, isReduced_flatten_iff hne,
    List.head?_flatten_of_ne_nil hne, List.getLast?_flatten_of_ne_nil hne, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [Option.mem_bind_iff]
  exact ⟨fun h hlen l₁ hl₁ l₂ hl₂ a ha b hb => h hlen a ⟨l₁, hl₁, ha⟩ b ⟨l₂, hl₂, hb⟩,
    fun h hlen a ⟨l₁, hl₁, ha⟩ b ⟨l₂, hl₂, hb⟩ => h hlen l₁ hl₁ l₂ hl₂ a ha b hb⟩

/-- Appending a reduced letter `a` to a flatten of nonempty reduced words whose boundaries do not
combine, and such that `a` combines with neither the last letter of the last block nor the first
letter of the first block, yields a cyclically reduced word. -/
theorem isCyclicallyReduced_flatten_append_singleton {blocks : List (List (G ⊕ X × Bool))}
    {a : G ⊕ X × Bool} (hne : ∀ l ∈ blocks, l ≠ []) (hred : ∀ l ∈ blocks, IsReduced l)
    (hchain : blocks.IsChain fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, ¬Combines x y)
    (hhead : ∀ l ∈ blocks.head?, ∀ b ∈ l.head?, ¬Combines a b)
    (hlast : ∀ l ∈ blocks.getLast?, ∀ c ∈ l.getLast?, ¬Combines c a) (ha : IsReduced [a]) :
    IsCyclicallyReduced (blocks.flatten ++ [a]) := by
  have hfl : blocks.flatten ++ [a] = (blocks ++ [[a]]).flatten := by simp
  rw [hfl]
  refine (isCyclicallyReduced_flatten_iff ?_).2 ⟨?_, ?_, ?_⟩
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hne l hl
    · obtain rfl : l = [a] := by simpa using hl
      simp
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hred l hl
    · obtain rfl : l = [a] := by simpa using hl
      exact ha
  · rw [List.isChain_append]
    refine ⟨hchain, List.isChain_singleton _, fun l₁ hl₁ l₂ hl₂ c hc b hb => ?_⟩
    obtain rfl : [a] = l₂ := by simpa using hl₂
    obtain rfl : a = b := by simpa using hb
    exact hlast l₁ hl₁ c hc
  · intro hlen l₁ hl₁ l₂ hl₂ c hc b hb
    rcases blocks with _ | ⟨l₀, rest⟩
    · simp at hlen
    obtain rfl : [a] = l₁ := by
      rw [List.getLast?_append_of_ne_nil _ (by simp)] at hl₁
      simpa using hl₁
    obtain rfl : l₀ = l₂ := by simpa using hl₂
    obtain rfl : a = c := by simpa using hc
    exact hhead l₀ rfl b hb

end Cyclic

@[simp]
theorem isCyclicallyReduced_invRev [DivisionMonoid G] {l : List (G ⊕ X × Bool)} :
    IsCyclicallyReduced (invRev l) ↔ IsCyclicallyReduced l := by
  induction l using List.bidirectionalRec with
  | nil => simp
  | singleton a => rcases a with _ | _ <;> simp
  | cons_append a m b =>
    have he : invRev (a :: (m ++ [b])) = Sum.map (·⁻¹) (fun p => (p.1, !p.2)) b ::
        (invRev m ++ [Sum.map (·⁻¹) (fun p => (p.1, !p.2)) a]) := by
      simp [invRev_def]
    rw [he, isCyclicallyReduced_cons_append, ← he, isReduced_invRev,
      isCyclicallyReduced_cons_append, combines_map_inv, combines_comm]

/-! ### Cyclic reduction -/

section CyclicReduction

variable [Group G]

/-- The product of `l` is the conjugate of the product of a cyclically reduced word `m` by the
product of an initial segment `u` of `l`, and each variable has as many letters in `l` as in `m`
plus twice as many as in `u`. -/
private def HasCyclicReduction (l : List (G ⊕ X × Bool)) : Prop :=
  ∃ u m : List (G ⊕ X × Bool), u <+: l ∧ IsCyclicallyReduced m ∧
    (u.map letter).prod * (m.map letter).prod * ((u.map letter).prod)⁻¹ = (l.map letter).prod ∧
    ∀ x, countVar x l = countVar x m + 2 * countVar x u

/- Cancelling a letter at the start against its inverse at the end moves it into the
conjugator. -/
private theorem hasCyclicReduction_cons_append {a b : G ⊕ X × Bool} {m : List (G ⊕ X × Bool)}
    (hab : letter b = (letter a)⁻¹) (hcount : ∀ x, countVar x [b] = countVar x [a])
    (h : HasCyclicReduction m) : HasCyclicReduction (a :: (m ++ [b])) := by
  obtain ⟨u, m', hu, hm', hprod, hc⟩ := h
  refine ⟨a :: u, m', (List.prefix_cons_inj _).2 (hu.trans (List.prefix_append _ _)), hm', ?_,
    fun x => ?_⟩
  · simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, hab, ← hprod,
      List.map_nil, List.prod_nil]
    group
  · have := hcount x
    simp only [← List.singleton_append (l := u), ← List.singleton_append (l := m ++ [b]),
      countVar_append, hc] at this ⊢
    omega

/- Two coefficients at the ends whose product is not `1` merge into one coefficient at the end. -/
private theorem hasCyclicReduction_inl_inl {g h : G} {m : List (G ⊕ X × Bool)}
    (hl : IsReduced (.inl g :: (m ++ [.inl h]))) (hhg : h * g ≠ 1) :
    HasCyclicReduction (.inl g :: (m ++ [.inl h])) := by
  have hl' := isReduced_cons.1 hl
  have hl'' := isReduced_append.1 hl'.2.2
  rcases m with _ | ⟨c, m⟩
  · simp at hl'
  refine ⟨[.inl g], c :: m ++ [.inl (h * g)], by simp, ?_, by simp [mul_assoc],
    fun x => by simp only [← List.cons_append, countVar_append]; simp⟩
  rw [List.cons_append, isCyclicallyReduced_cons_append, ← List.cons_append, isReduced_append]
  refine ⟨⟨hl''.1, by simpa using hhg, fun a ha b hb => ?_⟩,
    combines_inl_iff.not.2 (hl'.2.1 c (by simp))⟩
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
  subst hb
  exact (combines_inl_right_iff (h := h)).not.2 (hl''.2.2 a ha (.inl h) rfl)

/-- Cyclic reduction relative to `G`: the product of a reduced word `l` is the conjugate of the
product of a cyclically reduced word `m` by the product of an initial segment `u` of `l`, and
`countVar x l = countVar x m + 2 * countVar x u` for every variable `x`. -/
theorem IsReduced.exists_isCyclicallyReduced {l : List (G ⊕ X × Bool)} (hl : IsReduced l) :
    ∃ u m : List (G ⊕ X × Bool), u <+: l ∧ IsCyclicallyReduced m ∧
      (u.map letter).prod * (m.map letter).prod * ((u.map letter).prod)⁻¹ = (l.map letter).prod ∧
      ∀ x, countVar x l = countVar x m + 2 * countVar x u := by
  induction l using List.bidirectionalRec with
  | nil => exact ⟨[], [], by simp, isCyclicallyReduced_nil, by simp, by simp⟩
  | singleton a => exact ⟨[], [a], by simp, isCyclicallyReduced_singleton.2 hl, by simp, by simp⟩
  | cons_append a m b ih =>
    have ih := ih (hl.infix ⟨[a], [b], by simp⟩)
    by_cases hba : Combines b a
    swap
    · exact ⟨[], _, by simp, isCyclicallyReduced_cons_append.2 ⟨hl, hba⟩, by simp, by simp⟩
    rcases a with g | ⟨y, e⟩ <;> rcases b with h | ⟨z, f⟩
    · by_cases hhg : h * g = 1
      · obtain rfl := eq_inv_of_mul_eq_one_left hhg
        exact hasCyclicReduction_cons_append (by simp) (by simp) ih
      · exact hasCyclicReduction_inl_inl hl hhg
    · simp at hba
    · simp at hba
    · obtain ⟨rfl, hfe⟩ := hba
      refine hasCyclicReduction_cons_append (by cases e <;> cases f <;> simp_all) (fun x => ?_) ih
      by_cases hx : z = x
      · subst hx; simp
      · simp [hx]

/-- A cyclically reduced word whose product in `G[X]` is conjugate to a coefficient has no
variable letters. -/
theorem IsCyclicallyReduced.countVar_eq_zero_of_eq_conj_inl {l : List (G ⊕ X × Bool)}
    (hl : IsCyclicallyReduced l) {v : GX G X} {c : G}
    (hv : (l.map letter).prod = v * inl c * v⁻¹) (x : X) : countVar x l = 0 := by
  suffices ∀ (p : List (G ⊕ X × Bool)) (c : G), IsReduced p →
      (l.map letter).prod = (p.map letter).prod * inl c * ((p.map letter).prod)⁻¹ →
      countVar x l = 0 from
    this (reducedWord v) c (isReduced_reducedWord v) (by simpa using hv)
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro c _ hprod
    have hl' : l = reducedWord (inl c) :=
      ((reducedWord_eq_iff hl.isReduced).2 (by simpa using hprod)).symm
    by_cases hc : c = 1 <;> simp [hl', hc]
  | append_singleton q d ih =>
    intro c hp hprod
    by_cases hc : c = 1
    · have hl' : l = reducedWord 1 :=
        ((reducedWord_eq_iff hl.isReduced).2 (by simpa [hc] using hprod)).symm
      simp [hl']
    rcases d with g | ⟨y, b⟩
    · exact ih (g * c * g⁻¹) (isReduced_append.1 hp).1 (by simpa [mul_assoc] using hprod)
    · -- A nonempty reduced word `p'` ending in a variable letter yields a reduced word
      -- `p' ++ [.inl c] ++ invRev p'`, which must equal `l` by normal form, contradicting
      -- cyclic reducedness of `l` since its first and last letters are formal inverses.
      exfalso
      have hm_red :
          IsReduced ((q ++ [.inr (y, b)]) ++ [.inl c] ++ invRev (q ++ [.inr (y, b)])) := by
        rw [isReduced_append, isReduced_append]
        refine ⟨⟨hp, isReduced_singleton_inl.2 hc, by simp⟩, isReduced_invRev.2 hp, ?_⟩
        simp [invRev_append]
      have hm_eq : l = (q ++ [.inr (y, b)]) ++ [.inl c] ++ invRev (q ++ [.inr (y, b)]) := by
        rw [← hl.isReduced.reducedWord_prod, ← hm_red.reducedWord_prod]
        congr 1
        simpa only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          letter_inl, prod_map_letter_invRev] using hprod
      set p' := q ++ [.inr (y, b)]
      have hp'_ne : p' ≠ [] := by simp [p']
      let a := p'.head hp'_ne
      have ha_head : l.head? = some a := by
        rw [hm_eq, List.append_assoc, List.head?_append_of_ne_nil _ hp'_ne,
          List.head?_eq_some_head hp'_ne]
      have ha_last : l.getLast? = some (Sum.map (·⁻¹) (fun s => (s.1, !s.2)) a) := by
        rw [hm_eq, List.getLast?_append_of_ne_nil _ (by simp [p']), getLast?_invRev,
          List.head?_eq_some_head hp'_ne, Option.map_some]
      have hnc := (isCyclicallyReduced_iff_head?_getLast?.1 hl).2
        (by rw [hm_eq]; simp [p']; omega) _ (Option.mem_def.2 ha_last) _
        (Option.mem_def.2 ha_head)
      rcases a with _ | ⟨_, _⟩ <;> simp at hnc

end CyclicReduction

/-! ### Occurrences of a variable -/

section Occurrences

open scoped commutatorElement

variable [Group G]

/-- The number of occurrences of the variable `x` in `w ∈ G[X]`: the number of letters `x^{±1}` in
the reduced word of `w`. By `GX.countVar_reducedWord_le` it is the least number of letters `x^{±1}`
in an expression of `w` as a product of coefficients and letters `y^{±1}`. -/
noncomputable def occurrences (x : X) (w : GX G X) : ℕ :=
  countVar x (reducedWord w)

theorem occurrences_eq_countVar_reducedWord (x : X) (w : GX G X) :
    occurrences x w = countVar x (reducedWord w) :=
  (rfl)

/-- The number of occurrences of `x` in the product of a reduced word is its number of letters
`x^{±1}`. -/
theorem IsReduced.occurrences_prod {l : List (G ⊕ X × Bool)} (hl : IsReduced l) (x : X) :
    occurrences x (l.map letter).prod = countVar x l := by
  rw [occurrences_eq_countVar_reducedWord, hl.reducedWord_prod]

/-- `occurrences x` is the largest subadditive function on `G[X]` vanishing on coefficients and
on the letters `y^{±1}` with `y ≠ x`, and bounded by `1` on the letters `x^{±1}`. -/
theorem le_occurrences (x : X) (f : GX G X → ℕ) (hmul : ∀ u v, f (u * v) ≤ f u + f v)
    (hcoeff : ∀ g, f (inl g) = 0) (hx : f (inr (FreeGroup.of x)) ≤ 1)
    (hx' : f (inr (FreeGroup.of x))⁻¹ ≤ 1)
    (hy : ∀ y, y ≠ x → f (inr (FreeGroup.of y)) = 0 ∧ f (inr (FreeGroup.of y))⁻¹ = 0)
    (w : GX G X) :
    f w ≤ occurrences x w := by
  rw [occurrences_eq_countVar_reducedWord]
  nth_rw 1 [← prod_reducedWord w]
  generalize reducedWord w = l
  induction l with
  | nil => simpa using (hcoeff 1).le
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (hmul _ _).trans ?_
    rcases a with g | ⟨y, b⟩
    · simpa [hcoeff] using ih
    · by_cases h : y = x
      · subst h
        rw [countVar_cons_inr_self, add_comm (countVar y l)]
        refine add_le_add ?_ ih
        cases b <;> simpa
      · rw [countVar_cons_inr_of_ne h]
        cases b <;> simpa [hy y h] using ih

/-- Variables cancel in pairs: `x` occurs in `u` and `v` together as often as in `u * v` plus an
even number. -/
theorem exists_occurrences_add_occurrences_eq_add_two_mul (x : X) (u v : GX G X) :
    ∃ k, occurrences x u + occurrences x v = occurrences x (u * v) + 2 * k := by
  simpa [occurrences_eq_countVar_reducedWord] using
    exists_countVar_eq_add_two_mul x (reducedWord u ++ reducedWord v)

theorem occurrences_mul_le (x : X) (u v : GX G X) :
    occurrences x (u * v) ≤ occurrences x u + occurrences x v := by
  obtain ⟨k, hk⟩ := exists_occurrences_add_occurrences_eq_add_two_mul x u v
  omega

@[simp]
theorem occurrences_inl (x : X) (g : G) : occurrences x (inl g : GX G X) = 0 := by
  by_cases hg : g = 1 <;> simp [occurrences_eq_countVar_reducedWord, hg]

@[simp]
theorem occurrences_one (x : X) : occurrences x (1 : GX G X) = 0 := by
  simpa using occurrences_inl (G := G) x 1

@[simp]
theorem occurrences_inv (x : X) (w : GX G X) : occurrences x w⁻¹ = occurrences x w := by
  simp [occurrences_eq_countVar_reducedWord]

theorem occurrences_pow_le (x : X) (w : GX G X) (n : ℕ) :
    occurrences x (w ^ n) ≤ n * occurrences x w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, add_one_mul]
    exact (occurrences_mul_le x _ _).trans (by omega)

theorem occurrences_list_prod_le (x : X) (l : List (GX G X)) :
    occurrences x l.prod ≤ (l.map (occurrences x)).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (occurrences_mul_le x _ _).trans (by omega)

theorem occurrences_commutatorElement_le (x : X) (u v : GX G X) :
    occurrences x ⁅u, v⁆ ≤ 2 * (occurrences x u + occurrences x v) := by
  rw [commutatorElement_def]
  have h₁ := occurrences_mul_le x (u * v * u⁻¹) v⁻¹
  have h₂ := occurrences_mul_le x (u * v) u⁻¹
  have h₃ := occurrences_mul_le x u v
  simp only [occurrences_inv] at h₁ h₂
  omega

theorem occurrences_conj_le (x : X) (u w : GX G X) :
    occurrences x (u⁻¹ * w * u) ≤ 2 * occurrences x u + occurrences x w := by
  have h₁ := occurrences_mul_le x (u⁻¹ * w) u
  have h₂ := occurrences_mul_le x u⁻¹ w
  simp only [occurrences_inv] at h₂
  omega

/-- The number of letters `x^{±1}` in the reduced word of the image of `w` in `F(X)`, where the
coefficients are deleted, is a lower bound for the number of occurrences of `x` in `w`. -/
theorem countP_toWord_snd_le_occurrences [DecidableEq X] (x : X) (w : GX G X) :
    ((snd w).toWord.countP fun p => p.1 = x) ≤ occurrences x w := by
  refine le_occurrences x (fun u => (snd u).toWord.countP fun p => p.1 = x) (fun u v => ?_)
    (fun _ => by simp) (by simp [FreeGroup.toWord_of]) ?_ (fun y hy => ⟨?_, ?_⟩) w
  · rw [map_mul, ← List.countP_append]
    exact (FreeGroup.toWord_mul_sublist _ _).countP_le
  · simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev]
  · simp [FreeGroup.toWord_of, hy]
  · simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev, hy]

@[simp]
theorem occurrences_inr_of_self (x : X) : occurrences x (inr (FreeGroup.of x) : GX G X) = 1 := by
  simp [occurrences_eq_countVar_reducedWord]

@[simp]
theorem occurrences_inr_of_of_ne {x y : X} (h : y ≠ x) :
    occurrences x (inr (FreeGroup.of y) : GX G X) = 0 := by
  simp [occurrences_eq_countVar_reducedWord, h]

theorem occurrences_inr_of [DecidableEq X] (x y : X) :
    occurrences x (inr (FreeGroup.of y) : GX G X) = if y = x then 1 else 0 := by
  split_ifs with h
  · subst h; exact occurrences_inr_of_self y
  · exact occurrences_inr_of_of_ne h

/-- The number of occurrences of `x` in an element `f` of `F(X)` is the number of letters `x^{±1}`
in the reduced word of `f`. -/
theorem occurrences_inr [DecidableEq X] (x : X) (f : FreeGroup X) :
    occurrences x (inr f : GX G X) = f.toWord.countP fun p => p.1 = x := by
  rw [occurrences_eq_countVar_reducedWord, reducedWord_inr, countVar_map_inr]

/-- A homomorphism `φ : G[X] → H[Y]` does not increase occurrence counts from `x` to `y` when
`y` does not occur in the images of the coefficients and of the variables other than `x`, and
occurs at most once in the image of `x`. -/
theorem occurrences_map_le {H Y F : Type*} [Group H] [FunLike F (GX G X) (GX H Y)]
    [MonoidHomClass F (GX G X) (GX H Y)] (φ : F) (x : X) (y : Y)
    (hcoeff : ∀ g, occurrences y (φ (inl g)) = 0)
    (hx : occurrences y (φ (inr (FreeGroup.of x))) ≤ 1)
    (hne : ∀ z, z ≠ x → occurrences y (φ (inr (FreeGroup.of z))) = 0) (w : GX G X) :
    occurrences y (φ w) ≤ occurrences x w :=
  le_occurrences x (fun u => occurrences y (φ u))
    (fun u v => by simpa using occurrences_mul_le y (φ u) (φ v)) hcoeff hx (by simpa using hx)
    (fun z hz => ⟨hne z hz, by simpa using hne z hz⟩) w

/-- A variable `y` occurs in no image under a homomorphism `φ : G[X] → H[Y]` when it occurs
neither in the images of the coefficients nor in the images of the variables. -/
theorem occurrences_map_eq_zero {H Y F : Type*} [Group H] [FunLike F (GX G X) (GX H Y)]
    [MonoidHomClass F (GX G X) (GX H Y)] (φ : F) (y : Y)
    (hcoeff : ∀ g, occurrences y (φ (inl g)) = 0)
    (hvar : ∀ x, occurrences y (φ (inr (FreeGroup.of x))) = 0) (w : GX G X) :
    occurrences y (φ w) = 0 := by
  have hmul : ∀ u v, occurrences y (φ u) = 0 → occurrences y (φ v) = 0 →
      occurrences y (φ (u * v)) = 0 := fun u v hu hv =>
    Nat.eq_zero_of_le_zero <| by simpa [hu, hv] using occurrences_mul_le y (φ u) (φ v)
  induction w using Monoid.Coprod.induction_on with
  | inl g => exact hcoeff g
  | inr f =>
    induction f using FreeGroup.induction_on with
    | one => simp
    | of x => exact hvar x
    | inv_of x ih => simpa using ih
    | mul f₁ f₂ h₁ h₂ => simpa using hmul _ _ h₁ h₂
  | mul u v hu hv => exact hmul u v hu hv

open Classical in
/-- The finite set of variables occurring in `w ∈ G[X]`. -/
noncomputable def occVars (w : GX G X) : Finset X :=
  ((reducedWord w).filterMap fun | .inl _ => none | .inr p => some p.1).toFinset

@[simp] theorem mem_occVars_iff {x : X} {w : GX G X} :
    x ∈ occVars w ↔ occurrences x w ≠ 0 := by
  classical
  rw [occVars, List.mem_toFinset, List.mem_filterMap, occurrences_eq_countVar_reducedWord,
    ne_eq, countVar_eq_zero, not_forall]
  refine ⟨?_, fun ⟨b, hb⟩ => ⟨.inr (x, b), not_not.1 hb, rfl⟩⟩
  rintro ⟨_ | ⟨y, b⟩, hm, hy⟩
  · simp at hy
  · exact ⟨b, not_not.2 ((Option.some.inj hy) ▸ hm)⟩

@[simp] theorem coe_occVars (w : GX G X) : (occVars w : Set X) = {x | occurrences x w ≠ 0} :=
  Set.ext fun _ => mem_occVars_iff

@[simp] theorem occVars_inl (g : G) : occVars (inl g : GX G X) = ∅ := by ext; simp
@[simp] theorem occVars_one : occVars (1 : GX G X) = ∅ := by ext; simp
@[simp] theorem occVars_inv (w : GX G X) : occVars w⁻¹ = occVars w := by ext; simp

@[simp] theorem occVars_inr_of (x : X) : occVars (inr (FreeGroup.of x) : GX G X) = {x} := by
  ext y; rcases eq_or_ne x y with rfl | h <;> [simp; simp [h, h.symm]]

/-- Every variable occurring in a product `u * v` occurs in `u` or in `v`. -/
theorem occVars_mul_subset (u v : GX G X) :
    (occVars (u * v) : Set X) ⊆ (occVars u : Set X) ∪ (occVars v : Set X) := fun x hx => by
  have hle := occurrences_mul_le x u v
  simp only [Set.mem_union, Finset.mem_coe, mem_occVars_iff] at hx ⊢
  omega

/-- No variable occurs in `w` if and only if `w` is a coefficient. -/
theorem occVars_eq_empty_iff {w : GX G X} :
    occVars w = ∅ ↔ w ∈ Set.range (inl : G →* GX G X) := by
  rw [mem_range_inl_iff]
  simp [Finset.eq_empty_iff_forall_notMem, occurrences_eq_countVar_reducedWord]

/-- Only finitely many variables occur in any word of `G[X]`. -/
theorem finite_setOf_occurrences_ne_zero (w : GX G X) : {x | occurrences x w ≠ 0}.Finite :=
  coe_occVars w ▸ (occVars w).finite_toSet

/-- The variable `x` does not occur in a word after the substitution `x ↦ 1`. -/
@[simp]
theorem occurrences_eval_update_one [DecidableEq X] (x : X) (w : GX G X) :
    occurrences x (eval inl (Function.update (fun y => inr (FreeGroup.of y)) x 1) w) = 0 := by
  refine occurrences_map_eq_zero _ x (by simp) (fun y => ?_) w
  by_cases h : y = x
  · subst h; simp
  · simp [h]

/-- The words of `GX.avoiding x` are the words in which `x` does not occur. -/
theorem mem_avoiding_iff_occurrences_eq_zero [DecidableEq X] {x : X} {a : GX G X} :
    a ∈ avoiding x ↔ occurrences x a = 0 := by
  classical
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [← mem_avoiding.1 ha, occurrences_eval_update_one]
  · have h := le_occurrences x
      (fun u => if u ∈ avoiding x then 0 else 1)
      (fun u v => by
        by_cases hu : u ∈ avoiding x
        · by_cases hv : v ∈ avoiding x
          · simp [hu, hv, mul_mem hu hv]
          · simp only [hv, ite_false]; split_ifs <;> omega
        · simp only [hu, ite_false]; split_ifs <;> omega)
      (by simp) (by split_ifs <;> simp) (by split_ifs <;> simp)
      (fun y hy => by simp [hy]) a
    by_contra ha'
    simp [ha, ha'] at h

end Occurrences

/-! ### Examples -/

section Examples

variable [Group G] {a : G} {z : X}

/-- For a nontrivial coefficient `a`, the conjugate `z⁻¹ a z` is reduced as written. -/
theorem reducedWord_inv_mul_inl_mul (ha : a ≠ 1) :
    reducedWord ((inr (FreeGroup.of z))⁻¹ * inl a * inr (FreeGroup.of z) : GX G X) =
      [.inr (z, false), .inl a, .inr (z, true)] :=
  (reducedWord_eq_iff (by simp [ha])).2 (by simp [mul_assoc])

end Examples

end TauCeti.GroupAlgGeom.GX
