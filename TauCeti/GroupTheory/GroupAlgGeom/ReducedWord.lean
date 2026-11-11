/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

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
and its inverse. Every reduced word is a conjugate `u l u⁻¹` of a cyclically reduced word `l`, where
`u` is an initial segment of the word; this is cyclic reduction relative to `G`, which cancels a
variable letter at the start against its inverse at the end and merges a coefficient at the end
into the coefficient at the start. Every letter `x^{±1}` of the word is either a letter of `l` or
one of a pair of letters of `u` and `u⁻¹`.

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
* `TauCeti.GroupAlgGeom.GX.reducedWord w`: the reduced word of `w ∈ G[X]`.

## Main results

* `TauCeti.GroupAlgGeom.GX.prod_reducedWord`, `TauCeti.GroupAlgGeom.GX.reducedWord_eq_iff`: the
  normal form theorem: `w` is the product of `reducedWord w`, which is the only reduced word with
  product `w`.
* `TauCeti.GroupAlgGeom.GX.countVar_reducedWord_le`: reduction does not increase the number of
  letters `x^{±1}`.
* `TauCeti.GroupAlgGeom.GX.IsReduced.exists_isCyclicallyReduced`: cyclic reduction of reduced
  words.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.2.
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

theorem letter_inr (p : X × Bool) : letter (.inr p : G ⊕ X × Bool) = inr (FreeGroup.mk [p]) := by
  rcases p with ⟨y, _ | _⟩
  · simp [← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, FreeGroup.of]
  · rfl

/- Every element of `G[X]` is a product of letters. -/
private theorem exists_map_letter_prod_eq (w : GX G X) :
    ∃ l : List (G ⊕ X × Bool), (l.map letter).prod = w := by
  induction w using Monoid.Coprod.induction_on with
  | inl g => exact ⟨[.inl g], by simp⟩
  | inr f =>
    induction f using FreeGroup.induction_on with
    | one => exact ⟨[], by simp⟩
    | of y => exact ⟨[.inr (y, true)], by simp⟩
    | inv_of y _ => exact ⟨[.inr (y, false)], by simp⟩
    | mul f₁ f₂ h₁ h₂ =>
      obtain ⟨l₁, hl₁⟩ := h₁
      obtain ⟨l₂, hl₂⟩ := h₂
      exact ⟨l₁ ++ l₂, by simp [hl₁, hl₂]⟩
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

end Reduced

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
    | simp [isReduced_cons_cons] at hl; done
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
    { toFun l := ⟨letterMul (.inl g) l, isReduced_letterMul l.2 _⟩
      invFun l := ⟨letterMul (.inl g⁻¹) l, isReduced_letterMul l.2 _⟩
      left_inv l := Subtype.ext <| by
        dsimp only
        rw [letterMul_inl_mul l.2, inv_mul_cancel, letterMul_inl_one l.2]
      right_inv l := Subtype.ext <| by
        dsimp only
        rw [letterMul_inl_mul l.2, mul_inv_cancel, letterMul_inl_one l.2] }
  map_one' := Equiv.ext fun l => Subtype.ext (letterMul_inl_one l.2)
  map_mul' g h := Equiv.ext fun l => Subtype.ext (letterMul_inl_mul l.2 g h).symm

/-- The action of a variable on reduced words. -/
private noncomputable def varPerm (x : X) :
    Equiv.Perm {l : List (G ⊕ X × Bool) // IsReduced l} where
  toFun l := ⟨letterMul (.inr (x, true)) l, isReduced_letterMul l.2 _⟩
  invFun l := ⟨letterMul (.inr (x, false)) l, isReduced_letterMul l.2 _⟩
  left_inv l := Subtype.ext (letterMul_inr_letterMul_inr l.2 (x, true))
  right_inv l := Subtype.ext (letterMul_inr_letterMul_inr l.2 (x, false))

/-- The action of `G[X]` on reduced words, by left multiplication followed by reduction. -/
private noncomputable def act : GX G X →* Equiv.Perm {l : List (G ⊕ X × Bool) // IsReduced l} :=
  Monoid.Coprod.lift coeffPerm (FreeGroup.lift varPerm)

/-- The reduced word of an element `w` of `G[X]`: the unique reduced word in coefficients and
variable letters whose product is `w` (`reducedWord_eq_iff`). -/
noncomputable def reducedWord (w : GX G X) : List (G ⊕ X × Bool) :=
  (act w ⟨[], by simp⟩).1

private theorem act_letter (a : G ⊕ X × Bool) (l : {l : List (G ⊕ X × Bool) // IsReduced l}) :
    (act (letter a) l).1 = letterMul a l.1 := by
  rcases a with g | ⟨y, _ | _⟩ <;> simp [act, coeffPerm, varPerm, Equiv.Perm.inv_def]

private theorem act_prod (l : List (G ⊕ X × Bool)) (m : {l : List (G ⊕ X × Bool) // IsReduced l}) :
    (act (l.map letter).prod m).1 = l.foldr letterMul m.1 := by
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

private theorem countVar_letterMul_le (x : X) (a : G ⊕ X × Bool) (l : List (G ⊕ X × Bool)) :
    countVar x (letterMul a l) ≤ countVar x [a] + countVar x l := by
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
  · simp [isReduced_cons_cons] at h
  · simp_all [isReduced_cons_cons]
  · have := (isReduced_cons_cons.1 h).2.1
    simp only [combines_inr_inr] at this
    simp [this]

theorem isReduced_reducedWord (w : GX G X) : IsReduced (reducedWord w) :=
  (act w _).2

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
theorem reducedWord_eq_nil_iff {w : GX G X} : reducedWord w = [] ↔ w = 1 := by
  simp [reducedWord_eq_iff isReduced_nil, eq_comm]

@[simp]
theorem reducedWord_one : reducedWord (1 : GX G X) = [] :=
  reducedWord_eq_nil_iff.2 rfl

theorem reducedWord_inl_of_ne_one {g : G} (hg : g ≠ 1) : reducedWord (inl g : GX G X) = [.inl g] :=
  (reducedWord_eq_iff (by simpa using hg)).2 (by simp)

/-- The reduced word of a variable word `inr f` consists of the letters of the reduced word of `f`
in the free group `F(X)`. -/
@[simp]
theorem reducedWord_inr [DecidableEq X] (f : FreeGroup X) :
    reducedWord (inr f : GX G X) = f.toWord.map .inr := by
  refine (reducedWord_eq_iff ⟨by simp, ?_⟩).2 ?_
  · exact (List.isChain_map _).2 <| FreeGroup.isReduced_toWord.imp fun a b h ⟨h₁, h₂⟩ => h₂ (h h₁)
  · rw [List.map_map]
    conv_rhs => rw [← FreeGroup.mk_toWord (x := f)]
    induction f.toWord with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons p L ih =>
      rw [List.map_cons, List.prod_cons, ih, Function.comp_apply, letter_inr, ← map_mul,
        FreeGroup.mul_mk, List.singleton_append]

/-- Reduction does not increase the number of letters `x^{±1}`: the reduced word of the product of
a word `l` has at most as many letters `x^{±1}` as `l`. -/
theorem countVar_reducedWord_le (x : X) (l : List (G ⊕ X × Bool)) :
    countVar x (reducedWord (l.map letter).prod) ≤ countVar x l := by
  rw [reducedWord_prod_eq_foldr]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ← List.singleton_append, countVar_append]
    exact (countVar_letterMul_le x a _).trans (by omega)

end NormalForm

/-! ### Cyclically reduced words -/

section Cyclic

variable [One G]

/-- A word is cyclically reduced when it is reduced and, if it has at least two letters, its last
and first letters do not combine: no letter of the cyclic word it spells combines with the next
one. This condition is on letters: on words without coefficients it is
`FreeGroup.IsCyclicallyReduced`. It differs from the condition of [IFT, §2.2] on syllables, that
the first and last syllables lie in different factors of `G ∗ F(X)`: `x g y` is cyclically reduced
here but not there, and `z⁻¹ y z` (one syllable of `F(X)`) is not cyclically reduced here. -/
def IsCyclicallyReduced (l : List (G ⊕ X × Bool)) : Prop :=
  IsReduced l ∧ ∀ a b m, l = a :: (m ++ [b]) → ¬Combines b a

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

/-- The word `z⁻¹ a z` is not cyclically reduced: its last letter `z` cancels against its first
letter `z⁻¹`. -/
theorem not_isCyclicallyReduced_inv_inl_self {a : G} {z : X} :
    ¬IsCyclicallyReduced ([.inr (z, false), .inl a, .inr (z, true)] : List (G ⊕ X × Bool)) :=
  fun h => h.2 _ _ [.inl a] rfl (by simp)

end Cyclic

/-! ### Cyclic reduction -/

section CyclicReduction

variable [Group G]

/-- `l` is the conjugate of a cyclically reduced word `m` by the product of an initial segment `u`
of `l`, and every letter `x^{±1}` of `l` is a letter of `m` or one of a pair in `u` and `u⁻¹`. -/
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

/-- Cyclic reduction relative to `G`: a reduced word `l` is the conjugate `u m u⁻¹` of a
cyclically reduced word `m` by the product of an initial segment `u` of `l`, and every letter
`x^{±1}` of `l` is a letter of `m` or one of a pair of letters of `u` and `u⁻¹`. -/
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

end CyclicReduction

/-! ### Examples -/

section Examples

variable [Group G] {a : G} {z : X}

/-- For a nontrivial coefficient `a`, the conjugate `z⁻¹ a z` is reduced as written. -/
theorem reducedWord_inv_mul_inl_mul (ha : a ≠ 1) :
    reducedWord ((inr (FreeGroup.of z))⁻¹ * inl a * inr (FreeGroup.of z) : GX G X) =
      [.inr (z, false), .inl a, .inr (z, true)] :=
  (reducedWord_eq_iff (by simp [isReduced_cons_cons, ha])).2 (by simp [mul_assoc])

end Examples

end TauCeti.GroupAlgGeom.GX
