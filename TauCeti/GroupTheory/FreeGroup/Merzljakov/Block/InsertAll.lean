/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Cancellation
public import TauCeti.GroupTheory.FreeGroup.Merzljakov.Block.Insertion
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Inserting several variables into the blocks of a word

For letters `a`, `b` of `A`, exponents `m : X → ℕ` and a list `l` of variables,
`FreeGroup.blockInsertAll a b m l v` is the word over `X ⊕ A` obtained from `v` by inserting, for
each `x ∈ l`, the variable `x` into the blocks `b a^{m x} b` of `v` and `x⁻¹` into their formal
inverses (`FreeGroup.blockInsert`), one variable after the other. When two variables of `l` have
the same exponent, only the one inserted first, the later in `l`, enters their common blocks; the
proofs below use distinct exponents. This is the substitution of the proof of Merzljakov's theorem
which turns a solution of an equation in `FreeGroup A`, whose values at the universally quantified
variables are Merzljakov words, into a solution in `FreeGroup (X ⊕ A)`. This file proves the steps
of that proof which do not depend on the order of the quantifiers, shared by its form for
alternating blocks of quantifiers (`FreeGroup.exists_formalSolution_of_skolem`) and its form for
one block (`FreeGroup.exists_formalSolution_lift_eq_of_skolem`).

## Main definitions

* `FreeGroup.blockInsertAll`: the insertion of the variables of a list into their blocks.

## Main results

* `TauCeti.CancellationPieces.exists_mem_forall_isUnsplit_merzljakovBlock`: the choice of an
  exponent whose block no factorisation into cancellation pieces splits.
* `FreeGroup.exists_lift_mk_blockInsertAll_eq_one`: if substituting reduced words for the letters
  of a word gives the identity, so does substituting them with the variables inserted, for
  exponents chosen from given lists of more than `L²` exponents, `L` the length of the word.
* `FreeGroup.exists_mk_blockInsertAll_merzljakovWord`: the inserted Merzljakov word `u v` of a
  variable `x` is `u x v`.
* `FreeGroup.lift_eq_one_of_translate`: the endomorphism `x ↦ u⁻¹ x v⁻¹` of `FreeGroup (X ⊕ A)`
  turns a solution taking the values `u x v` at the variables into one taking the values `x`.

## References

* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.4, Merzljakov's Theorem.
-/

public section

namespace TauCeti.CancellationPieces

open FreeGroup List

/-- Over distinct letters `a ≠ b`, given cancellation pieces `P` of `L` words and more than `L²`
distinct exponents, one of the exponents `m` gives a block `b a^m b` that, like its formal inverse
`b⁻¹ a^{-m} b⁻¹`, is split by none of the factorisations of the words into the pieces. -/
theorem exists_mem_forall_isUnsplit_merzljakovBlock {A Z : Type*} {a b : A} (hab : a ≠ b)
    {ws : List (List (A × Bool))} (P : CancellationPieces ws Z) {ms : List ℕ} (hnd : ms.Nodup)
    (hlen : ws.length * ws.length < ms.length) :
    ∃ m ∈ ms, ∀ V ∈ P.patterns,
      (merzljakovBlock a b m).IsUnsplit (V.map (substituteLetter P.piece)) ∧
        (invRev (merzljakovBlock a b m)).IsUnsplit (V.map (substituteLetter P.piece)) := by
  let Fs := P.patterns.map fun V ↦ V.map (substituteLetter P.piece)
  suffices ∃ m ∈ ms, ∀ F ∈ Fs,
      (merzljakovBlock a b m).IsUnsplit F ∧ (invRev (merzljakovBlock a b m)).IsUnsplit F by
    obtain ⟨m, hm, hF⟩ := this
    exact ⟨m, hm, fun V hV ↦ hF _ (mem_map_of_mem hV)⟩
  refine FreeGroup.exists_mem_forall_isUnsplit_merzljakovBlock hab hnd ?_
  -- each of the `L` factorisations has at most `L - 1` pieces
  have hle : ∀ n ∈ Fs.map (fun F ↦ F.length - 1), n ≤ ws.length := by
    intro n hn
    obtain ⟨F, hF, rfl⟩ := mem_map.1 hn
    obtain ⟨V, hV, rfl⟩ := mem_map.1 hF
    have hVlen := P.length_le_of_mem_patterns hV
    simp only [length_map] at hVlen ⊢
    lia
  calc (Fs.map fun F ↦ F.length - 1).sum
    _ ≤ (Fs.map fun F ↦ F.length - 1).length • ws.length := sum_le_length_nsmul _ _ hle
    _ = ws.length * ws.length := by simp [Fs]
    _ < ms.length := hlen

end TauCeti.CancellationPieces

namespace FreeGroup

open List

private theorem injective_prodMap_inr {A X : Type*} :
    Function.Injective (Prod.map (Sum.inr : A → X ⊕ A) (id : Bool → Bool)) :=
  Sum.inr_injective.prodMap Function.injective_id

private theorem fst_ne_inl_of_mem_merzljakovBlock {A X : Type*} {a b : A} {n : ℕ}
    {c : (X ⊕ A) × Bool} (hc : c ∈ merzljakovBlock (Sum.inr a) (Sum.inr b) n) (x : X) :
    c.1 ≠ Sum.inl x := by
  rcases fst_eq_or_eq_of_mem_merzljakovBlock hc with h | h <;> simp [h]

section BlockInsertAll

variable {A X : Type*} [DecidableEq A] [DecidableEq X] (a b : A) (m : X → ℕ)

/-- Insert, for each variable `x` of the list `l`, the letter `x` into the blocks `b a^{m x} b` of
a word over `X ⊕ A` and the letter `x⁻¹` into their formal inverses, the last variable of `l`
first. A block already broken by an earlier insertion, of a variable with the same exponent, is
no longer a block. -/
def blockInsertAll : List X → List ((X ⊕ A) × Bool) → List ((X ⊕ A) × Bool)
  | [], v => v
  | x :: l, v => blockInsert (Sum.inr a) (Sum.inr b) (Sum.inl x) (m x) (blockInsertAll l v)

@[simp]
theorem blockInsertAll_nil (v : List ((X ⊕ A) × Bool)) : blockInsertAll a b m [] v = v :=
  (rfl)

@[simp]
theorem blockInsertAll_cons (x : X) (l : List X) (v : List ((X ⊕ A) × Bool)) :
    blockInsertAll a b m (x :: l) v =
      blockInsert (Sum.inr a) (Sum.inr b) (Sum.inl x) (m x) (blockInsertAll a b m l v) :=
  (rfl)

variable {a b m}

private theorem map_blockInsertAll_cons (x : X) (l : List X) (L : List (List ((X ⊕ A) × Bool))) :
    L.map (blockInsertAll a b m (x :: l)) = (L.map (blockInsertAll a b m l)).map
      (blockInsert (Sum.inr a) (Sum.inr b) (Sum.inl x) (m x)) := by
  simp [List.map_map, Function.comp_def]

/-- The insertion commutes with formal inverses. -/
theorem blockInsertAll_invRev (l : List X) (v : List ((X ⊕ A) × Bool)) :
    blockInsertAll a b m l (invRev v) = invRev (blockInsertAll a b m l v) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [blockInsertAll_cons, blockInsertAll_cons, ih, blockInsert_invRev]

/-- The insertion commutes with substituting a word, or its formal inverse, for a letter. -/
theorem blockInsertAll_substituteLetter {α : Type*} (l : List X)
    (f : α → List ((X ⊕ A) × Bool)) (z : α × Bool) :
    blockInsertAll a b m l (substituteLetter f z) =
      substituteLetter (fun x ↦ blockInsertAll a b m l (f x)) z := by
  obtain ⟨x, _ | _⟩ := z <;> simp [substituteLetter, blockInsertAll_invRev]

/-- A word of one letter contains no block, so the insertion leaves it unchanged. -/
@[simp]
theorem blockInsertAll_singleton (l : List X) (c : (X ⊕ A) × Bool) :
    blockInsertAll a b m l [c] = [c] := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [blockInsertAll_cons, ih, blockInsert_singleton]

/-- Erasing the inserted variables undoes the insertion. -/
theorem map_mk_blockInsertAll {G : Type*} [Monoid G] (φ : FreeGroup (X ⊕ A) →* G) {l : List X}
    (hφ : ∀ x ∈ l, φ (of (Sum.inl x)) = 1) (v : List ((X ⊕ A) × Bool)) :
    φ (mk (blockInsertAll a b m l v)) = φ (mk v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [blockInsertAll_cons, map_mk_blockInsert φ (hφ x mem_cons_self),
      ih fun x' hx' ↦ hφ x' (mem_cons_of_mem _ hx')]

/-- Every letter of an inserted word is a letter of the original word or an inserted variable. -/
theorem mem_or_exists_of_mem_blockInsertAll {l : List X} {v : List ((X ⊕ A) × Bool)}
    {c : (X ⊕ A) × Bool} (hc : c ∈ blockInsertAll a b m l v) :
    c ∈ v ∨ ∃ x ∈ l, c.1 = Sum.inl x := by
  induction l with
  | nil => exact .inl hc
  | cons x l ih =>
    rcases fst_eq_or_mem_of_mem_blockInsert hc with h | h
    · exact .inr ⟨x, mem_cons_self, h⟩
    · exact (ih h).imp_right fun ⟨x', hx', h'⟩ ↦ ⟨x', mem_cons_of_mem _ hx', h'⟩

/-- A word containing none of the inserted variables occurs in an inserted word only if it occurs
in the original word. -/
theorem isInfix_of_isInfix_blockInsertAll {l : List X} {u v : List ((X ⊕ A) × Bool)}
    (h : u <:+: blockInsertAll a b m l v) (hu : ∀ c ∈ u, ∀ x ∈ l, c.1 ≠ Sum.inl x) : u <:+: v := by
  induction l with
  | nil => exact h
  | cons x l ih =>
    exact ih (isInfix_of_isInfix_blockInsert h fun c hc ↦ hu c hc x mem_cons_self)
      fun c hc x' hx' ↦ hu c hc x' (mem_cons_of_mem _ hx')

/-- In a word over the letters `A`, the variables whose blocks, and their formal inverses, do not
occur can be left out of the insertion. -/
theorem blockInsertAll_filter_map (p : X → Bool) {l : List X} {w : List (A × Bool)}
    (h : ∀ x ∈ l, p x = false →
      ¬ merzljakovBlock a b (m x) <:+: w ∧ ¬ invRev (merzljakovBlock a b (m x)) <:+: w) :
    blockInsertAll a b m (l.filter p) (w.map (Prod.map Sum.inr id)) =
      blockInsertAll a b m l (w.map (Prod.map Sum.inr id)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun x' hx' ↦ h x' (mem_cons_of_mem _ hx')
    cases hp : p x
    · -- the blocks of `x` do not occur after the insertion of the other variables either
      have hx := h x mem_cons_self hp
      rw [filter_cons_of_neg (by simp [hp]), ih', blockInsertAll_cons, blockInsert_eq_self]
      · refine fun hinf ↦ hx.1 ?_
        have := isInfix_of_isInfix_blockInsertAll hinf fun c hc x' _ ↦
          fst_ne_inl_of_mem_merzljakovBlock hc x'
        rwa [← map_prodMap_merzljakovBlock, infix_map_iff_of_injective injective_prodMap_inr]
          at this
      · refine fun hinf ↦ hx.2 ?_
        have := isInfix_of_isInfix_blockInsertAll hinf fun c hc x' _ ↦
          fst_ne_inl_of_mem_merzljakovBlock (TauCeti.FreeGroup.mem_invRev_iff.1 hc) x'
        rwa [← map_prodMap_merzljakovBlock, ← map_prodMap_invRev,
          infix_map_iff_of_injective injective_prodMap_inr] at this
    · rw [filter_cons_of_pos hp, blockInsertAll_cons, blockInsertAll_cons, ih']

/-- The insertion respects a factorisation of a word that splits none of the blocks and none of
their formal inverses, provided the blocks contain no variables. -/
theorem isUnsplit_map_blockInsertAll (l : List X) {u : List ((X ⊕ A) × Bool)}
    {L : List (List ((X ⊕ A) × Bool))} (huL : u.IsUnsplit L)
    (hu : ∀ c ∈ u, ∀ x ∈ l, c.1 ≠ Sum.inl x) : u.IsUnsplit (L.map (blockInsertAll a b m l)) := by
  induction l with
  | nil => simpa [blockInsertAll] using huL
  | cons x l ih =>
    rw [map_blockInsertAll_cons]
    exact isUnsplit_map_blockInsert (ih fun c hc x' hx' ↦ hu c hc x' (mem_cons_of_mem _ hx'))
      fun c hc ↦ hu c hc x mem_cons_self

/-- The insertion commutes with a concatenation that splits none of the blocks and none of their
formal inverses. -/
theorem blockInsertAll_flatten (l : List X) {L : List (List ((X ⊕ A) × Bool))}
    (h : ∀ x ∈ l, (merzljakovBlock (Sum.inr a) (Sum.inr b) (m x)).IsUnsplit L ∧
      (invRev (merzljakovBlock (Sum.inr a) (Sum.inr b) (m x))).IsUnsplit L) :
    blockInsertAll a b m l L.flatten = (L.map (blockInsertAll a b m l)).flatten := by
  induction l with
  | nil => simp [blockInsertAll]
  | cons x l ih =>
    have hx := h x mem_cons_self
    rw [blockInsertAll_cons, ih fun x' hx' ↦ h x' (mem_cons_of_mem _ hx'),
      blockInsert_flatten
        (isUnsplit_map_blockInsertAll l hx.1 fun c hc x' _ ↦
          fst_ne_inl_of_mem_merzljakovBlock hc x')
        (isUnsplit_map_blockInsertAll l hx.2 fun c hc x' _ ↦
          fst_ne_inl_of_mem_merzljakovBlock (TauCeti.FreeGroup.mem_invRev_iff.1 hc) x'),
      map_blockInsertAll_cons]

end BlockInsertAll

section Cancellation

variable {A X : Type*} [DecidableEq A] [DecidableEq X] {a b : A} {m : X → ℕ}

/-- Inserting into the substitution of the pieces into one pattern of the cancellation pieces
is substituting the inserted pieces, when the factorisation along the pieces splits none of the
blocks. -/
private theorem flatMap_substituteLetter_blockInsertAll {ι : Type*} (piece : ι → List (A × Bool))
    (l : List X) {V : List (ι × Bool)} (hm : ∀ x ∈ l,
      (merzljakovBlock a b (m x)).IsUnsplit (V.map (substituteLetter piece)) ∧
        (invRev (merzljakovBlock a b (m x))).IsUnsplit (V.map (substituteLetter piece))) :
    V.flatMap (substituteLetter fun q ↦
        blockInsertAll a b m l ((piece q).map (Prod.map Sum.inr id))) =
      blockInsertAll a b m l ((V.flatMap (substituteLetter piece)).map (Prod.map Sum.inr id)) := by
  let L₀ := (V.map (substituteLetter piece)).map (List.map (Prod.map (Sum.inr : A → X ⊕ A) id))
  have hL₀ (x : X) (hx : x ∈ l) :
      (merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) (m x)).IsUnsplit L₀ ∧
        (invRev (merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) (m x))).IsUnsplit L₀ := by
    rw [← map_prodMap_merzljakovBlock, ← map_prodMap_invRev,
      map_isUnsplit_iff injective_prodMap_inr, map_isUnsplit_iff injective_prodMap_inr]
    exact hm x hx
  have hflat : L₀.flatten = (V.flatMap (substituteLetter piece)).map (Prod.map Sum.inr id) := by
    rw [← map_flatten, flatMap_def]
  rw [← hflat, blockInsertAll_flatten l hL₀]
  simp [L₀, flatMap_def, List.map_map, Function.comp_def, blockInsertAll_substituteLetter,
    map_prodMap_substituteLetter]

/-- Substituting the inserted words into the patterns of the cancellation pieces gives the words
obtained by inserting into the substituted letters. -/
private theorem map_flatMap_patterns_blockInsertAll {α ι : Type*} (W : List (α × Bool))
    (U : α → List (A × Bool)) (P : TauCeti.CancellationPieces (W.map (substituteLetter U)) ι)
    (l : List X) (hm : ∀ x, ∀ V ∈ P.patterns,
      (merzljakovBlock a b (m x)).IsUnsplit (V.map (substituteLetter P.piece)) ∧
        (invRev (merzljakovBlock a b (m x))).IsUnsplit (V.map (substituteLetter P.piece))) :
    P.patterns.map (fun V ↦ V.flatMap (substituteLetter fun q ↦
        blockInsertAll a b m l ((P.piece q).map (Prod.map Sum.inr id)))) =
      W.map (substituteLetter fun z ↦
        blockInsertAll a b m l ((U z).map (Prod.map Sum.inr id))) := by
  calc _ = P.patterns.map (fun V ↦ blockInsertAll a b m l
          ((V.flatMap (substituteLetter P.piece)).map (Prod.map Sum.inr id))) :=
      map_congr_left fun V hV ↦ flatMap_substituteLetter_blockInsertAll _ l fun x _ ↦ hm x V hV
    _ = (W.map (substituteLetter U)).map
          (fun v ↦ blockInsertAll a b m l (v.map (Prod.map Sum.inr id))) := by
      have hmap := congrArg
        (List.map fun v ↦ blockInsertAll a b m l (v.map (Prod.map Sum.inr id)))
        P.map_flatMap_patterns
      simpa only [List.map_map, Function.comp_def] using hmap
    _ = _ := by
      simp [List.map_map, Function.comp_def, blockInsertAll_substituteLetter,
        map_prodMap_substituteLetter]

/-- If substituting reduced words `U z` for the letters `z` of a word `W` gives the identity, so
does substituting the words with the variables of `l` inserted into the blocks `b a^{m x} b`, for
some exponents `m x` taken from given lists `ms x` of more than `|W|²` distinct exponents. -/
theorem exists_lift_mk_blockInsertAll_eq_one (hab : a ≠ b) {α : Type*} {W : List (α × Bool)}
    {U : α → List (A × Bool)} (hU : ∀ c ∈ W, IsReduced (U c.1))
    (hW : lift (fun z ↦ mk (U z)) (mk W) = 1)
    {ms : X → List ℕ} (hms : ∀ x, (ms x).Nodup) (hlen : ∀ x, W.length * W.length < (ms x).length)
    (l : List X) : ∃ m : X → ℕ, (∀ x, m x ∈ ms x) ∧
      lift (fun z ↦ mk (blockInsertAll a b m l ((U z).map (Prod.map Sum.inr id)))) (mk W) = 1 := by
  have hws_red : ∀ v ∈ W.map (substituteLetter U), IsReduced v := by
    intro v hv
    obtain ⟨⟨z, _ | _⟩, hz, rfl⟩ := mem_map.1 hv
    exacts [(hU _ hz).invRev, hU _ hz]
  obtain ⟨p, ⟨P⟩⟩ := TauCeti.exists_cancellationPieces hws_red
    (by rw [← flatMap_def, mk_flatMap_substituteLetter, hW])
  choose m hm_mem hm_unsplit using fun x ↦
    P.exists_mem_forall_isUnsplit_merzljakovBlock hab (hms x) (by simpa using hlen x)
  refine ⟨m, hm_mem, ?_⟩
  have hflat : W.flatMap (substituteLetter fun z ↦
      blockInsertAll a b m l ((U z).map (Prod.map Sum.inr id))) =
        P.patterns.flatten.flatMap (substituteLetter fun q ↦
          blockInsertAll a b m l ((P.piece q).map (Prod.map Sum.inr id))) := by
    rw [flatMap_def, ← map_flatMap_patterns_blockInsertAll W U P l hm_unsplit]
    simp [flatMap_def, map_flatten, flatten_flatten, List.map_map, Function.comp_def]
  rw [← mk_flatMap_substituteLetter, hflat, mk_flatMap_substituteLetter, P.mk_flatten_patterns,
    _root_.map_one]

end Cancellation

section MerzljakovWord

variable {A X : Type*} [DecidableEq A] [DecidableEq X] {a b : A} {m : X → ℕ}

omit [DecidableEq A] [DecidableEq X] in
/-- A word over `X ⊕ A` which becomes a Merzljakov word without the exponent `n` when every
variable is sent to `a` contains neither the block `b a^n b` nor its formal inverse. -/
private theorem not_isInfix_of_map_eq_merzljakovWord (hab : a ≠ b) {ms : List ℕ} {n : ℕ}
    (hn : n ∉ ms) {R : List ((X ⊕ A) × Bool)}
    (hR : R.map (Prod.map (Sum.elim (fun _ ↦ a) id) id) = merzljakovWord a b ms) :
    ¬ merzljakovBlock (Sum.inr a) (Sum.inr b) n <:+: R ∧
      ¬ invRev (merzljakovBlock (Sum.inr a) (Sum.inr b) n) <:+: R := by
  have hblock : (merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) n).map
      (Prod.map (Sum.elim (fun _ ↦ a) id) id) = merzljakovBlock a b n := by
    simp [map_prodMap_merzljakovBlock]
  refine ⟨fun h ↦ hn ?_, fun h ↦ ?_⟩
  · have := h.map (Prod.map (Sum.elim (fun _ ↦ a) id) id)
    rwa [hblock, hR, merzljakovBlock_isInfix_merzljakovWord_iff hab] at this
  · have := h.map (Prod.map (Sum.elim (fun _ ↦ a) id) id)
    rw [map_prodMap_invRev, hblock, hR] at this
    exact not_invRev_merzljakovBlock_isInfix_merzljakovWord a b _ _ this

/-- Inserting into a Merzljakov word whose exponent list contains the exponent `m x` of the
inserted variable `x`, and no exponent of another inserted variable, inserts `x` into its block
`b a^{m x} b` and changes nothing else. -/
private theorem blockInsertAll_merzljakovWord (hab : a ≠ b) {l : List X} {x : X} (hx : x ∈ l)
    {ms₁ ms₂ : List ℕ} (hms : (ms₁ ++ m x :: ms₂).Nodup)
    (hdisj : ∀ x' ∈ l, x' ≠ x → m x' ∉ ms₁ ++ m x :: ms₂) :
    blockInsertAll a b m l ((merzljakovWord a b (ms₁ ++ m x :: ms₂)).map (Prod.map Sum.inr id)) =
      (merzljakovWord a b ms₁ ++ replicate (m x) (a, true)).map (Prod.map Sum.inr id) ++
        (Sum.inl x, true) :: (merzljakovWord a b ms₂).map (Prod.map Sum.inr id) := by
  have hm₁ : m x ∉ ms₁ := fun h₁ ↦ (nodup_append.1 hms).2.2 _ h₁ _ mem_cons_self rfl
  have hm₂ : m x ∉ ms₂ := (nodup_cons.1 (nodup_append.1 hms).2.1).1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (count_pos_iff.2 hx).ne'
  -- only the insertions of `x` change the word, and only the first of them
  rw [← blockInsertAll_filter_map (· = x) fun x' hx' hne ↦
      ⟨fun h ↦ hdisj x' hx' (by simpa using hne)
        ((merzljakovBlock_isInfix_merzljakovWord_iff hab).1 h),
      not_invRev_merzljakovBlock_isInfix_merzljakovWord a b _ _⟩, filter_eq, hk]
  clear hk
  induction k with
  | zero =>
    rw [zero_add, replicate_one, blockInsertAll_cons, blockInsertAll_nil,
      map_prodMap_merzljakovWord, blockInsert_merzljakovWord (Sum.inr_injective.ne hab) hm₁ hm₂]
    simp [map_prodMap_merzljakovWord]
  | succ k ih =>
    -- sending `x` to `a` turns the inserted word into the Merzljakov word with `m x + 1`
    have hR : ((merzljakovWord a b ms₁ ++ replicate (m x) (a, true)).map (Prod.map Sum.inr id) ++
        (Sum.inl x, true) :: (merzljakovWord a b ms₂).map (Prod.map Sum.inr id)).map
          (Prod.map (Sum.elim (fun _ ↦ a) id) id) =
        merzljakovWord a b (ms₁ ++ (m x + 1) :: ms₂) := by
      simp [merzljakovWord_append_cons, replicate_succ']
    obtain ⟨hnot, hnot'⟩ :=
      not_isInfix_of_map_eq_merzljakovWord hab (n := m x) (by simp [hm₁, hm₂]) hR
    rw [replicate_succ, blockInsertAll_cons, ih, blockInsert_eq_self hnot hnot']

/-- The Merzljakov word `u v` of a variable `x`, after the insertion of the variables of `l`,
becomes `u x v` when `x ∈ l`, provided the exponent lists are nodup and contain the exponents of
the insertion, and the lists of distinct variables of `l` are disjoint. -/
theorem exists_mk_blockInsertAll_merzljakovWord (hab : a ≠ b) {l : List X} {ms : X → List ℕ}
    (hms : ∀ x, (ms x).Nodup) (hm : ∀ x, m x ∈ ms x)
    (hdisj : ∀ x ∈ l, ∀ x' ∈ l, ∀ n ∈ ms x, n ∈ ms x' → x = x') (x : X) :
    ∃ u v : FreeGroup A, mk (merzljakovWord a b (ms x)) = u * v ∧ (x ∈ l →
      mk (blockInsertAll a b m l ((merzljakovWord a b (ms x)).map (Prod.map Sum.inr id))) =
        map Sum.inr u * of (Sum.inl x) * map Sum.inr v) := by
  by_cases hx : x ∈ l
  · obtain ⟨ms₁, ms₂, hms₁₂⟩ := append_of_mem (hm x)
    refine ⟨mk (merzljakovWord a b ms₁ ++ replicate (m x) (a, true)), mk (merzljakovWord a b ms₂),
      by rw [hms₁₂, mul_mk, merzljakovWord_append_cons, append_assoc], fun _ ↦ ?_⟩
    rw [hms₁₂, blockInsertAll_merzljakovWord hab hx (hms₁₂ ▸ hms x)
      fun x' hx' hne h ↦ hne (hdisj x' hx' x hx _ (hm x') (hms₁₂ ▸ h)), ← singleton_append,
      ← append_assoc, ← mul_mk, ← mul_mk]
    simp [Prod.map_def, map.mk, of]
  · exact ⟨_, 1, (mul_one _).symm, fun h ↦ absurd h hx⟩

end MerzljakovWord

/-- If `w = 1` has a solution in `FreeGroup (X ⊕ A)` whose value at each variable `x` is its
two-sided translate `u x * x * v x` by constants `u x`, `v x` of `FreeGroup A`, then composing
with the endomorphism `x ↦ (u x)⁻¹ * x * (v x)⁻¹`, which fixes the constants, gives a solution
whose value at each variable `x` is `x`. -/
theorem lift_eq_one_of_translate {A X Y : Type*} (w : FreeGroup ((X ⊕ Y) ⊕ A))
    {u v : X → FreeGroup A} {y₀ : Y → FreeGroup (X ⊕ A)}
    (hw : lift (Sum.elim (Sum.elim (fun x ↦ map Sum.inr (u x) * of (Sum.inl x) * map Sum.inr (v x))
      y₀) (of ∘ Sum.inr)) w = 1) :
    lift (Sum.elim (Sum.elim (of ∘ Sum.inl) fun j ↦ lift (Sum.elim
      (fun x ↦ (map Sum.inr (u x))⁻¹ * of (Sum.inl x) * (map Sum.inr (v x))⁻¹) (of ∘ Sum.inr))
        (y₀ j)) (of ∘ Sum.inr)) w = 1 := by
  set ψ : FreeGroup (X ⊕ A) →* FreeGroup (X ⊕ A) :=
    lift (Sum.elim (fun x ↦ (map Sum.inr (u x))⁻¹ * of (Sum.inl x) * (map Sum.inr (v x))⁻¹)
      (of ∘ Sum.inr))
  have hψ_inr (q : FreeGroup A) : ψ (map Sum.inr q) = map Sum.inr q := by
    have hcomp : ψ.comp (map Sum.inr) = map Sum.inr := ext_hom _ _ fun c ↦ by simp [ψ]
    exact DFunLike.congr_fun hcomp q
  have hcomp : ψ.comp (lift (Sum.elim (Sum.elim
      (fun x ↦ map Sum.inr (u x) * of (Sum.inl x) * map Sum.inr (v x)) y₀) (of ∘ Sum.inr))) =
      lift (Sum.elim (Sum.elim (of ∘ Sum.inl) fun j ↦ ψ (y₀ j)) (of ∘ Sum.inr)) := by
    refine ext_hom _ _ fun z ↦ ?_
    rcases z with (x | j) | c
    · simp only [MonoidHom.comp_apply, lift_apply_of, Sum.elim_inl, _root_.map_mul, hψ_inr,
        Function.comp_apply]
      simp only [ψ, lift_apply_of, Sum.elim_inl]
      group
    · simp
    · simp [ψ]
  rw [← hcomp, MonoidHom.comp_apply, hw, _root_.map_one]

end FreeGroup
