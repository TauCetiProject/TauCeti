/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Merzljakov.BlockInsertion
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Merzljakov.FormalSolution

/-!
# Merzljakov's theorem for one block of quantifiers, and the values of the formal solution

Let `w` be an element of `FreeGroup ((X ⊕ Y) ⊕ A)`, viewed as the left-hand side of an equation
`w(x, y) = 1` with constants in `FreeGroup A`, universally quantified variables
`x = Sum.inl (Sum.inl i)` and existentially quantified variables `y = Sum.inl (Sum.inr j)`, all of
them after the universal ones. Suppose that `f` chooses witnesses: `w(x, f x) = 1` holds in
`FreeGroup A` for all `x`. If `A` has two distinct letters, the equation has a formal solution:
words `y j ∈ FreeGroup (X ⊕ A)` such that `w(x, y) = 1` holds in `FreeGroup (X ⊕ A)`. Moreover,
the formal solution takes, at some point `g : X → FreeGroup A`, the values of the chosen
witnesses: `y j (g) = f g j`.

The last property is what turns Merzljakov's theorem into its form with an inequation: if the
witnesses `f x` also satisfy `u(x, f x) ≠ 1`, then `u(x, y) ≠ 1` in `FreeGroup (X ⊕ A)`, since its
specialisation at `g` is `u(g, f g) ≠ 1`.

## Main results

* `FreeGroup.exists_formalSolution_lift_eq_of_skolem`: a formal solution of `w(x, y) = 1` whose
  values at one point are the chosen witnesses.

## References

* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.4, Merzljakov's Theorem and the proof of Theorem 4.
-/

public section

namespace FreeGroup

open List

section InsertAll

variable {A X : Type*} [DecidableEq A] [DecidableEq X] (a b : A) (m : X → ℕ)

/-- Insert, for each `x` of the list `l`, the letter `x` into the blocks `b a^{m x} b` and `x⁻¹`
into their formal inverses, the last element of `l` first. -/
private def insertAll : List X → List ((X ⊕ A) × Bool) → List ((X ⊕ A) × Bool)
  | [], v => v
  | x :: l, v => blockInsert (Sum.inr a) (Sum.inr b) (Sum.inl x) (m x) (insertAll l v)

variable {a b m}

private theorem insertAll_cons (x : X) (l : List X) (v : List ((X ⊕ A) × Bool)) :
    insertAll a b m (x :: l) v =
      blockInsert (Sum.inr a) (Sum.inr b) (Sum.inl x) (m x) (insertAll a b m l v) :=
  rfl

private theorem insertAll_append (l₁ l₂ : List X) (v : List ((X ⊕ A) × Bool)) :
    insertAll a b m (l₁ ++ l₂) v = insertAll a b m l₁ (insertAll a b m l₂ v) := by
  induction l₁ with
  | nil => rfl
  | cons x l₁ ih => rw [cons_append, insertAll_cons, insertAll_cons, ih]

private theorem insertAll_invRev (l : List X) (v : List ((X ⊕ A) × Bool)) :
    insertAll a b m l (invRev v) = invRev (insertAll a b m l v) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [insertAll_cons, insertAll_cons, ih, blockInsert_invRev]

private theorem insertAll_substituteLetter {α : Type*} (l : List X) (f : α → List ((X ⊕ A) × Bool))
    (z : α × Bool) : insertAll a b m l (substituteLetter f z) =
      substituteLetter (fun x ↦ insertAll a b m l (f x)) z := by
  obtain ⟨x, _ | _⟩ := z <;> simp [substituteLetter, insertAll_invRev]

private theorem insertAll_singleton (l : List X) (c : (X ⊕ A) × Bool) :
    insertAll a b m l [c] = [c] := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [insertAll_cons, ih, blockInsert_singleton]

/-- Insertion leaves a word unchanged when none of the blocks, nor their inverses, occurs in it. -/
private theorem insertAll_eq_self {l : List X} {v : List ((X ⊕ A) × Bool)}
    (h : ∀ x ∈ l, ¬ merzljakovBlock (Sum.inr a) (Sum.inr b) (m x) <:+: v ∧
      ¬ invRev (merzljakovBlock (Sum.inr a) (Sum.inr b) (m x)) <:+: v) :
    insertAll a b m l v = v := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [insertAll_cons, ih fun x' hx' ↦ h x' (mem_cons_of_mem _ hx'),
      blockInsert_eq_self (h x mem_cons_self).1 (h x mem_cons_self).2]

/-- Erasing the inserted letters undoes the insertion. -/
private theorem map_mk_insertAll {G : Type*} [Monoid G] (φ : FreeGroup (X ⊕ A) →* G)
    (hφ : ∀ x, φ (of (Sum.inl x)) = 1) (l : List X) (v : List ((X ⊕ A) × Bool)) :
    φ (mk (insertAll a b m l v)) = φ (mk v) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [insertAll_cons, map_mk_blockInsert φ (hφ x), ih]

omit [DecidableEq A] [DecidableEq X] in
private theorem fst_ne_inl_of_mem_merzljakovBlock {n : ℕ} {c : (X ⊕ A) × Bool}
    (hc : c ∈ merzljakovBlock (Sum.inr a) (Sum.inr b) n) (x : X) : c.1 ≠ Sum.inl x := by
  rcases fst_eq_or_eq_of_mem_merzljakovBlock hc with h | h <;> simp [h]

private theorem isUnsplit_map_insertAll (l : List X) {u : List ((X ⊕ A) × Bool)}
    {L : List (List ((X ⊕ A) × Bool))} (huL : u.IsUnsplit L)
    (hu : ∀ c ∈ u, ∀ x ∈ l, c.1 ≠ Sum.inl x) : u.IsUnsplit (L.map (insertAll a b m l)) := by
  induction l with
  | nil => simpa [insertAll] using huL
  | cons x l ih =>
    have hmap : L.map (insertAll a b m (x :: l)) = (L.map (insertAll a b m l)).map
        (blockInsert (Sum.inr a) (Sum.inr b) (Sum.inl x) (m x)) := by
      simp [insertAll_cons, List.map_map, Function.comp_def]
    rw [hmap]
    exact isUnsplit_map_blockInsert (ih fun c hc x' hx' ↦ hu c hc x' (mem_cons_of_mem _ hx'))
      fun c hc ↦ hu c hc x mem_cons_self

/-- Insertion commutes with a concatenation that splits none of the blocks and none of their
inverses. -/
private theorem insertAll_flatten (l : List X) {L : List (List ((X ⊕ A) × Bool))}
    (h : ∀ x ∈ l, (merzljakovBlock (Sum.inr a) (Sum.inr b) (m x)).IsUnsplit L ∧
      (invRev (merzljakovBlock (Sum.inr a) (Sum.inr b) (m x))).IsUnsplit L) :
    insertAll a b m l L.flatten = (L.map (insertAll a b m l)).flatten := by
  induction l with
  | nil => simp [insertAll]
  | cons x l ih =>
    have hx := h x mem_cons_self
    rw [insertAll_cons, ih fun x' hx' ↦ h x' (mem_cons_of_mem _ hx'),
      blockInsert_flatten
        (isUnsplit_map_insertAll l hx.1 fun c hc x' _ ↦ fst_ne_inl_of_mem_merzljakovBlock hc x')
        (isUnsplit_map_insertAll l hx.2 fun c hc x' _ ↦
          fst_ne_inl_of_mem_merzljakovBlock (mem_invRev_iff.1 hc) x'), List.map_map]
    rfl

end InsertAll

section Construction

variable {A X : Type*} [DecidableEq A] [DecidableEq X] {a b : A} {m : X → ℕ}

/-- Inserting into the substitution of the pieces into one pattern of the cancellation pieces
is substituting the inserted pieces, when the factorisation along the pieces splits none of the
blocks. -/
private theorem flatMap_substituteLetter_insertAll {ι : Type*} (piece : ι → List (A × Bool))
    (l : List X) {V : List (ι × Bool)} (hm : ∀ x ∈ l,
      (merzljakovBlock a b (m x)).IsUnsplit (V.map (substituteLetter piece)) ∧
        (invRev (merzljakovBlock a b (m x))).IsUnsplit (V.map (substituteLetter piece))) :
    V.flatMap (substituteLetter fun q ↦ insertAll a b m l ((piece q).map (Prod.map Sum.inr id))) =
      insertAll a b m l ((V.flatMap (substituteLetter piece)).map (Prod.map Sum.inr id)) := by
  have hinj : Function.Injective (Prod.map (Sum.inr : A → X ⊕ A) (id : Bool → Bool)) :=
    Sum.inr_injective.prodMap Function.injective_id
  let L₀ := (V.map (substituteLetter piece)).map (List.map (Prod.map (Sum.inr : A → X ⊕ A) id))
  have hL₀ (x : X) (hx : x ∈ l) :
      (merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) (m x)).IsUnsplit L₀ ∧
        (invRev (merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) (m x))).IsUnsplit L₀ := by
    rw [← map_prodMap_merzljakovBlock, ← map_prodMap_invRev, map_isUnsplit_iff hinj,
      map_isUnsplit_iff hinj]
    exact hm x hx
  have hflat : L₀.flatten = (V.flatMap (substituteLetter piece)).map (Prod.map Sum.inr id) := by
    rw [← map_flatten, flatMap_def]
  rw [← hflat, insertAll_flatten l hL₀]
  simp [L₀, flatMap_def, List.map_map, Function.comp_def, insertAll_substituteLetter,
    map_prodMap_substituteLetter]

/-- Substituting the inserted words into the patterns of the cancellation pieces gives the words
obtained by inserting into the substituted letters. -/
private theorem map_flatMap_patterns_insertAll {α ι : Type*} (W : List (α × Bool))
    (U : α → List (A × Bool)) (P : TauCeti.CancellationPieces (W.map (substituteLetter U)) ι)
    (l : List X) (hm : ∀ x, ∀ V ∈ P.patterns,
      (merzljakovBlock a b (m x)).IsUnsplit (V.map (substituteLetter P.piece)) ∧
        (invRev (merzljakovBlock a b (m x))).IsUnsplit (V.map (substituteLetter P.piece))) :
    P.patterns.map (fun V ↦ V.flatMap (substituteLetter fun q ↦
        insertAll a b m l ((P.piece q).map (Prod.map Sum.inr id)))) =
      W.map (substituteLetter fun z ↦ insertAll a b m l ((U z).map (Prod.map Sum.inr id))) := by
  calc _ = P.patterns.map (fun V ↦ insertAll a b m l
          ((V.flatMap (substituteLetter P.piece)).map (Prod.map Sum.inr id))) :=
      map_congr_left fun V hV ↦ flatMap_substituteLetter_insertAll _ l fun x _ ↦ hm x V hV
    _ = (W.map (substituteLetter U)).map
          (fun v ↦ insertAll a b m l (v.map (Prod.map Sum.inr id))) := by
      have hmap := congrArg
        (List.map fun v ↦ insertAll a b m l (v.map (Prod.map Sum.inr id))) P.map_flatMap_patterns
      simpa only [List.map_map, Function.comp_def] using hmap
    _ = _ := by
      simp [List.map_map, Function.comp_def, insertAll_substituteLetter,
        map_prodMap_substituteLetter]

/-- If substituting reduced words `U z` for the letters of `W` gives the identity, so does
substituting the words with the letters of `l` inserted into blocks `b a^{m x} b`, for exponents
`m x` taken from given nodup lists `ms x` of more than `|W|²` exponents. -/
private theorem exists_lift_mk_insertAll_eq_one (hab : a ≠ b) {α : Type*} {W : List (α × Bool)}
    {U : α → List (A × Bool)} (hU : ∀ z, IsReduced (U z)) (hW : lift (fun z ↦ mk (U z)) (mk W) = 1)
    {ms : X → List ℕ} (hms : ∀ x, (ms x).Nodup) (hlen : ∀ x, W.length * W.length < (ms x).length)
    (l : List X) : ∃ m : X → ℕ, (∀ x, m x ∈ ms x) ∧
      lift (fun z ↦ mk (insertAll a b m l ((U z).map (Prod.map Sum.inr id)))) (mk W) = 1 := by
  have hws_red : ∀ v ∈ W.map (substituteLetter U), IsReduced v := by
    intro v hv
    obtain ⟨⟨z, _ | _⟩, -, rfl⟩ := mem_map.1 hv
    exacts [(hU z).invRev, hU z]
  obtain ⟨p, ⟨P⟩⟩ := TauCeti.exists_cancellationPieces hws_red
    (by rw [← flatMap_def, mk_flatMap_substituteLetter, hW])
  choose m hm_mem hm_unsplit using fun x ↦
    P.exists_mem_forall_isUnsplit_merzljakovBlock hab (hms x) (by simpa using hlen x)
  refine ⟨m, hm_mem, ?_⟩
  have hflat : W.flatMap (substituteLetter fun z ↦
      insertAll a b m l ((U z).map (Prod.map Sum.inr id))) = P.patterns.flatten.flatMap
        (substituteLetter fun q ↦ insertAll a b m l ((P.piece q).map (Prod.map Sum.inr id))) := by
    rw [flatMap_def, ← map_flatMap_patterns_insertAll W U P l hm_unsplit]
    simp [flatMap_def, map_flatten, flatten_flatten, List.map_map, Function.comp_def]
  rw [← mk_flatMap_substituteLetter, hflat, mk_flatMap_substituteLetter, P.mk_flatten_patterns,
    _root_.map_one]

/-- Insertion leaves a word unchanged when the blocks of the inserted letters, and their inverses,
occur in it only where they occur in the Merzljakov word `merzljakovWord a b ms`, whose exponent
list contains none of the inserted exponents. -/
private theorem insertAll_eq_self_of_merzljakovWord (hab : a ≠ b) {ms : List ℕ} {l : List X}
    (hl : ∀ x ∈ l, m x ∉ ms) {w : List ((X ⊕ A) × Bool)}
    (hw : ∀ n, merzljakovBlock (Sum.inr a) (Sum.inr b) n <:+: w →
      merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) n <:+:
        (merzljakovWord a b ms).map (Prod.map Sum.inr id))
    (hw' : ∀ n, invRev (merzljakovBlock (Sum.inr a) (Sum.inr b) n) <:+: w →
      invRev (merzljakovBlock (Sum.inr a : X ⊕ A) (Sum.inr b) n) <:+:
        (merzljakovWord a b ms).map (Prod.map Sum.inr id)) :
    insertAll a b m l w = w := by
  have hinj : Function.Injective (Prod.map (Sum.inr : A → X ⊕ A) (id : Bool → Bool)) :=
    Sum.inr_injective.prodMap Function.injective_id
  refine insertAll_eq_self fun x hx ↦ ⟨fun h ↦ hl x hx ?_, fun h ↦ ?_⟩
  · have := hw _ h
    rwa [← map_prodMap_merzljakovBlock, infix_map_iff_of_injective hinj,
      merzljakovBlock_isInfix_merzljakovWord_iff hab] at this
  · have := hw' _ h
    rw [← map_prodMap_merzljakovBlock, ← map_prodMap_invRev,
      infix_map_iff_of_injective hinj] at this
    exact not_invRev_merzljakovBlock_isInfix_merzljakovWord a b _ _ this

/-- Inserting into a Merzljakov word whose exponent list contains the exponent `m x` of exactly
one inserted letter `x`, and no other inserted exponent, inserts `x` into its block `b a^{m x} b`
and changes nothing else. -/
private theorem insertAll_merzljakovWord (hab : a ≠ b) {l : List X} (hl : l.Nodup) {x : X}
    (hx : x ∈ l) {ms₁ ms₂ : List ℕ} (hms : (ms₁ ++ m x :: ms₂).Nodup)
    (hdisj : ∀ x' ∈ l, x' ≠ x → m x' ∉ ms₁ ++ m x :: ms₂) :
    insertAll a b m l ((merzljakovWord a b (ms₁ ++ m x :: ms₂)).map (Prod.map Sum.inr id)) =
      (merzljakovWord a b ms₁ ++ replicate (m x) (a, true)).map (Prod.map Sum.inr id) ++
        (Sum.inl x, true) :: (merzljakovWord a b ms₂).map (Prod.map Sum.inr id) := by
  obtain ⟨l₁, l₂, rfl⟩ := append_of_mem hx
  have hm₁ : m x ∉ ms₁ := fun h₁ ↦ (nodup_append.1 hms).2.2 _ h₁ _ mem_cons_self rfl
  have hm₂ : m x ∉ ms₂ := (nodup_cons.1 (nodup_append.1 hms).2.1).1
  -- the letters inserted before and after `x` leave the word unchanged
  have hne₁ (x' : X) (hx' : x' ∈ l₁) : x' ≠ x := by
    rintro rfl
    exact (nodup_append.1 hl).2.2 _ hx' _ mem_cons_self rfl
  have hne₂ (x' : X) (hx' : x' ∈ l₂) : x' ≠ x := by
    rintro rfl
    exact (nodup_cons.1 (nodup_append.1 hl).2.1).1 hx'
  rw [insertAll_append, insertAll_cons,
    insertAll_eq_self_of_merzljakovWord hab (fun x' hx' ↦ hdisj x' (by simp [hx']) (hne₂ x' hx'))
      (fun _ ↦ id) (fun _ ↦ id),
    insertAll_eq_self_of_merzljakovWord hab (fun x' hx' ↦ hdisj x' (by simp [hx']) (hne₁ x' hx'))
      (fun n h ↦ isInfix_of_isInfix_blockInsert h fun c hc ↦
        fst_ne_inl_of_mem_merzljakovBlock hc x)
      (fun n h ↦ isInfix_of_isInfix_blockInsert h fun c hc ↦
        fst_ne_inl_of_mem_merzljakovBlock (mem_invRev_iff.1 hc) x),
    map_prodMap_merzljakovWord, blockInsert_merzljakovWord (Sum.inr_injective.ne hab) hm₁ hm₂]
  simp [map_prodMap_merzljakovWord]

/-- The Merzljakov word `g = u v` of a letter `x`, after the insertion of the letters of `l`,
becomes `u x v` when `x ∈ l`, provided the exponent lists are nodup, contain the exponents of the
insertion, and the list of a letter of `l` is disjoint from the others. -/
private theorem exists_mk_insertAll_merzljakovWord (hab : a ≠ b) {l : List X} (hl : l.Nodup)
    {ms : X → List ℕ} (hms : ∀ x, (ms x).Nodup) (hm : ∀ x, m x ∈ ms x)
    (hdisj : ∀ x ∈ l, ∀ x', ∀ n ∈ ms x, n ∈ ms x' → x = x') (x : X) :
    ∃ u v : FreeGroup A, mk (merzljakovWord a b (ms x)) = u * v ∧ (x ∈ l →
      mk (insertAll a b m l ((merzljakovWord a b (ms x)).map (Prod.map Sum.inr id))) =
        map Sum.inr u * of (Sum.inl x) * map Sum.inr v) := by
  by_cases hx : x ∈ l
  · obtain ⟨ms₁, ms₂, hms₁₂⟩ := append_of_mem (hm x)
    refine ⟨mk (merzljakovWord a b ms₁ ++ replicate (m x) (a, true)), mk (merzljakovWord a b ms₂),
      by rw [hms₁₂, mul_mk, merzljakovWord_append_cons, append_assoc], fun _ ↦ ?_⟩
    rw [hms₁₂, insertAll_merzljakovWord hab hl hx (hms₁₂ ▸ hms x)
      fun x' hx' hne h ↦ hne (hdisj x' hx' x _ (hm x') (hms₁₂ ▸ h)), ← singleton_append,
      ← append_assoc, ← mul_mk, ← mul_mk]
    simp [Prod.map_def, map.mk, of]
  · exact ⟨_, 1, (mul_one _).symm, fun h ↦ absurd h hx⟩

omit [DecidableEq A] [DecidableEq X] in
/-- For every list `l` of letters there are nodup exponent lists of a given length, one for each
letter, such that the list of a letter of `l` is disjoint from the lists of the other letters. -/
private theorem exists_exponentLists (l : List X) (N : ℕ) : ∃ ms : X → List ℕ,
    (∀ x, (ms x).Nodup ∧ (ms x).length = N) ∧ ∀ x ∈ l, ∀ x', ∀ n ∈ ms x, n ∈ ms x' → x = x' := by
  classical
  refine ⟨fun x ↦ (range N).map (Nat.pair (l.idxOf x)), fun x ↦ ⟨nodup_range.map fun _ _ h ↦
    (Nat.pair_eq_pair.1 h).2, by simp⟩, fun x hx x' n h h' ↦ ?_⟩
  obtain ⟨r, -, rfl⟩ := mem_map.1 h
  obtain ⟨r', -, hr'⟩ := mem_map.1 h'
  exact (idxOf_inj hx).1 (Nat.pair_eq_pair.1 hr').1.symm

end Construction

private theorem mk_map_prodMap {A B : Type*} (f : A → B) (l : List (A × Bool)) :
    mk (l.map (Prod.map f id)) = map f (mk l) := by
  rw [map.mk]
  rfl

/-- Composing a solution `(x₀, y₀)` in which each `x₀ x` is a two-sided translate `u x * x * v x`
of `x` by constants with the automorphism `x ↦ (u x)⁻¹ * x * (v x)⁻¹` gives a formal solution,
whose values at the point `x ↦ u x * v x` are the values of `y₀` with the variables erased. -/
private theorem exists_formalSolution_of_mul {A X Y : Type*} (w : FreeGroup ((X ⊕ Y) ⊕ A))
    {y₀ : Y → FreeGroup (X ⊕ A)} {u v : X → FreeGroup A}
    (hw : lift (Sum.elim (Sum.elim (fun x ↦ map Sum.inr (u x) * of (Sum.inl x) * map Sum.inr (v x))
      y₀) (of ∘ Sum.inr)) w = 1) :
    ∃ y : Y → FreeGroup (X ⊕ A), lift (Sum.elim (Sum.elim (of ∘ Sum.inl) y) (of ∘ Sum.inr)) w = 1 ∧
      ∀ j, lift (Sum.elim (fun x ↦ u x * v x) of) (y j) = lift (Sum.elim 1 of) (y₀ j) := by
  let ψ : FreeGroup (X ⊕ A) →* FreeGroup (X ⊕ A) :=
    lift (Sum.elim (fun x ↦ (map Sum.inr (u x))⁻¹ * of (Sum.inl x) * (map Sum.inr (v x))⁻¹)
      (of ∘ Sum.inr))
  have hψ_inr (q : FreeGroup A) : ψ (map Sum.inr q) = map Sum.inr q := by
    have hcomp : ψ.comp (map Sum.inr) = map Sum.inr := ext_hom _ _ fun c ↦ by simp [ψ]
    exact DFunLike.congr_fun hcomp q
  refine ⟨fun j ↦ ψ (y₀ j), ?_, fun j ↦ ?_⟩
  · have hcomp : ψ.comp (lift (Sum.elim (Sum.elim
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
  · have hcomp : (lift (Sum.elim (fun x ↦ u x * v x) of)).comp ψ = lift (Sum.elim 1 of) :=
      ext_hom _ _ fun z ↦ by rcases z with x | c <;> simp [ψ, Function.comp_def]
    exact DFunLike.congr_fun hcomp (y₀ j)

/-- **Merzljakov's theorem** for one block of quantifiers `∀ x ∃ y`, with the values of the formal
solution: if `a ≠ b` are letters of `A` and `w(x, f x) = 1` holds in `FreeGroup A` for all `x`,
then `w(x, y) = 1` has a solution `y` in `FreeGroup (X ⊕ A)` whose values at some point `g` are
the witnesses `f g`. -/
theorem exists_formalSolution_lift_eq_of_skolem {A X Y : Type*} {a b : A} (hab : a ≠ b)
    (w : FreeGroup ((X ⊕ Y) ⊕ A)) (f : (X → FreeGroup A) → Y → FreeGroup A)
    (hw : ∀ x, lift (Sum.elim (Sum.elim x (f x)) of) w = 1) :
    ∃ (y : Y → FreeGroup (X ⊕ A)) (g : X → FreeGroup A),
      lift (Sum.elim (Sum.elim (of ∘ Sum.inl) y) (of ∘ Sum.inr)) w = 1 ∧
        ∀ j, lift (Sum.elim g of) (y j) = f g j := by
  classical
  obtain ⟨W, rfl⟩ : ∃ W, mk W = w := ⟨w.toWord, mk_toWord⟩
  -- the variables `x` occurring in `W`, and for each `x` a list of `|W|² + 1` exponents, the
  -- list of a variable of `W` being disjoint from the others
  let xs : List X := (W.filterMap fun c ↦ c.1.getLeft?.bind Sum.getLeft?).dedup
  obtain ⟨ms, hms, hdisj⟩ := exists_exponentLists xs (W.length * W.length + 1)
  -- substitute the Merzljakov words `g x` and the witnesses `f g`, and insert the variables
  let g (x : X) : FreeGroup A := mk (merzljakovWord a b (ms x))
  let U : (X ⊕ Y) ⊕ A → List (A × Bool) :=
    Sum.elim (Sum.elim (fun x ↦ merzljakovWord a b (ms x)) fun j ↦ (f g j).toWord)
      fun c ↦ [(c, true)]
  have hU : (fun z ↦ mk (U z)) = Sum.elim (Sum.elim g (f g)) of := by
    ext ((x | j) | c) <;> simp [U, g, of, mk_toWord]
  obtain ⟨m, hm, hU'⟩ := exists_lift_mk_insertAll_eq_one hab (U := U)
    (by rintro ((x | j) | c) <;> simp [U, isReduced_toWord]) (hU ▸ hw g) (fun x ↦ (hms x).1)
    (fun x ↦ by rw [(hms x).2]; lia) xs
  -- the inserted Merzljakov word of `x ∈ xs` is `u x * x * v x`, with `g x = u x * v x`
  choose u v hg hx₀ using exists_mk_insertAll_merzljakovWord hab (nodup_dedup _)
    (fun x ↦ (hms x).1) hm hdisj
  obtain ⟨y, hy, hyg⟩ := exists_formalSolution_of_mul (mk W)
    (y₀ := fun j ↦ mk (insertAll a b m xs ((U (Sum.inl (Sum.inr j))).map (Prod.map Sum.inr id))))
    (by
      rw [← hU', lift_mk, lift_mk]
      refine congrArg _ (map_congr_left fun ⟨z, e⟩ hz ↦ congrArg (fun q ↦ cond e q q⁻¹) ?_)
      rcases z with (x | j) | c
      · exact (hx₀ x (mem_dedup.2 (mem_filterMap.2 ⟨_, hz, rfl⟩))).symm
      · rfl
      · simp [U, insertAll_singleton, of])
  refine ⟨y, fun x ↦ u x * v x, hy, fun j ↦ ?_⟩
  rw [hyg j, map_mk_insertAll _ (by simp), mk_map_prodMap]
  simp only [lift_map, Sum.elim_comp_inr, lift_of_eq_id, MonoidHom.id_apply, U, Sum.elim_inl,
    Sum.elim_inr, mk_toWord]
  exact congrArg (f · j) (funext hg)

end FreeGroup
