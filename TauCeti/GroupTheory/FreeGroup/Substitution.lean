/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Computability
public import TauCeti.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Primitive-recursive substitution of free-group words

A substitution specified by a primitive-recursive table of words is primitive recursive on
the standard signed-letter list codes. The result is reduced after substitution, so it is
the canonical representative of the value of `FreeGroup.lift`. This supplies the word
substitutions used when evaluating finite systems of equations over free groups.

Substitution without free reduction is also recorded, for words in variables and constant
letters (`FreeGroup.substituteVars`): it is the substitution in Makanin's generalised equations,
where both sides must agree letter by letter. It is primitive recursive jointly in the word
and a finite table of the substituted words (`FreeGroup.primrec₂_substituteVars_getD`). It only
depends on the words assigned to the generators that occur, so changing the word of one generator
changes the substitution only at the letters of that generator, and substituting words of length at
most `k` multiplies the length of a word by at most `k`.
-/

public section

namespace FreeGroup

variable {α β : Type*}

/-- Replace a signed letter by the word assigned to its generator, reversing and inverting
the assigned word for a negative letter. -/
@[expose] def substituteLetter (f : α → List (β × Bool)) (a : α × Bool) : List (β × Bool) :=
  bif a.2 then f a.1 else invRev (f a.1)

/-- A positive letter is replaced by its assigned word. -/
@[simp] theorem substituteLetter_true (f : α → List (β × Bool)) (a : α) :
    substituteLetter f (a, true) = f a := by simp [substituteLetter]

/-- A negative letter is replaced by the inverse of its assigned word. -/
@[simp] theorem substituteLetter_false (f : α → List (β × Bool)) (a : α) :
    substituteLetter f (a, false) = invRev (f a) := by simp [substituteLetter]

/-- Substitution without free reduction only depends on the words assigned to the generators
that occur. -/
theorem flatMap_substituteLetter_congr {f g : α → List (β × Bool)} {w : List (α × Bool)}
    (h : ∀ a ∈ w, f a.1 = g a.1) :
    w.flatMap (substituteLetter f) = w.flatMap (substituteLetter g) :=
  List.flatMap_congr fun a ha => by simp [substituteLetter, h a ha]

/-- Renaming the generators of a word along `g` and then substituting `f` is substituting
`f ∘ g`. -/
@[simp]
theorem flatMap_substituteLetter_map {γ : Type*} (f : α → List (β × Bool)) (g : γ → α)
    (w : List (γ × Bool)) :
    (w.map (Prod.map g id)).flatMap (substituteLetter f) =
      w.flatMap (substituteLetter (f ∘ g)) := by
  rw [List.flatMap_map]
  exact List.flatMap_congr fun a _ => by simp [substituteLetter]

/-- Renaming the generators after substituting a letter is substituting the renamed words. -/
@[simp]
theorem map_prodMap_substituteLetter {γ : Type*} (g : β → γ) (f : α → List (β × Bool))
    (z : α × Bool) :
    (substituteLetter f z).map (Prod.map g id) =
      substituteLetter (fun x => (f x).map (Prod.map g id)) z := by
  obtain ⟨x, _ | _⟩ := z <;> simp [substituteLetter]

/-- Changing the word assigned to a generator that does not occur in a word does not change the
substitution without free reduction. -/
theorem flatMap_substituteLetter_update_of_notMem [DecidableEq α] {w : List (α × Bool)} {y : α}
    (hy : y ∉ w.map Prod.fst) (f : α → List (β × Bool)) (s : List (β × Bool)) :
    w.flatMap (substituteLetter (Function.update f y s)) = w.flatMap (substituteLetter f) :=
  flatMap_substituteLetter_congr fun a ha =>
    Function.update_of_ne (fun h : a.1 = y => hy (h ▸ List.mem_map_of_mem ha)) _ _

/-- Changing the word assigned to a generator that occurs in none of a list of words does not
change the substitutions without free reduction into these words. -/
theorem map_flatMap_substituteLetter_update_of_notMem [DecidableEq α]
    {V : List (List (α × Bool))} {y : α} (hy : y ∉ V.flatten.map Prod.fst)
    (f : α → List (β × Bool)) (s : List (β × Bool)) :
    V.map (·.flatMap (substituteLetter (Function.update f y s))) =
      V.map (·.flatMap (substituteLetter f)) :=
  List.map_congr_left fun v hv => flatMap_substituteLetter_update_of_notMem
    (fun h => hy (List.map_subset _ (fun _ ha => List.mem_flatten.2 ⟨v, hv, ha⟩) h)) f s

/-- Substitution without free reduction commutes with formal inverses. -/
theorem flatMap_substituteLetter_invRev (f : α → List (β × Bool)) (w : List (α × Bool)) :
    (invRev w).flatMap (substituteLetter f) = invRev (w.flatMap (substituteLetter f)) := by
  induction w with
  | nil => simp [invRev_empty]
  | cons a w ih =>
    rw [invRev_cons, List.flatMap_append, ih, List.flatMap_cons, invRev_append]
    congr 1
    have hs : invRev [a] = [(a.1, !a.2)] := by simp [invRev]
    obtain ⟨x, _ | _⟩ := a <;> simp [hs, invRev_invRev]

/-- If the generators occurring in a word are assigned words of length at most `k`, substitution
without free reduction multiplies the length of the word by at most `k`. -/
theorem length_flatMap_substituteLetter_le {f : α → List (β × Bool)} {k : ℕ} {w : List (α × Bool)}
    (hf : ∀ a ∈ w, (f a.1).length ≤ k) :
    (w.flatMap (substituteLetter f)).length ≤ k * w.length := by
  rw [List.length_flatMap]
  refine (List.sum_le_sum (g := fun _ => k) fun a ha => ?_).trans (by simp [mul_comm])
  obtain ⟨a, _ | _⟩ := a <;> simpa [invRev_length] using hf _ ha

/-- Substitution without free reduction agrees with the universal homomorphism from the free
group. -/
theorem mk_flatMap_substituteLetter (f : α → List (β × Bool)) (w : List (α × Bool)) :
    mk (w.flatMap (substituteLetter f)) = lift (fun a => mk (f a)) (mk w) := by
  induction w with
  | nil => simp only [List.flatMap_nil, ← one_eq_mk, _root_.map_one]
  | cons a w ih =>
    rw [List.flatMap_cons, ← mul_mk, ih]
    have h : mk (a :: w) = mk [a] * mk w := by simp only [mul_mk, List.singleton_append]
    rw [h, _root_.map_mul]
    cases a with
    | mk x b =>
      cases b <;> simp [substituteLetter, inv_mk, lift_mk]

/-- Substituting words for the generators of a word, without free reduction, gives the empty word
only for the empty word, if the generators occurring in it are assigned nonempty words. -/
theorem flatMap_substituteLetter_eq_nil_iff {f : α → List (β × Bool)} {w : List (α × Bool)}
    (hf : ∀ a ∈ w, f a.1 ≠ []) : w.flatMap (substituteLetter f) = [] ↔ w = [] := by
  refine ⟨fun h => List.eq_nil_iff_forall_not_mem.2 fun a ha => hf a ha ?_, by rintro rfl; rfl⟩
  have := List.flatMap_eq_nil_iff.1 h a ha
  obtain ⟨x, _ | _⟩ := a <;> simpa [invRev] using this

/-- If substituting words for the generators of a word, without free reduction, gives a reduced
word, every generator occurring in the word is assigned a reduced word. -/
theorem IsReduced.of_flatMap_substituteLetter_of_mem {f : α → List (β × Bool)}
    {w : List (α × Bool)} (h : IsReduced (w.flatMap (substituteLetter f))) {a : α} {b : Bool}
    (ha : (a, b) ∈ w) : IsReduced (f a) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  rw [List.flatMap_append, List.flatMap_cons] at h
  have := h.infix ⟨_, _, List.append_assoc ..⟩
  cases b <;> simpa using this

/-- If substituting words for the generators of a word, without free reduction, gives a reduced
word, and the generators occurring in the word are assigned nonempty words, then the word was
already reduced: a cancelling pair of letters is replaced by a nonempty word followed by its formal
inverse. -/
theorem IsReduced.of_flatMap_substituteLetter {f : α → List (β × Bool)} {w : List (α × Bool)}
    (hf : ∀ a ∈ w, f a.1 ≠ []) (h : IsReduced (w.flatMap (substituteLetter f))) :
    IsReduced w := by
  refine IsReduced.of_forall_not_step fun w' hstep => ?_
  obtain @⟨L₁, L₂, y, b⟩ := hstep
  have hy := hf (y, b) (by simp)
  have hinv : substituteLetter f (y, !b) = FreeGroup.invRev (substituteLetter f (y, b)) := by
    cases b <;> simp [FreeGroup.invRev_invRev]
  have hred : IsReduced (substituteLetter f (y, b) ++ substituteLetter f (y, !b)) :=
    h.infix ⟨L₁.flatMap (substituteLetter f), L₂.flatMap (substituteLetter f), by simp⟩
  have hnil := hred.eq_of_mk_eq .nil <| by
    rw [hinv, ← mul_mk, ← inv_mk, mul_inv_cancel, one_eq_mk]
  cases b <;> simp [hy] at hnil

/-- Substitute words for the generators of a word and freely reduce the result. -/
def substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) : List (β × Bool) :=
  reduce (w.flatMap (substituteLetter f))

/-- Substitution agrees with the universal homomorphism from the free group. -/
theorem mk_substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) :
    mk (substituteWord f w) = lift (fun a => mk (f a)) (mk w) := by
  rw [substituteWord, reduce.self, mk_flatMap_substituteLetter]

/-- Substitution computes the reduced word of the induced free-group homomorphism. -/
@[simp] theorem substituteWord_eq_toWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) :
    substituteWord f w = (lift (fun a => mk (f a)) (mk w)).toWord := by
  rw [← mk_substituteWord, toWord_mk]
  exact (reduce.idem).symm

section Vars

variable {X A : Type*}

/-- Substitute words over `A^{±1}` for the variables of a word in variables `X` and letters of
`A`, without free reduction: a variable `x` becomes `U x`, its inverse becomes the formal inverse
of `U x`, and a letter of `A^{±1}` is kept. -/
@[expose] def substituteVars (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    List (A × Bool) :=
  w.flatMap (substituteLetter (Sum.elim U fun a => [(a, true)]))

@[simp]
theorem substituteVars_nil (U : X → List (A × Bool)) : substituteVars U [] = [] :=
  List.flatMap_nil

/-- Substitution proceeds letter by letter. -/
theorem substituteVars_cons (U : X → List (A × Bool)) (y : (X ⊕ A) × Bool)
    (w : List ((X ⊕ A) × Bool)) :
    substituteVars U (y :: w) = substituteVars U [y] ++ substituteVars U w := by
  simp [substituteVars]

@[simp]
theorem substituteVars_append (U : X → List (A × Bool)) (w w' : List ((X ⊕ A) × Bool)) :
    substituteVars U (w ++ w') = substituteVars U w ++ substituteVars U w' :=
  List.flatMap_append

/-- A positive variable is replaced by its assigned word. -/
@[simp]
theorem substituteVars_singleton_inl (U : X → List (A × Bool)) (x : X) :
    substituteVars U [(Sum.inl x, true)] = U x := by
  simp [substituteVars]

/-- A negative variable is replaced by the formal inverse of its assigned word. -/
@[simp]
theorem substituteVars_singleton_inl_false (U : X → List (A × Bool)) (x : X) :
    substituteVars U [(Sum.inl x, false)] = invRev (U x) := by
  simp [substituteVars]

/-- A letter of `A^{±1}` is kept. -/
@[simp]
theorem substituteVars_singleton_inr (U : X → List (A × Bool)) (a : A) (b : Bool) :
    substituteVars U [(Sum.inr a, b)] = [(a, b)] := by
  cases b <;> simp [substituteVars, invRev]

/-- A word of positive variables is replaced by the concatenation of their assigned words. -/
theorem substituteVars_map_inl (U : X → List (A × Bool)) (l : List X) :
    substituteVars U (l.map fun x => (Sum.inl x, true)) = l.flatMap U := by
  simp [substituteVars, List.flatMap_map]

/-- Substitution without free reduction only depends on the words assigned to the variables that
occur. -/
theorem substituteVars_congr {U U' : X → List (A × Bool)} {w : List ((X ⊕ A) × Bool)}
    (h : ∀ x b, (Sum.inl x, b) ∈ w → U x = U' x) : substituteVars U w = substituteVars U' w := by
  refine flatMap_substituteLetter_congr ?_
  rintro ⟨x | a, b⟩ hy
  · exact h x b hy
  · rfl

/-- Renaming the variables of a word along `g` and then substituting `U` is substituting
`U ∘ g`. -/
@[simp]
theorem substituteVars_map {Y : Type*} (U : X → List (A × Bool)) (g : Y → X)
    (w : List ((Y ⊕ A) × Bool)) :
    substituteVars U (w.map (Prod.map (Sum.map g id) id)) = substituteVars (U ∘ g) w := by
  simp [substituteVars, Sum.elim_comp_map]

/-- Substitution without free reduction commutes with formal inverses. -/
theorem substituteVars_invRev (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    substituteVars U (invRev w) = invRev (substituteVars U w) :=
  flatMap_substituteLetter_invRev _ w

/-- Substituting into a formal inverse gives a reduced word exactly when substituting into the
original word does. -/
@[simp]
theorem isReduced_substituteVars_invRev (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    IsReduced (substituteVars U (invRev w)) ↔ IsReduced (substituteVars U w) := by
  rw [substituteVars_invRev, isReduced_invRev]

/-- If substituting into a word gives a reduced word, so does substituting into the word raised
to a sign. -/
theorem isReduced_substituteVars_cond (U : X → List (A × Bool)) (s : Bool)
    (w : List ((X ⊕ A) × Bool)) (h : IsReduced (substituteVars U w)) :
    IsReduced (substituteVars U (cond s w (invRev w))) := by
  cases s <;> simpa

/-- Substituting into a single letter gives a reduced word if the letter is in `A^{±1}` or its
variable is assigned a reduced word. -/
theorem isReduced_substituteVars_singleton {U : X → List (A × Bool)} {y : (X ⊕ A) × Bool}
    (hU : ∀ x, y.1 = Sum.inl x → IsReduced (U x)) : IsReduced (substituteVars U [y]) := by
  obtain ⟨x | a, b⟩ := y
  · cases b <;> simpa using hU x rfl
  · simp

/-- If substituting into a word gives a reduced word, every variable occurring in the word is
assigned a reduced word. -/
theorem IsReduced.of_substituteVars_of_mem {U : X → List (A × Bool)} {w : List ((X ⊕ A) × Bool)}
    (h : IsReduced (substituteVars U w)) {x : X} {b : Bool} (hx : (Sum.inl x, b) ∈ w) :
    IsReduced (U x) :=
  h.of_flatMap_substituteLetter_of_mem hx

/-- Substitution followed by free reduction is evaluation in the free group. -/
theorem mk_substituteVars (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    mk (substituteVars U w) = lift (Sum.elim (fun x => mk (U x)) of) (mk w) := by
  rw [substituteVars, mk_flatMap_substituteLetter]
  congr 2
  funext y
  -- `of a` is the one-letter word `mk [(a, true)]` by definition.
  cases y <;> rfl

/-- If substituting words for the variables, without free reduction, gives a reduced word, and
the variables occurring in the word are assigned nonempty words, then the word in variables and
letters was already reduced: a cancelling pair of letters is replaced by a nonempty word followed
by its formal inverse. -/
theorem IsReduced.of_substituteVars {U : X → List (A × Bool)} {w : List ((X ⊕ A) × Bool)}
    (hU : ∀ x b, (Sum.inl x, b) ∈ w → U x ≠ []) (h : IsReduced (substituteVars U w)) :
    IsReduced w :=
  h.of_flatMap_substituteLetter fun
    | (.inl x, b), hx => hU x b hx
    | (.inr _, _), _ => List.cons_ne_nil _ _

end Vars

variable [Primcodable α] [Primcodable β]

/-- The signed-letter substitution determined by a primitive-recursive word table is
primitive recursive. -/
theorem primrec_substituteLetter (f : α → List (β × Bool)) (hf : Primrec f) :
    Primrec (substituteLetter f) := by
  unfold substituteLetter
  exact Primrec.cond (Primrec.snd)
    (hf.comp Primrec.fst) (primrec_invRev.comp (hf.comp Primrec.fst))

/-- Substitution followed by free reduction is primitive recursive on word codes. -/
theorem primrec_substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (hf : Primrec f) : Primrec (substituteWord f) := by
  unfold substituteWord
  exact primrec_reduce.comp
    (Primrec.list_flatMap Primrec.id
      ((primrec_substituteLetter f hf).comp Primrec.snd).to₂)

/-- Evaluating a word under a primitive-recursive assignment of words is
primitive recursive, with the reduced word of the value as output. -/
theorem primrec_toWord_lift_mk [DecidableEq β] (f : α → List (β × Bool))
    (hf : Primrec f) :
    Primrec fun w : List (α × Bool) => (lift (fun a => mk (f a)) (mk w)).toWord := by
  simpa only [← substituteWord_eq_toWord] using primrec_substituteWord f hf

/-- A primitive-recursive map of alphabets induces a primitive-recursive map on reduced
representatives of free-group elements. -/
theorem primrec_toWord_map_mk [DecidableEq β] (g : α → β) (hg : Primrec g) :
    Primrec fun w : List (α × Bool) => (map g (mk w)).toWord := by
  have htable : Primrec fun a : α => ([(g a, true)] : List (β × Bool)) :=
    Primrec.list_cons.comp (Primrec.pair hg (Primrec.const true)) (Primrec.const [])
  simpa only [map_eq_lift, Function.comp_def, of] using
    (primrec_toWord_lift_mk (fun a : α => [(g a, true)]) htable)

/-- Substitution of words for the variables of a word, without free reduction, is primitive
recursive jointly in the word and a finite table of the substituted words; variables beyond the
table receive the empty word. -/
theorem primrec₂_substituteVars_getD {A : Type*} [Primcodable A] :
    Primrec₂ fun (u : List (List (A × Bool))) (w : List ((ℕ ⊕ A) × Bool)) =>
      substituteVars (fun x => u.getD x []) w := by
  have table : Primrec₂ fun (u : List (List (A × Bool))) (y : ℕ ⊕ A) =>
      Sum.elim (fun x => u.getD x []) (fun a => [(a, true)]) y :=
    (Primrec.sumCasesOn Primrec.snd
      ((Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (Primrec.list_cons.comp (Primrec.pair Primrec.snd (Primrec.const true))
        (Primrec.const [])).to₂).to₂.of_eq fun u y => by cases y <;> rfl
  have letter : Primrec₂ fun (u : List (List (A × Bool))) (y : (ℕ ⊕ A) × Bool) =>
      substituteLetter (Sum.elim (fun x => u.getD x []) fun a => [(a, true)]) y :=
    (Primrec.cond (Primrec.snd.comp Primrec.snd)
      (table.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (primrec_invRev.comp (table.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))).to₂
  exact (Primrec.list_flatMap Primrec.snd
    (letter.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

end FreeGroup
