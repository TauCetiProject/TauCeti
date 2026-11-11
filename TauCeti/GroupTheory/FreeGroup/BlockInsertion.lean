/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.Unsplit
public import TauCeti.GroupTheory.FreeGroup.MerzljakovWord

/-!
# Inserting a letter into the blocks of a word

For letters `a`, `b`, `x` and an exponent `m`, `FreeGroup.blockInsert a b x m w` is the word
obtained from `w` by replacing every occurrence of the block `b a^m b` by `b a^m x b`, and every
occurrence of its formal inverse `b⁻¹ a^{-m} b⁻¹` by `b⁻¹ x⁻¹ a^{-m} b⁻¹`. This is the
replacement used in the proof of Merzljakov's theorem to turn a solution of an equation in a
free group, whose values at the universally quantified variables are Merzljakov words, into a
solution over the free group with new generators.

Here a word is a list of signed letters `α × Bool` and a subword is an infix, `List.IsInfix`.

## Main definitions

* `FreeGroup.blockInsert a b x m w`: insert `x` into the blocks `b a^m b` of `w`, and `x⁻¹` into
  their formal inverses.

## Main results

* `FreeGroup.blockInsert_invRev`: the replacement commutes with formal inverses.
* `FreeGroup.blockInsert_flatten`: the replacement commutes with a concatenation that does not
  split a block or an inverse block.
* `FreeGroup.blockInsert_merzljakovWord`: the value on a Merzljakov word in which the exponent
  `m` occurs once.
* `FreeGroup.IsReduced.blockInsert`: the replacement keeps a word reduced.
* `FreeGroup.map_mk_blockInsert`: a homomorphism killing `x` does not see the replacement.
* `FreeGroup.isInfix_of_isInfix_blockInsert`: the replacement creates no occurrence of a word
  in which the letter `x` does not appear.

## Implementation notes

`FreeGroup.blockInsert` is defined position by position: at each position of the word it looks
whether a block ends there or an inverse block has just begun. The proofs go through a private
recursive description of the same word, which also records the letters before and after the part
of the word being read.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), 1–203, Section 4.4, proof of Merzljakov's Theorem.
* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
-/

public section

namespace FreeGroup

open List

variable {α : Type*} {a b x : α} {m k k' : ℕ} {l u u₀ v w t t₀ : List (α × Bool)}

/-- The word `l` occurs in `u ++ v` in such a way that the gap between `u` and `v` comes after
the first `k` letters of the occurrence. -/
private def OccursAt (l : List (α × Bool)) (k : ℕ) (u v : List (α × Bool)) : Prop :=
  ∃ s t, s ++ l ++ t = u ++ v ∧ s.length + k = u.length

private theorem OccursAt.invRev (h : OccursAt l k u v) (hk : k + k' = l.length) :
    OccursAt (invRev l) k' (invRev v) (invRev u) := by
  obtain ⟨s, t, hst, hs⟩ := h
  refine ⟨FreeGroup.invRev t, FreeGroup.invRev s, by simp [← invRev_append, ← hst], ?_⟩
  have := congrArg length hst
  simp only [length_append] at this
  simp only [invRev_length]
  omega

private theorem occursAt_invRev_iff (hk : k + k' = l.length) :
    OccursAt (invRev l) k' (invRev v) (invRev u) ↔ OccursAt l k u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.invRev hk⟩
  simpa using h.invRev (k' := k) (by simp; omega)

private theorem occursAt_append_left_iff (h : l.IsUnsplit [u₀, u ++ v]) (hk : k < l.length) :
    OccursAt l k (u₀ ++ u) v ↔ OccursAt l k u v := by
  refine ⟨?_, fun ⟨s, t, hst, hs⟩ ↦ ⟨u₀ ++ s, t, by simp [← hst], by simp; omega⟩⟩
  rintro ⟨s, t, hst, hs⟩
  rw [append_assoc u₀] at hst
  rw [length_append] at hs
  have hle : u₀.length ≤ s.length := by have := isUnsplit_pair_iff.1 h s t hst; omega
  obtain ⟨s', rfl⟩ : u₀ <+: s := prefix_of_prefix_length_le
    (prefix_append u₀ (u ++ v)) ⟨l ++ t, by simpa using hst⟩ hle
  exact ⟨s', t, by simpa using hst, by simp at hs; omega⟩

private theorem occursAt_append_right_iff (h : l.IsUnsplit [u ++ v, t₀]) (hk : 0 < k) :
    OccursAt l k u (v ++ t₀) ↔ OccursAt l k u v := by
  refine ⟨?_, fun ⟨s, t, hst, hs⟩ ↦ ⟨s, t ++ t₀, by rw [← append_assoc, hst, append_assoc], hs⟩⟩
  rintro ⟨s, t, hst, hs⟩
  rw [← append_assoc] at hst
  have hle : (s ++ l).length ≤ (u ++ v).length := by
    have := isUnsplit_pair_iff.1 h s t hst
    simp only [length_append] at this ⊢
    omega
  obtain ⟨t', ht'⟩ : s ++ l <+: u ++ v :=
    prefix_of_prefix_length_le ⟨t, hst⟩ (prefix_append (u ++ v) t₀) hle
  exact ⟨s, t', ht', hs⟩

section BlockInsert

private theorem suffix_and_head?_iff :
    ((b, true) :: replicate m (a, true) <:+ u ∧ v.head? = some (b, true)) ↔
      OccursAt (merzljakovBlock a b m) (m + 1) u v := by
  constructor
  · rintro ⟨⟨s, rfl⟩, hv⟩
    obtain ⟨t, rfl⟩ := head?_eq_some_iff.1 hv
    exact ⟨s, t, by simp [merzljakovBlock_eq], by simp⟩
  · rintro ⟨s, t, hst, hs⟩
    obtain ⟨rfl, rfl⟩ := append_inj (s₁ := s ++ (b, true) :: replicate m (a, true))
      (t₁ := (b, true) :: t) (by simpa [merzljakovBlock_eq] using hst) (by simp; omega)
    exact ⟨suffix_append _ _, rfl⟩

private theorem getLast?_and_prefix_iff :
    (u.getLast? = some (b, false) ∧ replicate m (a, false) ++ [(b, false)] <+: v) ↔
      OccursAt (invRev (merzljakovBlock a b m)) 1 u v := by
  constructor
  · rintro ⟨hu, t, rfl⟩
    obtain ⟨s, rfl⟩ := getLast?_eq_some_iff.1 hu
    exact ⟨s, t, by simp [invRev_merzljakovBlock], by simp⟩
  · rintro ⟨s, t, hst, hs⟩
    obtain ⟨rfl, rfl⟩ := append_inj (s₁ := s ++ [(b, false)])
      (t₁ := replicate m (a, false) ++ [(b, false)] ++ t)
      (by simpa [invRev_merzljakovBlock] using hst) (by simp; omega)
    exact ⟨by simp, prefix_append _ _⟩

variable [DecidableEq α]

/-- The letters inserted at the gap between `u` and `v` of the word `u ++ v`: the letter `x` if
the gap is before the last letter of an occurrence of the block `b a^m b`, and `x⁻¹` if it is
after the first letter of an occurrence of the formal inverse of the block. -/
private def gapInsert (a b x : α) (m : ℕ) (u v : List (α × Bool)) : List (α × Bool) :=
  (if (b, true) :: replicate m (a, true) <:+ u ∧ v.head? = some (b, true)
    then [(x, true)] else []) ++
  (if u.getLast? = some (b, false) ∧ replicate m (a, false) ++ [(b, false)] <+: v
    then [(x, false)] else [])

/-- The word obtained from `w` by inserting the letter `x` before the last letter of every
occurrence of the block `b a^m b`, and `x⁻¹` after the first letter of every occurrence of its
formal inverse `b⁻¹ a^{-m} b⁻¹`. -/
def blockInsert (a b x : α) (m : ℕ) (w : List (α × Bool)) : List (α × Bool) :=
  (range w.length).flatMap fun p ↦
    (if (b, true) :: replicate m (a, true) <:+ w.take p ∧ w[p]? = some (b, true)
      then [(x, true)] else []) ++
    (if (w.take p).getLast? = some (b, false) ∧
        replicate m (a, false) ++ [(b, false)] <+: w.drop p
      then [(x, false)] else []) ++ w[p]?.toList

/-- The word `v` with the insertions of `blockInsert` made in the word `u ++ v ++ t`, at the gaps
before the letters of `v`. -/
private def insertAux (a b x : α) (m : ℕ) :
    List (α × Bool) → List (α × Bool) → List (α × Bool) → List (α × Bool)
  | _, [], _ => []
  | u, c :: v, t => gapInsert a b x m u (c :: v ++ t) ++ c :: insertAux a b x m (u ++ [c]) v t

@[simp]
private theorem insertAux_nil (a b x : α) (m : ℕ) (u t : List (α × Bool)) :
    insertAux a b x m u [] t = [] :=
  rfl

private theorem insertAux_cons (a b x : α) (m : ℕ) (u : List (α × Bool)) (c : α × Bool)
    (v t : List (α × Bool)) :
    insertAux a b x m u (c :: v) t =
      gapInsert a b x m u (c :: v ++ t) ++ c :: insertAux a b x m (u ++ [c]) v t :=
  rfl

/-! ### The insertion at one gap -/

private theorem gapInsert_congr {u' v' : List (α × Bool)}
    (h : OccursAt (merzljakovBlock a b m) (m + 1) u v ↔
      OccursAt (merzljakovBlock a b m) (m + 1) u' v')
    (h' : OccursAt (invRev (merzljakovBlock a b m)) 1 u v ↔
      OccursAt (invRev (merzljakovBlock a b m)) 1 u' v') :
    gapInsert a b x m u v = gapInsert a b x m u' v' :=
  congrArg₂ (· ++ ·)
    (if_congr (suffix_and_head?_iff.trans (h.trans suffix_and_head?_iff.symm)) rfl rfl)
    (if_congr (getLast?_and_prefix_iff.trans (h'.trans getLast?_and_prefix_iff.symm)) rfl rfl)

private theorem gapInsert_eq_nil (h : ¬ OccursAt (merzljakovBlock a b m) (m + 1) u v)
    (h' : ¬ OccursAt (invRev (merzljakovBlock a b m)) 1 u v) : gapInsert a b x m u v = [] := by
  rw [gapInsert, ite_eq_right (mt suffix_and_head?_iff.1 h),
    ite_eq_right (mt getLast?_and_prefix_iff.1 h'), append_nil]

private theorem gapInsert_append_left (h : (merzljakovBlock a b m).IsUnsplit [u₀, u ++ v])
    (h' : (invRev (merzljakovBlock a b m)).IsUnsplit [u₀, u ++ v]) :
    gapInsert a b x m (u₀ ++ u) v = gapInsert a b x m u v :=
  gapInsert_congr (occursAt_append_left_iff h (by simp))
    (occursAt_append_left_iff h' (by simp))

private theorem gapInsert_append_right (h : (merzljakovBlock a b m).IsUnsplit [u ++ v, t₀])
    (h' : (invRev (merzljakovBlock a b m)).IsUnsplit [u ++ v, t₀]) :
    gapInsert a b x m u (v ++ t₀) = gapInsert a b x m u v :=
  gapInsert_congr (occursAt_append_right_iff h (by simp))
    (occursAt_append_right_iff h' (by simp))

private theorem gapInsert_invRev (a b x : α) (m : ℕ) (u v : List (α × Bool)) :
    gapInsert a b x m (invRev v) (invRev u) = invRev (gapInsert a b x m u v) := by
  have h₁ : OccursAt (merzljakovBlock a b m) (m + 1) (invRev v) (invRev u) ↔
      OccursAt (invRev (merzljakovBlock a b m)) 1 u v := by
    simpa using occursAt_invRev_iff (l := invRev (merzljakovBlock a b m)) (k := 1) (k' := m + 1)
      (u := u) (v := v) (by simp; omega)
  have h₂ : OccursAt (invRev (merzljakovBlock a b m)) 1 (invRev v) (invRev u) ↔
      OccursAt (merzljakovBlock a b m) (m + 1) u v :=
    occursAt_invRev_iff (by simp)
  unfold gapInsert
  rw [if_congr (suffix_and_head?_iff.trans (h₁.trans getLast?_and_prefix_iff.symm)) rfl rfl,
    if_congr (getLast?_and_prefix_iff.trans (h₂.trans suffix_and_head?_iff.symm)) rfl rfl]
  split_ifs <;> simp [invRev]

@[simp]
private theorem gapInsert_nil_left (a b x : α) (m : ℕ) (v : List (α × Bool)) :
    gapInsert a b x m [] v = [] := by
  simp [gapInsert]

@[simp]
private theorem gapInsert_nil_right (a b x : α) (m : ℕ) (u : List (α × Bool)) :
    gapInsert a b x m u [] = [] := by
  simp [gapInsert]

omit [DecidableEq α] in
private theorem exists_eq_append_of_suffix (h : (b, true) :: replicate m (a, true) <:+ u) :
    ∃ u' d, u = u' ++ [(d, true)] := by
  obtain ⟨s, rfl⟩ := h
  cases m with
  | zero => exact ⟨s, b, rfl⟩
  | succ n => exact ⟨s ++ (b, true) :: replicate n (a, true), a, by simp [replicate_succ']⟩

omit [DecidableEq α] in
private theorem exists_eq_cons_of_prefix (h : replicate m (a, false) ++ [(b, false)] <+: v) :
    ∃ d v', v = (d, false) :: v' := by
  obtain ⟨t, rfl⟩ := h
  cases m with
  | zero => exact ⟨b, t, rfl⟩
  | succ n => exact ⟨a, replicate n (a, false) ++ [(b, false)] ++ t, by simp [replicate_succ]⟩

/-- At most one letter is inserted at a gap, and it has the sign of both neighbours. -/
private theorem gapInsert_eq_nil_or (a b x : α) (m : ℕ) (u v : List (α × Bool)) :
    gapInsert a b x m u v = [] ∨ ∃ e, gapInsert a b x m u v = [(x, e)] ∧
      (∃ u' d, u = u' ++ [(d, e)]) ∧ ∃ d v', v = (d, e) :: v' := by
  by_cases hp : (b, true) :: replicate m (a, true) <:+ u ∧ v.head? = some (b, true)
  · obtain ⟨u', d, rfl⟩ := exists_eq_append_of_suffix hp.1
    obtain ⟨t, hv⟩ := head?_eq_some_iff.1 hp.2
    have hn : ¬ ((u' ++ [(d, true)]).getLast? = some (b, false) ∧
        replicate m (a, false) ++ [(b, false)] <+: v) := fun hn ↦ by simpa using hn.1
    exact .inr ⟨true, by simp only [gapInsert, ite_eq_left hp, ite_eq_right hn, append_nil],
      ⟨u', d, rfl⟩, b, t, hv⟩
  · by_cases hn : u.getLast? = some (b, false) ∧ replicate m (a, false) ++ [(b, false)] <+: v
    · obtain ⟨s, hs⟩ := getLast?_eq_some_iff.1 hn.1
      obtain ⟨d, v', hv⟩ := exists_eq_cons_of_prefix hn.2
      exact .inr ⟨false, by simp only [gapInsert, ite_eq_right hp, ite_eq_left hn, nil_append],
        ⟨s, b, hs⟩, d, v', hv⟩
    · exact .inl (by simp only [gapInsert, ite_eq_right hp, ite_eq_right hn, append_nil])

private theorem fst_eq_of_mem_gapInsert {c : α × Bool} (hc : c ∈ gapInsert a b x m u v) :
    c.1 = x := by
  obtain h | ⟨e, h, -⟩ := gapInsert_eq_nil_or a b x m u v
  · simp [h] at hc
  · rw [h, mem_singleton] at hc
    rw [hc]

/-! ### The insertions inside a word with a context -/

private theorem blockInsert_eq_insertAux (a b x : α) (m : ℕ) (w : List (α × Bool)) :
    blockInsert a b x m w = insertAux a b x m [] w [] := by
  have key (u v : List (α × Bool)) : ((range v.length).flatMap fun p ↦
      gapInsert a b x m (u ++ v.take p) (v.drop p) ++ (v.drop p).head?.toList) =
      insertAux a b x m u v [] := by
    induction v generalizing u with
    | nil => simp
    | cons c v ih => simp [range_succ_eq_map, flatMap_map, insertAux_cons, ← ih (u ++ [c])]
  simp [← key, blockInsert, gapInsert]

private theorem insertAux_append (u v₁ v₂ t : List (α × Bool)) :
    insertAux a b x m u (v₁ ++ v₂) t =
      insertAux a b x m u v₁ (v₂ ++ t) ++ insertAux a b x m (u ++ v₁) v₂ t := by
  induction v₁ generalizing u with
  | nil => simp
  | cons c v₁ ih => simp [insertAux_cons, ih]

private theorem insertAux_congr {u' t' : List (α × Bool)}
    (h : ∀ v₁ c v₂, v = v₁ ++ c :: v₂ → gapInsert a b x m (u ++ v₁) (c :: v₂ ++ t) =
      gapInsert a b x m (u' ++ v₁) (c :: v₂ ++ t')) :
    insertAux a b x m u v t = insertAux a b x m u' v t' := by
  induction v generalizing u u' with
  | nil => simp
  | cons c v ih =>
    rw [insertAux_cons, insertAux_cons, ih (u := u ++ [c]) (u' := u' ++ [c]) fun v₁ d v₂ hv ↦ by
      simpa using h (c :: v₁) d v₂ (by simp [hv])]
    simpa using h [] c v rfl

private theorem insertAux_eq_self
    (h : ∀ v₁ c v₂, v = v₁ ++ c :: v₂ → gapInsert a b x m (u ++ v₁) (c :: v₂ ++ t) = []) :
    insertAux a b x m u v t = v := by
  induction v generalizing u with
  | nil => simp
  | cons c v ih =>
    rw [insertAux_cons, ih fun v₁ d v₂ hv ↦ by simpa using h (c :: v₁) d v₂ (by simp [hv])]
    simpa using h [] c v rfl

private theorem insertAux_left (h : (merzljakovBlock a b m).IsUnsplit [u, v ++ t])
    (h' : (invRev (merzljakovBlock a b m)).IsUnsplit [u, v ++ t]) :
    insertAux a b x m u v t = insertAux a b x m [] v t := by
  refine insertAux_congr fun v₁ c v₂ hv ↦ ?_
  subst hv
  simpa using gapInsert_append_left (by simpa using h) (by simpa using h')

private theorem insertAux_right (h : (merzljakovBlock a b m).IsUnsplit [u ++ v, t])
    (h' : (invRev (merzljakovBlock a b m)).IsUnsplit [u ++ v, t]) :
    insertAux a b x m u v t = insertAux a b x m u v [] := by
  refine insertAux_congr fun v₁ c v₂ hv ↦ ?_
  subst hv
  simpa using gapInsert_append_right (u := u ++ v₁) (v := c :: v₂)
    (by simpa using h) (by simpa using h')

/-- The replacement commutes with a concatenation of two words whose gap is strictly inside no
occurrence of the block or of its formal inverse. -/
private theorem blockInsert_append (h : (merzljakovBlock a b m).IsUnsplit [u, v])
    (h' : (invRev (merzljakovBlock a b m)).IsUnsplit [u, v]) :
    blockInsert a b x m (u ++ v) = blockInsert a b x m u ++ blockInsert a b x m v := by
  simp only [blockInsert_eq_insertAux, insertAux_append, append_nil, nil_append]
  rw [insertAux_right (u := []) (v := u) (t := v) (by simpa using h) (by simpa using h'),
    insertAux_left (u := u) (v := v) (t := []) (by simpa using h) (by simpa using h')]

private theorem insertAux_invRev (a b x : α) (m : ℕ) (u v t : List (α × Bool)) :
    insertAux a b x m (invRev t) (invRev v) (invRev u) ++
        gapInsert a b x m (invRev t ++ invRev v) (invRev u) =
      invRev (insertAux a b x m u v t ++ gapInsert a b x m (u ++ v) t) := by
  induction v generalizing u with
  | nil => simp [gapInsert_invRev]
  | cons c v ih =>
    have hc (L : List (α × Bool)) : invRev (c :: L) = invRev L ++ [(c.1, !c.2)] := by
      simp [invRev]
    have h := ih (u ++ [c])
    simp only [invRev_append, hc, invRev_empty, nil_append, append_assoc, cons_append,
      ← gapInsert_invRev] at h
    simp only [hc, insertAux_append, insertAux_cons, insertAux_nil, invRev_append, append_assoc,
      cons_append, nil_append, ← gapInsert_invRev]
    rw [← append_assoc, h, append_assoc]

/-! ### Properties of the replacement -/

/-- Nothing is inserted into the empty word. -/
@[simp]
theorem blockInsert_nil (a b x : α) (m : ℕ) : blockInsert a b x m [] = [] := by
  simp [blockInsert]

/-- The replacement commutes with formal inverses. -/
theorem blockInsert_invRev (a b x : α) (m : ℕ) (w : List (α × Bool)) :
    blockInsert a b x m (invRev w) = invRev (blockInsert a b x m w) := by
  simpa [blockInsert_eq_insertAux] using insertAux_invRev a b x m [] w []

/-- The replacement commutes with a concatenation that splits no occurrence of the block and no
occurrence of its formal inverse. -/
theorem blockInsert_flatten {L : List (List (α × Bool))}
    (h : (merzljakovBlock a b m).IsUnsplit L)
    (h' : (invRev (merzljakovBlock a b m)).IsUnsplit L) :
    blockInsert a b x m L.flatten = (L.map (blockInsert a b x m)).flatten := by
  induction L with
  | nil => simp
  | cons w L ih =>
    rw [flatten_cons, blockInsert_append (by simpa using h.pair_flatten (L₁ := [w]))
      (by simpa using h'.pair_flatten (L₁ := [w])), ih (h.of_append_right (L₁ := [w]))
      (h'.of_append_right (L₁ := [w])), map_cons, flatten_cons]

/-- A word containing neither the block nor its formal inverse is left unchanged. -/
theorem blockInsert_eq_self (h : ¬ merzljakovBlock a b m <:+: w)
    (h' : ¬ invRev (merzljakovBlock a b m) <:+: w) : blockInsert a b x m w = w := by
  rw [blockInsert_eq_insertAux]
  refine insertAux_eq_self fun v₁ c v₂ hv ↦ gapInsert_eq_nil ?_ ?_
  · rintro ⟨s, t, hst, -⟩
    exact h ⟨s, t, by simpa [hv] using hst⟩
  · rintro ⟨s, t, hst, -⟩
    exact h' ⟨s, t, by simpa [hv] using hst⟩

omit [DecidableEq α] in
private theorem exists_merzljakovWord_eq (hab : a ≠ b) {ms₁ ms₂ : List ℕ} (h₁ : m ∉ ms₁)
    (h₂ : m ∉ ms₂) :
    ∃ s t, merzljakovWord a b ms₁ = s ++ [(b, true)] ∧ merzljakovWord a b ms₂ = (b, true) :: t ∧
      ∀ s' t', s' ++ merzljakovBlock a b m ++ t' = merzljakovWord a b (ms₁ ++ m :: ms₂) →
        s'.length = s.length := by
  have key : ∀ s t, s ++ merzljakovBlock a b m ++ t = merzljakovWord a b (ms₁ ++ m :: ms₂) →
      s ++ [(b, true)] = merzljakovWord a b ms₁ ∧ (b, true) :: t = merzljakovWord a b ms₂ := by
    intro s t hst
    obtain ⟨ms₁', ms₂', e, hs, ht⟩ :=
      (append_merzljakovBlock_append_eq_merzljakovWord_iff hab).1 hst
    obtain ⟨rfl, -, rfl⟩ := (append_cons_inj_of_notMem h₁ h₂).1 e
    exact ⟨hs, ht⟩
  obtain ⟨s, t, hst⟩ := merzljakovBlock_isInfix_merzljakovWord a b (m := m)
    (ms := ms₁ ++ m :: ms₂) (by simp)
  obtain ⟨hs, ht⟩ := key s t hst
  refine ⟨s, t, hs.symm, ht.symm, fun s' t' h' ↦ ?_⟩
  simpa using congrArg length ((key s' t' h').1.trans hs.symm)

/-- In a Merzljakov word over distinct letters `a ≠ b` in which the exponent `m` occurs once, the
replacement inserts `x` once, after `a^m`. -/
theorem blockInsert_merzljakovWord (hab : a ≠ b) {ms₁ ms₂ : List ℕ} (h₁ : m ∉ ms₁)
    (h₂ : m ∉ ms₂) :
    blockInsert a b x m (merzljakovWord a b (ms₁ ++ m :: ms₂)) =
      merzljakovWord a b ms₁ ++ (replicate m (a, true) ++ (x, true) :: merzljakovWord a b ms₂) := by
  obtain ⟨s, t, hs, ht, huniq⟩ := exists_merzljakovWord_eq hab h₁ h₂
  generalize hp : s ++ (b, true) :: replicate m (a, true) = p
  have hw : merzljakovWord a b (ms₁ ++ m :: ms₂) = p ++ (b, true) :: t := by
    simp [merzljakovWord_append_cons, hs, ht, ← hp]
  have hinv (u v : List (α × Bool)) (huv : u ++ v = p ++ (b, true) :: t) :
      ¬ OccursAt (invRev (merzljakovBlock a b m)) 1 u v := fun ⟨s', t', h', _⟩ ↦
    not_invRev_merzljakovBlock_isInfix_merzljakovWord a b m _ ⟨s', t', h'.trans (huv.trans hw.symm)⟩
  have hocc (u v : List (α × Bool)) (huv : u ++ v = p ++ (b, true) :: t)
      (h : OccursAt (merzljakovBlock a b m) (m + 1) u v) : u.length = p.length := by
    obtain ⟨s', t', h', hl⟩ := h
    rw [← hl, huniq s' t' (h'.trans (huv.trans hw.symm)), ← hp]
    simp
  have e₁ : insertAux a b x m [] p ((b, true) :: t ++ []) = p :=
    insertAux_eq_self fun v₁ c v₂ hv ↦ gapInsert_eq_nil
      (fun h ↦ by simpa [hv] using hocc _ _ (by simp [hv]) h) (hinv _ _ (by simp [hv]))
  have e₂ : gapInsert a b x m p ((b, true) :: t ++ []) = [(x, true)] := by
    rw [gapInsert, ite_eq_left ⟨hp ▸ suffix_append _ _, rfl⟩,
      ite_eq_right (mt getLast?_and_prefix_iff.1 (hinv _ _ (by simp))), append_nil]
  have e₃ : insertAux a b x m (p ++ [(b, true)]) t [] = t :=
    insertAux_eq_self fun v₁ c v₂ hv ↦ gapInsert_eq_nil
      (fun h ↦ by simpa using hocc _ _ (by simp [hv]) h) (hinv _ _ (by simp [hv]))
  rw [blockInsert_eq_insertAux, hw, insertAux_append, nil_append, insertAux_cons, e₁, e₂, e₃]
  simp [← hp, hs, ht]

private theorem map_mk_gapInsert {G : Type*} [Monoid G] (φ : FreeGroup α →* G)
    (hφ : φ (of x) = 1) (a b : α) (m : ℕ) (u v : List (α × Bool)) :
    φ (mk (gapInsert a b x m u v)) = 1 := by
  obtain h | ⟨e, h, -⟩ := gapInsert_eq_nil_or a b x m u v
  · rw [h]
    exact _root_.map_one φ
  · rw [h]
    cases e
    · have hx : mk [(x, false)] = (of x)⁻¹ := by simp [of, inv_mk, invRev]
      have := _root_.map_mul φ (of x)⁻¹ (of x)
      rwa [inv_mul_cancel, _root_.map_one, hφ, mul_one, eq_comm, ← hx] at this
    · exact hφ

private theorem map_mk_insertAux {G : Type*} [Monoid G] (φ : FreeGroup α →* G)
    (hφ : φ (of x) = 1) (a b : α) (m : ℕ) (u v t : List (α × Bool)) :
    φ (mk (insertAux a b x m u v t)) = φ (mk v) := by
  induction v generalizing u with
  | nil => rfl
  | cons c v ih =>
    rw [insertAux_cons, ← mul_mk, _root_.map_mul, map_mk_gapInsert φ hφ, one_mul,
      ← singleton_append, ← mul_mk, _root_.map_mul, ih, ← _root_.map_mul, mul_mk,
      singleton_append]

/-- A homomorphism killing the letter `x` does not see the replacement. -/
theorem map_mk_blockInsert {G : Type*} [Monoid G] (φ : FreeGroup α →* G) (hφ : φ (of x) = 1)
    (a b : α) (m : ℕ) (w : List (α × Bool)) : φ (mk (blockInsert a b x m w)) = φ (mk w) := by
  rw [blockInsert_eq_insertAux, map_mk_insertAux φ hφ]

private theorem isReduced_insertAux (h : IsReduced (u.getLast?.toList ++ v)) :
    IsReduced (u.getLast?.toList ++ insertAux a b x m u v t) := by
  induction v generalizing u with
  | nil => simpa using h
  | cons c v ih =>
    have hA : IsReduced (c :: insertAux a b x m (u ++ [c]) v t) := by
      simpa using ih (u := u ++ [c]) (by simpa using h.infix ⟨u.getLast?.toList, [], by simp⟩)
    rw [insertAux_cons]
    obtain hg | ⟨e, hg, ⟨u', d, rfl⟩, d', v', hv⟩ := gapInsert_eq_nil_or a b x m u (c :: v ++ t)
    · rw [hg, nil_append]
      rcases eq_nil_or_concat' u with rfl | ⟨u', d, rfl⟩
      · simpa using hA
      · simp only [getLast?_concat, Option.toList_some, singleton_append] at h ⊢
        exact isReduced_cons_cons.2 ⟨(isReduced_cons_cons.1 h).1, hA⟩
    · obtain rfl : c = (d', e) := by simpa using congrArg head? hv
      rw [hg]
      simpa [isReduced_cons_cons] using hA

/-- The replacement keeps a word reduced. -/
theorem IsReduced.blockInsert (hw : IsReduced w) (a b x : α) (m : ℕ) :
    IsReduced (blockInsert a b x m w) := by
  simpa [blockInsert_eq_insertAux] using
    isReduced_insertAux (a := a) (b := b) (x := x) (m := m) (u := []) (t := []) (by simpa using hw)

private theorem mem_insertAux {c : α × Bool} (hc : c ∈ insertAux a b x m u v t) :
    c.1 = x ∨ c ∈ v := by
  induction v generalizing u with
  | nil => simp at hc
  | cons d v ih =>
    rw [insertAux_cons, mem_append, mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact .inl (fst_eq_of_mem_gapInsert hc)
    · exact .inr mem_cons_self
    · exact (ih hc).imp_right (mem_cons_of_mem _)

/-- A letter of the new word is `x` or a letter of the old word. -/
theorem mem_blockInsert {c : α × Bool} (hc : c ∈ blockInsert a b x m w) : c.1 = x ∨ c ∈ w :=
  mem_insertAux (blockInsert_eq_insertAux a b x m w ▸ hc)

private theorem prefix_of_prefix_insertAux {u₁ : List (α × Bool)} (hu : ∀ c ∈ u₁, c.1 ≠ x)
    (h : u₁ <+: insertAux a b x m u v t) : u₁ <+: v := by
  induction v generalizing u u₁ with
  | nil => simpa using h
  | cons c v ih =>
    rcases u₁ with _ | ⟨e, u₁⟩
    · exact nil_prefix
    rw [insertAux_cons] at h
    rcases hg : gapInsert a b x m u (c :: v ++ t) with _ | ⟨e', I⟩
    · rw [hg, nil_append, cons_prefix_cons] at h
      exact cons_prefix_cons.2 ⟨h.1, ih (fun c hc ↦ hu c (mem_cons_of_mem _ hc)) h.2⟩
    · rw [hg, cons_append, cons_prefix_cons] at h
      have he' : e'.1 = x := fst_eq_of_mem_gapInsert (a := a) (b := b) (m := m) (u := u)
        (v := c :: v ++ t) (by rw [hg]; exact mem_cons_self)
      exact absurd (h.1 ▸ he') (hu e mem_cons_self)

omit [DecidableEq α] in
private theorem isInfix_of_isInfix_append {u₁ I l : List (α × Bool)} (hI : ∀ c ∈ I, c.1 = x)
    (hu : ∀ c ∈ u₁, c.1 ≠ x) (h : u₁ <:+: I ++ l) : u₁ <:+: l := by
  induction I with
  | nil => simpa using h
  | cons e I ih =>
    rcases infix_cons_iff.1 h with h | h
    · rcases u₁ with _ | ⟨e', u₁⟩
      · exact nil_infix
      · exact absurd ((cons_prefix_cons.1 h).1 ▸ hI e mem_cons_self) (hu e' mem_cons_self)
    · exact ih (fun c hc ↦ hI c (mem_cons_of_mem _ hc)) h

private theorem isInfix_of_isInfix_insertAux {u₁ : List (α × Bool)} (hu : ∀ c ∈ u₁, c.1 ≠ x)
    (h : u₁ <:+: insertAux a b x m u v t) : u₁ <:+: v := by
  induction v generalizing u with
  | nil => simpa using h
  | cons c v ih =>
    rw [insertAux_cons] at h
    rcases infix_cons_iff.1
      (isInfix_of_isInfix_append (fun _ ↦ fst_eq_of_mem_gapInsert) hu h) with h | h
    · rcases u₁ with _ | ⟨e, u₁⟩
      · exact nil_infix
      · rw [cons_prefix_cons] at h
        exact (cons_prefix_cons.2 ⟨h.1, prefix_of_prefix_insertAux
          (fun c hc ↦ hu c (mem_cons_of_mem _ hc)) h.2⟩).isInfix
    · exact infix_cons (ih h)

/-- A word without the letter `x` that occurs in the new word already occurs in the old word:
the replacement creates no occurrence of a word in the other letters. -/
theorem isInfix_of_isInfix_blockInsert {u : List (α × Bool)}
    (h : u <:+: blockInsert a b x m w) (hu : ∀ c ∈ u, c.1 ≠ x) : u <:+: w :=
  isInfix_of_isInfix_insertAux hu (blockInsert_eq_insertAux a b x m w ▸ h)

/-- In the word `b a b a² b a³ b` the block `b a² b` occurs once, and the letter `x` is inserted
before its last letter. -/
example (hab : a ≠ b) : blockInsert a b x 2 (merzljakovWord a b [1, 2, 3]) =
    [(b, true), (a, true), (b, true), (a, true), (a, true), (x, true), (b, true), (a, true),
      (a, true), (a, true), (b, true)] := by
  simpa [merzljakovWord_cons, replicate_succ] using
    blockInsert_merzljakovWord (x := x) (m := 2) (ms₁ := [1]) (ms₂ := [3]) hab (by simp) (by simp)

/-- In the formal inverse of the word `b a b a² b a³ b`, the letter `x⁻¹` is inserted after the
first letter of the inverse of the block `b a² b`. -/
example (hab : a ≠ b) : blockInsert a b x 2 (invRev (merzljakovWord a b [1, 2, 3])) =
    [(b, false), (a, false), (a, false), (a, false), (b, false), (x, false), (a, false),
      (a, false), (b, false), (a, false), (b, false)] := by
  rw [blockInsert_invRev]
  simpa [merzljakovWord_cons, replicate_succ, invRev] using congrArg invRev
    (blockInsert_merzljakovWord (x := x) (m := 2) (ms₁ := [1]) (ms₂ := [3]) hab (by simp)
      (by simp))

end BlockInsert

end FreeGroup
