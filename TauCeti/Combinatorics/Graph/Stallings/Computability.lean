/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import TauCeti.GroupTheory.FreeGroup.Computability

/-!
# Primitive-recursive membership in finite Stallings graphs

A finite dart table records the source number, signed label and target number of each dart.
Reading a word in such a table, testing whether it closes, and testing the reduced word are
primitive recursive jointly in the table, vertex and word. On the table of a folded labelled
Serre graph these tests characterize actual closed paths and membership in its accepted
subgroup. Reducing the input is essential for the subgroup test: unreduced words need not
label paths even when they represent accepted group elements.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  J. Algebra 248 (2002), 608–668, Section 7, Proposition 7.2.
-/

public section

namespace TauCeti.StallingsGraph

/-- The incidence and label table of a finite graph, with vertices numbered by natural numbers.
Each entry contains the source, signed label and target of a dart. Repeated entries are allowed. -/
abbrev DartTable (α : Type*) := List (ℕ × (α × Bool) × ℕ)

namespace DartTable

variable {α : Type*} [DecidableEq α]

/-- Follow one letter, using the first matching outgoing dart, or fail if none exists. -/
def step (t : DartTable α) (n : ℕ) (x : α × Bool) : Option ℕ :=
  (t.find? fun e => decide (e.1 = n ∧ e.2.1 = x)).map fun e => e.2.2

/-- Read a word from a numbered vertex, failing as soon as a transition is missing. -/
def follow (t : DartTable α) (n : ℕ) (w : List (α × Bool)) : Option ℕ :=
  w.foldlM (step t) n

/-- Test whether following the word in the table returns to its starting vertex. -/
def closes (t : DartTable α) (n : ℕ) (w : List (α × Bool)) : Bool :=
  decide (follow t n w = some n)

/-- Test subgroup membership by reading the freely reduced input word. -/
def accepts (t : DartTable α) (n : ℕ) (w : List (α × Bool)) : Bool :=
  closes t n (FreeGroup.reduce w)

/-- The one-letter transition is the target of the first matching table entry. -/
theorem step_eq (t : DartTable α) (n : ℕ) (x : α × Bool) :
    step t n x = (t.find? fun e => decide (e.1 = n ∧ e.2.1 = x)).map
      (fun e => e.2.2) := (rfl)

/-- Reading the empty word stays at the starting vertex. -/
@[simp] theorem follow_nil (t : DartTable α) (n : ℕ) : follow t n [] = some n := by
  simp [follow]

/-- Reading a nonempty word takes its first transition and then reads the remaining word. -/
@[simp] theorem follow_cons (t : DartTable α) (n : ℕ)
    (x : α × Bool) (w : List (α × Bool)) :
    follow t n (x :: w) = (step t n x).bind fun k => follow t k w := by
  simp [follow]

/-- Reading a concatenation continues from the endpoint of its first word. -/
@[simp] theorem follow_append (t : DartTable α) (n : ℕ) (u v : List (α × Bool)) :
    follow t n (u ++ v) = (follow t n u).bind fun k => follow t k v := by
  simp [follow]

/-- A word passes the closed-path test exactly when reading it returns its starting vertex. -/
@[simp] theorem closes_eq_true (t : DartTable α) (n : ℕ) (w : List (α × Bool)) :
    closes t n w = true ↔ follow t n w = some n := by simp [closes]

/-- Subgroup testing first freely reduces the word and then tests whether it closes. -/
theorem accepts_eq (t : DartTable α) (n : ℕ) (w : List (α × Bool)) :
    accepts t n w = closes t n (FreeGroup.reduce w) := (rfl)

section Primrec

variable [Primcodable α]

/-- One transition is primitive recursive jointly in the table, vertex and signed letter. -/
theorem primrec_step : Primrec fun p : DartTable α × ℕ × (α × Bool) =>
    step p.1 p.2.1 p.2.2 := by
  have test : Primrec₂ fun (p : DartTable α × ℕ × (α × Bool))
      (e : ℕ × (α × Bool) × ℕ) => decide (e.1 = p.2.1 ∧ e.2.1 = p.2.2) :=
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).and
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).decide
  exact (Primrec.option_map (Primrec.list_find? Primrec.fst test)
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- Word traversal is primitive recursive jointly in the table, vertex and word. -/
theorem primrec_follow : Primrec fun p : DartTable α × ℕ × List (α × Bool) =>
    follow p.1 p.2.1 p.2.2 := by
  have transition : Primrec₂ fun (p : DartTable α × ℕ × List (α × Bool))
      (q : Option ℕ × (α × Bool)) => q.1.bind fun k => step p.1 k q.2 :=
    (Primrec.option_bind (Primrec.fst.comp Primrec.snd)
      (primrec_step.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂).to₂
  exact (Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) transition).of_eq fun _ =>
      (List.foldlM_eq_foldl _ _ _).symm

/-- Closed-path testing is primitive recursive uniformly in all its finite inputs. -/
theorem primrec_closes : Primrec fun p : DartTable α × ℕ × List (α × Bool) =>
    closes p.1 p.2.1 p.2.2 :=
  (Primrec.eq.comp primrec_follow
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))).decide

/-- Subgroup testing is primitive recursive, including on unreduced input words. -/
theorem primrec_accepts : Primrec fun p : DartTable α × ℕ × List (α × Bool) =>
    accepts p.1 p.2.1 p.2.2 :=
  primrec_closes.comp (Primrec.pair Primrec.fst (Primrec.pair
    (Primrec.fst.comp Primrec.snd)
    (FreeGroup.primrec_reduce.comp (Primrec.snd.comp Primrec.snd))))

end Primrec

end DartTable

variable {α : Type*} (S : StallingsGraph α)

/-- A table records exactly the darts of `S` under the chosen vertex numbering. Vertex numbers
outside the image of the numbering have no incident darts in this table. -/
def IsDartTable (number : S.graph.V → ℕ) (t : DartTable α) : Prop :=
  ∀ n x m, (n, x, m) ∈ t ↔ ∃ e : S.graph.E,
    number (S.graph.src e) = n ∧ S.label e = x ∧ number (S.graph.tgt e) = m

/-- Exact table representation means that its entries are precisely numbered graph darts. -/
theorem isDartTable_iff (number : S.graph.V → ℕ) (t : DartTable α) :
    S.IsDartTable number t ↔ ∀ n x m, (n, x, m) ∈ t ↔ ∃ e : S.graph.E,
      number (S.graph.src e) = n ∧ S.label e = x ∧ number (S.graph.tgt e) = m := Iff.rfl

/-- Extract the incidence and label table from an explicit finite dart enumeration. -/
def dartTable {n : ℕ} (number : S.graph.V → ℕ) (enumerate : Fin n ≃ S.graph.E) :
    DartTable α :=
  List.ofFn fun i =>
    (number (S.graph.src (enumerate i)), S.label (enumerate i),
      number (S.graph.tgt (enumerate i)))

/-- The entries of the incidence table occur in the order of the given enumeration. -/
theorem dartTable_eq {n : ℕ} (number : S.graph.V → ℕ) (enumerate : Fin n ≃ S.graph.E) :
    S.dartTable number enumerate = List.ofFn fun i =>
      (number (S.graph.src (enumerate i)), S.label (enumerate i),
        number (S.graph.tgt (enumerate i))) := (rfl)

/-- The table extracted from a finite dart enumeration records exactly the graph darts. -/
theorem isDartTable_dartTable {n : ℕ} (number : S.graph.V → ℕ)
    (enumerate : Fin n ≃ S.graph.E) : S.IsDartTable number (S.dartTable number enumerate) := by
  intro a x b
  simp only [dartTable_eq, List.mem_ofFn, Prod.ext_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨enumerate i, hi.1, hi.2.1, hi.2.2⟩
  · rintro ⟨e, hs, hl, ht⟩
    exact ⟨enumerate.symm e, by simpa using And.intro hs (And.intro hl ht)⟩

variable [DecidableEq α] {S} {number : S.graph.V → ℕ} {t : DartTable α}

private theorem step_eq_some_iff_exists_dart (hS : S.IsFolded)
    (hn : Function.Injective number) (ht : S.IsDartTable number t)
    (a : S.graph.V) (x : α × Bool) (m : ℕ) :
    t.step (number a) x = some m ↔ ∃ e : S.graph.E,
      S.graph.src e = a ∧ S.label e = x ∧ number (S.graph.tgt e) = m := by
  have found {d : ℕ × (α × Bool) × ℕ}
      (hd : t.find? (fun e => decide (e.1 = number a ∧ e.2.1 = x)) = some d) :
      ∃ e : S.graph.E, S.graph.src e = a ∧ S.label e = x ∧
        number (S.graph.tgt e) = d.2.2 := by
    obtain ⟨e, he⟩ := (ht _ _ _).mp (List.mem_of_find?_eq_some hd)
    have hmatch := List.find?_some hd
    simp only [decide_eq_true_eq] at hmatch
    exact ⟨e, hn (he.1.trans hmatch.1), he.2.1.trans hmatch.2, he.2.2⟩
  constructor
  · intro h
    obtain ⟨d, hd, hm⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨e, hs, hl, he⟩ := found hd
    exact ⟨e, hs, hl, he.trans hm⟩
  · rintro ⟨e, hs, hl, hm⟩
    have hex : (t.find? (fun d => decide (d.1 = number a ∧ d.2.1 = x))).isSome := by
      rw [List.find?_isSome]
      exact ⟨(number a, x, m), (ht _ _ _).mpr ⟨e, by simp [hs, hl, hm]⟩, by simp⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hex
    obtain ⟨f, hfs, hfl, hfm⟩ := found hd
    have hef : f = e := (S.isFolded_def.mp hS) f e (hfs.trans hs.symm) (hfl.trans hl.symm)
    simp only [DartTable.step, hd, Option.map_some]
    exact congrArg some ((hfm.symm.trans (congrArg (fun e => number (S.graph.tgt e)) hef)).trans hm)

/-- Reading the exact word of a path returns the number of its endpoint. -/
theorem IsFolded.follow_word (hS : S.IsFolded) (hn : Function.Injective number)
    (ht : S.IsDartTable number t) {a b : S.graph.V} (p : S.graph.Path a b) :
    t.follow (number a) (S.word p) = some (number b) := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
    simpa [ih] using (step_eq_some_iff_exists_dart hS hn ht b (S.label e.val) (number c)).mpr
      ⟨e.val, e.property.1, rfl, congrArg number e.property.2⟩

private theorem exists_path_of_follow_eq_some (hS : S.IsFolded)
    (hn : Function.Injective number) (ht : S.IsDartTable number t)
    (a : S.graph.V) (w : List (α × Bool)) (m : ℕ)
    (h : t.follow (number a) w = some m) :
    ∃ b, ∃ p : S.graph.Path a b, S.word p = w ∧ number b = m := by
  induction w using List.reverseRecOn generalizing m with
  | nil =>
    simp only [DartTable.follow_nil, Option.some.injEq] at h
    exact ⟨a, .nil, S.word_nil a, h⟩
  | append_singleton w x ih =>
    rw [DartTable.follow_append] at h
    obtain ⟨k, hk, hx⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, p, hp, hb⟩ := ih k hk
    rw [← hb] at hx
    obtain ⟨e, hs, hl, he⟩ := (step_eq_some_iff_exists_dart hS hn ht b x m).mp (by simpa using hx)
    exact ⟨S.graph.tgt e, p.cons ⟨e, hs, rfl⟩, by simp [hp, hl], he⟩

/-- A finite folded graph's table returns a vertex exactly when a path with that endpoint
spells the input word. -/
theorem IsFolded.follow_eq_some_iff (hS : S.IsFolded) (hn : Function.Injective number)
    (ht : S.IsDartTable number t) (a b : S.graph.V) (w : List (α × Bool)) :
    t.follow (number a) w = some (number b) ↔ ∃ p : S.graph.Path a b, S.word p = w := by
  constructor
  · intro h
    obtain ⟨c, p, hp, hc⟩ := exists_path_of_follow_eq_some hS hn ht a w (number b) h
    obtain rfl := hn hc
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact hS.follow_word hn ht p

/-- The primitive-recursive closed-word test characterizes actual based closed paths. -/
theorem IsFolded.closes_eq_true_iff (hS : S.IsFolded) (hn : Function.Injective number)
    (ht : S.IsDartTable number t) (a : S.graph.V) (w : List (α × Bool)) :
    t.closes (number a) w = true ↔ ∃ p : S.graph.Path a a, S.word p = w := by
  rw [DartTable.closes_eq_true, hS.follow_eq_some_iff hn ht]

/-- The primitive-recursive reduced-word test decides membership in the subgroup accepted by
the finite folded graph, for arbitrary input words, including unreduced ones. -/
theorem IsFolded.accepts_eq_true_iff (hS : S.IsFolded) (hn : Function.Injective number)
    (ht : S.IsDartTable number t) (a : S.graph.V) (w : List (α × Bool)) :
    t.accepts (number a) w = true ↔ FreeGroup.mk w ∈ S.subgroup a := by
  rw [DartTable.accepts_eq, hS.closes_eq_true_iff hn ht,
    hS.mem_subgroup_iff_exists_word_eq_toWord, FreeGroup.toWord_mk]

end TauCeti.StallingsGraph
