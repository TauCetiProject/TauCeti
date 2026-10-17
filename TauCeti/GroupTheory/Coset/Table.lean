/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Coset tables

A coset table records the action of the generators of a group on finitely many cosets of a
subgroup. Checked, it certifies that the subgroup has index at most the number of cosets listed.
This is how an upper bound on the order of a group given by a presentation is proved: Todd–Coxeter
coset enumeration produces such a table, and the check shows that the enumerated cosets are all
the cosets of the subgroup.

Here a table `T : TauCeti.CosetTable m k` on `k` points for `m` generators consists of the action
`T.act t : Fin k → Fin k` of each generator `t` and, for each point `i`, a word `T.word i` in the
generators. Given a group `G`, generators `g : Fin m → G` and a base point `a` of a `G`-set, the
point `i` is interpreted as `T.point g a i = (T.word i).prod • a`, the base point moved by the word.

Checking that `g t • T.point g a i = T.point g a (T.act t i)` for every generator and every point
is a statement in `G`, not a finite computation. It is established from a *deduction
certificate*, recording the deductions made during coset enumeration. Initially the edges
`(t, i)` with `T.word (T.act t i) = t :: T.word i` hold by definition of the points. A deduction
scans a *closed word* `t :: u` at a point `i`, that is a word acting trivially on the point `i`:
either a relator of the presentation, at any point, or a generator of the subgroup, at a point
whose word is empty. If every edge along `u` is already known and the table carries
`T.trace u i` to `i` along `t`, then the edge `(t, T.trace u i)` holds as well. The Boolean
`TauCeti.CosetTable.check` runs a list of deductions and verifies that every edge ends up
known; it is a finite computation, run by `decide`.

## Main definitions

* `TauCeti.CosetTable`: the action of the generators on `k` points, and a word for each point.
* `TauCeti.CosetTable.point`: the point of a `G`-set named by an index of the table.
* `TauCeti.CosetTable.checkAction`: the Boolean check that a certificate establishes every edge.
* `TauCeti.CosetTable.check`: the Boolean check of a deduction certificate.

## Main results

* `TauCeti.CosetTable.smul_mem_range_point_of_edges`: an empty root and sound generator edges
  imply orbit coverage when the generators generate the group.
* `TauCeti.CosetTable.surjective_point_of_edges`, `TauCeti.CosetTable.index_le_of_edges` and
  `TauCeti.CosetTable.finiteIndex_of_edges`: these hypotheses give surjective coset naming,
  an index bound and finite index, independently of how the edges were proved.

* `TauCeti.CosetTable.smul_point`: a certified table describes the action of the generators on
  the points it names.
* `TauCeti.CosetTable.smul_mem_range_point`: if the generators generate `G`, the named points
  contain the whole orbit of the base point.
* `TauCeti.CosetTable.index_le` and `TauCeti.CosetTable.finiteIndex`: a certified table on `k`
  points for a subgroup `H` shows `H.index ≤ k`, and in particular that `H` has finite index.

## References

* J. A. Todd, H. S. M. Coxeter, *A practical method for enumerating cosets of a finite abstract
  group*, Proc. Edinburgh Math. Soc. 5 (1936), 26–34.
* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*, Chapman &
  Hall/CRC, 2005, Chapter 5.
-/

public section

open scoped Pointwise

namespace TauCeti

/-- A coset table on `k` points for `m` generators: the action of each generator on the points,
together with a word in the generators for each point, naming the point as the image of a base
point under that word. -/
structure CosetTable (m k : ℕ) where
  /-- The action of the generator `t` on the points. -/
  act : Fin m → Fin k → Fin k
  /-- A word in the generators naming the point `i`, read as a product from left to right. -/
  word : Fin k → List (Fin m)

namespace CosetTable

variable {m k : ℕ} (T : CosetTable m k)

/-! ### The Boolean certificate check

The bodies below are exposed because a certificate is checked by `decide`, which has to evaluate
them. -/

/-- The point reached from `i` along the word `u`, whose letters act from the right, as the
product of the word acts on a point. -/
@[expose]
def trace (u : List (Fin m)) (i : Fin k) : Fin k :=
  u.foldr T.act i

/-- The edges `(t, j)` of the table traversed by `T.trace u i`: each letter `t` of `u` together
with the point it is applied to. -/
@[expose]
def edges : List (Fin m) → Fin k → List (Fin m × Fin k)
  | [], _ => []
  | t :: u, i => (t, T.trace u i) :: edges u i

/-- One deduction: scanning the closed word `t :: u` at the point `i`. If every edge of `u` is
among the known edges and the table carries `T.trace u i` to `i` along `t`, the edge
`(t, T.trace u i)` is added to the known edges. -/
@[expose]
def deduce (known : List (Fin m × Fin k)) (i : Fin k) : List (Fin m) → List (Fin m × Fin k)
  | [] => known
  | t :: u =>
    if (T.edges u i).all (· ∈ known) && T.act t (T.trace u i) = i then
      (t, T.trace u i) :: known
    else known

/-- The edges `(t, i)` holding by definition of the points: those with
`T.word (T.act t i) = t :: T.word i`. -/
@[expose]
def treeEdges : List (Fin m × Fin k) :=
  (List.finRange m ×ˢ List.finRange k).filter fun e ↦ T.word (T.act e.1 e.2) = e.1 :: T.word e.2

/-- The action check of a deduction certificate `cert` for the relators `rels` and the subgroup
generators `stab`. It verifies that each deduction scans a relator, or a subgroup generator at a
point with the empty word, and that running the deductions makes every edge of the table known. -/
@[expose]
def checkAction (rels stab : List (List (Fin m))) (cert : List (Fin k × List (Fin m))) : Bool :=
  cert.all (fun c ↦ c.2 ∈ rels || (T.word c.1 = [] && c.2 ∈ stab)) &&
    (List.finRange m).all fun t ↦ (List.finRange k).all fun i ↦
      (t, i) ∈ cert.foldl (fun known c ↦ T.deduce known c.1 c.2) T.treeEdges

/-- The check of a deduction certificate `cert` for the relators `rels` and the subgroup
generators `stab`. It verifies that some point has the empty word, that each deduction `(i, r)`
scans a relator, or a subgroup generator at a point with the empty word, and that running the
deductions in order from `T.treeEdges` makes every edge of the table known. -/
@[expose]
def check (rels stab : List (List (Fin m))) (cert : List (Fin k × List (Fin m))) : Bool :=
  (List.finRange k).any (T.word · = []) &&
    T.checkAction rels stab cert

@[simp]
theorem trace_nil (i : Fin k) : T.trace [] i = i := rfl

@[simp]
theorem trace_cons (t : Fin m) (u : List (Fin m)) (i : Fin k) :
    T.trace (t :: u) i = T.act t (T.trace u i) := rfl

/-! ### Soundness -/

section Monoid

variable {G α : Type*} [Monoid G] [MulAction G α] (g : Fin m → G) (a : α)

/-- The point of a `G`-set named by the index `i` of the table: the base point `a` moved by the
word `T.word i` in the generators `g`. -/
def point (i : Fin k) : α :=
  ((T.word i).map g).prod • a

theorem point_def (i : Fin k) : T.point g a i = ((T.word i).map g).prod • a := (rfl)

/-- A list of edges all of which describe the action of the generators on the named points. -/
private def Sound (known : List (Fin m × Fin k)) : Prop :=
  ∀ e ∈ known, g e.1 • T.point g a e.2 = T.point g a (T.act e.1 e.2)

variable {T g a}

private theorem prod_smul_point_of_sound {known : List (Fin m × Fin k)}
    (hk : Sound T g a known) (i : Fin k) :
    ∀ u : List (Fin m), (∀ e ∈ T.edges u i, e ∈ known) →
      (u.map g).prod • T.point g a i = T.point g a (T.trace u i)
  | [], _ => by simp [trace_nil]
  | t :: u, hu => by
    have hu' : ∀ e ∈ T.edges u i, e ∈ known := fun e he ↦ hu e (List.mem_cons_of_mem _ he)
    rw [List.map_cons, List.prod_cons, mul_smul, prod_smul_point_of_sound hk i u hu', trace_cons]
    exact hk _ (hu _ List.mem_cons_self)

private theorem sound_deduce {known : List (Fin m × Fin k)} (hk : Sound T g a known)
    {i : Fin k} {r : List (Fin m)} (hr : (r.map g).prod • T.point g a i = T.point g a i) :
    Sound T g a (T.deduce known i r) := by
  match r with
  | [] => exact hk
  | t :: u =>
    rw [deduce]
    split_ifs with h
    · simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · rw [List.map_cons, List.prod_cons, mul_smul,
          prod_smul_point_of_sound hk i u h.1] at hr
        rw [h.2]
        exact hr
      · exact hk e he
    · exact hk

private theorem sound_treeEdges : Sound T g a T.treeEdges := by
  intro e he
  simp only [treeEdges, List.mem_filter, decide_eq_true_eq] at he
  rw [point_def, point_def, he.2, List.map_cons, List.prod_cons, mul_smul]

private theorem sound_foldl {rels stab : List (List (Fin m))}
    (hrels : ∀ r ∈ rels, (r.map g).prod = 1) (hstab : ∀ r ∈ stab, (r.map g).prod • a = a) :
    ∀ (cert : List (Fin k × List (Fin m))) (known : List (Fin m × Fin k)),
      (∀ c ∈ cert, c.2 ∈ rels ∨ (T.word c.1 = [] ∧ c.2 ∈ stab)) → Sound T g a known →
        Sound T g a (cert.foldl (fun known c ↦ T.deduce known c.1 c.2) known)
  | [], _, _, hk => hk
  | c :: cert, known, hc, hk => by
    rw [List.foldl_cons]
    refine sound_foldl hrels hstab cert _ (fun c' hc' ↦ hc c' (List.mem_cons_of_mem _ hc')) ?_
    refine sound_deduce hk ?_
    rcases hc c List.mem_cons_self with h | ⟨hw, h⟩
    · rw [hrels _ h, one_smul]
    · rw [point_def, hw, List.map_nil, List.prod_nil, one_smul, hstab _ h]

/-- **Soundness of a certified coset table.** If the relators `rels` hold for the generators `g`
and the words `stab` fix the base point `a`, a table whose certificate checks describes the action
of each generator on the points it names. -/
theorem smul_point {rels stab : List (List (Fin m))} {cert : List (Fin k × List (Fin m))}
    (hT : T.checkAction rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod • a = a) (t : Fin m) (i : Fin k) :
    g t • T.point g a i = T.point g a (T.act t i) := by
  simp only [checkAction, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.mem_finRange, forall_const] at hT
  exact sound_foldl hrels hstab cert _ hT.1 sound_treeEdges _ (hT.2 t i)

end Monoid

section Group

variable {T} {G α : Type*} [Group G] [MulAction G α] {g : Fin m → G} {a : α}

/-- If a table names the base point by an empty word and every generator edge is sound,
its named points contain the whole orbit, provided the generators generate the group. -/
theorem smul_mem_range_point_of_edges (hg : Subgroup.closure (Set.range g) = ⊤)
    (hroot : ∃ i, T.word i = [])
    (hedges : ∀ t i, g t • T.point g a i = T.point g a (T.act t i)) (x : G) :
    x • a ∈ Set.range (T.point g a) := by
  have hfin : (Set.range (T.point g a)).Finite := Set.finite_range _
  have hstabilizer : Subgroup.closure (Set.range g) ≤
      MulAction.stabilizer G (Set.range (T.point g a)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_set' hfin]
    rintro _ ⟨i, rfl⟩
    exact ⟨T.act t i, (hedges t i).symm⟩
  have hx : x ∈ MulAction.stabilizer G (Set.range (T.point g a)) :=
    hstabilizer (hg ▸ Subgroup.mem_top x)
  refine (MulAction.mem_stabilizer_set' hfin).1 hx ?_
  obtain ⟨i, hi⟩ := hroot
  exact ⟨i, by rw [point_def, hi, List.map_nil, List.prod_nil, one_smul]⟩

/-- A table with an empty root and sound generator edges names every coset of an arbitrary
subgroup, provided its generators generate the ambient group. -/
theorem surjective_point_of_edges {H : Subgroup G}
    (hg : Subgroup.closure (Set.range g) = ⊤) (hroot : ∃ i, T.word i = [])
    (hedges : ∀ t i, g t • T.point g ((1 : G) : G ⧸ H) i =
      T.point g ((1 : G) : G ⧸ H) (T.act t i)) :
    Function.Surjective (T.point g ((1 : G) : G ⧸ H)) := by
  refine QuotientGroup.mk_surjective.forall.2 fun x ↦ ?_
  simpa [MulAction.Quotient.smul_mk] using smul_mem_range_point_of_edges hg hroot hedges x

/-- An empty root and sound generator edges bound the subgroup index by the table size,
provided the generators generate the ambient group. -/
theorem index_le_of_edges {H : Subgroup G} (hg : Subgroup.closure (Set.range g) = ⊤)
    (hroot : ∃ i, T.word i = [])
    (hedges : ∀ t i, g t • T.point g ((1 : G) : G ⧸ H) i =
      T.point g ((1 : G) : G ⧸ H) (T.act t i)) : H.index ≤ k := by
  rw [Subgroup.index_eq_card]
  exact (Nat.card_le_card_of_surjective _ (surjective_point_of_edges hg hroot hedges)).trans_eq
    (Nat.card_fin k)

/-- An empty root and sound generator edges establish finite index, provided the generators
generate the ambient group. No finiteness or normality of the subgroup is required. -/
theorem finiteIndex_of_edges {H : Subgroup G} (hg : Subgroup.closure (Set.range g) = ⊤)
    (hroot : ∃ i, T.word i = [])
    (hedges : ∀ t i, g t • T.point g ((1 : G) : G ⧸ H) i =
      T.point g ((1 : G) : G ⧸ H) (T.act t i)) : H.FiniteIndex :=
  have : Finite (G ⧸ H) := Finite.of_surjective _ (surjective_point_of_edges hg hroot hedges)
  H.finiteIndex_of_finite_quotient

/-- If the generators `g` generate `G`, the points named by a certified coset table contain the
whole orbit of the base point `a`. -/
theorem smul_mem_range_point {rels stab : List (List (Fin m))}
    {cert : List (Fin k × List (Fin m))} (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod • a = a) (x : G) :
    x • a ∈ Set.range (T.point g a) := by
  rw [check, Bool.and_eq_true] at hT
  have hroot : ∃ i, T.word i = [] := by
    simpa only [List.any_eq_true, decide_eq_true_eq, List.mem_finRange, true_and] using hT.1
  exact smul_mem_range_point_of_edges hg hroot (smul_point hT.2 hrels hstab) x

/-- The cosets named by a certified coset table for a subgroup `H` are all the cosets of `H`. -/
private theorem surjective_point {H : Subgroup G} {rels stab : List (List (Fin m))}
    {cert : List (Fin k × List (Fin m))} (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) :
    Function.Surjective (T.point g ((1 : G) : G ⧸ H)) := by
  refine QuotientGroup.mk_surjective.forall.2 fun x ↦ ?_
  have hstab' : ∀ r ∈ stab, (r.map g).prod • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    intro r hr
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
    exact H.inv_mem (hstab r hr)
  simpa [MulAction.Quotient.smul_mk] using smul_mem_range_point hg hT hrels hstab' x

/-- **Coset enumeration bounds the index.** If the generators `g` generate `G`, the relators
`rels` hold for them and the words `stab` lie in the subgroup `H`, a coset table on `k` points
whose certificate checks shows that `H` has index at most `k`. -/
theorem index_le {H : Subgroup G} {rels stab : List (List (Fin m))}
    {cert : List (Fin k × List (Fin m))} (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) : H.index ≤ k := by
  rw [Subgroup.index_eq_card]
  exact (Nat.card_le_card_of_surjective _ (surjective_point hg hT hrels hstab)).trans_eq
    (Nat.card_fin k)

/-- A subgroup admitting a certified coset table has finite index. -/
theorem finiteIndex {H : Subgroup G} {rels stab : List (List (Fin m))}
    {cert : List (Fin k × List (Fin m))} (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) : H.FiniteIndex :=
  have : Finite (G ⧸ H) := Finite.of_surjective _ (surjective_point hg hT hrels hstab)
  H.finiteIndex_of_finite_quotient

end Group

end CosetTable

end TauCeti
