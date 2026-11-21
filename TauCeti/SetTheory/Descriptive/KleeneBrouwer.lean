/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.WellFoundedTree

/-!
# The Kleene–Brouwer order

The **Kleene–Brouwer order** `Descriptive.KBLT` on finite sequences of natural numbers puts a
proper extension before the sequence it extends, and otherwise lets the first difference decide.
It is a strict total order on `List ℕ`, and it is well-founded on the nodes of a descriptive tree
`T : Descriptive.tree ℕ` exactly when `T` has no infinite branch. On a well-founded tree the rank
of the tree is at most the order type of the Kleene–Brouwer order on its nodes.

## Main definitions

* `Descriptive.KBLT`: the Kleene–Brouwer order on `List ℕ`.

## Main results

* `Descriptive.isStrictTotalOrder_kbLT`: the Kleene–Brouwer order is a strict total order.
* `Descriptive.wellFounded_kbLT_iff`: the Kleene–Brouwer order is well-founded on the nodes of a
  tree exactly when the tree has empty body.
* `Descriptive.rank_le_type_kbLT`: the rank of a well-founded tree is at most the order type of
  the Kleene–Brouwer order on its nodes.

## References

* David Marker, *Lectures on infinitary model theory*, Definition 9.38 and Exercise 9.39.
* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Section 2.G.
-/

public section

open Set

namespace Descriptive

open _root_.Descriptive.Tree

/-- The **Kleene–Brouwer order** on finite sequences of natural numbers: `KBLT x y` holds when `x`
properly extends `y`, or when at the first position where they differ the entry of `x` is
smaller. -/
def KBLT (x y : List ℕ) : Prop :=
  (y <+: x ∧ x ≠ y) ∨
    ∃ (p : List ℕ) (a b : ℕ) (x' y' : List ℕ), a < b ∧ x = p ++ a :: x' ∧ y = p ++ b :: y'

/-- Unfolding lemma for `Descriptive.KBLT`. -/
theorem kbLT_iff {x y : List ℕ} :
    KBLT x y ↔ (y <+: x ∧ x ≠ y) ∨
      ∃ (p : List ℕ) (a b : ℕ) (x' y' : List ℕ), a < b ∧ x = p ++ a :: x' ∧ y = p ++ b :: y' :=
  Iff.rfl

/-- A proper extension comes first in the Kleene–Brouwer order. -/
theorem kbLT_of_prefix {x y : List ℕ} (h : x <+: y) (hne : x ≠ y) : KBLT y x :=
  Or.inl ⟨h, hne.symm⟩

/-- The empty sequence comes before nothing: it is the largest element of the Kleene–Brouwer
order. -/
@[simp]
theorem not_kbLT_nil_left (y : List ℕ) : ¬ KBLT [] y := by
  rintro (⟨h, hne⟩ | ⟨p, a, b, x', y', -, h, -⟩)
  · exact hne (List.prefix_nil.1 h).symm
  · simp at h

/-- Every nonempty sequence comes before the empty sequence. -/
@[simp]
theorem kbLT_nil_right_iff {x : List ℕ} : KBLT x [] ↔ x ≠ [] := by
  refine ⟨?_, fun h => kbLT_of_prefix (List.nil_prefix) (Ne.symm h)⟩
  rintro (⟨-, hne⟩ | ⟨p, a, b, x', y', -, -, h⟩)
  · exact hne
  · simp at h

/-- The Kleene–Brouwer order on sequences with a first entry: the first entries decide, and equal
first entries pass to the tails. -/
theorem kbLT_cons_cons_iff {a b : ℕ} {x y : List ℕ} :
    KBLT (a :: x) (b :: y) ↔ a < b ∨ a = b ∧ KBLT x y := by
  constructor
  · rintro (⟨h, hne⟩ | ⟨p, c, d, x', y', hcd, hx, hy⟩)
    · rw [List.cons_prefix_cons] at h
      obtain ⟨rfl, hyx⟩ := h
      exact Or.inr ⟨rfl, Or.inl ⟨hyx, fun h' => hne (by rw [h'])⟩⟩
    · obtain _ | ⟨e, p⟩ := p
      · simp only [List.nil_append, List.cons.injEq] at hx hy
        exact Or.inl (hx.1 ▸ hy.1 ▸ hcd)
      · simp only [List.cons_append, List.cons.injEq] at hx hy
        exact Or.inr ⟨hx.1.trans hy.1.symm, Or.inr ⟨p, c, d, x', y', hcd, hx.2, hy.2⟩⟩
  · rintro (hab | ⟨rfl, ⟨h, hne⟩ | ⟨p, c, d, _, _, hcd, rfl, rfl⟩⟩)
    · exact Or.inr ⟨[], a, b, x, y, hab, rfl, rfl⟩
    · exact Or.inl ⟨List.cons_prefix_cons.2 ⟨rfl, h⟩, fun h' => hne (List.cons.inj h').2⟩
    · exact Or.inr ⟨a :: p, c, d, _, _, hcd, rfl, rfl⟩

/-- The sort key of a sequence for the Kleene–Brouwer order: its entries followed by `⊤`. -/
private def kbKey (x : List ℕ) : List (WithTop ℕ) :=
  x.map WithTop.some ++ [⊤]

private theorem kbKey_injective : Function.Injective kbKey := fun _ _ h =>
  List.map_injective_iff.2 WithTop.coe_injective (List.append_inj_left' h rfl)

/-- The Kleene–Brouwer order is the lexicographic order of the sort keys. -/
private theorem kbLT_iff_kbKey_lt {x y : List ℕ} : KBLT x y ↔ kbKey x < kbKey y := by
  induction x generalizing y with
  | nil =>
    simp only [not_kbLT_nil_left, false_iff, kbKey, List.map_nil, List.nil_append]
    obtain _ | ⟨b, y⟩ := y
    · exact lt_irrefl _
    · simp [List.cons_lt_cons_iff]
  | cons a x ih =>
    obtain _ | ⟨b, y⟩ := y
    · simp [kbKey, List.cons_lt_cons_iff]
    · rw [kbLT_cons_cons_iff, ih]
      simp only [kbKey, List.map_cons, List.cons_append]
      rw [List.cons_lt_cons_iff, WithTop.coe_lt_coe, WithTop.coe_inj]

/-- The Kleene–Brouwer order is a strict total order. -/
instance isStrictTotalOrder_kbLT : IsStrictTotalOrder (List ℕ) KBLT := by
  have h : KBLT = InvImage (· < ·) kbKey := by
    ext x y
    exact kbLT_iff_kbKey_lt
  rw [h]
  exact InvImage.isStrictTotalOrder kbKey_injective

/-- `LeftmostPrefix S p`: some element of `S` extends `p`, and no element of `S` branches off to
the left of `p`. -/
private def LeftmostPrefix {T : tree ℕ} (S : Set T) (p : List ℕ) : Prop :=
  (∃ s ∈ S, p <+: (s : List ℕ)) ∧
    ∀ s ∈ S, ∀ (q : List ℕ) (c d : ℕ) (x' y' : List ℕ),
      c < d → (s : List ℕ) = q ++ c :: x' → p = q ++ d :: y' → False

/-- If `S` has no Kleene–Brouwer-minimal element, every leftmost prefix of `S` extends by one
entry to a longer leftmost prefix: the least entry continuing it inside `S`. -/
private theorem LeftmostPrefix.exists_append {T : tree ℕ} {S : Set T}
    (hmin : ∀ m ∈ S, ∃ x ∈ S, KBLT x m) {p : List ℕ} (hp : LeftmostPrefix S p) :
    ∃ a, LeftmostPrefix S (p ++ [a]) := by
  classical
  obtain ⟨⟨s, hs, hps⟩, hleft⟩ := hp
  have hext : ∃ c, ∃ s ∈ S, p ++ [c] <+: (s : List ℕ) := by
    by_contra! hno
    obtain ⟨l, hl⟩ := hps
    have hsp : (s : List ℕ) = p := by
      obtain _ | ⟨c, l⟩ := l
      · simpa using hl.symm
      · exact absurd ⟨l, by simp [← hl]⟩ (hno c s hs)
    obtain ⟨t, ht, (⟨⟨l', hl'⟩, hne⟩ | ⟨q, c, d, x', y', hcd, htq, hsq⟩)⟩ := hmin s hs
    · obtain _ | ⟨c, l'⟩ := l'
      · exact hne (by simpa using hl'.symm)
      · exact hno c t ht ⟨l', by simp [← hl', hsp]⟩
    · exact hleft t ht q c d x' y' hcd htq (hsp ▸ hsq)
  refine ⟨Nat.find hext, Nat.find_spec hext |>.imp fun s hs => ⟨hs.1, hs.2⟩, ?_⟩
  intro t ht q c d x' y' hcd htq hpq
  rcases List.eq_nil_or_concat y' with rfl | ⟨y'', e, rfl⟩
  · obtain ⟨rfl, hd⟩ := List.append_inj' hpq rfl
    simp only [List.cons.injEq, and_true] at hd
    exact Nat.find_min hext (hd ▸ hcd) ⟨t, ht, ⟨x', by simp [htq]⟩⟩
  · have h2 : p ++ [Nat.find hext] = (q ++ d :: y'') ++ [e] := by
      simpa [List.concat_eq_append] using hpq
    exact hleft t ht q c d x' y'' hcd htq (List.append_inj_left' h2 rfl)

/-- **Kleene–Brouwer and bodies.** The Kleene–Brouwer order is well-founded on the nodes of a tree
exactly when the tree has no infinite branch. -/
theorem wellFounded_kbLT_iff (T : tree ℕ) :
    WellFounded (fun x y : T => KBLT x y) ↔ body T = ∅ := by
  refine ⟨fun hwf => eq_empty_of_forall_notMem fun x hx => ?_, fun hT => ?_⟩
  · let c : ℕ → T := fun n => ⟨initialSegment x n, mem_body.1 hx n⟩
    have hstep (n : ℕ) : KBLT (c (n + 1)) (c n) :=
      kbLT_of_prefix (initialSegment_prefix_initialSegment x n.le_succ) fun h => by
        simpa [c] using congrArg List.length h
    exact (wellFounded_iff_isEmpty_descending_chain.mp hwf).false ⟨c, hstep⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro S ⟨s₀, hs₀⟩
  by_contra! hmin
  -- Without a minimal element, the leftmost prefixes of `S` form an infinite branch of `T`.
  have h₀ : LeftmostPrefix S [] :=
    ⟨⟨s₀, hs₀, List.nil_prefix⟩, fun _ _ _ _ _ _ _ _ _ h => by simp at h⟩
  choose f hf using fun p : {p // LeftmostPrefix S p} => p.property.exists_append hmin
  let seq : ℕ → {p // LeftmostPrefix S p} :=
    fun n => Nat.rec ⟨[], h₀⟩ (fun _ p => ⟨p.val ++ [f p], hf p⟩) n
  have hseq (n : ℕ) : initialSegment (fun k => f (seq k)) n = (seq n).val := by
    induction n with
    | zero => simp [seq]
    | succ n ih => rw [initialSegment_succ, ih]
  refine (eq_empty_iff_forall_notMem.1 hT) (fun k => f (seq k)) (mem_body.2 fun n => ?_)
  obtain ⟨s, -, hps⟩ := (seq n).property.1
  exact hseq n ▸ mem_of_prefix hps s.property

/-- On a tree with empty body the Kleene–Brouwer order of its nodes is a well-order. -/
theorem isWellOrder_kbLT {T : tree ℕ} (hT : body T = ∅) :
    IsWellOrder T (fun x y : T => KBLT x y) :=
  { InvImage.isStrictTotalOrder (r := KBLT) (Subtype.val_injective (p := (· ∈ T))) with
    wf := (wellFounded_kbLT_iff T).2 hT }

/-- **Height and the Kleene–Brouwer order.** The rank of a well-founded tree is at most the order
type of the Kleene–Brouwer order on its nodes. -/
theorem rank_le_type_kbLT (T : tree ℕ) [hT : IsWellOrder T (fun x y : T => KBLT x y)] :
    rank T ≤ Ordinal.type (fun x y : T => KBLT x y) := by
  have hT : Tree.IsWellFounded T :=
    isWellFounded_iff_body_eq_empty.2 ((wellFounded_kbLT_iff T).1 hT.wf)
  have hnode (u : T) : (hT.apply u).rank ≤ Ordinal.typein (fun x y : T => KBLT x y) u := by
    induction u using (isWellFounded_iff.1 hT).induction with
    | h u ih =>
      rw [(hT.apply u).rank_eq]
      refine Ordinal.iSup_le fun v => Order.succ_le_of_lt ((ih v.val v.property).trans_lt ?_)
      obtain ⟨h, hne⟩ := strictExt_iff.1 v.property.strictExt
      exact (Ordinal.typein_lt_typein _).2 (kbLT_of_prefix h hne)
  rw [hT.rank_eq_iSup]
  exact Ordinal.iSup_le fun u =>
    Order.succ_le_of_lt ((hnode u).trans_lt (Ordinal.typein_lt_type _ u))

end Descriptive
