/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Basic
public import TauCeti.Combinatorics.TreeWalk.Canonical
public import TauCeti.Combinatorics.TraceWord.Counting

/-!
# Leading trace words and coupled walks via canonical tree walks

A cyclic word of length `2 * m` with no singleton unordered edge and `m + 1` vertices is a
leading word in the Wigner moment expansion. Labeling each vertex by its first visit turns it
into a closed tree walk. The existing equivalence with Dyck words therefore applies to these
words, not just to walks already supplied in canonical labels.

`canonicalWalk` extends the first-visit canonical labeling of a finite path by zero after its
endpoint. Equality of vertices, and hence equality of unordered edges, is preserved and reflected.
`isTreeWalk_canonicalWalk_iff` characterizes closed tree paths via `canonicalWalk`,
`canonicalWalk_closedTreeWalk` shows `ClosedTreeWalk` is fixed by `canonicalWalk`, and
`isTreeWalk_canonicalWalk_cyclic` identifies canonicalized leading cyclic words as tree walks.

For variance bounds in the Wigner moment method,
`card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge` bounds the number of distinct
vertices visited by two edge-sharing cyclic words `(w₁, w₂)` of length `k` whose combined
`2 * k`-step edge multiset has no singleton nonloop edge by `k`, by splicing rotated copies of
`w₁` and `w₂` into a single cyclic word of length `2 * k` that returns to its root at the
midpoint `k`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemmas 2.1.6 and 2.1.7.
-/

public section

open Finset

namespace TauCeti.TreeWalk

variable {α : Type*} {m : ℕ}

/-- A cyclic word viewed as a path, with its initial vertex repeated at the endpoint. -/
def cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) : Fin (k + 1) → α :=
  fun i ↦ w (Fin.ofNat k i.val)

/-- Evaluate the path extension by reducing the index modulo the cyclic word's length. -/
theorem cyclicPath_apply {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin (k + 1)) :
    cyclicPath w i = w (Fin.ofNat k i.val) := (rfl)

@[simp] theorem cyclicPath_castSucc {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin k) :
    cyclicPath w i.castSucc = w i := by
  simp [cyclicPath]

@[simp] theorem cyclicPath_succ {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin k) :
    cyclicPath w i.succ = w (finRotate k i) := by
  apply congrArg w
  simp [finRotate_apply, Fin.ext_iff, Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]

@[simp] theorem cyclicPath_zero {k : ℕ} [NeZero k] (w : Fin k → α) :
    cyclicPath w 0 = w 0 := by
  simp [cyclicPath]

@[simp] theorem cyclicPath_last {k : ℕ} [NeZero k] (w : Fin k → α) :
    cyclicPath w (Fin.last k) = w 0 := by
  simp [cyclicPath]

/-- Repeating the initial vertex at the endpoint preserves the set of visited vertices. -/
@[simp] theorem range_cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) :
    Set.range (cyclicPath w) = Set.range w := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.ofNat k i.val, (cyclicPath_apply w i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, cyclicPath_castSucc w i⟩

/-- Vertex relabeling commutes with extending a cyclic word to a path. -/
theorem comp_cyclicPath {β : Type*} {k : ℕ} [NeZero k] (f : α → β) (w : Fin k → α) :
    f ∘ cyclicPath w = cyclicPath (f ∘ w) := (rfl)

/-- The path extension determines the original cyclic word. -/
@[simp] theorem cyclicPath_inj {k : ℕ} [NeZero k] {w₁ w₂ : Fin k → α} :
    cyclicPath w₁ = cyclicPath w₂ ↔ w₁ = w₂ := by
  constructor
  · intro h
    funext i
    simpa only [cyclicPath_castSucc] using congrFun h i.castSucc
  · rintro rfl
    rfl

/-- A closed tree walk in first-visit labeling is equal to the `canonicalWalk` of its restriction
to `Fin (2 * m + 1)`. -/
@[simp]
theorem canonicalWalk_closedTreeWalk (w : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ w.1 i) = w.1 := by
  set u : Fin (2 * m + 1) → ℕ := fun i ↦ w.1 i
  funext i
  rcases lt_or_ge (2 * m) i with hi | hi
  · rw [canonicalWalk_eq_zero u hi, w.2.2 i hi]
  · have hi' : i < 2 * m + 1 := Nat.lt_succ_of_le hi
    have hc_le : w.1 i ≤ i := w.2.1.le_self i hi
    have hc' : w.1 i < 2 * m + 1 := hc_le.trans_lt hi'
    have hcw_eq : canonicalWalk u i = canonicalWalk u (w.1 i) :=
      ((canonicalWalk_eq_iff u ⟨w.1 i, hc'⟩ ⟨i, hi'⟩).mpr (w.2.1.idem hi)).symm
    have hle : canonicalWalk u i ≤ w.1 i := hcw_eq ▸ canonicalWalk_le u (w.1 i)
    have hwk : w.1 (canonicalWalk u i) = w.1 i :=
      (canonicalWalk_eq_iff u ⟨canonicalWalk u i, hle.trans_lt hc'⟩ ⟨i, hi'⟩).mp
        (canonicalWalk_idem u i)
    exact le_antisymm hle (hwk ▸ w.2.1.le_self _ (hle.trans (hc_le.trans hi)))

variable [DecidableEq α]

@[simp] theorem image_cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) :
    univ.image (cyclicPath w) = univ.image w := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.ofNat k i.val, by simp [cyclicPath]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, cyclicPath_castSucc w i⟩

/-- A leading cyclic word has two occurrences of every edge when viewed as a path. -/
theorem card_edge_fiber_cyclicPath [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) (i : Fin (2 * m)) :
    #{j : Fin (2 * m) |
      s(cyclicPath w j.castSucc, cyclicPath w j.succ) =
        s(cyclicPath w i.castSucc, cyclicPath w i.succ)} = 2 := by
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using
    (ne_and_card_edge_fiber_eq_two_of_no_singleton_nonloop_edge_of_card_image_eq w
      (fun i _ ↦ h i) hv).2 i

/-- A closed path with `m + 1` vertices and each unordered edge traversed twice becomes a tree
walk after first-visit relabeling. No order on the original vertex type is needed. -/
theorem isTreeWalk_canonicalWalk (w : Fin (2 * m + 1) → α)
    (hclosed : w (Fin.last (2 * m)) = w 0)
    (hv : #(univ.image w) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(w j.castSucc, w j.succ) = s(w i.castSucc, w i.succ)} = 2) :
    IsTreeWalk m (canonicalWalk w) where
  root := canonicalWalk_zero w
  closed := by
    rw [← canonicalWalk_zero w]
    exact (canonicalWalk_eq_iff w (Fin.last _) 0).2 hclosed
  le_self i _ := canonicalWalk_le w i
  card_vertices := (card_fixed_canonicalWalk w).trans hv
  card_edge i hi := by
    have hedge (a b : Fin (2 * m)) :
        s(canonicalWalk w a.castSucc, canonicalWalk w a.succ) =
          s(canonicalWalk w b.castSucc, canonicalWalk w b.succ) ↔
        s(w a.castSucc, w a.succ) = s(w b.castSucc, w b.succ) := by
      simp only [Sym2.eq_iff, canonicalWalk_eq_iff]
    refine Eq.trans ?_ (he ⟨i, hi⟩)
    apply card_bij (fun j hj => (⟨j, mem_range.mp (mem_filter.mp hj).1⟩ : Fin (2 * m)))
    · intro j hj
      simp only [mem_filter, mem_univ, true_and]
      apply (hedge _ ⟨i, hi⟩).mp
      simpa only [Fin.val_castSucc, Fin.val_succ] using (mem_filter.mp hj).2
    · intro j hj k hk h
      exact Fin.mk.inj h
    · intro j hj
      refine ⟨j.val, mem_filter.mpr ⟨mem_range.mpr j.isLt, ?_⟩, rfl⟩
      have hh := (hedge j ⟨i, hi⟩).mpr (mem_filter.mp hj).2
      simpa only [Fin.val_castSucc, Fin.val_succ] using hh

/-- The `canonicalWalk` of `v : Fin (2 * m + 1) → α` is a closed tree walk if and only if `v` is
closed, visits `m + 1` distinct vertices, and traverses every unordered edge twice. -/
theorem isTreeWalk_canonicalWalk_iff (v : Fin (2 * m + 1) → α) :
    IsTreeWalk m (canonicalWalk v) ↔
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2 := by
  refine ⟨fun hw ↦ ⟨(canonicalWalk_eq_iff v (Fin.last (2 * m)) 0).mp
    (hw.closed.trans hw.root.symm), (card_fixed_canonicalWalk v).symm.trans hw.card_vertices,
    fun i ↦ ?_⟩, fun ⟨hc, hv, he⟩ ↦ isTreeWalk_canonicalWalk v hc hv he⟩
  have hedge (a b : Fin (2 * m)) :
      s(canonicalWalk v a.castSucc, canonicalWalk v a.succ) =
        s(canonicalWalk v b.castSucc, canonicalWalk v b.succ) ↔
      s(v a.castSucc, v a.succ) = s(v b.castSucc, v b.succ) := by
    simp only [Sym2.eq_iff, canonicalWalk_eq_iff]
  refine Eq.trans (card_bij (fun j _ ↦ j.val) (fun j hj ↦ mem_filter.mpr ⟨mem_range.mpr j.isLt,
    by simpa using (hedge j i).mpr (mem_filter.mp hj).2⟩) (fun _ _ _ _ ↦ Fin.ext) ?_)
    (hw.card_edge i i.isLt)
  intro j hj; obtain ⟨hj_lt, hj_eq⟩ := mem_filter.mp hj
  exact ⟨⟨j, mem_range.mp hj_lt⟩, mem_filter.mpr ⟨mem_univ _,
    (hedge ⟨j, mem_range.mp hj_lt⟩ i).mp (by simpa using hj_eq)⟩, rfl⟩

/-- A leading cyclic trace word becomes a tree walk under first-visit labeling. The endpoint
is added by cycling back to the initial vertex. The no-singleton condition alone, together with
the maximal vertex count, forces the required double traversal of every edge. The cyclic word
has positive length; the path theorem also covers the zero-step walk. -/
theorem isTreeWalk_canonicalWalk_cyclic [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    IsTreeWalk m (canonicalWalk (cyclicPath w)) :=
  isTreeWalk_canonicalWalk (cyclicPath w) (by simp) (by simpa using hv)
    (card_edge_fiber_cyclicPath w h hv)

section CoupledWalks

omit [DecidableEq α]

private def spliceEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul n).symm)

private def spliceWords {n : ℕ} (u₁ u₂ : Fin n → α) : Fin (2 * n) → α :=
  Sum.elim u₁ u₂ ∘ (spliceEquiv n).symm

@[simp]
private theorem spliceWords_spliceEquiv {n : ℕ} (u₁ u₂ : Fin n → α) (x : Fin n ⊕ Fin n) :
    spliceWords u₁ u₂ (spliceEquiv n x) = Sum.elim u₁ u₂ x := by
  simp [spliceWords]

private theorem image_spliceWords [DecidableEq α] {n : ℕ} (u₁ u₂ : Fin n → α) :
    univ.image (spliceWords u₁ u₂) = univ.image u₁ ∪ univ.image u₂ := by
  ext x; simp only [mem_image, mem_univ, true_and, mem_union]
  exact (spliceEquiv n).surjective.exists.trans (by simp)

private theorem val_finRotate_of_lt {n : ℕ} {i : Fin n} (h : i.val + 1 < n) :
    (finRotate n i).val = i.val + 1 := by
  rcases n with _ | n
  · exact i.elim0
  · simp [finRotate_apply, Fin.add_def]; omega

private theorem spliceWords_edge {u₁ u₂ : Fin (m + 1) → α} (h0 : u₁ 0 = u₂ 0)
    (x : Fin (m + 1) ⊕ Fin (m + 1)) :
    s(spliceWords u₁ u₂ (spliceEquiv (m + 1) x),
        spliceWords u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) x))) =
      Sum.elim (fun t ↦ s(u₁ t, u₁ (finRotate (m + 1) t)))
        (fun t ↦ s(u₂ t, u₂ (finRotate (m + 1) t))) x := by
  have hcast (j : Fin m) : finRotate (m + 1) j.castSucc = j.succ := by
    cases j with | mk j hj => exact finRotate_of_lt hj
  cases x with
  | inl i =>
    suffices spliceWords u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inl i))) =
        u₁ (finRotate (m + 1) i) by rw [spliceWords_spliceEquiv, this]; rfl
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inl (Fin.last m))) =
          spliceEquiv (m + 1) (.inr 0) := by
        ext; rw [val_finRotate_of_lt (by simp [spliceEquiv])]; simp [spliceEquiv]
      rw [hrot, spliceWords_spliceEquiv, finRotate_last, Sum.elim_inr, h0]
    · have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inl j.castSucc)) =
          spliceEquiv (m + 1) (.inl j.succ) := by
        ext; rw [val_finRotate_of_lt (by simp [spliceEquiv]; omega)]; simp [spliceEquiv]
      rw [hrot, spliceWords_spliceEquiv, hcast]; rfl
  | inr i =>
    suffices spliceWords u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inr i))) =
        u₂ (finRotate (m + 1) i) by rw [spliceWords_spliceEquiv, this]; rfl
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inr (Fin.last m))) =
          spliceEquiv (m + 1) (.inl 0) := by
        have hlast : spliceEquiv (m + 1) (.inr (Fin.last m)) = Fin.last (2 * m + 1) := by
          ext; simp [spliceEquiv]; omega
        rw [hlast]; ext; simp [spliceEquiv]
      rw [hrot, spliceWords_spliceEquiv, finRotate_last, Sum.elim_inl, h0]
    · have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inr j.castSucc)) =
          spliceEquiv (m + 1) (.inr j.succ) := by
        ext; rw [val_finRotate_of_lt (by simp [spliceEquiv]; omega)]; simp [spliceEquiv]; omega
      rw [hrot, spliceWords_spliceEquiv, hcast]; rfl

private theorem rotateWord_image [DecidableEq α] (w : Fin (m + 1) → α) (r : Fin (m + 1)) :
    univ.image (fun i ↦ w (i + r)) = univ.image w := by
  ext x; simp only [mem_image, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨i + r, hi⟩, fun ⟨j, hj⟩ ↦ ⟨j - r, by simpa using hj⟩⟩

private theorem spliceWords_shifted_edge_and_no_singleton_nonloop {w₁ w₂ : Fin (m + 1) → α}
    {t₁ r₂ : Fin (m + 1)} (hr₂ : w₁ t₁ = w₂ r₂)
    (hns : ∀ x : Fin (m + 1) ⊕ Fin (m + 1),
      Sum.elim w₁ w₂ x ≠ Sum.elim (w₁ ∘ finRotate (m + 1)) (w₂ ∘ finRotate (m + 1)) x →
      ∃ y ≠ x,
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) y =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) x) :
    let W := spliceWords (fun i ↦ w₁ (i + t₁)) (fun i ↦ w₂ (i + r₂))
    let shiftSum := Equiv.sumCongr (Equiv.addRight t₁) (Equiv.addRight r₂)
    (∀ j : Fin (2 * (m + 1)), s(W j, W (finRotate (2 * (m + 1)) j)) =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) (shiftSum ((spliceEquiv (m + 1)).symm j))) ∧
    (∀ j : Fin (2 * (m + 1)), W j ≠ W (finRotate (2 * (m + 1)) j) →
      ∃ j' ≠ j, s(W j', W (finRotate (2 * (m + 1)) j')) =
        s(W j, W (finRotate (2 * (m + 1)) j))) := by
  intro W shiftSum
  have hu0 : (fun i ↦ w₁ (i + t₁)) 0 = (fun i ↦ w₂ (i + r₂)) 0 := by simpa using hr₂
  have hW_edge (j : Fin (2 * (m + 1))) : s(W j, W (finRotate (2 * (m + 1)) j)) =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) (shiftSum ((spliceEquiv (m + 1)).symm j)) := by
    set x := (spliceEquiv (m + 1)).symm j
    rw [((spliceEquiv (m + 1)).apply_symm_apply j).symm, spliceWords_edge hu0 x]
    cases x <;> simp [shiftSum, finRotate_apply, add_right_comm]
  refine ⟨hW_edge, fun j hj_ne ↦ ?_⟩
  set z := shiftSum ((spliceEquiv (m + 1)).symm j)
  have hz_ne : Sum.elim w₁ w₂ z ≠
      Sum.elim (w₁ ∘ finRotate (m + 1)) (w₂ ∘ finRotate (m + 1)) z := fun hz_eq ↦ by
    have hdiag : s(W j, W (finRotate (2 * (m + 1)) j)) =
        s(Sum.elim w₁ w₂ z, Sum.elim w₁ w₂ z) := by
      have hsum : ∀ x, Sum.elim w₁ w₂ x =
          Sum.elim (w₁ ∘ finRotate (m + 1)) (w₂ ∘ finRotate (m + 1)) x →
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) x =
            s(Sum.elim w₁ w₂ x, Sum.elim w₁ w₂ x)
        | .inl t, h => congrArg (s(w₁ t, ·)) h.symm
        | .inr t, h => congrArg (s(w₂ t, ·)) h.symm
      exact (hW_edge j).trans (hsum z hz_eq)
    rcases Sym2.eq_iff.mp hdiag with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hj_ne (h1.trans h2.symm)
  obtain ⟨y, hy_ne, hy_eq⟩ := hns z hz_ne
  refine ⟨spliceEquiv (m + 1) (shiftSum.symm y), fun h ↦ hy_ne (by simp [z, ← h]), ?_⟩
  rw [hW_edge, hW_edge]; simpa [z] using hy_eq

private theorem not_card_image_eq_of_midpoint_root [DecidableEq α] {W : Fin (2 * (m + 1)) → α}
    (hW_ns_nl : ∀ j, W j ≠ W (finRotate (2 * (m + 1)) j) →
      ∃ j' ≠ j, s(W j', W (finRotate (2 * (m + 1)) j')) = s(W j, W (finRotate (2 * (m + 1)) j)))
    (hW_eq : #(univ.image W) = (m + 1) + 1)
    (hW_mid : W (spliceEquiv (m + 1) (.inr 0)) = W (spliceEquiv (m + 1) (.inl 0)))
    {j₁ j₂ : Fin (2 * (m + 1))} (hj₁ : j₁.val < m + 1) (hj₂ : m + 1 ≤ j₂.val)
    (hW12 : s(W j₁, W (finRotate (2 * (m + 1)) j₁)) = s(W j₂, W (finRotate (2 * (m + 1)) j₂))) :
    False := by
  obtain ⟨hnoloop, hW_ns⟩ :=
    ne_and_no_singleton_edge_of_no_singleton_nonloop_edge_of_card_image_eq W hW_ns_nl hW_eq
  have htree : IsTreeWalk (m + 1) (canonicalWalk (cyclicPath W)) :=
    isTreeWalk_canonicalWalk_cyclic W hW_ns hW_eq
  have hmid0 : canonicalWalk (cyclicPath W) (m + 1) = 0 := by
    have hval : (spliceEquiv (m + 1) (.inr 0)).val = m + 1 := by simp [spliceEquiv]
    have hzero : spliceEquiv (m + 1) (.inl 0) = 0 := by ext; simp [spliceEquiv]
    have h0 : canonicalWalk (cyclicPath W) ((spliceEquiv (m + 1) (.inr 0)).castSucc) = 0 :=
      ((canonicalWalk_eq_iff (cyclicPath W) ((spliceEquiv (m + 1) (.inr 0)).castSucc) 0).mpr
        (by rw [cyclicPath_castSucc, cyclicPath_zero, ← hzero]; exact hW_mid)).trans
        (canonicalWalk_zero _)
    rwa [Fin.val_castSucc, hval] at h0
  have hj_edge : s(canonicalWalk (cyclicPath W) j₁.val, canonicalWalk (cyclicPath W) (j₁.val + 1)) =
      s(canonicalWalk (cyclicPath W) j₂.val, canonicalWalk (cyclicPath W) (j₂.val + 1)) := by
    rw [← cyclicPath_castSucc W j₁, ← cyclicPath_succ W j₁, ← cyclicPath_castSucc W j₂,
      ← cyclicPath_succ W j₂] at hW12
    simpa only [Sym2.eq_iff, ← canonicalWalk_eq_iff (cyclicPath W), Fin.val_castSucc, Fin.val_succ]
      using hW12
  have := (htree.le_self j₁.val (by omega)).trans (by omega : j₁.val ≤ m + 1)
  have := (htree.le_self (j₁.val + 1) (by omega)).trans (by omega : j₁.val + 1 ≤ m + 1)
  have := htree.eq_zero_or_lt_of_eq_zero hmid0 (j := j₂.val) hj₂ (by omega)
  have := htree.eq_zero_or_lt_of_eq_zero hmid0 (j := j₂.val + 1) (by omega) (by omega)
  have hj2_eq : canonicalWalk (cyclicPath W) j₂.val =
      canonicalWalk (cyclicPath W) (j₂.val + 1) := by rw [Sym2.eq_iff] at hj_edge; omega
  exact hnoloop j₂ (by
    rw [← cyclicPath_castSucc W j₂, ← cyclicPath_succ W j₂]
    exact (canonicalWalk_eq_iff (cyclicPath W) j₂.castSucc j₂.succ).mp hj2_eq)

/-- **Coupled two-walk vertex bound.** If two cyclic words `w₁, w₂ : Fin k → α` share at least one
unordered edge and their combined `2 * k`-step edge multiset on `Fin k ⊕ Fin k` has no singleton
nonloop edge, then together they visit at most `k` distinct vertices. -/
theorem card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge [DecidableEq α] {k : ℕ}
    (w₁ w₂ : Fin k → α)
    (hshare : ∃ t₁ t₂ : Fin k, s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂)))
    (hns : ∀ x : Fin k ⊕ Fin k,
      Sum.elim w₁ w₂ x ≠ Sum.elim (w₁ ∘ finRotate k) (w₂ ∘ finRotate k) x →
      ∃ y ≠ x,
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate k t))) y =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate k t))) x) :
    #(univ.image w₁ ∪ univ.image w₂) ≤ k := by
  rcases k with _ | m
  · obtain ⟨t₁, -⟩ := hshare; exact Fin.elim0 t₁
  obtain ⟨t₁, t₂, hedge_eq⟩ := hshare
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : Fin (m + 1), w₁ t₁ = w₂ r₂ := by
    rcases Sym2.mem_iff.mp (hedge_eq ▸ Sym2.mem_mk_left _ _) with h | h
    · exact ⟨t₂, h⟩
    · exact ⟨finRotate (m + 1) t₂, h⟩
  set W := spliceWords (fun i ↦ w₁ (i + t₁)) (fun i ↦ w₂ (i + r₂)) with hW_def
  obtain ⟨hW_edge, hW_ns_nl⟩ := spliceWords_shifted_edge_and_no_singleton_nonloop hr₂ hns
  rw [← hW_def] at hW_edge hW_ns_nl
  have hW_img : univ.image W = univ.image w₁ ∪ univ.image w₂ := by
    rw [hW_def, image_spliceWords, rotateWord_image, rotateWord_image]
  have hW_le : #(univ.image W) ≤ m + 2 := by
    simpa [Nat.mul_div_right _ two_pos] using
      card_image_le_div_two_add_one_of_no_singleton_nonloop_edge W hW_ns_nl
  rw [← hW_img]
  by_contra hgt
  exact not_card_image_eq_of_midpoint_root hW_ns_nl (by omega) (by simp [hW_def, hr₂])
    (j₁ := spliceEquiv (m + 1) (.inl 0)) (j₂ := spliceEquiv (m + 1) (.inr (t₂ - r₂)))
    (by simp [spliceEquiv]) (by simp [spliceEquiv]) (by rw [hW_edge, hW_edge]; simpa using hedge_eq)

end CoupledWalks

end TauCeti.TreeWalk
