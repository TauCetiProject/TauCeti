/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Order.Lattice.Nat

/-!
# Ramsey numbers of complete uniform hypergraphs

`HypergraphRamseyProp m f n` says that every colouring of the `m`-element subsets of `Fin n`
contains a set of `f k` vertices whose `m`-element subsets all have colour `k`, for some colour
`k`. For finitely many colours the least such `n` is `hypergraphRamseyNumber m f`.

For finitely many colours, `hypergraphRamseyProp_iff` identifies the property with the inequality
`hypergraphRamseyNumber m f ≤ n`. Restriction to arbitrary finite vertex sets and the recursive
step in uniformity make this form usable inside larger coloured hypergraphs. Uniformity zero is
included: colouring the unique empty subset selects a colour, and every demand must fit.

## References

* R. Diestel, *Graph Theory*, sixth edition, Theorem 9.1.3.
* P. Erdős, *Some remarks on the theory of graphs*, Bulletin of the American Mathematical Society
  53 (1947), 292–294, inequality (3), for the recursive step attributed there to Szekeres.
* S. P. Radziszowski, *Small Ramsey numbers*, Electronic Journal of Combinatorics, DS1, §1.
-/

public section

open Finset

namespace TauCeti

variable {K V : Type*} {f : K → ℕ} {m n N : ℕ}

/-- Every colouring of the `m`-element subsets of `Fin n` has a set of `f k` vertices all of whose
`m`-element subsets have colour `k`, for some colour `k`. Sets of fewer than `m` vertices are
monochromatic in every colour. -/
def HypergraphRamseyProp (m : ℕ) (f : K → ℕ) (n : ℕ) : Prop :=
  ∀ c : {t : Finset (Fin n) // #t = m} → K,
    ∃ k, ∃ S : Finset (Fin n), #S = f k ∧ ∀ t, (ht : #t = m) → t ⊆ S → c ⟨t, ht⟩ = k

/-- Unfolding the hypergraph Ramsey property. -/
theorem hypergraphRamseyProp_iff_forall : HypergraphRamseyProp m f n ↔
    ∀ c : {t : Finset (Fin n) // #t = m} → K,
      ∃ k, ∃ S : Finset (Fin n), #S = f k ∧ ∀ t, (ht : #t = m) → t ⊆ S → c ⟨t, ht⟩ = k :=
  Iff.rfl

/-- The infimum of the numbers of vertices with the hypergraph Ramsey property. For finitely
many colours it is the least such number, by `hypergraphRamseyProp_iff`. -/
noncomputable def hypergraphRamseyNumber (m : ℕ) (f : K → ℕ) : ℕ :=
  sInf {n | HypergraphRamseyProp m f n}

/-- Unfolding the hypergraph Ramsey number. -/
theorem hypergraphRamseyNumber_def (m : ℕ) (f : K → ℕ) :
    hypergraphRamseyNumber m f = sInf {n | HypergraphRamseyProp m f n} :=
  (rfl)

/-- Every number with the hypergraph Ramsey property bounds its infimum from above. -/
theorem HypergraphRamseyProp.hypergraphRamseyNumber_le (h : HypergraphRamseyProp m f n) :
    hypergraphRamseyNumber m f ≤ n :=
  Nat.sInf_le h

/-- The hypergraph Ramsey property yields a monochromatic set inside any sufficiently large
finite vertex set, on an arbitrary vertex type. -/
theorem HypergraphRamseyProp.exists_monochromatic_subset (h : HypergraphRamseyProp m f n)
    (c : {t : Finset V // #t = m} → K) {A : Finset V} (hA : n ≤ #A) :
    ∃ k, ∃ S ⊆ A, #S = f k ∧ ∀ t, (ht : #t = m) → t ⊆ S → c ⟨t, ht⟩ = k := by
  let e : Fin n ↪ V :=
    (Fin.castLEEmb hA).trans (A.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _))
  obtain ⟨k, S, hS, hc⟩ := h (fun t ↦ c ⟨t.val.map e, by simp [t.property]⟩)
  refine ⟨k, S.map e, ?_, by simpa using hS, ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    simp [e]
  · intro t ht htS
    obtain ⟨u, hu, rfl⟩ := subset_map_iff.1 htS
    exact hc u (by simpa using ht) hu

/-- The hypergraph Ramsey property is upward closed in the number of vertices. -/
theorem HypergraphRamseyProp.mono (h : HypergraphRamseyProp m f n) (hn : n ≤ N) :
    HypergraphRamseyProp m f N := by
  intro c
  obtain ⟨k, S, -, hS, hc⟩ := h.exists_monochromatic_subset c (A := univ) (by simpa using hn)
  exact ⟨k, S, hS, hc⟩

/-- A demand smaller than the uniformity is met as soon as that many vertices are available. -/
theorem hypergraphRamseyProp_of_lt_uniformity {k : K} (hk : f k < m) (hn : f k ≤ n) :
    HypergraphRamseyProp m f n := by
  intro c
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hn)
  refine ⟨k, S, hS, ?_⟩
  intro t ht htS
  have := card_le_card htS
  omega

/-- At positive uniformity a zero demand is met by the empty vertex set. -/
theorem hypergraphRamseyProp_of_eq_zero (hm : 0 < m) {k : K} (hk : f k = 0) :
    HypergraphRamseyProp m f n :=
  hypergraphRamseyProp_of_lt_uniformity (hk ▸ hm) (by simp [hk])

/-- At uniformity zero the property holds exactly when every demand fits in the vertex set. -/
@[simp]
theorem hypergraphRamseyProp_zero_uniformity_iff :
    HypergraphRamseyProp 0 f n ↔ ∀ k, f k ≤ n := by
  constructor
  · intro h k
    obtain ⟨j, S, hS, hc⟩ := h (fun _ ↦ k)
    have hj : k = j := hc ∅ (by simp) (empty_subset _)
    subst j
    simpa [hS] using S.card_le_univ
  · intro h c
    let k := c ⟨∅, by simp⟩
    obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n)))
      (by simpa using h k)
    refine ⟨k, S, hS, ?_⟩
    intro t ht _
    have : t = ∅ := card_eq_zero.1 ht
    subst t
    rfl

/-- The recursive step in uniformity: homogeneous `m`-subsets around one extra vertex reduce
one colour's demand for `(m + 1)`-subsets by one. -/
theorem hypergraphRamseyProp_succ [DecidableEq K] {g : K → ℕ}
    (h : ∀ k, HypergraphRamseyProp (m + 1) (Function.update f k (f k - 1)) (g k))
    (hN : HypergraphRamseyProp m g N) : HypergraphRamseyProp (m + 1) f (N + 1) := by
  by_cases h0 : ∃ k, f k = 0
  · obtain ⟨k, hk⟩ := h0
    exact hypergraphRamseyProp_of_eq_zero (by omega) hk
  push Not at h0
  intro c
  let e : Fin N ↪ Fin (N + 1) := Fin.succEmb N
  let d : {t : Finset (Fin N) // #t = m} → K := fun t ↦
    c ⟨insert 0 (t.val.map e), by simp [e, t.property]⟩
  obtain ⟨k, S, hS, hd⟩ := hN d
  obtain ⟨j, T, hTS, hT, hc⟩ :=
    (h k).exists_monochromatic_subset c (A := S.map e) (by simpa using hS.ge)
  by_cases hj : j = k
  · subst j
    have hzero : (0 : Fin (N + 1)) ∉ T := by
      intro hmem
      have := hTS hmem
      simp [e] at this
    refine ⟨k, insert 0 T, ?_, ?_⟩
    · rw [card_insert_of_notMem hzero, hT, Function.update_self]
      exact Nat.sub_add_cancel (Nat.pos_of_ne_zero (h0 k))
    · intro t ht htT
      by_cases ht0 : 0 ∈ t
      · have hsub : t.erase 0 ⊆ T := by
          intro x hx
          exact (mem_insert.mp (htT (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
        obtain ⟨u, hu, heq⟩ := subset_map_iff.1 (hsub.trans hTS)
        have hu_card : #u = m := by
          have := card_erase_add_one ht0
          rw [heq, card_map, ht] at this
          omega
        have heq' : insert 0 (u.map e) = t := by rw [← heq, insert_erase ht0]
        simpa only [d, heq'] using hd u hu_card hu
      · apply hc t ht
        intro x hx
        exact (mem_insert.mp (htT hx)).resolve_left (fun hx0 ↦ ht0 (hx0 ▸ hx))
  · refine ⟨j, T, ?_, hc⟩
    simpa [Function.update_of_ne hj] using hT

/-- **Finite Ramsey's theorem for uniform hypergraphs**: every demand in finitely many colours
is met on some finite vertex set, at every uniformity. -/
theorem exists_hypergraphRamseyProp [Finite K] (m : ℕ) (f : K → ℕ) :
    ∃ n, HypergraphRamseyProp m f n := by
  classical
  let := Fintype.ofFinite K
  induction m generalizing f with
  | zero =>
    exact ⟨univ.sup f, hypergraphRamseyProp_zero_uniformity_iff.2 fun k ↦ le_sup (mem_univ k)⟩
  | succ m ihm =>
    suffices ∀ s, ∀ f : K → ℕ, (∑ k, f k) = s → ∃ n, HypergraphRamseyProp (m + 1) f n from
      this _ f rfl
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro f hs
      by_cases h0 : ∃ k, f k = 0
      · obtain ⟨k, hk⟩ := h0
        exact ⟨0, hypergraphRamseyProp_of_eq_zero (by omega) hk⟩
      push Not at h0
      have key (k : K) : ∃ n,
          HypergraphRamseyProp (m + 1) (Function.update f k (f k - 1)) n := by
        refine ih _ ?_ _ rfl
        rw [sum_update_of_mem (mem_univ k), sdiff_singleton_eq_erase]
        have := sum_erase_add univ f (mem_univ k)
        have := h0 k
        omega
      choose g hg using key
      obtain ⟨N, hN⟩ := ihm g
      exact ⟨N + 1, hypergraphRamseyProp_succ hg hN⟩

/-- For finitely many colours, the hypergraph Ramsey number has the hypergraph Ramsey property. -/
theorem hypergraphRamseyProp_hypergraphRamseyNumber [Finite K] (m : ℕ) (f : K → ℕ) :
    HypergraphRamseyProp m f (hypergraphRamseyNumber m f) :=
  Nat.sInf_mem (s := {n | HypergraphRamseyProp m f n}) (exists_hypergraphRamseyProp m f)

/-- **The finite hypergraph Ramsey theorem** in least-number form: with finitely many colours,
the property holds exactly from the hypergraph Ramsey number onward. -/
theorem hypergraphRamseyProp_iff [Finite K] :
    HypergraphRamseyProp m f n ↔ hypergraphRamseyNumber m f ≤ n :=
  ⟨HypergraphRamseyProp.hypergraphRamseyNumber_le,
    (hypergraphRamseyProp_hypergraphRamseyNumber m f).mono⟩

/-- The Szekeres upper bound: the Ramsey numbers for lowered demands at uniformity `m + 1`
serve as demands at uniformity `m`, with one extra vertex. -/
theorem hypergraphRamseyNumber_succ_le [Finite K] [DecidableEq K] (m : ℕ) (f : K → ℕ) :
    hypergraphRamseyNumber (m + 1) f ≤ 1 + hypergraphRamseyNumber m
      (fun k ↦ hypergraphRamseyNumber (m + 1) (Function.update f k (f k - 1))) := by
  rw [Nat.add_comm 1]
  exact (hypergraphRamseyProp_succ
    (fun k ↦ hypergraphRamseyProp_hypergraphRamseyNumber (m + 1) _)
    (hypergraphRamseyProp_hypergraphRamseyNumber m _)).hypergraphRamseyNumber_le

/-- At uniformity zero the Ramsey number is the largest demand, with value zero for no colours. -/
@[simp]
theorem hypergraphRamseyNumber_zero_uniformity [Fintype K] (f : K → ℕ) :
    hypergraphRamseyNumber 0 f = univ.sup f := by
  apply le_antisymm
  · apply HypergraphRamseyProp.hypergraphRamseyNumber_le
    exact hypergraphRamseyProp_zero_uniformity_iff.2 fun k ↦ le_sup (mem_univ k)
  · exact Finset.sup_le fun k _ ↦ hypergraphRamseyProp_zero_uniformity_iff.1
      (hypergraphRamseyProp_hypergraphRamseyNumber 0 f) k

/-- At positive uniformity a zero demand makes the Ramsey number zero. -/
theorem hypergraphRamseyNumber_of_eq_zero (hm : 0 < m) {k : K} (hk : f k = 0) :
    hypergraphRamseyNumber m f = 0 :=
  Nat.eq_zero_of_le_zero (hypergraphRamseyProp_of_eq_zero hm hk).hypergraphRamseyNumber_le

/-- With no colours the hypergraph Ramsey property holds exactly when an `m`-element subset
exists: such a subset makes a colouring impossible. -/
@[simp]
theorem hypergraphRamseyProp_of_isEmpty_iff [IsEmpty K] :
    HypergraphRamseyProp m f n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    have c : {t : Finset (Fin n) // #t = m} → K := fun t ↦ False.elim (by
      have := t.val.card_le_univ
      simp only [Fintype.card_fin, t.property] at this
      exact hn this)
    obtain ⟨k, -⟩ := h c
    exact isEmptyElim k
  · intro hn c
    obtain ⟨t, -, ht⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hn)
    exact isEmptyElim (c ⟨t, ht⟩)

/-- With no colours the hypergraph Ramsey number equals the uniformity. -/
@[simp]
theorem hypergraphRamseyNumber_of_isEmpty [IsEmpty K] (m : ℕ) (f : K → ℕ) :
    hypergraphRamseyNumber m f = m := by
  apply le_antisymm (hypergraphRamseyProp_of_isEmpty_iff.2 le_rfl).hypergraphRamseyNumber_le
  exact hypergraphRamseyProp_of_isEmpty_iff.1 (hypergraphRamseyProp_hypergraphRamseyNumber m f)

/-- For one colour the property holds exactly when the demand fits in the vertex set,
independently of the uniformity. -/
@[simp]
theorem hypergraphRamseyProp_of_unique_iff [Unique K] :
    HypergraphRamseyProp m f n ↔ f default ≤ n := by
  constructor
  · intro h
    obtain ⟨k, S, hS, -⟩ := h (fun _ ↦ default)
    simpa [Unique.eq_default k, hS] using S.card_le_univ
  · intro hn c
    obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hn)
    exact ⟨default, S, hS, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- With one colour the hypergraph Ramsey number is the demand, at every uniformity. -/
@[simp]
theorem hypergraphRamseyNumber_of_unique [Unique K] (m : ℕ) (f : K → ℕ) :
    hypergraphRamseyNumber m f = f default := by
  apply le_antisymm (hypergraphRamseyProp_of_unique_iff.2 le_rfl).hypergraphRamseyNumber_le
  exact hypergraphRamseyProp_of_unique_iff.1 (hypergraphRamseyProp_hypergraphRamseyNumber m f)

end TauCeti
