/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fin.VecNotation
public import TauCeti.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Tactic.FinCases

/-!
# Ramsey numbers of complete graphs

For a type of colours `K` and a demand `f : K → ℕ`, the Ramsey property `RamseyProp f n` says that
every colouring of the edges of the complete graph on `Fin n` with colours in `K` (a
`SimpleGraph.TopEdgeLabeling (Fin n) K`) has, for some colour `k`, a set of `f k` vertices any two
of which are joined by an edge of colour `k`, that is, an `f k`-clique of `C.labelGraph k`. The
Ramsey number `ramseyNumber f` is the infimum in `ℕ` of the `n` with this property. The
two-colour Ramsey number `R(s, t)` is `ramseyNumber ![s, t]`.

Sets of zero or one vertex count as monochromatic, so the degenerate values are fixed by the
definition: for finitely many colours the number is `0` exactly when some demand is `0`
(`TauCeti.ramseyNumber_eq_zero_iff`), `1` exactly when every demand is positive and one of them is
`1` (`TauCeti.ramseyNumber_eq_one_iff`), `2` when there are no colours
(`TauCeti.ramseyNumber_of_isEmpty`), the demand itself for one colour
(`TauCeti.ramseyNumber_of_unique`), and `R(2, t) = t` (`TauCeti.ramseyNumber_two_left`).

## Main results

* `TauCeti.RamseyProp.exists_isNClique_subset`: the property on `m` vertices gives a monochromatic
  clique inside every set of at least `m` vertices of a coloured complete graph, on any vertex
  type; in particular the property is upward closed (`TauCeti.RamseyProp.mono`).
* `TauCeti.RamseyProp.exists_isNClique_of_le_degree`: a large enough neighbourhood in colour `k`
  for the lowered Ramsey property yields a clique for the original demand.
* `TauCeti.ramseyProp_succ_of_sum_lt`: the recursive step of Greenwood and Gleason, stated for the
  property: if `RamseyProp (f − eₖ) (n k)` for each colour `k`, then `RamseyProp f (N + 1)` as soon
  as `∑ₖ (n k − 1) < N`.
* `TauCeti.ramseyProp_iff_ramseyNumber_le`: the finite Ramsey theorem. For finitely many colours,
  `RamseyProp f n` holds exactly when `ramseyNumber f ≤ n`.
* `TauCeti.ramseyNumber_comp_equiv`: relabelling the colours by a bijection does not change the
  Ramsey number; in particular `R(s, t) = R(t, s)` (`TauCeti.ramseyNumber_comm`).
* `TauCeti.ramseyProp_iff_forall_isNIndepSet_or_isNClique`: for two colours, the property says that
  every graph on `n` vertices has an independent set of `s` vertices or a clique of `t` vertices.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs*, Canadian
  Journal of Mathematics 7 (1955), 1–7: the definition (§1), Theorem 2 and Corollary 2 for the
  recursive step and the existence of the numbers.
* S. P. Radziszowski, *Small Ramsey numbers*, Electronic Journal of Combinatorics, Dynamic Survey
  DS1, §1.
* R. Diestel, *Graph Theory*, Theorems 9.1.1 and 9.1.3.
-/

public section

open Finset SimpleGraph

namespace TauCeti

variable {K K' : Type*} {f : K → ℕ} {m n : ℕ}

/-- The Ramsey property `RamseyProp f n`: every colouring of the edges of the complete graph on `n`
vertices with colours in `K` has, for some colour `k`, a set of `f k` vertices all of whose edges
have colour `k`. -/
def RamseyProp (f : K → ℕ) (n : ℕ) : Prop :=
  ∀ C : TopEdgeLabeling (Fin n) K, ∃ k, ∃ s : Finset (Fin n), (C.labelGraph k).IsNClique (f k) s

/-- Unfolding the Ramsey property. -/
theorem ramseyProp_iff : RamseyProp f n ↔ ∀ C : TopEdgeLabeling (Fin n) K,
    ∃ k, ∃ s : Finset (Fin n), (C.labelGraph k).IsNClique (f k) s :=
  Iff.rfl

/-- The Ramsey number `R(f)`: the infimum in `ℕ` of the numbers of vertices with the Ramsey
property. For finitely many colours it is the least such number, and the property holds exactly
from it on (`ramseyProp_iff_ramseyNumber_le`). -/
noncomputable def ramseyNumber (f : K → ℕ) : ℕ :=
  sInf {n | RamseyProp f n}

/-- Unfolding the Ramsey number. -/
theorem ramseyNumber_def (f : K → ℕ) : ramseyNumber f = sInf {n | RamseyProp f n} :=
  (rfl)

/-- The Ramsey number is at most every number of vertices with the Ramsey property. -/
theorem RamseyProp.ramseyNumber_le (h : RamseyProp f n) : ramseyNumber f ≤ n :=
  Nat.sInf_le h

/-- If the Ramsey property holds on `m` vertices, then in every colouring of the edges of a complete
graph, every set of at least `m` vertices contains, for some colour `k`, a set of `f k` vertices all
of whose edges have colour `k`. -/
theorem RamseyProp.exists_isNClique_subset {V : Type*} (h : RamseyProp f m)
    (C : TopEdgeLabeling V K) {A : Finset V} (hA : m ≤ #A) :
    ∃ k, ∃ s ⊆ A, (C.labelGraph k).IsNClique (f k) s := by
  let e : Fin m ↪ V :=
    (Fin.castLEEmb hA).trans (A.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _))
  obtain ⟨k, s, hs⟩ := h (C.pullback e)
  refine ⟨k, s.map e, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    simp [e]
  · rw [TopEdgeLabeling.labelGraph_pullback] at hs
    exact hs.map.mono (map_comap_le _ _)

/-- If the Ramsey property holds on `m` vertices, then every colouring of the edges of a complete
graph on at least `m` vertices has, for some colour `k`, a set of `f k` vertices all of whose edges
have colour `k`. -/
theorem RamseyProp.exists_isNClique {V : Type*} [Fintype V] (h : RamseyProp f m)
    (C : TopEdgeLabeling V K) (hV : m ≤ Fintype.card V) :
    ∃ k, ∃ s : Finset V, (C.labelGraph k).IsNClique (f k) s :=
  let ⟨k, s, _, hs⟩ := h.exists_isNClique_subset C (A := univ) (by simpa using hV)
  ⟨k, s, hs⟩

/-- If the lowered Ramsey property holds on `m` vertices and the `k`-coloured neighbourhood of `v`
has at least `m` vertices, then the colouring contains a monochromatic clique meeting `f`. -/
theorem RamseyProp.exists_isNClique_of_le_degree {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq K]
    {v : V} {k : K} (h : RamseyProp (Function.update f k (f k - 1)) m)
    (C : TopEdgeLabeling V K) (hv : m ≤ (C.labelGraph k).degree v) :
    ∃ j s, (C.labelGraph j).IsNClique (f j) s := by
  obtain ⟨j, s, hsA, hs⟩ := h.exists_isNClique_subset C (A := (C.labelGraph k).neighborFinset v) hv
  obtain rfl | hjk := eq_or_ne j k
  · obtain hj | hj := eq_or_ne (f j) 0
    · exact ⟨j, ∅, by simp [hj]⟩
    rw [Function.update_self] at hs
    refine ⟨j, insert v s, ?_⟩
    rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj)]
    exact hs.insert fun w hw ↦ by simpa using hsA hw
  · rw [Function.update_of_ne hjk] at hs
    exact ⟨j, s, hs⟩

/-- The Ramsey property is upward closed in the number of vertices. -/
theorem RamseyProp.mono (h : RamseyProp f m) (hmn : m ≤ n) : RamseyProp f n := fun C ↦
  h.exists_isNClique C (by simpa using hmn)

/-- A demand of `0` is met by the empty set, so the Ramsey property holds on any number of
vertices. -/
theorem ramseyProp_of_eq_zero {k : K} (hk : f k = 0) : RamseyProp f n := fun _ ↦
  ⟨k, ∅, by simp [hk]⟩

/-- The Ramsey property holds on no vertices exactly when some demand is `0`. -/
theorem ramseyProp_zero_iff : RamseyProp f 0 ↔ ∃ k, f k = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ramseyProp_of_eq_zero hk⟩
  obtain ⟨k, s, hs⟩ := h (EdgeLabeling.mk (fun x _ _ ↦ x.elim0) fun x ↦ x.elim0)
  exact ⟨k, by simpa [hs.card_eq] using s.card_le_univ⟩

/-- The Ramsey property holds on one vertex exactly when some demand is at most `1`. -/
theorem ramseyProp_one_iff : RamseyProp f 1 ↔ ∃ k, f k ≤ 1 := by
  constructor
  · intro h
    obtain ⟨k, s, hs⟩ :=
      h (EdgeLabeling.mk (fun x y h ↦ (h (Subsingleton.elim x y)).elim) fun _ _ h ↦
        (h.symm (Subsingleton.elim _ _)).elim)
    exact ⟨k, by simpa [hs.card_eq] using s.card_le_univ⟩
  · rintro ⟨k, hk⟩ _
    obtain hk | hk := Nat.le_one_iff_eq_zero_or_eq_one.1 hk
    · exact ⟨k, ∅, by simp [hk]⟩
    · exact ⟨k, {0}, by simp [hk]⟩

/-- **The recursive step of Greenwood and Gleason**, for the Ramsey property. Suppose that for each
colour `k`, the property holds on `n k` vertices for the demand `f − eₖ`, which lowers the demand of
`k` by one. Then the property holds for `f` on `N + 1` vertices as soon as `∑ₖ (n k − 1) < N`. -/
theorem ramseyProp_succ_of_sum_lt [Fintype K] [DecidableEq K] {n : K → ℕ} {N : ℕ}
    (h : ∀ k, RamseyProp (Function.update f k (f k - 1)) (n k)) (hN : ∑ k, (n k - 1) < N) :
    RamseyProp f (N + 1) := by
  intro C
  have hcard : ∑ k, (C.labelGraph k).degree 0 = N := by
    rw [TopEdgeLabeling.sum_degree_labelGraph]
    simp
  obtain ⟨k, -, hk⟩ := exists_lt_of_sum_lt (hN.trans_eq hcard.symm)
  exact (h k).exists_isNClique_of_le_degree (v := 0) C (by omega)

/-- **Ramsey's theorem** for complete graphs, in finitely many colours: for every demand, the
Ramsey property holds on some number of vertices. -/
theorem exists_ramseyProp [Finite K] (f : K → ℕ) : ∃ n, RamseyProp f n := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨s, hs⟩ : ∃ s, ∑ k, f k = s := ⟨_, rfl⟩
  induction s using Nat.strong_induction_on generalizing f with
  | _ s ih =>
    by_cases h0 : ∃ k, f k = 0
    · obtain ⟨k, hk⟩ := h0
      exact ⟨0, ramseyProp_of_eq_zero hk⟩
    push Not at h0
    have key (k : K) : ∃ n, RamseyProp (Function.update f k (f k - 1)) n := by
      refine ih _ (hs ▸ sum_lt_sum (fun i _ ↦ ?_) ⟨k, mem_univ _, ?_⟩) _ rfl
      · rw [Function.update_apply]
        split_ifs with hik
        · rw [hik]
          omega
        · exact le_rfl
      · rw [Function.update_self]
        have := h0 k
        omega
    choose n hn using key
    exact ⟨_, ramseyProp_succ_of_sum_lt hn (Nat.lt_succ_self _)⟩

/-- For finitely many colours, the Ramsey property holds on `ramseyNumber f` vertices. -/
theorem ramseyProp_ramseyNumber [Finite K] (f : K → ℕ) : RamseyProp f (ramseyNumber f) :=
  Nat.sInf_mem (s := {n | RamseyProp f n}) (exists_ramseyProp f)

/-- **The finite Ramsey theorem** for complete graphs: for finitely many colours, the Ramsey
property holds on `n` vertices exactly when `n` is at least the Ramsey number. So the Ramsey number
is the least number of vertices with the property, and the property persists for all larger
numbers. -/
theorem ramseyProp_iff_ramseyNumber_le [Finite K] : RamseyProp f n ↔ ramseyNumber f ≤ n :=
  ⟨RamseyProp.ramseyNumber_le, (ramseyProp_ramseyNumber f).mono⟩

/-- For finitely many colours, every colouring of the edges of a complete graph on at least
`ramseyNumber f` vertices has, for some colour `k`, a set of `f k` vertices all of whose edges have
colour `k`. -/
theorem exists_isNClique_of_ramseyNumber_le [Finite K] {V : Type*} [Fintype V]
    (C : TopEdgeLabeling V K) (hV : ramseyNumber f ≤ Fintype.card V) :
    ∃ k, ∃ s : Finset V, (C.labelGraph k).IsNClique (f k) s :=
  (ramseyProp_ramseyNumber f).exists_isNClique C hV

/-- For finitely many colours, the Ramsey number is `0` exactly when some demand is `0`. -/
theorem ramseyNumber_eq_zero_iff [Finite K] : ramseyNumber f = 0 ↔ ∃ k, f k = 0 := by
  rw [← Nat.le_zero, ← ramseyProp_iff_ramseyNumber_le, ramseyProp_zero_iff]

/-- For finitely many colours, the Ramsey number is positive exactly when every demand is
positive. -/
theorem ramseyNumber_pos_iff [Finite K] : 0 < ramseyNumber f ↔ ∀ k, 0 < f k := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ramseyNumber_eq_zero_iff]
  simp only [not_exists, Nat.pos_iff_ne_zero]

/-- For finitely many colours, the Ramsey number is at most `1` exactly when some demand is at
most `1`. -/
theorem ramseyNumber_le_one_iff [Finite K] : ramseyNumber f ≤ 1 ↔ ∃ k, f k ≤ 1 := by
  rw [← ramseyProp_iff_ramseyNumber_le, ramseyProp_one_iff]

/-- For finitely many colours, the Ramsey number is `1` exactly when every demand is positive and
some demand is `1`. -/
theorem ramseyNumber_eq_one_iff [Finite K] :
    ramseyNumber f = 1 ↔ (∀ k, f k ≠ 0) ∧ ∃ k, f k = 1 := by
  constructor
  · intro h
    have h0 (k : K) : f k ≠ 0 := fun hk ↦ by simpa [h] using ramseyNumber_eq_zero_iff.2 ⟨k, hk⟩
    obtain ⟨k, hk⟩ := ramseyNumber_le_one_iff.1 h.le
    exact ⟨h0, k, by have := h0 k; omega⟩
  · rintro ⟨h0, k, hk⟩
    have h1 := ramseyNumber_le_one_iff.2 ⟨k, hk.le⟩
    have h2 : ramseyNumber f ≠ 0 := fun h ↦
      let ⟨j, hj⟩ := ramseyNumber_eq_zero_iff.1 h
      h0 j hj
    omega

/-- With no colours the Ramsey number is `2`. -/
@[simp]
theorem ramseyNumber_of_isEmpty [IsEmpty K] (f : K → ℕ) : ramseyNumber f = 2 := by
  refine le_antisymm (RamseyProp.ramseyNumber_le fun C ↦ isEmptyElim (C.get 0 1 (by simp))) ?_
  by_contra h
  simpa using ramseyNumber_le_one_iff.1 (Nat.le_of_lt_succ (not_le.1 h))

/-- With one colour the Ramsey number is the demand. -/
@[simp]
theorem ramseyNumber_of_unique [Unique K] (f : K → ℕ) : ramseyNumber f = f default := by
  have key {n : ℕ} : RamseyProp f n ↔ f default ≤ n := by
    constructor
    · intro h
      obtain ⟨k, s, hs⟩ := h (EdgeLabeling.mk (fun _ _ _ ↦ default) fun _ _ _ ↦ rfl)
      simpa [Unique.eq_default k, hs.card_eq] using s.card_le_univ
    · intro h C
      obtain ⟨s, -, hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using h)
      refine ⟨default, s, ⟨fun x _ y _ hxy ↦ ?_, hs⟩⟩
      simpa using ⟨hxy, Subsingleton.elim _ _⟩
  refine le_antisymm (key.2 le_rfl).ramseyNumber_le ?_
  rw [← key]
  exact ramseyProp_ramseyNumber f

private theorem RamseyProp.of_comp_equiv (e : K' ≃ K) (h : RamseyProp (f ∘ e) n) :
    RamseyProp f n := by
  intro C
  obtain ⟨k, s, hs⟩ := h (C.compRight e.symm)
  have hC := C.labelGraph_compRight_of_injective e.symm.injective (e k)
  rw [e.symm_apply_apply] at hC
  exact ⟨e k, s, hC ▸ hs⟩

/-- Relabelling the colours by a bijection does not change the Ramsey property. -/
@[simp]
theorem ramseyProp_comp_equiv (e : K' ≃ K) : RamseyProp (f ∘ e) n ↔ RamseyProp f n := by
  refine ⟨.of_comp_equiv e, fun h ↦ .of_comp_equiv e.symm ?_⟩
  rwa [Function.comp_assoc, e.self_comp_symm, Function.comp_id]

/-- Relabelling the colours by a bijection does not change the Ramsey number. -/
@[simp]
theorem ramseyNumber_comp_equiv (f : K → ℕ) (e : K' ≃ K) :
    ramseyNumber (f ∘ e) = ramseyNumber f := by
  simp only [ramseyNumber, ramseyProp_comp_equiv]

/-- The two-colour Ramsey number is symmetric: `R(s, t) = R(t, s)`. -/
theorem ramseyNumber_comm (s t : ℕ) : ramseyNumber ![s, t] = ramseyNumber ![t, s] := by
  rw [← ramseyNumber_comp_equiv ![s, t] (Equiv.swap 0 1)]
  congr 1
  ext i
  fin_cases i <;> simp

/-- For two colours, the Ramsey property says that every simple graph on `n` vertices has an
independent set of `s` vertices or a clique of `t` vertices: colour `0` is a non-edge and colour
`1` an edge. -/
theorem ramseyProp_iff_forall_isNIndepSet_or_isNClique {s t : ℕ} :
    RamseyProp ![s, t] n ↔
      ∀ G : SimpleGraph (Fin n), (∃ u, G.IsNIndepSet s u) ∨ ∃ u, G.IsNClique t u := by
  classical
  constructor
  · intro h G
    obtain ⟨k, u, hu⟩ := h G.toTopEdgeLabeling
    fin_cases k
    · exact .inl ⟨u, by simpa using hu⟩
    · exact .inr ⟨u, by simpa using hu⟩
  · intro h C
    have hC := toTopEdgeLabeling_labelGraph_compl (C.labelGraph 1)
    rw [C.labelGraph_toTopEdgeLabeling] at hC
    obtain ⟨u, hu⟩ | ⟨u, hu⟩ := h (C.labelGraph 1)
    · exact ⟨0, u, by simpa [hC] using hu⟩
    · exact ⟨1, u, by simpa using hu⟩

/-- The Ramsey property for the two-colour demand `(2, t)` holds exactly on at least `t`
vertices. -/
theorem ramseyProp_two_left_iff {t : ℕ} : RamseyProp ![2, t] n ↔ t ≤ n := by
  rw [ramseyProp_iff_forall_isNIndepSet_or_isNClique]
  constructor
  · intro h
    obtain ⟨u, hu⟩ | ⟨u, hu⟩ := h ⊤
    · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hu.card_eq
      exact absurd (hu.isIndepSet (by simp) (by simp) hxy) (by simpa using hxy)
    · simpa [hu.card_eq] using u.card_le_univ
  · intro ht G
    by_cases hG : ∃ x y, x ≠ y ∧ ¬G.Adj x y
    · obtain ⟨x, y, hxy, hadj⟩ := hG
      refine .inl ⟨{x, y}, ⟨?_, card_pair hxy⟩⟩
      simp [isIndepSet_iff, Set.pairwise_pair, hadj, G.adj_comm]
    · push Not at hG
      obtain ⟨u, -, hu⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using ht)
      exact .inr ⟨u, ⟨fun x _ y _ hxy ↦ hG x y hxy, hu⟩⟩

/-- `R(2, t) = t`. -/
@[simp]
theorem ramseyNumber_two_left (t : ℕ) : ramseyNumber ![2, t] = t :=
  le_antisymm (ramseyProp_two_left_iff.2 le_rfl).ramseyNumber_le
    (ramseyProp_two_left_iff.1 (ramseyProp_ramseyNumber _))

/-- `R(s, 2) = s`. -/
@[simp]
theorem ramseyNumber_two_right (s : ℕ) : ramseyNumber ![s, 2] = s := by
  rw [ramseyNumber_comm, ramseyNumber_two_left]

end TauCeti
