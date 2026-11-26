/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Combinatorics.SimpleGraph.Backtracking
import Mathlib.Data.Set.Finite.List

/-!
# The Hashimoto matrix of a simple graph

The Hashimoto matrix, or non-backtracking edge matrix, of a simple graph is indexed by its darts:
the entry at `(a, b)` is `1` when `a` ends where `b` starts and `b` is not the reverse of `a`, and
`0` otherwise. Its powers count the walks that never step straight back along the dart they
arrived on. In particular, for `m ≥ 1`, the trace of its `m`-th power is the number `N_m` of
closed non-backtracking walks of length `m` that do not backtrack across their closing step either,
each counted with its starting vertex. These numbers are the coefficients of the logarithmic
derivative of the Ihara zeta function of the graph, which is how the trace formula below turns into
the determinant formula `ζ(u) = det(1 - u B)⁻¹`.

## Main definitions

* `SimpleGraph.hashimotoMatrix R G`: the Hashimoto matrix of `G` with entries in `R`.
* `SimpleGraph.NonBacktrackingDartSeq k a b`: the sequences `a = d₀, d₁, …, d_k = b` of
  non-backtracking adjacent darts.
* `SimpleGraph.closedNonBacktrackingCount G m`: the number `N_m` of closed non-backtracking walks
  of length `m` (`SimpleGraph.Walk.IsNonBacktrackingCycle`), each counted with its starting vertex.

## Main results

* `SimpleGraph.sum_row_hashimotoMatrix`, `SimpleGraph.sum_col_hashimotoMatrix`: the row of a dart
  `a` sums to `deg a.snd - 1` and the column of a dart `b` sums to `deg b.fst - 1`.
* `SimpleGraph.hashimotoMatrix_pow_apply`: the entry `(Bᵏ) a b` is the number of sequences of darts
  `a = d₀, d₁, …, d_k = b` in which each dart ends where the next starts and is not followed by its
  reverse.
* `SimpleGraph.trace_hashimotoMatrix_pow`: for `m ≠ 0`, `tr Bᵐ = N_m`. For `m = 0` the trace is
  the number of darts, while `N₀` is the number of vertices (`closedNonBacktrackingCount_zero`).

## References

* K. Hashimoto, *Zeta functions of finite graphs and representations of p-adic groups*, in
  Automorphic Forms and Geometry of Arithmetic Varieties, Adv. Stud. Pure Math. 15 (1989), 211–280.
* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge Studies in Advanced
  Mathematics 128, Cambridge University Press, 2011: the edge adjacency matrix `W₁` and the trace
  formula for its powers.
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The sequences of darts `a = d₀, d₁, …, d_k = b` in which each dart ends where the next starts
and is not followed by its reverse (`SimpleGraph.NonBacktrackingDartAdj`), recorded as the list `l`
of the `k` darts after `a`. -/
abbrev NonBacktrackingDartSeq (k : ℕ) (a b : G.Dart) : Type _ :=
  {l : List G.Dart // l.length = k ∧ (a :: l).IsChain G.NonBacktrackingDartAdj ∧
    (a :: l).getLast (List.cons_ne_nil a l) = b}

/-- The number `N_m` of closed non-backtracking walks of length `m`
(`SimpleGraph.Walk.IsNonBacktrackingCycle`), each counted with its starting vertex: a primitive
cycle of length `m ≥ 1` traversed in one direction contributes `m` walks, one for each starting
point. -/
noncomputable def closedNonBacktrackingCount (G : SimpleGraph V) (m : ℕ) : ℕ :=
  Nat.card {c : Σ u : V, G.Walk u u // c.2.length = m ∧ c.2.IsNonBacktrackingCycle}

/-- The closed walks of length zero are the walks `nil`, one at each vertex. -/
theorem closedNonBacktrackingCount_zero (G : SimpleGraph V) :
    G.closedNonBacktrackingCount 0 = Nat.card V :=
  Nat.card_congr
    { toFun c := c.val.fst
      invFun u := ⟨⟨u, .nil⟩, rfl, Walk.isNonBacktrackingCycle_nil⟩
      left_inv := by
        rintro ⟨⟨u, _ | _⟩, hp, -⟩
        · rfl
        · simp at hp
      right_inv _ := rfl }

variable [DecidableEq V] (R : Type*) (G)

/-- The *Hashimoto matrix* (non-backtracking edge matrix) of a simple graph, indexed by its darts:
the entry at `(a, b)` is `1` if `a` ends where `b` starts and `b` is not the reverse of `a`, and `0`
otherwise. -/
def hashimotoMatrix [Zero R] [One R] : Matrix G.Dart G.Dart R :=
  of fun a b => if a.snd = b.fst ∧ b ≠ a.symm then 1 else 0

variable {R G}

@[simp]
theorem hashimotoMatrix_apply [Zero R] [One R] (a b : G.Dart) :
    G.hashimotoMatrix R a b = if a.snd = b.fst ∧ b ≠ a.symm then 1 else 0 :=
  (rfl)

/-- A dart is never followed by its reverse. -/
theorem hashimotoMatrix_apply_symm [Zero R] [One R] (a : G.Dart) :
    G.hashimotoMatrix R a a.symm = 0 := by
  simp

/-- Reversing two darts and swapping them does not change their entry. -/
theorem hashimotoMatrix_apply_symm_symm [Zero R] [One R] (a b : G.Dart) :
    G.hashimotoMatrix R b.symm a.symm = G.hashimotoMatrix R a b := by
  simp only [hashimotoMatrix_apply, Dart.symm_toProd, Prod.snd_swap, Dart.symm_symm]
  grind [Dart.symm_symm, Dart.fst_symm]

variable [Fintype V] [DecidableRel G.Adj]

/-- The row of a dart `a` sums to `deg a.snd - 1`: it is followed by every dart leaving its end
except its reverse. -/
theorem sum_row_hashimotoMatrix [AddCommMonoidWithOne R] (a : G.Dart) :
    ∑ b, G.hashimotoMatrix R a b = (G.degree a.snd - 1 : ℕ) := by
  simp only [hashimotoMatrix_apply, sum_boole]
  rw [← G.dart_fst_fiber_card_eq_degree a.snd,
    ← card_erase_of_mem (s := {d : G.Dart | d.fst = a.snd}) (a := a.symm) (by simp)]
  congr 2
  ext b
  simp [eq_comm, and_comm]

/-- The column of a dart `b` sums to `deg b.fst - 1`: it follows every dart entering its start
except its reverse. -/
theorem sum_col_hashimotoMatrix [AddCommMonoidWithOne R] (b : G.Dart) :
    ∑ a, G.hashimotoMatrix R a b = (G.degree b.fst - 1 : ℕ) := by
  have h (a : G.Dart) : G.hashimotoMatrix R a.symm b = G.hashimotoMatrix R b.symm a := by
    rw [← hashimotoMatrix_apply_symm_symm, Dart.symm_symm]
  rw [← Equiv.sum_comp (Dart.symm_involutive.toPerm _)]
  simp only [Function.Involutive.coe_toPerm, h, sum_row_hashimotoMatrix]
  rw [← Dart.fst_symm b.symm, Dart.symm_symm]

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- There are finitely many sequences of `k` darts after a given dart, as there are finitely many
lists of darts of length `k`. -/
instance [Finite G.Dart] (k : ℕ) (a b : G.Dart) : Finite (NonBacktrackingDartSeq k a b) :=
  have := (List.finite_length_eq G.Dart k).to_subtype
  Finite.of_injective (fun l => (⟨l.val, l.property.1⟩ : {l : List G.Dart | l.length = k}))
    fun _ _ h => Subtype.ext (by simpa using h)

/-- The entry `(Bᵏ) a b` of a power of the Hashimoto matrix is the number of sequences of darts
`a = d₀, d₁, …, d_k = b` in which each dart ends where the next starts and is not followed by its
reverse, here written `a :: l`. -/
theorem hashimotoMatrix_pow_apply [Semiring R] (k : ℕ) (a b : G.Dart) :
    (G.hashimotoMatrix R ^ k) a b = Nat.card (NonBacktrackingDartSeq k a b) := by
  induction k generalizing a with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [Nat.card_eq_one_iff_exists.mpr ⟨⟨[], rfl, by simp, rfl⟩, fun ⟨l, hl, _⟩ =>
        Subtype.ext (List.eq_nil_of_length_eq_zero hl)⟩, Nat.cast_one]
    · have : IsEmpty (NonBacktrackingDartSeq 0 a b) :=
        ⟨fun ⟨l, hl, _, hb⟩ => h (by simpa [List.eq_nil_of_length_eq_zero hl] using hb)⟩
      rw [Nat.card_of_isEmpty, Nat.cast_zero]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, hashimotoMatrix_apply, boole_mul]
    rw [← sum_filter, sum_subtype _ (fun _ => mem_filter_univ _), ← Nat.cast_sum,
      ← Nat.card_sigma]
    congr 1
    -- A sequence of `k + 1` darts after `a` is its first dart `c`, which may follow `a`, and a
    -- sequence of `k` darts after `c`.
    refine Nat.card_eq_of_bijective (fun ⟨⟨c, hac⟩, ⟨l, hl, hc, hb⟩⟩ =>
      ⟨c :: l, by simp [hl], List.isChain_cons_cons.mpr ⟨hac, hc⟩, by simpa using hb⟩) ⟨?_, ?_⟩
    · rintro ⟨⟨c₁, h₁⟩, ⟨l₁, _⟩⟩ ⟨⟨c₂, h₂⟩, ⟨l₂, _⟩⟩ h
      simp only [Subtype.mk.injEq, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · rintro ⟨_ | ⟨c, l⟩, hl, hc, hb⟩
      · simp at hl
      · rw [List.isChain_cons_cons] at hc
        exact ⟨⟨⟨c, hc.1⟩, ⟨l, by simpa using hl, hc.2, by simpa using hb⟩⟩, rfl⟩

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- A sequence `a, d₁, …, d_k, a` of darts in which each dart ends where the next starts and is not
followed by its reverse lists the darts of a closed non-backtracking walk at the start of `a`,
followed by `a` again. -/
private theorem exists_isNonBacktrackingCycle_darts {a : G.Dart} {l : List G.Dart} (hl : l ≠ [])
    (hc : (a :: l).IsChain G.NonBacktrackingDartAdj)
    (hb : (a :: l).getLast (List.cons_ne_nil a l) = a) :
    ∃ p : G.Walk a.fst a.fst, p.IsNonBacktrackingCycle ∧ p.darts ++ p.darts.take 1 = a :: l := by
  have hsplit : a :: l = (a :: l.dropLast) ++ [a] := by
    rw [List.getLast_cons hl] at hb
    conv_lhs => rw [← List.dropLast_append_getLast hl, hb]
    rfl
  rw [hsplit] at hc ⊢
  obtain ⟨hD, -, hDa⟩ := List.isChain_append.mp hc
  have hlast : ((a :: l.dropLast).getLast (List.cons_ne_nil _ _)).snd = a.fst :=
    (hDa _ (List.getLast?_eq_some_getLast _) _ rfl).1
  let p : G.Walk a.fst a.fst :=
    (Walk.ofDarts _ (List.cons_ne_nil _ _) (hD.imp fun _ _ h => h.1)).copy rfl hlast
  have hpd : p.darts ++ p.darts.take 1 = (a :: l.dropLast) ++ [a] := by
    rw [show p.darts = a :: l.dropLast from (Walk.darts_copy _ _ _).trans (Walk.darts_ofDarts _ _)]
    simp
  exact ⟨p, (Walk.isNonBacktrackingCycle_iff_isChain p).mpr (hpd ▸ hc), hpd⟩

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- The closed non-backtracking walks of length `k + 1` correspond to the sequences
`a, d₁, …, d_k, a` of darts in which each dart ends where the next starts and is not followed by
its reverse: a walk is sent to its darts followed by its first dart again. -/
private theorem closedNonBacktrackingCount_add_one (k : ℕ) :
    G.closedNonBacktrackingCount (k + 1) =
      Nat.card (Σ a : G.Dart, NonBacktrackingDartSeq (k + 1) a a) := by
  -- `ψ` reads a sequence of darts as a list.
  let ψ : (Σ a : G.Dart, NonBacktrackingDartSeq (k + 1) a a) → List G.Dart :=
    fun ⟨a, l, _⟩ => a :: l
  have hψ : Function.Injective ψ := by
    rintro ⟨a, l, hl⟩ ⟨b, l', hl'⟩ h
    simp only [ψ, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hne {u : V} {p : G.Walk u u} (hp : p.length = k + 1) : p.darts ≠ [] := by
    rw [← List.length_pos_iff, Walk.length_darts, hp]
    exact k.succ_pos
  have hcons {u : V} {p : G.Walk u u} (hp : p.length = k + 1) :
      p.darts.head (hne hp) :: (p.darts ++ p.darts.take 1).tail = p.darts ++ p.darts.take 1 := by
    obtain ⟨d, l, hdl⟩ := List.exists_cons_of_ne_nil (hne hp)
    simp [hdl]
  -- `φ` sends a closed walk to its darts followed by its first dart again.
  let φ : {c : Σ u : V, G.Walk u u // c.2.length = k + 1 ∧ c.2.IsNonBacktrackingCycle} →
      Σ a : G.Dart, NonBacktrackingDartSeq (k + 1) a a := fun ⟨⟨_, p⟩, hp, hnb⟩ =>
    ⟨p.darts.head (hne hp), (p.darts ++ p.darts.take 1).tail, by simp [hp],
      by rw [hcons hp]; exact (Walk.isNonBacktrackingCycle_iff_isChain p).mp hnb,
      by simp only [hcons hp]; simp [List.take_one, List.head?_eq_some_head (hne hp)]⟩
  have hψφ {u : V} {p : G.Walk u u} (hp : p.length = k + 1) (hnb : p.IsNonBacktrackingCycle) :
      ψ (φ ⟨⟨u, p⟩, hp, hnb⟩) = p.darts ++ p.darts.take 1 :=
    hcons hp
  refine Nat.card_eq_of_bijective φ ⟨?_, fun ⟨a, l, hl, hc, hb⟩ => ?_⟩
  · -- A closed walk of positive length is determined by its darts, the first of which starts at
    -- its base vertex.
    rintro ⟨⟨u₁, p₁⟩, hp₁ : p₁.length = k + 1, hn₁ : p₁.IsNonBacktrackingCycle⟩
      ⟨⟨u₂, p₂⟩, hp₂ : p₂.length = k + 1, hn₂ : p₂.IsNonBacktrackingCycle⟩ h
    have hfst {u : V} {p : G.Walk u u} (hp : p.length = k + 1) : (p.darts.head (hne hp)).fst = u :=
      by simp
    obtain rfl : u₁ = u₂ :=
      (hfst hp₁).symm.trans ((congrArg (fun x => x.fst.fst) h).trans (hfst hp₂))
    have hd := (hψφ hp₁ hn₁).symm.trans ((congrArg ψ h).trans (hψφ hp₂ hn₂))
    obtain rfl := Walk.darts_injective (List.append_inj hd (by simp [hp₁, hp₂])).1
    rfl
  · have hl0 : l ≠ [] := by simp [← List.length_pos_iff, hl]
    obtain ⟨p, hp, hpd⟩ := exists_isNonBacktrackingCycle_darts hl0 hc hb
    have hlen : p.length = k + 1 := by
      have := congrArg List.length hpd
      grind [Walk.length_darts, List.length_append, List.length_take]
    exact ⟨⟨⟨a.fst, p⟩, hlen, hp⟩, hψ ((hψφ hlen hp).trans hpd)⟩

/-- **The trace formula.** For `m ≠ 0` the trace of the `m`-th power of the Hashimoto matrix is the
number `N_m` of closed non-backtracking walks of length `m`, each counted with its starting
vertex. For `m = 0` the trace is the number of darts, while `N₀` is the number of vertices
(`SimpleGraph.closedNonBacktrackingCount_zero`). -/
theorem trace_hashimotoMatrix_pow [Semiring R] {m : ℕ} (hm : m ≠ 0) :
    (G.hashimotoMatrix R ^ m).trace = G.closedNonBacktrackingCount m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  simp only [trace, diag_apply, hashimotoMatrix_pow_apply]
  rw [← Nat.cast_sum, ← Nat.card_sigma, Nat.succ_eq_add_one, closedNonBacktrackingCount_add_one]

end SimpleGraph
