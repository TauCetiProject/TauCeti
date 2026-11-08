/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Replication
public import TauCeti.GroupTheory.Perm.ParityRetract

/-!
# Staircase seeds for `Sym(3)`, and `h₁(K_k) = k/3` for every `k ≥ 3`

Attribution: the seeds are Kozlov's staircase graphs [D. N. Kozlov, arXiv:1610.07136, Def. 3.2
and §3.1]; the cut-minimality bound is proved directly here, following [Kozlov, Lemma 3.8 and
Cor. 3.13] (triangle count after [Kozlov, Lemma 3.10]); the `Sym(3)` transfer (parity retraction)
and the `k/3` theorem are [Beasley, Cor. 7, Thm. 8].

The seeds are the staircase graphs of D. N. Kozlov (arXiv:1610.07136), built from the partition
`(t, t-1, …, 1)`: on `m = 2t + 1` vertices `u, v₁, …, v_t, y₁, …, y_t`, join `vᵢ` to `y_j`
exactly when `i ≤ j`, and put the transposition `t01` on those edges and the identity elsewhere.
Here the vertices are numbered `u = 0`, `vᵢ = 2i - 1`, `y_j = 2j`, so an edge `p < q` carries
`t01` exactly when `p` is odd and `q` is even (`stair`). For `t = 2, 3` these are the
staircases on `K_5` and `K_7` up to relabelling.

All counts are moved-point counts, as in `Basic`: a staircase edge costs `2`.

* `stair_gaugeDist`: the gauge distance of the staircase on `K_{2t+1}` is exactly `t(t+1)`,
  twice its number of edges. The lower bound is the parity retraction (a `Sym(3)` gauge costs at
  least twice the `F₂` count of its signs, `stair_cost_ge`) followed by cut-minimality: adding
  the two newest vertices adds at least `t + 1` to every `F₂` count (`st_cutF_ge`).
* `stair_defect_mul`: `3N = (2t+1) D`, from the triangle count
  `N = 2(1² + 2² + … + t²) = t(t+1)(2t+1)/3` (`st_tri`).
* `h1_stair_mul`: `Sym3.h1_mul_of_seed` of `Replication` turns the staircase into
  `h₁(K_{(2t+1)q}) = (2t+1)q/3` for every `q ≥ 1`.
* `h1_eq_card_div_three`: every `k ≥ 3` is `4q` or `(2t+1)q` with `t ≥ 1`, so
  `h₁(K_k) = k/3` for every `k ≥ 3` (Beasley's Theorem 8 is the case `k ≥ 4`).

The parity retraction is `Equiv.Perm.parityRetract` with `Equiv.Perm.movedNorm_parityRetract_le`.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

open Finset

/-! ## Indicator, parity and the staircase -/

/-- `1` for `true`, `0` for `false`. -/
private def bnat (b : Bool) : ℕ := if b then 1 else 0

/-- The staircase edge predicate on positions `p < q`: `p` odd and `q` even. -/
def stEdge (p q : ℕ) : Bool := decide (p % 2 = 1) && decide (q % 2 = 0)

/-- **Kozlov's staircase cochain** on `K_k`: `t01` on the edges `p < q` with `p` odd and `q`
even, the identity elsewhere. For `k = 2t + 1` this is the staircase of the partition
`(t, …, 1)` with one loose vertex `0`. -/
def stair (k : ℕ) : Fin k → Fin k → S3 := fun p q => if stEdge p.val q.val then t01 else 1

/-- The sign of a permutation of three points, as a Boolean (`true` for a transposition). -/
private def oddPerm (σ : S3) : Bool := decide (σ = t01) || decide (σ = t12) || decide (σ = t02)

/-- `oddPerm` is the sign: `true` exactly for the odd permutations. -/
private theorem oddPerm_eq_decide (σ : S3) : oddPerm σ = decide (Equiv.Perm.sign σ = -1) := by
  have h01 : Equiv.Perm.sign t01 = -1 := Equiv.Perm.sign_swap (by decide)
  have h12 : Equiv.Perm.sign t12 = -1 := Equiv.Perm.sign_swap (by decide)
  have h02 : Equiv.Perm.sign t02 = -1 := Equiv.Perm.sign_swap (by decide)
  have hc1 : Equiv.Perm.sign c1 = 1 := by
    rw [c1, Equiv.Perm.sign_mul, ← t01, ← t12, h01, h12]
    rfl
  have hc2 : Equiv.Perm.sign c2 = 1 := by
    rw [c2, Equiv.Perm.sign_mul, ← t01, ← t12, h01, h12]
    rfl
  have h := mem_S3list σ
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Equiv.Perm.sign_one]
    decide
  · rw [h01]
    decide
  · rw [h12]
    decide
  · rw [h02]
    decide
  · rw [hc1]
    decide
  · rw [hc2]
    decide

/-- The sign of a permutation as a Boolean is additive (`xor`) along products. -/
private theorem oddPerm_mul (σ τ : S3) : oddPerm (σ * τ) = xor (oddPerm σ) (oddPerm τ) := by
  rw [oddPerm_eq_decide, oddPerm_eq_decide, oddPerm_eq_decide, Equiv.Perm.sign_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hτ | hτ <;> simp [hσ, hτ, Units.ext_iff]

/-- `t01` is a transposition. -/
private theorem t01_isSwap : t01.IsSwap := ⟨0, 1, by decide, rfl⟩

/-- The parity retraction onto `{1, t01}` moves `2` points on odd permutations and none on even
ones. -/
private theorem movedNorm_parityRetract_t01 (σ : S3) :
    Equiv.Perm.movedNorm (Fin 3) (Equiv.Perm.parityRetract t01_isSwap σ) =
      2 * (bnat (oddPerm σ) : ℝ) := by
  have ht := t01_isSwap
  rw [oddPerm_eq_decide]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [Equiv.Perm.parityRetract_of_sign_eq_one ht hσ, hσ]
    simp [bnat, Units.ext_iff]
  · rw [Equiv.Perm.parityRetract_of_sign_eq_neg_one ht hσ, ht.movedNorm, hσ]
    simp [bnat]

/-- **Parity retraction, one edge.** An odd edge term moves at least two points
(`Equiv.Perm.movedNorm_parityRetract_le`). -/
private theorem st_par_bound (a b : S3) (e : Bool) :
    2 * bnat (xor (xor (oddPerm a) (oddPerm b)) e) ≤
      moved (a⁻¹ * (if e then t01 else 1) * b) := by
  have hodd :
      xor (xor (oddPerm a) (oddPerm b)) e = oddPerm (a⁻¹ * (if e then t01 else 1) * b) := by
    have ha : oddPerm a⁻¹ = oddPerm a := by
      rw [oddPerm_eq_decide, oddPerm_eq_decide, Equiv.Perm.sign_inv]
    have he : oddPerm (if e then t01 else 1) = e := by cases e <;> decide
    rw [oddPerm_mul, oddPerm_mul, ha, he]
    cases oddPerm a <;> cases oddPerm b <;> cases e <;> rfl
  rw [hodd]
  have h := Equiv.Perm.movedNorm_parityRetract_le t01_isSwap (a⁻¹ * (if e then t01 else 1) * b)
  rw [movedNorm_parityRetract_t01, ← moved_eq_movedNorm] at h
  exact_mod_cast h

/-- Under the identity gauge a staircase-valued edge term moves `2` points exactly when it is
an edge. -/
private theorem st_moved_one (b : Bool) :
    moved ((1 : S3)⁻¹ * (if b then t01 else 1) * 1) = 2 * bnat b := by
  cases b <;> decide

/-- The holonomy of a triangle with `{1, t01}` labels moves `2` points exactly when an odd
number of its edges carry `t01`. -/
private theorem st_moved_tri (a b c : Bool) :
    moved ((if a then t01 else 1) * (if b then t01 else 1) * (if c then t01 else 1)⁻¹) =
      2 * bnat (xor (xor a b) c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- No staircase edge ends at an odd position. -/
private theorem stEdge_of_odd (p q : ℕ) (hq : q % 2 = 1) : stEdge p q = false := by
  unfold stEdge
  rw [hq]
  simp

/-- A pair ending at an even position is an edge exactly when it starts at an odd one. -/
private theorem stEdge_of_even (p q : ℕ) (hq : q % 2 = 0) : stEdge p q = decide (p % 2 = 1) := by
  unfold stEdge
  rw [hq]
  simp

/-! ## From `Fin` sums to sums over `range` -/

/-- Truncating a sum over `range n` by the indicator of `u < v` (`v ≤ n`) gives a sum over
`range v`. -/
private theorem st_sum_lt (n v : ℕ) (hv : v ≤ n) (f : ℕ → ℕ) :
    (∑ u ∈ range n, if u < v then f u else 0) = ∑ u ∈ range v, f u := by
  rw [← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨lt_of_lt_of_le h hv, h⟩

/-- A sum over the edges `u < v` of `K_n`, as a sum over `range`. -/
private theorem st_fin_pair (n : ℕ) (G : ℕ → ℕ → ℕ) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then G u.val v.val else 0) =
      ∑ v ∈ range n, ∑ u ∈ range v, G u v := by
  have hA : (∑ u : Fin n, ∑ v : Fin n, if u < v then G u.val v.val else 0) =
      ∑ u ∈ range n, ∑ v ∈ range n, if u < v then G u v else 0 := by
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun u => ∑ v ∈ range n, if u < v then G u v else 0) n)
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun v => if u.val < v then G u.val v else 0) n)
    refine Finset.sum_congr rfl fun v _ => ?_
    -- `Fin.sum_univ_eq_sum_range` reads the summand at the `val`s; `Fin` order is `val` order.
    show (if u < v then G u.val v.val else 0) = (if u.val < v.val then G u.val v.val else 0)
    by_cases h : u < v
    · rw [ite_eq_left h, ite_eq_left (show u.val < v.val from h)]
    · rw [ite_eq_right h, ite_eq_right (show ¬ (u.val < v.val) from h)]
  rw [hA, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  exact st_sum_lt n v (Finset.mem_range.mp hv).le (fun u => G u v)

/-- A sum over the triangles `u < v < w` of `K_n`, as a sum over `range`. -/
private theorem st_fin_triple (n : ℕ) (Y : ℕ → ℕ → ℕ → ℕ) :
    (∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
      if u < v ∧ v < w then Y u.val v.val w.val else 0) =
      ∑ w ∈ range n, ∑ v ∈ range w, ∑ u ∈ range v, Y u v w := by
  have hA : (∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
      if u < v ∧ v < w then Y u.val v.val w.val else 0) =
      ∑ u ∈ range n, ∑ v ∈ range n, ∑ w ∈ range n,
        if u < v ∧ v < w then Y u v w else 0 := by
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun u => ∑ v ∈ range n, ∑ w ∈ range n, if u < v ∧ v < w then Y u v w else 0) n)
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun v => ∑ w ∈ range n, if u.val < v ∧ v < w then Y u.val v w else 0) n)
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun w => if u.val < v.val ∧ v.val < w then Y u.val v.val w else 0) n)
    refine Finset.sum_congr rfl fun w _ => ?_
    -- As in `st_fin_pair`: the summand read at the `val`s, with `Fin` order as `val` order.
    show (if u < v ∧ v < w then Y u.val v.val w.val else 0) =
      (if u.val < v.val ∧ v.val < w.val then Y u.val v.val w.val else 0)
    by_cases h : u < v ∧ v < w
    · rw [ite_eq_left h, ite_eq_left (show u.val < v.val ∧ v.val < w.val from h)]
    · rw [ite_eq_right h, ite_eq_right (show ¬ (u.val < v.val ∧ v.val < w.val) from h)]
  have hB : (∑ u ∈ range n, ∑ v ∈ range n, ∑ w ∈ range n,
        if u < v ∧ v < w then Y u v w else 0) =
      ∑ w ∈ range n, ∑ v ∈ range n, ∑ u ∈ range n,
        if u < v ∧ v < w then Y u v w else 0 := by
    calc _ = ∑ v ∈ range n, ∑ u ∈ range n, ∑ w ∈ range n,
          (if u < v ∧ v < w then Y u v w else 0) := Finset.sum_comm
      _ = ∑ v ∈ range n, ∑ w ∈ range n, ∑ u ∈ range n,
          (if u < v ∧ v < w then Y u v w else 0) :=
          Finset.sum_congr rfl fun v _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hA, hB]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : w < n := Finset.mem_range.mp hw
  have e : ∀ v, (∑ u ∈ range n, if u < v ∧ v < w then Y u v w else 0) =
      if v < w then ∑ u ∈ range v, Y u v w else 0 := by
    intro v
    by_cases hv : v < w
    · rw [ite_eq_left hv]
      refine Eq.trans ?_ (st_sum_lt n v (by omega) (fun u => Y u v w))
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u < v
      · rw [ite_eq_left (And.intro hu hv), ite_eq_left hu]
      · rw [ite_eq_right (show ¬ (u < v ∧ v < w) from fun h => hu h.1), ite_eq_right hu]
    · rw [ite_eq_right hv]
      exact Finset.sum_eq_zero fun u _ =>
        ite_eq_right (show ¬ (u < v ∧ v < w) from fun h => hv h.2)
  simp only [e]
  exact st_sum_lt n w hw'.le (fun v => ∑ u ∈ range v, Y u v w)

/-! ## The `F₂` counts on positions -/

/-- The term of the pair `p < q` under the sign pattern `σ`: odd exactly when the edge term
is a transposition. -/
private def gx (σ : ℕ → Bool) (p q : ℕ) : ℕ := bnat (xor (xor (σ p) (σ q)) (stEdge p q))

/-- The `F₂` cost of the sign pattern `σ` on the first `n` positions. -/
private def cutF (σ : ℕ → Bool) (n : ℕ) : ℕ := ∑ q ∈ range n, ∑ p ∈ range q, gx σ p q

/-- The number of staircase edges among the first `n` positions. -/
private def stE (n : ℕ) : ℕ := ∑ q ∈ range n, ∑ p ∈ range q, bnat (stEdge p q)

/-- The pairs `u < v < n` with `u` even and `v` odd, written as the triangle term at an even
third vertex. -/
private def stP (n : ℕ) : ℕ :=
  ∑ v ∈ range n, ∑ u ∈ range v,
    bnat (xor (xor (stEdge u v) (decide (v % 2 = 1))) (decide (u % 2 = 1)))

/-- The number of broken triangles (an odd number of staircase edges) among the first `n`
positions. -/
private def stT (n : ℕ) : ℕ :=
  ∑ w ∈ range n, ∑ v ∈ range w, ∑ u ∈ range v,
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w))

/-- Adding position `n` adds the terms of the pairs `p < n`. -/
private theorem st_cutF_succ (σ : ℕ → Bool) (n : ℕ) :
    cutF σ (n + 1) = cutF σ n + ∑ p ∈ range n, gx σ p n := by
  unfold cutF
  exact Finset.sum_range_succ (fun q => ∑ p ∈ range q, gx σ p q) n

/-- Adding position `n` adds the edges `p < n`. -/
private theorem st_stE_succ (n : ℕ) : stE (n + 1) = stE n + ∑ p ∈ range n, bnat (stEdge p n) := by
  unfold stE
  exact Finset.sum_range_succ (fun q => ∑ p ∈ range q, bnat (stEdge p q)) n

/-- Adding position `n` adds the pairs `u < n`. -/
private theorem st_stP_succ (n : ℕ) : stP (n + 1) = stP n +
    ∑ u ∈ range n, bnat (xor (xor (stEdge u n) (decide (n % 2 = 1))) (decide (u % 2 = 1))) := by
  unfold stP
  exact Finset.sum_range_succ (fun v => ∑ u ∈ range v,
    bnat (xor (xor (stEdge u v) (decide (v % 2 = 1))) (decide (u % 2 = 1)))) n

/-- Adding position `n` adds the triangles with largest vertex `n`. -/
private theorem st_stT_succ (n : ℕ) : stT (n + 1) = stT n +
    ∑ v ∈ range n, ∑ u ∈ range v, bnat (xor (xor (stEdge u v) (stEdge v n)) (stEdge u n)) := by
  unfold stT
  exact Finset.sum_range_succ (fun w => ∑ v ∈ range w, ∑ u ∈ range v,
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w))) n

/-- Among the positions `0, …, 2t`, exactly `t` are odd. -/
private theorem st_cnt_odd (t : ℕ) : ∑ p ∈ range (2 * t + 1), bnat (decide (p % 2 = 1)) = t := by
  induction t with
  | zero => simp [bnat]
  | succ t ih =>
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h1, h2]
    rfl

/-- Among the positions `0, …, 2t`, exactly `t + 1` are even. -/
private theorem st_cnt_even (t : ℕ) :
    ∑ p ∈ range (2 * t + 1), bnat (!decide (p % 2 = 1)) = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h1, h2]
    rfl

/-- One earlier position against the two newest positions: if their signs agree it contributes
at least its oddness, if they differ at least its evenness. -/
private theorem st_pair_bound (x A B o : Bool) :
    (if A = B then bnat o else bnat (!o)) ≤
      bnat (xor (xor x A) false) + bnat (xor (xor x B) o) := by
  cases x <;> cases A <;> cases B <;> cases o <;> decide

/-- The new edge between the two newest positions is odd whenever their signs agree. -/
private theorem st_ab_bound (A B : Bool) :
    (if A = B then 1 else 0) ≤ bnat (xor (xor A B) (decide (1 = 1))) := by
  cases A <;> cases B <;> decide

/-- **Cut-minimality.** Every sign pattern on the staircase of `K_{2t+1}` costs at least the
number of edges `t(t+1)/2`. Adding the two newest positions `2t+1` (a new `v`, whose only
neighbour is the new `y`) and `2t+2` (a new `y`, joined to every `v`, the new one included) adds
at least `t + 1`: if their signs agree,
each of the `t` odd earlier positions contributes one and the new edge one; if they differ, each of
the `t + 1` even earlier positions contributes one. -/
private theorem st_cutF_ge (t : ℕ) : ∀ σ : ℕ → Bool, t * (t + 1) ≤ 2 * cutF σ (2 * t + 1) := by
  induction t with
  | zero => intro σ; simp
  | succ t ih =>
    intro σ
    have ha : (2 * t + 1) % 2 = 1 := by omega
    have hb : (2 * t + 1 + 1) % 2 = 0 := by omega
    have hp : ∀ p, (if σ (2 * t + 1) = σ (2 * t + 1 + 1) then bnat (decide (p % 2 = 1))
        else bnat (!decide (p % 2 = 1))) ≤ gx σ p (2 * t + 1) + gx σ p (2 * t + 1 + 1) := by
      intro p
      unfold gx
      rw [stEdge_of_odd p _ ha, stEdge_of_even p _ hb]
      exact st_pair_bound _ _ _ _
    have hab : (if σ (2 * t + 1) = σ (2 * t + 1 + 1) then 1 else 0) ≤
        gx σ (2 * t + 1) (2 * t + 1 + 1) := by
      unfold gx
      rw [stEdge_of_even _ _ hb, ha]
      exact st_ab_bound _ _
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, st_cutF_succ, st_cutF_succ,
      Finset.sum_range_succ _ (2 * t + 1)]
    have hi := ih σ
    by_cases h : σ (2 * t + 1) = σ (2 * t + 1 + 1)
    · have hc := st_cnt_odd t
      have hle : ∑ p ∈ range (2 * t + 1), bnat (decide (p % 2 = 1)) ≤
          ∑ p ∈ range (2 * t + 1), (gx σ p (2 * t + 1) + gx σ p (2 * t + 1 + 1)) :=
        Finset.sum_le_sum fun p _ => by
          have := hp p
          rwa [ite_eq_left h] at this
      rw [Finset.sum_add_distrib] at hle
      have h3 : 1 ≤ gx σ (2 * t + 1) (2 * t + 1 + 1) := by
        have := hab
        rwa [ite_eq_left h] at this
      nlinarith
    · have hc := st_cnt_even t
      have hle : ∑ p ∈ range (2 * t + 1), bnat (!decide (p % 2 = 1)) ≤
          ∑ p ∈ range (2 * t + 1), (gx σ p (2 * t + 1) + gx σ p (2 * t + 1 + 1)) :=
        Finset.sum_le_sum fun p _ => by
          have := hp p
          rwa [ite_eq_right h] at this
      rw [Finset.sum_add_distrib] at hle
      nlinarith

/-- The staircase on `K_{2t+1}` has `t(t+1)/2` edges. -/
private theorem st_edges (t : ℕ) : 2 * stE (2 * t + 1) = t * (t + 1) := by
  induction t with
  | zero => simp [stE]
  | succ t ih =>
    have ha : (2 * t + 1) % 2 = 1 := by omega
    have hb : (2 * t + 1 + 1) % 2 = 0 := by omega
    have r1 : ∑ p ∈ range (2 * t + 1), bnat (stEdge p (2 * t + 1)) = 0 :=
      Finset.sum_eq_zero fun p _ => by rw [stEdge_of_odd p _ ha]; rfl
    have hs : ∀ p, bnat (stEdge p (2 * t + 1 + 1)) = bnat (decide (p % 2 = 1)) := fun p => by
      rw [stEdge_of_even p _ hb]
    have r2 : ∑ p ∈ range (2 * t + 1 + 1), bnat (stEdge p (2 * t + 1 + 1)) = t + 1 := by
      rw [Finset.sum_range_succ]
      simp only [hs]
      rw [st_cnt_odd t, ha]
      rfl
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, st_stE_succ, st_stE_succ, r1, r2]
    nlinarith

/-- The triangle term of `stP` at an odd last vertex is the evenness of `u`. -/
private theorem st_row_odd (u q : ℕ) (hq : q % 2 = 1) :
    bnat (xor (xor (stEdge u q) (decide (q % 2 = 1))) (decide (u % 2 = 1))) =
      bnat (!decide (u % 2 = 1)) := by
  rw [stEdge_of_odd u q hq, hq]
  generalize decide (u % 2 = 1) = o
  cases o <;> rfl

/-- The triangle term of `stP` at an even last vertex vanishes. -/
private theorem st_row_even (u q : ℕ) (hq : q % 2 = 0) :
    bnat (xor (xor (stEdge u q) (decide (q % 2 = 1))) (decide (u % 2 = 1))) = 0 := by
  rw [stEdge_of_even u q hq, hq]
  generalize decide (u % 2 = 1) = o
  cases o <;> rfl

/-- `2 · #{u < v < 2t+2 : u even, v odd} = (t+1)(t+2)`. -/
private theorem st_P (t : ℕ) : 2 * stP (2 * t + 2) = (t + 1) * (t + 2) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have hc : (2 * t + 2) % 2 = 0 := by omega
    have hd : (2 * t + 2 + 1) % 2 = 1 := by omega
    have r1 : ∑ u ∈ range (2 * t + 2),
        bnat (xor (xor (stEdge u (2 * t + 2)) (decide ((2 * t + 2) % 2 = 1)))
          (decide (u % 2 = 1))) = 0 :=
      Finset.sum_eq_zero fun u _ => st_row_even u _ hc
    have hce := st_cnt_even (t + 1)
    rw [show 2 * (t + 1) + 1 = 2 * t + 2 + 1 by ring] at hce
    have r2 : ∑ u ∈ range (2 * t + 2 + 1),
        bnat (xor (xor (stEdge u (2 * t + 2 + 1)) (decide ((2 * t + 2 + 1) % 2 = 1)))
          (decide (u % 2 = 1))) = t + 1 + 1 :=
      (Finset.sum_congr rfl fun u _ => st_row_odd u _ hd).trans hce
    rw [show 2 * (t + 1) + 2 = 2 * t + 2 + 1 + 1 by ring, st_stP_succ, st_stP_succ, r1, r2]
    nlinarith

/-- A triangle whose largest vertex is odd is broken exactly when its first edge is an edge. -/
private theorem st_tri_odd (u v w : ℕ) (hw : w % 2 = 1) :
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w)) = bnat (stEdge u v) := by
  rw [stEdge_of_odd v w hw, stEdge_of_odd u w hw]
  simp

/-- A triangle whose largest vertex is even reduces to the `stP` term. -/
private theorem st_tri_even (u v w : ℕ) (hw : w % 2 = 0) :
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w)) =
      bnat (xor (xor (stEdge u v) (decide (v % 2 = 1))) (decide (u % 2 = 1))) := by
  rw [stEdge_of_even v w hw, stEdge_of_even u w hw]

/-- **The triangle count.** `6 · #{broken triangles} = t(t+1)(2t+1)`: adding the two newest
positions breaks `(t+1)²` new triangles. -/
private theorem st_tri (t : ℕ) : 6 * stT (2 * t + 1) = t * (t + 1) * (2 * t + 1) := by
  induction t with
  | zero => simp [stT]
  | succ t ih =>
    have ha : (2 * t + 1) % 2 = 1 := by omega
    have hb : (2 * t + 1 + 1) % 2 = 0 := by omega
    have r1 : ∑ v ∈ range (2 * t + 1), ∑ u ∈ range v,
        bnat (xor (xor (stEdge u v) (stEdge v (2 * t + 1))) (stEdge u (2 * t + 1))) =
          stE (2 * t + 1) := by
      unfold stE
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
        st_tri_odd u v _ ha
    have r2 : ∑ v ∈ range (2 * t + 1 + 1), ∑ u ∈ range v,
        bnat (xor (xor (stEdge u v) (stEdge v (2 * t + 1 + 1))) (stEdge u (2 * t + 1 + 1))) =
          stP (2 * t + 1 + 1) := by
      unfold stP
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
        st_tri_even u v _ hb
    have hE := st_edges t
    have hP := st_P t
    rw [show 2 * t + 2 = 2 * t + 1 + 1 by ring] at hP
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, st_stT_succ, st_stT_succ, r1, r2]
    nlinarith

/-! ## The staircase cochain: gauge distance and defect -/

/-- The sign pattern of a gauge, on positions. -/
private def sgnPat {n : ℕ} (β : Fin n → S3) (i : ℕ) : Bool :=
  if h : i < n then oddPerm (β ⟨i, h⟩) else false

/-- At a vertex, the sign pattern is the sign of the gauge. -/
private theorem sgnPat_val {n : ℕ} (β : Fin n → S3) (u : Fin n) :
    sgnPat β u.val = oddPerm (β u) := by
  simp [sgnPat]

/-- **Parity retraction.** A `Sym(3)` gauge of the staircase costs at least twice the `F₂` count
of its sign pattern. -/
private theorem stair_cost_ge (n : ℕ) (β : Fin n → S3) :
    2 * cutF (sgnPat β) n ≤ cost (stair n) β := by
  calc 2 * cutF (sgnPat β) n = ∑ v ∈ range n, ∑ u ∈ range v, 2 * gx (sgnPat β) u v := by
        simp only [cutF, Finset.mul_sum]
    _ = ∑ u : Fin n, ∑ v : Fin n, (if u < v then 2 * gx (sgnPat β) u.val v.val else 0) :=
        (st_fin_pair n (fun a b => 2 * gx (sgnPat β) a b)).symm
    _ ≤ ∑ u : Fin n, ∑ v : Fin n,
          (if u < v then moved ((β u)⁻¹ * stair n u v * β v) else 0) := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        by_cases huv : u < v
        · rw [ite_eq_left huv, ite_eq_left huv]
          unfold gx
          rw [sgnPat_val, sgnPat_val]
          exact st_par_bound (β u) (β v) (stEdge u.val v.val)
        · simp [huv]
    _ = cost (stair n) β := (cost_eq_sum _ _).symm

/-- The identity gauge costs twice the number of staircase edges. -/
private theorem stair_cost_one (n : ℕ) : cost (stair n) (fun _ => 1) = 2 * stE n := by
  calc cost (stair n) (fun _ => 1) = ∑ u : Fin n, ∑ v : Fin n,
        (if u < v then moved ((1 : S3)⁻¹ * stair n u v * 1) else 0) := cost_eq_sum _ _
    _ = ∑ u : Fin n, ∑ v : Fin n, (if u < v then 2 * bnat (stEdge u.val v.val) else 0) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        by_cases huv : u < v
        · rw [ite_eq_left huv, ite_eq_left huv]
          exact st_moved_one (stEdge u.val v.val)
        · simp [huv]
    _ = ∑ v ∈ range n, ∑ u ∈ range v, 2 * bnat (stEdge u v) :=
        st_fin_pair n (fun a b => 2 * bnat (stEdge a b))
    _ = 2 * stE n := by simp only [stE, Finset.mul_sum]

/-- Every gauge of the staircase on `K_{2t+1}` costs at least `t(t+1)`. -/
theorem stair_cost_lower (t : ℕ) (β : Fin (2 * t + 1) → S3) :
    t * (t + 1) ≤ cost (stair (2 * t + 1)) β :=
  (st_cutF_ge t (sgnPat β)).trans (stair_cost_ge _ β)

/-- The identity gauge of the staircase on `K_{2t+1}` costs exactly `t(t+1)`. -/
theorem stair_cost_id (t : ℕ) : cost (stair (2 * t + 1)) (fun _ => 1) = t * (t + 1) := by
  rw [stair_cost_one]
  exact st_edges t

/-- **The gauge distance of the staircase** on `K_{2t+1}` is exactly `t(t+1)`: leaving the
cochain alone is optimal. -/
theorem stair_gaugeDist (t : ℕ) : gaugeDist (stair (2 * t + 1)) = t * (t + 1) :=
  gaugeDist_eq_of (stair_cost_lower t) _ (stair_cost_id t)

/-- The term of a triangle `u < v < w` in the staircase defect, as a parity of edge labels. -/
private theorem stair_tri_term (n : ℕ) (u v w : Fin n) :
    (if u < v ∧ v < w then
      moved (val (stair n) u v * val (stair n) v w * val (stair n) w u) else 0) =
      if u < v ∧ v < w then
        2 * bnat (xor (xor (stEdge u.val v.val) (stEdge v.val w.val)) (stEdge u.val w.val))
      else 0 := by
  by_cases h : u < v ∧ v < w
  · rw [ite_eq_left h, ite_eq_left h]
    have huw : ¬ w < u := not_lt.mpr (h.1.trans h.2).le
    unfold Sym3.val
    rw [ite_eq_left h.1, ite_eq_left h.2, ite_eq_right huw]
    exact st_moved_tri (stEdge u.val v.val) (stEdge v.val w.val) (stEdge u.val w.val)
  · rw [ite_eq_right h, ite_eq_right h]

/-- The defect of the staircase is twice its number of broken triangles. -/
private theorem stair_defect (n : ℕ) : defect (stair n) = 2 * stT n := by
  calc defect (stair n) = ∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
        (if u < v ∧ v < w then
          2 * bnat (xor (xor (stEdge u.val v.val) (stEdge v.val w.val)) (stEdge u.val w.val))
        else 0) := by
        rw [defect_eq_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun w _ => stair_tri_term n u v w
    _ = ∑ w ∈ range n, ∑ v ∈ range w, ∑ u ∈ range v,
          2 * bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w)) :=
        st_fin_triple n (fun a b c => 2 * bnat (xor (xor (stEdge a b) (stEdge b c)) (stEdge a c)))
    _ = 2 * stT n := by simp only [stT, Finset.mul_sum]

/-- **`N/D = m/3` for the staircase.** `3N = (2t+1) · D` with `D = t(t+1)`. -/
theorem stair_defect_mul (t : ℕ) :
    3 * defect (stair (2 * t + 1)) = (2 * t + 1) * (t * (t + 1)) := by
  rw [stair_defect]
  have h := st_tri t
  nlinarith

/-! ## Replicated staircases, and every `k ≥ 3` -/

/-- **Odd seeds.** `h₁(K_{(2t+1)q}) = (2t+1)q/3` for every `t ≥ 1` and `q ≥ 1`, from Kozlov's
staircase. -/
theorem h1_stair_mul (t q : ℕ) (ht : 1 ≤ t) (hq : 0 < q) :
    h1 ((2 * t + 1) * q) = (((2 * t + 1) * q : ℕ) : ℝ) / 3 :=
  h1_mul_of_seed (stair (2 * t + 1))
    (by rw [stair_gaugeDist]; exact Nat.mul_pos (by omega) (by omega))
    (by rw [stair_gaugeDist]; exact stair_defect_mul t) q hq

/-- Every `k ≥ 3` is `4q` or `(2t+1)q` with `t ≥ 1` and `q ≥ 1` (halve while even). -/
theorem st_decomp (n : ℕ) : ∀ k, k ≤ n → 3 ≤ k →
    ∃ m q, 0 < q ∧ k = m * q ∧ (m = 4 ∨ ∃ t, 1 ≤ t ∧ m = 2 * t + 1) := by
  induction n with
  | zero => intro k hk h3; omega
  | succ n ih =>
    intro k hk h3
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨t, ht⟩
    · by_cases hj2 : j = 2
      · exact ⟨4, 1, by norm_num, by omega, Or.inl rfl⟩
      · obtain ⟨m, q, hq, hjm, hm⟩ := ih j (by omega) (by omega)
        exact ⟨m, 2 * q, by omega, by rw [hj, hjm]; ring, hm⟩
    · exact ⟨k, 1, by norm_num, by ring, Or.inr ⟨t, by omega, ht⟩⟩

/-- **`h₁(K_k) = k/3` for every `k ≥ 3`** (Beasley, Theorem 8, for `k ≥ 4`). Powers of two
`k ≥ 4` come from the replicated `k = 4` seed (`h1_eq_four_mul`); every other `k` from a
replicated staircase. -/
theorem h1_eq_card_div_three (k : ℕ) (hk : 3 ≤ k) : h1 k = (k : ℝ) / 3 := by
  obtain ⟨m, q, hq, rfl, hm⟩ := st_decomp k k le_rfl hk
  rcases hm with rfl | ⟨t, ht, rfl⟩
  · exact h1_eq_four_mul q hq
  · exact h1_stair_mul t q ht hq

end TauCeti.CoboundaryExpansion.Sym3
