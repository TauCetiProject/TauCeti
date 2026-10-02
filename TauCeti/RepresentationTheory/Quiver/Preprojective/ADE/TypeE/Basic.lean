/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.LadderValley
public import TauCeti.Algebra.Algebra.NilpotentPair
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Preprojective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# The preprojective algebras of `E₆` and `E₈` are finite-dimensional

In the Bourbaki labelling of `Eₙ` (`n ≥ 4`, Mathlib's `CartanMatrix.E n`), the node `3` is the
branch node, and three arms leave it: the leaf `1`; the arm `2, 0`; and the long arm
`4, 5, …, n - 1`. Read each arm as a ladder whose rung `0` is the branch node, so that its rung
`r` is the node at distance `r` from the branch node. In the signless algebra
`TauCeti.signlessPreprojectiveAlgebra` of the doubled graph, the relation at each node of an arm
says that the two backtracks there cancel: these are the ladder relations of
`TauCeti.Algebra.Ring.LadderValley` at every rung except the bottom one. Write

* `x`, `y` and `z` for the backtracks from the branch node into the leaf, into the arm `2, 0` and
  into the long arm.

A ladder with `N` rungs above the bottom one has nilpotent bottom turn
(`TauCeti.pow_d_mul_u_eq_zero`), so `x ^ 2 = 0`, `y ^ 3 = 0` and `z ^ (n - 3) = 0`, and the
relation at the branch node is `x + y + z = 0`.

A path is rewritten, one arrow at a time, into one of two normal forms: a valley word on one
arm which does not reach the branch node; or a word of the shape
`(climb out of the branch node) · w · (path into the branch node)`, where `w` is a product of
backtracks at the branch node, and so lies in a power of the span of `x` and `y`. Every
backtrack added to `w` adds two to the length of the path, while the outer paths have length less
than `n`. Hence if the `M`-th power of the span of `x` and `y` vanishes, every path of length at
least `2 n + 2 M` vanishes.

For `E₆` the long arm has two nodes, so `(x + y) ^ 3 = (-z) ^ 3 = 0`, and every product of six
factors from `{x, y}` vanishes (`TauCeti.span_pair_pow_six_eq_bot`). Hence **every path of
length at least `24` vanishes** in the signless algebra of `E₆`. The bound `24` is not sharp; the
sharp bound `h - 1 = 11`, for the Coxeter number `h = 12` of `E₆`, is not proved here.

For `E₈` the long arm has four nodes, so `(x + y) ^ 5 = (-z) ^ 5 = 0`, and every product of
fifteen factors from `{x, y}` vanishes (`TauCeti.span_pair_pow_fifteen_eq_bot`). Hence **every
path of length at least `46` vanishes** in the signless algebra of `E₈`. Again the bound is not
sharp: the sharp bound is `h - 1 = 29`, for the Coxeter number `h = 30` of `E₈`. The `E₈`
results are stated for the named Bourbaki-labelled graph `TauCeti.zigzagE8Graph`.

The signless algebra of a bipartite graph is the preprojective algebra of each of its
orientations, by an explicit sign rescaling of the arrows. Thus the same bound holds in the
preprojective algebra `Π_k(Q)` of every orientation `Q` of `E₆` or `E₈`, over every commutative
ring; the relation ideal is admissible, and `Π_k(Q)` is finite-dimensional over every field.

## Main results

* `TauCeti.signlessPreprojectiveMk_E6_ofPath_eq_zero_of_le`: paths of length at least `24` vanish
  in the signless algebra of `E₆`.
* `TauCeti.preprojectiveMk_E6_ofPath_eq_zero_of_le`: the same in the preprojective algebra of
  every orientation of `E₆`.
* `TauCeti.isAdmissibleIdeal_preprojectiveIdeal_E6`: the preprojective relation ideal of every
  orientation of `E₆` is admissible.
* `TauCeti.instFiniteDimensionalPreprojectiveAlgebraE6` and
  `TauCeti.instFiniteDimensionalSignlessPreprojectiveAlgebraE6`: the preprojective algebra of
  every orientation of `E₆`, and the signless algebra of `E₆`, are finite-dimensional.
* `TauCeti.signlessPreprojectiveMk_E8_ofPath_eq_zero_of_le`,
  `TauCeti.preprojectiveMk_E8_ofPath_eq_zero_of_le`,
  `TauCeti.isAdmissibleIdeal_preprojectiveIdeal_E8`,
  `TauCeti.instFiniteDimensionalPreprojectiveAlgebraE8` and
  `TauCeti.instFiniteDimensionalSignlessPreprojectiveAlgebraE8`: the same for `E₈`, with the
  bound `46`.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective algebra and its local relations.
* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3, for the
  signless relation and its comparison with the preprojective relation of a bipartite graph.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-- The neighbours of a vertex in a finite graph form a finite type; this is the finiteness
structure of the orientation comparisons of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective`. -/
noncomputable local instance eNeighborSetFintype {V : Type*} [Finite V] (G : SimpleGraph V)
    (i : V) : Fintype (G.neighborSet i) :=
  Fintype.ofFinite _

/-! ### The arms of the `Eₙ` diagram -/

/-- Adjacency of the nodes `i` and `j` of the Bourbaki-labelled `Eₙ` diagram, read on natural
numbers: the edges are `0 — 2`, `1 — 3` and `i — i + 1` for `i ≥ 2`. -/
private def EAdj (i j : ℕ) : Prop :=
  i = 0 ∧ j = 2 ∨ j = 0 ∧ i = 2 ∨ i = 1 ∧ j = 3 ∨ j = 1 ∧ i = 3 ∨ 2 ≤ i ∧ i + 1 = j ∨
    2 ≤ j ∧ j + 1 = i

/-- The node at distance `r` from the branch node `3` along the arm `a` of the `Eₙ` diagram: the
leaf `1` for `a = 0`, the arm `2, 0` for `a = 1`, and the long arm `4, 5, …` for `a = 2`. Beyond
the end of the two short arms the value is `n`, which is not a node. -/
private def eArm (n : ℕ) : Fin 3 → ℕ → ℕ
  | 0, r => if r = 0 then 3 else if r = 1 then 1 else n
  | 1, r => if r = 0 then 3 else if r = 1 then 2 else if r = 2 then 0 else n
  | 2, r => 3 + r

@[simp]
private theorem eArm_zero (n : ℕ) (a : Fin 3) : eArm n a 0 = 3 := by
  fin_cases a <;> simp [eArm]

/-- **The neighbours of a node on an arm** are its neighbours on that arm. -/
private theorem eq_eArm_of_eAdj {n : ℕ} {a : Fin 3} {p j : ℕ} (hp : 0 < p) (hpn : eArm n a p < n)
    (h : EAdj (eArm n a p) j) : j = eArm n a (p + 1) ∨ j = eArm n a (p - 1) := by
  obtain _ | _ | _ | p := p
  · omega
  all_goals fin_cases a <;> simp [eArm, EAdj] at hpn h ⊢ <;> omega

/-- **The neighbours of the branch node** are the first nodes of the three arms. -/
private theorem exists_eq_eArm_of_eAdj (n : ℕ) {j : ℕ} (h : EAdj 3 j) : ∃ a, j = eArm n a 1 := by
  simp only [EAdj] at h
  rcases h with h | h | h | h | h | h
  · omega
  · omega
  · omega
  · exact ⟨0, by simp [eArm, h.1]⟩
  · exact ⟨2, by simp [eArm]; omega⟩
  · exact ⟨1, by simp [eArm]; omega⟩

/-- Adjacency in the Bourbaki-labelled `Eₙ` diagram. -/
private theorem diagramGraph_E_adj {n : ℕ} (i j : Fin n) :
    (diagramGraph (CartanMatrix.E n)).Adj i j ↔ EAdj i j := by
  rw [diagramGraph_adj]
  simp only [CartanMatrix.E, Matrix.of_apply, ne_eq, Fin.ext_iff, EAdj]
  split_ifs <;> simp <;> omega

/-- Every node other than the branch node lies on an arm. -/
private theorem exists_eArm_eq (n : ℕ) {i : ℕ} (hi : i ≠ 3) : ∃ a p, 0 < p ∧ eArm n a p = i := by
  rcases Nat.lt_or_ge i 3 with h | h
  · interval_cases i
    · exact ⟨1, 2, by norm_num, by simp [eArm]⟩
    · exact ⟨0, 1, by norm_num, by simp [eArm]⟩
    · exact ⟨1, 1, by norm_num, by simp [eArm]⟩
  · exact ⟨2, i - 3, by omega, by simp [eArm]; omega⟩

/-- A node at distance `p` from the branch node has `p < n`. -/
private theorem lt_of_eArm_lt {n : ℕ} (hn : 4 ≤ n) {a : Fin 3} {p : ℕ} (h : eArm n a p < n) :
    p < n := by
  obtain _ | _ | _ | p := p
  all_goals fin_cases a <;> simp [eArm] at h ⊢ <;> omega

/-! ### The ladders of the arms -/

section EGraph

variable (k : Type*) [CommRing k] (n : ℕ)

local notation "G" => diagramGraph (CartanMatrix.E n)

/-- The step along the arm `a` away from the branch node, from rung `r` to rung `r + 1`. -/
private noncomputable def eUp (a : Fin 3) (r : ℕ) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  signlessArrow k G (eArm n a r) (eArm n a (r + 1))

/-- The step along the arm `a` towards the branch node, from rung `r + 1` to rung `r`. -/
private noncomputable def eDown (a : Fin 3) (r : ℕ) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  signlessArrow k G (eArm n a (r + 1)) (eArm n a r)

/-- The backtrack from the branch node into the arm `a`. -/
private noncomputable def eTurn (a : Fin 3) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  eDown k n a 0 * eUp k n a 0

/-- The span of the backtracks from the branch node into the leaf and into the arm `2, 0`. -/
private noncomputable def eSpan : Submodule ℤ (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  Submodule.span ℤ {eTurn k n 0, eTurn k n 1}

variable {n}

/-- An arrow vanishes between two numbers which are not adjacent nodes. -/
private theorem signlessArrow_e_eq_zero {i j : ℕ} (h : ¬(i < n ∧ j < n ∧ EAdj i j)) :
    signlessArrow k G i j = 0 :=
  signlessArrow_eq_zero k fun hi hj hij => h ⟨hi, hj, (diagramGraph_E_adj _ _).1 hij⟩

/-- The relation at a node `v`, summed over a set `S` of numbers containing its neighbours. -/
private theorem sum_e_relation (v : ℕ) (hv : v < n) (S : Finset ℕ)
    (hnbr : ∀ w < n, EAdj v w → w ∈ S) :
    ∑ w ∈ S, signlessArrow k G w v * signlessArrow k G v w = 0 := by
  classical
  have h := sum_signlessArrow_mul_signlessArrow k G ⟨v, hv⟩
  rw [Fin.sum_univ_eq_sum_range (fun w => signlessArrow k G w v * signlessArrow k G v w) n] at h
  calc ∑ w ∈ S, signlessArrow k G w v * signlessArrow k G v w
      = ∑ w ∈ S ∪ Finset.range n, signlessArrow k G w v * signlessArrow k G v w := by
        refine Finset.sum_subset Finset.subset_union_left fun w hw hwS => ?_
        have hw' : w < n := by simp at hw; tauto
        rw [signlessArrow_e_eq_zero k (j := w) fun h => hwS (hnbr w hw' h.2.2), mul_zero]
    _ = ∑ w ∈ Finset.range n, signlessArrow k G w v * signlessArrow k G v w := by
        refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
        rw [signlessArrow_e_eq_zero k (by simp at hw; omega), zero_mul]
    _ = 0 := h

variable (hn : 4 ≤ n)
include hn

/-- **The ladder relations of the arms.** At every node of an arm, the backtrack away from the
branch node cancels the backtrack towards it; beyond the end of the arm both vanish. -/
private theorem eDown_mul_eUp_add (a : Fin 3) (w : ℕ) :
    eDown k n a (w + 1) * eUp k n a (w + 1) + eUp k n a w * eDown k n a w = 0 := by
  by_cases hp : eArm n a (w + 1) < n
  · have h := sum_e_relation k _ hp {eArm n a w, eArm n a (w + 2)} fun j _ hj => by
      rcases eq_eArm_of_eAdj (by omega) hp hj with rfl | rfl <;> simp
    have hne : eArm n a w ≠ eArm n a (w + 2) := by
      obtain _ | _ | w := w
      all_goals fin_cases a <;> simp [eArm] at hp ⊢ <;> omega
    rw [Finset.sum_pair hne, add_comm] at h
    exact h
  · have h₁ : signlessArrow k G (eArm n a (w + 1 + 1)) (eArm n a (w + 1)) = 0 :=
      signlessArrow_e_eq_zero k (by omega)
    have h₂ : signlessArrow k G (eArm n a w) (eArm n a (w + 1)) = 0 :=
      signlessArrow_e_eq_zero k (by omega)
    simp only [eDown, eUp, h₁, h₂, zero_mul, add_zero]

/-- **The relation at the branch node**: the backtracks into the three arms sum to zero. -/
private theorem eTurn_add_eTurn_add_eTurn : eTurn k n 0 + eTurn k n 1 + eTurn k n 2 = 0 := by
  have h := sum_e_relation k (n := n) 3 (by omega) {1, 2, 4} fun j _ hj => by
    obtain ⟨a, rfl⟩ := exists_eq_eArm_of_eAdj n hj
    fin_cases a <;> simp [eArm]
  rw [Finset.sum_insert (by simp), Finset.sum_pair (by simp)] at h
  simpa [eTurn, eDown, eUp, eArm, add_assoc] using h

/-- The backtrack into the long arm is minus the sum of the other two; in particular every
backtrack at the branch node lies in their span. -/
private theorem eTurn_mem_eSpan (a : Fin 3) : eTurn k n a ∈ eSpan k n := by
  have h₂ : eTurn k n 2 ∈ eSpan k n := by
    rw [eq_neg_of_add_eq_zero_right (eTurn_add_eTurn_add_eTurn k hn)]
    exact neg_mem (add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
  fin_cases a
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact h₂

/-- The backtrack into the leaf squares to zero. -/
private theorem eTurn_zero_sq : eTurn k n 0 ^ 2 = 0 :=
  pow_d_mul_u_eq_zero (N := 1) (eDown_mul_eUp_add k hn 0)
    (signlessArrow_e_eq_zero k (by simp [eArm]))

/-- The backtrack into the arm `2, 0` cubes to zero. -/
private theorem eTurn_one_pow_three : eTurn k n 1 ^ 3 = 0 :=
  pow_d_mul_u_eq_zero (N := 2) (eDown_mul_eUp_add k hn 1)
    (signlessArrow_e_eq_zero k (by simp [eArm]))

/-- The backtrack into the long arm `4, …, n - 1` has vanishing `n - 3`-rd power. -/
private theorem eTurn_two_pow : eTurn k n 2 ^ (n - 3) = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
  exact pow_d_mul_u_eq_zero (N := N) (eDown_mul_eUp_add k hn 2)
    (signlessArrow_e_eq_zero k (by simp [eArm]; omega))

end EGraph

/-! ### Normal forms of paths -/

section ENormalForm

variable (k : Type*) [CommRing k] (n : ℕ)

local notation "G" => diagramGraph (CartanMatrix.E n)

/-- The **normal forms of a path** from the node `i₀` to the node `j`, of length `L`, whose source
idempotent is `E`:

* a valley word on one arm `a`, with rungs counted from the branch node, which stays at least one
  rung away from it;
* a climb from the branch node to `j` along an arm `a`, after a product `w` of `t` backtracks at
  the branch node and a path `D` into the branch node of length `s₀ < n`. -/
private def ENormalForm (i₀ j L : ℕ) (E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)) :
    Prop :=
  (∃ (a : Fin 3) (m s r : ℕ) (ε : ℤ), 0 < m ∧ s + r = L ∧ eArm n a (m + s) = i₀ ∧
      eArm n a (m + r) = j ∧ z = ε • (ladderValley (eUp k n a) (eDown k n a) m s r * E)) ∨
  (∃ (a : Fin 3) (h t s₀ : ℕ) (w D : signlessPreprojectiveAlgebra k (DoubledQuiver G)),
      w ∈ eSpan k n ^ t ∧ s₀ < n ∧ eArm n a h = j ∧ L = s₀ + 2 * t + h ∧
      z = ladderValley (eUp k n a) (eDown k n a) 0 0 h * w * D)

variable {n} (hn : 4 ≤ n)
include hn

omit hn in
/-- A sign in the algebra is the integer sign acting by `zsmul`. -/
private theorem neg_one_pow_mul_eq_zsmul (r : ℕ)
    (z : signlessPreprojectiveAlgebra k (DoubledQuiver G)) :
    (-1) ^ r * z = ((-1 : ℤ) ^ r) • z := by
  simp [zsmul_eq_mul]

omit hn in
/-- The empty word in the backtracks at the branch node. -/
private theorem one_mem_eSpan_pow_zero : 1 ∈ eSpan k n ^ 0 := by
  rw [pow_zero]
  exact Submodule.one_le.1 le_rfl

/-- One more arrow after a valley word on an arm. -/
private theorem eNormalForm_cons_valley {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)} (hi₀ : i₀ < n) (hj : j < n)
    (hadj : EAdj j j')
    (h : ∃ (a : Fin 3) (m s r : ℕ) (ε : ℤ), 0 < m ∧ s + r = L ∧ eArm n a (m + s) = i₀ ∧
      eArm n a (m + r) = j ∧ z = ε • (ladderValley (eUp k n a) (eDown k n a) m s r * E)) :
    ENormalForm k n i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  obtain ⟨a, m, s, r, ε, hm, hL, rfl, rfl, rfl⟩ := h
  rcases eq_eArm_of_eAdj (by omega) hj hadj with rfl | rfl
  · -- A step away from the branch node extends the climb.
    have harr : signlessArrow k G (eArm n a (m + r)) (eArm n a (m + r + 1)) =
        eUp k n a (m + r) := by
      rw [eUp]
    refine .inl ⟨a, m, s, r + 1, ε, hm, by omega, rfl, by rw [add_assoc], ?_⟩
    rw [harr, mul_smul_comm, ← mul_assoc, u_mul_ladderValley]
  · -- A step towards the branch node moves the bottom of the valley down by one rung.
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have harr : signlessArrow k G (eArm n a (m + 1 + r)) (eArm n a (m + 1 + r - 1)) =
        eDown k n a (m + r) := by
      rw [eDown, Nat.add_right_comm m 1 r, Nat.add_sub_cancel]
    have hz : signlessArrow k G (eArm n a (m + 1 + r)) (eArm n a (m + 1 + r - 1)) *
        (ε • (ladderValley (eUp k n a) (eDown k n a) (m + 1) s r * E)) =
        (ε * (-1) ^ r) • (ladderValley (eUp k n a) (eDown k n a) m (s + 1) r * E) := by
      rw [harr, mul_smul_comm, ← mul_assoc, d_mul_ladderValley (eDown_mul_eUp_add k hn a),
        mul_assoc, neg_one_pow_mul_eq_zsmul, mul_smul]
    rw [hz, Nat.add_right_comm m 1 r, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · -- The valley reaches the branch node: a climb out of it after a descent into it.
      refine .inr ⟨a, r, 0, s + 1, 1, (ε * (-1) ^ r) • (ladderValley (eUp k n a) (eDown k n a) 0
        (s + 1) 0 * E), one_mem_eSpan_pow_zero k, lt_of_eArm_lt hn (by rwa [add_comm]),
        by rw [zero_add], by omega, ?_⟩
      rw [mul_one, mul_smul_comm, ← mul_assoc, ladderValley_zero_mul_ladderValley]
    · exact .inl ⟨a, m, s + 1, r, ε * (-1) ^ r, hm', by omega, by congr 1; omega, rfl, rfl⟩

/-- One more arrow after a climb out of the branch node. -/
private theorem eNormalForm_cons_climb {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)} (hj : j < n) (hadj : EAdj j j')
    (h : ∃ (a : Fin 3) (h t s₀ : ℕ) (w D : signlessPreprojectiveAlgebra k (DoubledQuiver G)),
      w ∈ eSpan k n ^ t ∧ s₀ < n ∧ eArm n a h = j ∧ L = s₀ + 2 * t + h ∧
      z = ladderValley (eUp k n a) (eDown k n a) 0 0 h * w * D) :
    ENormalForm k n i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  obtain ⟨a, h, t, s₀, w, D, hw, hs₀, rfl, hL, rfl⟩ := h
  rcases h with _ | h
  · -- From the branch node, a step into the first node of an arm.
    rw [eArm_zero] at hadj ⊢
    obtain ⟨b, rfl⟩ := exists_eq_eArm_of_eAdj n hadj
    refine .inr ⟨b, 1, t, s₀, w, D, hw, hs₀, rfl, by omega, ?_⟩
    rw [ladderValley_zero_zero, one_mul, ← mul_assoc, ← u_mul_ladderValley, ladderValley_zero_zero,
      mul_one, zero_add, eUp, eArm_zero]
  rcases eq_eArm_of_eAdj (by omega) hj hadj with rfl | rfl
  · -- A step away from the branch node extends the climb.
    have harr : signlessArrow k G (eArm n a (h + 1)) (eArm n a (h + 1 + 1)) =
        eUp k n a (0 + (h + 1)) := by
      rw [zero_add, eUp]
    refine .inr ⟨a, h + 1 + 1, t, s₀, w, D, hw, hs₀, rfl, by omega, ?_⟩
    rw [← mul_assoc, ← mul_assoc, harr, u_mul_ladderValley]
  · -- A step towards the branch node turns the climb back: one more backtrack at the branch node.
    refine .inr ⟨a, h, t + 1, s₀, ((-1 : ℤ) ^ h) • (eTurn k n a * w), D, ?_, hs₀,
      by rw [Nat.add_sub_cancel], by omega, ?_⟩
    · rw [pow_succ']
      exact Submodule.smul_mem _ _ (Submodule.mul_mem_mul (eTurn_mem_eSpan k hn a) hw)
    · have harr : signlessArrow k G (eArm n a (h + 1)) (eArm n a h) = eDown k n a h := by
        rw [eDown]
      rw [Nat.add_sub_cancel, ← mul_assoc, ← mul_assoc, harr,
        d_mul_ladderValley_zero_zero (eDown_mul_eUp_add k hn a), neg_one_pow_mul_eq_zsmul, eTurn]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- **One more arrow keeps a normal form.** -/
private theorem eNormalForm_cons {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)} (hi₀ : i₀ < n) (hj : j < n)
    (hadj : EAdj j j') (h : ENormalForm k n i₀ j L E z) :
    ENormalForm k n i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  rcases h with h | h
  · exact eNormalForm_cons_valley k hn hi₀ hj hadj h
  · exact eNormalForm_cons_climb k hn hj hadj h

/-- **Every path has a normal form**, by induction on the path. -/
private theorem eNormalForm_ofPath {a b : DoubledQuiver G} (p : Path a b) :
    ENormalForm k n ((vertexEquiv G).symm a) ((vertexEquiv G).symm b) p.length
      (signlessPreprojectiveMk k _ (ofPath ⟨a, a, .nil⟩))
      (signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩)) := by
  induction p with
  | nil =>
    -- The empty path is the empty valley word on an arm, or the empty word at the branch node.
    by_cases h : ((vertexEquiv G).symm a : ℕ) = 3
    · refine .inr ⟨0, 0, 0, 0, 1, signlessPreprojectiveMk k _ (ofPath ⟨a, a, .nil⟩),
        one_mem_eSpan_pow_zero k, by omega, by rw [h, eArm_zero], rfl, ?_⟩
      rw [ladderValley_zero_zero, one_mul, one_mul]
    · obtain ⟨c, q, hq, hcq⟩ := exists_eArm_eq n h
      exact .inl ⟨c, q, 0, 0, 1, hq, rfl, hcq, hcq, by
        rw [ladderValley_zero_zero, one_mul, one_smul]⟩
  | @cons b b' q e ih =>
    rw [← ofArrow_mul_ofPath, map_mul, signlessPreprojectiveMk_ofArrow_eq_signlessArrow,
      Path.length_cons]
    exact eNormalForm_cons k hn ((vertexEquiv G).symm a).2 ((vertexEquiv G).symm b).2
      ((diagramGraph_E_adj _ _).1 e.down) ih

/-- **Long paths vanish once long words at the branch node do.** If every product of `M`
backtracks at the branch node of `Eₙ` vanishes, then every path of length at least `2 n + 2 M`
vanishes in the signless algebra. -/
private theorem signlessPreprojectiveMk_ofPath_eq_zero_of_eSpan_pow {M : ℕ}
    (hM : eSpan k n ^ M = ⊥) (x : Quiver.TotalPath (DoubledQuiver G))
    (hx : 2 * n + 2 * M ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  obtain ⟨a, b, p⟩ := x
  dsimp only at hx
  have hb := ((vertexEquiv G).symm b).2
  rcases eNormalForm_ofPath k hn p with ⟨c, m, s, r, ε, -, hL, hs, hr, -⟩ |
    ⟨c, h, t, s₀, w, D, hw, hs₀, hh, hL, hz⟩
  · -- A valley word on an arm is too short.
    have := lt_of_eArm_lt hn (hs ▸ ((vertexEquiv G).symm a).2)
    have := lt_of_eArm_lt hn (hr ▸ hb)
    omega
  · -- Otherwise the word at the branch node is long enough to vanish.
    have := lt_of_eArm_lt hn (hh ▸ hb)
    obtain ⟨e, rfl⟩ : ∃ e, t = M + e := ⟨t - M, by omega⟩
    rw [pow_add, hM, Submodule.bot_mul, Submodule.mem_bot] at hw
    rw [hz, hw, mul_zero, zero_mul]

end ENormalForm

/-- The two-colouring of a graph with the adjacency of `Eₙ`: the parity along the chain
`0 — 2 — 3 — 4 — ⋯`, with the leaf `1` coloured like the node `2`. -/
private def eColoring {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : ∀ i j : Fin n, G.Adj i j ↔ EAdj i j) : G.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun i => decide ((if (i : ℕ) ≤ 1 then (i : ℕ) + 1 else i) % 2 = 0))
    fun {i j} h => by
      have h' := (hG i j).1 h
      simp only [EAdj] at h'
      simp only [ne_eq, decide_eq_decide]
      split_ifs <;> omega

/-! ### The `E₆` diagram -/

/-- Adjacency in the Bourbaki-labelled `E₆` diagram. -/
private theorem diagramGraph_E6_adj (i j : Fin 6) :
    (diagramGraph DynkinType.E6.cartanMatrix).Adj i j ↔ EAdj i j := by
  rw [DynkinType.cartanMatrix_E6]
  exact diagramGraph_E_adj i j

/-- The two-colouring of the `E₆` diagram. -/
private def e6Coloring : (diagramGraph DynkinType.E6.cartanMatrix).Coloring Bool :=
  eColoring _ diagramGraph_E6_adj

/-- **Every product of six backtracks at the branch node of `E₆` vanishes.** -/
private theorem eSpan_six_pow_six (k : Type*) [CommRing k] : eSpan k 6 ^ 6 = ⊥ := by
  have hsum : eTurn k 6 0 + eTurn k 6 1 = -eTurn k 6 2 :=
    eq_neg_of_add_eq_zero_left (eTurn_add_eTurn_add_eTurn k (by norm_num))
  refine span_pair_pow_six_eq_bot (eTurn_zero_sq k (by norm_num))
    (eTurn_one_pow_three k (by norm_num)) ?_
  rw [hsum, neg_pow, eTurn_two_pow k (n := 6) (by norm_num), mul_zero]

section CommRing

variable (k : Type*) [CommRing k]

/-- **Every path of length at least `24` vanishes in the signless algebra of `E₆`.** -/
@[simp]
theorem signlessPreprojectiveMk_E6_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (DoubledQuiver (diagramGraph DynkinType.E6.cartanMatrix)))
    (hx : 24 ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  -- The `E₆` Cartan matrix is `CartanMatrix.E 6`, for which the normal forms are proved.
  have key : ∀ C : Matrix (Fin 6) (Fin 6) ℤ, C = CartanMatrix.E 6 →
      ∀ x : Quiver.TotalPath (DoubledQuiver (diagramGraph C)), 24 ≤ x.2.2.length →
        signlessPreprojectiveMk k _ (ofPath x) = 0 := by
    rintro C rfl x hx
    exact signlessPreprojectiveMk_ofPath_eq_zero_of_eSpan_pow k (n := 6) (by norm_num)
      (eSpan_six_pow_six k) x hx
  exact key _ DynkinType.cartanMatrix_E6 x hx

variable (o : Orientation (diagramGraph DynkinType.E6.cartanMatrix))

/-- **Every path of length at least `24` vanishes in the preprojective algebra of `E₆`**, for
every orientation of the `E₆` graph. -/
@[simp]
theorem preprojectiveMk_E6_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath
      (Symmetrify (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o)))
    (hx : 24 ≤ x.2.2.length) :
    preprojectiveMk k (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o)
      (ofPath x) = 0 := by
  -- Every orientation of the bipartite `E₆` graph is compared with the signless algebra.
  have hc : ∀ ⦃i j : OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o⦄, (i ⟶ j) →
      e6Coloring ((OrientedQuiver.vertexEquiv _ o).symm i) ≠
        e6Coloring ((OrientedQuiver.vertexEquiv _ o).symm j) :=
    fun _ _ a => e6Coloring.valid a.1
  apply preprojectiveMk_ofPath_eq_zero_of_signless o k hc x
  exact signlessPreprojectiveMk_E6_ofPath_eq_zero_of_le k _
    (by rwa [Prefunctor.length_mapTotalPath])

/-- **The preprojective relation ideal of every orientation of `E₆` is admissible.** It lies in
the square of the arrow ideal, and it contains every path of length at least `24`. -/
theorem isAdmissibleIdeal_preprojectiveIdeal_E6 :
    IsAdmissibleIdeal
      (preprojectiveIdeal k
        (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o)).asIdeal :=
  isAdmissibleIdeal_iff.2 ⟨⟨24, fun x hx => by
    rw [TwoSidedIdeal.mem_asIdeal, ← preprojectiveMk_eq_zero_iff]
    exact preprojectiveMk_E6_ofPath_eq_zero_of_le k o x hx⟩,
    preprojectiveIdeal_le_arrowIdeal_sq k⟩

end CommRing

/-! ### Finite dimensionality -/

section Field

variable (k : Type*) [Field k]

/-- **The preprojective algebra of `E₆` is finite-dimensional**, for every orientation of the
`E₆` graph and over every field. -/
instance instFiniteDimensionalPreprojectiveAlgebraE6
    (o : Orientation (diagramGraph DynkinType.E6.cartanMatrix)) :
    FiniteDimensional k
      (preprojectiveAlgebra k (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o)) :=
  (isAdmissibleIdeal_preprojectiveIdeal_E6 k o).finiteDimensional_quotient

/-- **The signless algebra of `E₆` is finite-dimensional** over every field. -/
instance instFiniteDimensionalSignlessPreprojectiveAlgebraE6 :
    FiniteDimensional k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph DynkinType.E6.cartanMatrix))) :=
  (e6Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv k).symm.toLinearEquiv.finiteDimensional

end Field

/-! ### The `E₈` diagram -/

/-- The named `E₈` graph is the Bourbaki-labelled `Eₙ` diagram for `n = 8`. -/
private theorem zigzagE8Graph_eq : zigzagE8Graph = diagramGraph (CartanMatrix.E 8) := by
  ext i j
  rw [zigzagE8Graph_adj, diagramGraph_E_adj]
  fin_cases i <;> fin_cases j <;> simp only [EAdj] <;> decide

/-- **Every product of fifteen backtracks at the branch node of `E₈` vanishes.** -/
private theorem eSpan_eight_pow_fifteen (k : Type*) [CommRing k] : eSpan k 8 ^ 15 = ⊥ := by
  have hsum : eTurn k 8 0 + eTurn k 8 1 = -eTurn k 8 2 :=
    eq_neg_of_add_eq_zero_left (eTurn_add_eTurn_add_eTurn k (by norm_num))
  refine span_pair_pow_fifteen_eq_bot (eTurn_zero_sq k (by norm_num))
    (eTurn_one_pow_three k (by norm_num)) ?_
  rw [hsum, neg_pow, eTurn_two_pow k (n := 8) (by norm_num), mul_zero]

section CommRing

variable (k : Type*) [CommRing k]

/-- **Every path of length at least `46` vanishes in the signless algebra of `E₈`.** -/
@[simp]
theorem signlessPreprojectiveMk_E8_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (DoubledQuiver zigzagE8Graph)) (hx : 46 ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  -- The `E₈` graph is the diagram of `CartanMatrix.E 8`, for which the normal forms are proved.
  have key : ∀ G : SimpleGraph (Fin 8), G = diagramGraph (CartanMatrix.E 8) →
      ∀ x : Quiver.TotalPath (DoubledQuiver G), 46 ≤ x.2.2.length →
        signlessPreprojectiveMk k _ (ofPath x) = 0 := by
    rintro G rfl x hx
    exact signlessPreprojectiveMk_ofPath_eq_zero_of_eSpan_pow k (n := 8) (by norm_num)
      (eSpan_eight_pow_fifteen k) x hx
  exact key _ zigzagE8Graph_eq x hx

variable (o : Orientation zigzagE8Graph)

/-- **Every path of length at least `46` vanishes in the preprojective algebra of `E₈`**, for
every orientation of the `E₈` graph. -/
@[simp]
theorem preprojectiveMk_E8_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver zigzagE8Graph o)))
    (hx : 46 ≤ x.2.2.length) :
    preprojectiveMk k (OrientedQuiver zigzagE8Graph o) (ofPath x) = 0 := by
  -- Every orientation of the bipartite `E₈` graph is compared with the signless algebra.
  have hc : ∀ ⦃i j : OrientedQuiver zigzagE8Graph o⦄, (i ⟶ j) →
      zigzagE8Coloring ((OrientedQuiver.vertexEquiv _ o).symm i) ≠
        zigzagE8Coloring ((OrientedQuiver.vertexEquiv _ o).symm j) :=
    fun _ _ a => zigzagE8Coloring.valid a.1
  apply preprojectiveMk_ofPath_eq_zero_of_signless o k hc x
  exact signlessPreprojectiveMk_E8_ofPath_eq_zero_of_le k _
    (by rwa [Prefunctor.length_mapTotalPath])

/-- **The preprojective relation ideal of every orientation of `E₈` is admissible.** It lies in
the square of the arrow ideal, and it contains every path of length at least `46`. -/
theorem isAdmissibleIdeal_preprojectiveIdeal_E8 :
    IsAdmissibleIdeal (preprojectiveIdeal k (OrientedQuiver zigzagE8Graph o)).asIdeal :=
  isAdmissibleIdeal_iff.2 ⟨⟨46, fun x hx => by
    rw [TwoSidedIdeal.mem_asIdeal, ← preprojectiveMk_eq_zero_iff]
    exact preprojectiveMk_E8_ofPath_eq_zero_of_le k o x hx⟩,
    preprojectiveIdeal_le_arrowIdeal_sq k⟩

end CommRing

section Field

variable (k : Type*) [Field k]

/-- **The preprojective algebra of `E₈` is finite-dimensional**, for every orientation of the
`E₈` graph and over every field. -/
instance instFiniteDimensionalPreprojectiveAlgebraE8 (o : Orientation zigzagE8Graph) :
    FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver zigzagE8Graph o)) :=
  (isAdmissibleIdeal_preprojectiveIdeal_E8 k o).finiteDimensional_quotient

/-- **The signless algebra of `E₈` is finite-dimensional** over every field. -/
instance instFiniteDimensionalSignlessPreprojectiveAlgebraE8 :
    FiniteDimensional k (signlessPreprojectiveAlgebra k (DoubledQuiver zigzagE8Graph)) :=
  (zigzagE8SignlessEquivPreprojective k).symm.toLinearEquiv.finiteDimensional

end Field

end TauCeti
