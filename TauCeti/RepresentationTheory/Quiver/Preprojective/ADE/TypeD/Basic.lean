/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.LadderValley
public import TauCeti.Algebra.Algebra.SquareZeroPair
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# The preprojective algebra of `Dₙ` is finite-dimensional

In the Bourbaki labelling of `Dₙ` (`n ≥ 3`), write `c = n - 3`. The nodes `0 — 1 — ⋯ — c` form
the long arm, and the two leaves `c + 1` and `c + 2` are attached to the branch node `c`. In the
signless algebra `TauCeti.signlessPreprojectiveAlgebra` of the doubled graph write

* `x` and `y` for the backtracks `c → c + 1 → c` and `c → c + 2 → c`, and
* `q` for the backtrack `c → c - 1 → c` into the long arm.

The relation at a leaf says that the backtrack from the leaf vanishes, so `x * x = 0` and
`y * y = 0`, and the relation at the branch node says `x + y + q = 0`. Along the long arm, read
from the branch node, the relations are the ladder relations of
`TauCeti.Algebra.Ring.LadderValley` at every rung except the bottom one, and the ladder has only
`c` rungs; hence `q ^ (c + 1) = 0` (`TauCeti.pow_d_mul_u_eq_zero`). So `(x + y) ^ (c + 1) = 0`,
and every product of `c + 2` factors from `{x, y}` vanishes (`TauCeti.span_pair_pow_succ_eq_bot`).

A path is then rewritten, one arrow at a time, into one of the following normal forms: a valley
word on the long arm which does not reach the branch node; or a word of the shape
`(path out of c) · w · (path into c)`, where `w` is a product of factors from `{x, y}` and the
outer paths have length at most `c + 1`. A long enough path has a word `w` with at least `c + 2`
factors, so **every path of length at least `4 n` vanishes**. Below rank three the diagram has no
edges, and the same bound holds trivially. The bound `4 n` is not sharp; the sharp bound `h - 1`,
for the Coxeter number `h = 2 n - 2` of `Dₙ`, is not proved here.

The signless algebra of a bipartite graph is the preprojective algebra of each of its
orientations, by an explicit sign rescaling of the arrows. Thus the same bound holds in the
preprojective algebra `Π_k(Q)` of every orientation `Q` of `Dₙ`, over every commutative ring; the
relation ideal is admissible, and `Π_k(Q)` is finite-dimensional over every field.

## Main results

* `TauCeti.signlessPreprojectiveMk_D_ofPath_eq_zero_of_le`: paths of length at least `4 n` vanish
  in the signless algebra of `Dₙ`.
* `TauCeti.preprojectiveMk_D_ofPath_eq_zero_of_le`: the same in the preprojective algebra of every
  orientation of `Dₙ`.
* `TauCeti.isAdmissibleIdeal_preprojectiveIdeal_D`: the preprojective relation ideal of every
  orientation of `Dₙ` is admissible.
* `TauCeti.instFiniteDimensionalPreprojectiveAlgebraD` and
  `TauCeti.instFiniteDimensionalSignlessPreprojectiveAlgebraD`: the preprojective algebra of
  every orientation of `Dₙ`, and the signless algebra of `Dₙ`, are finite-dimensional.

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
noncomputable local instance forkNeighborSetFintype {V : Type*} [Finite V] (G : SimpleGraph V)
    (i : V) : Fintype (G.neighborSet i) :=
  Fintype.ofFinite _

/-! ### Graphs with a long arm and two leaves at its end -/

section ForkGraph

variable (k : Type*) [CommRing k] {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ)

/-- The step away from the branch node `c` along the long arm, from rung `r` (the node `c - r`) to
rung `r + 1`. It vanishes from rung `c` on. -/
private noncomputable def forkUp (r : ℕ) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  signlessArrow k G (c - r) (c - r - 1)

/-- The step towards the branch node `c` along the long arm, from rung `r + 1` to rung `r`. -/
private noncomputable def forkDown (r : ℕ) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  signlessArrow k G (c - r - 1) (c - r)

/-- The backtrack `c → l → c` from the branch node into the vertex `l`. -/
private noncomputable def forkTurn (l : ℕ) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  signlessArrow k G l c * signlessArrow k G c l

/-- The span of the two backtracks from the branch node into the leaves. -/
private noncomputable def forkSpan :
    Submodule ℤ (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  Submodule.span ℤ {forkTurn k G c (c + 1), forkTurn k G c (c + 2)}

/-- The **normal forms of a path** from the vertex `i₀` to the vertex `j`, of length `L`, whose
source idempotent is `E`:

* a valley word on the long arm, with rungs counted from the branch node, which stays at least
  one rung away from it;
* a climb from the branch node to `j` on the long arm, after a product `w` of `t` backtracks into
  the leaves and a path `D` into the branch node of length at most `c + 1`;
* the arrow from the branch node to the leaf `j`, after such `w` and `D`;
* the empty path at a leaf. -/
private def ForkNormalForm (i₀ j L : ℕ) (E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)) :
    Prop :=
  (∃ m s r : ℕ, ∃ ε : ℤ, 0 < m ∧ s + r = L ∧ m + s = c - i₀ ∧ m + r = c - j ∧
      z = ε • (ladderValley (forkUp k G c) (forkDown k G c) m s r * E)) ∨
  (∃ t s₀ : ℕ, ∃ w D, w ∈ forkSpan k G c ^ t ∧ s₀ ≤ c + 1 ∧ j ≤ c ∧ L = s₀ + 2 * t + (c - j) ∧
      z = ladderValley (forkUp k G c) (forkDown k G c) 0 0 (c - j) * w * D) ∨
  (∃ t s₀ : ℕ, ∃ w D, w ∈ forkSpan k G c ^ t ∧ s₀ ≤ c + 1 ∧ c < j ∧ L = s₀ + 2 * t + 1 ∧
      z = signlessArrow k G c j * w * D) ∨
  (L = 0 ∧ c < j ∧ z = E)

variable {G} {c}
variable (hn : n = c + 3)
  (hG : ∀ i j : Fin n, G.Adj i j ↔ (i : ℕ) + 1 = j ∧ (j : ℕ) ≤ c ∨ (j : ℕ) + 1 = i ∧ (i : ℕ) ≤ c ∨
    (i : ℕ) = c ∧ c < j ∨ (j : ℕ) = c ∧ c < i)
include hn hG

omit hn in
/-- The relation at a vertex `v`, summed over a set `S` of vertices containing its neighbours. -/
private theorem sum_fork_relation (v : ℕ) (hv : v < n) (S : Finset ℕ) (hS : ∀ w ∈ S, w < n)
    (hnbr : ∀ w < n, w ∉ S → ¬(v + 1 = w ∧ w ≤ c ∨ w + 1 = v ∧ v ≤ c ∨ v = c ∧ c < w ∨
      w = c ∧ c < v)) :
    ∑ w ∈ S, signlessArrow k G w v * signlessArrow k G v w = 0 := by
  have h := sum_signlessArrow_mul_signlessArrow k G ⟨v, hv⟩
  rw [Fin.sum_univ_eq_sum_range (fun w => signlessArrow k G w v * signlessArrow k G v w) n] at h
  rw [← h]
  refine Finset.sum_subset (fun w hw => Finset.mem_range.2 (hS w hw)) fun w hw hwS => ?_
  rw [signlessArrow_eq_zero k fun _ _ hvw => hnbr w (Finset.mem_range.1 hw) hwS ((hG _ _).1 hvw),
    mul_zero]

omit hn in
/-- An arrow vanishes between two vertices which are not adjacent. -/
private theorem signlessArrow_fork_eq_zero {i j : ℕ}
    (h : ¬(i + 1 = j ∧ j ≤ c ∨ j + 1 = i ∧ i ≤ c ∨ i = c ∧ c < j ∨ j = c ∧ c < i)) :
    signlessArrow k G i j = 0 :=
  signlessArrow_eq_zero k fun _ _ hij => h ((hG _ _).1 hij)

/-- **The ladder relations of the long arm.** At every vertex of the long arm other than the
branch node, the backtrack away from the branch node cancels the backtrack towards it. -/
private theorem forkDown_mul_forkUp_add (w : ℕ) :
    forkDown k G c (w + 1) * forkUp k G c (w + 1) + forkUp k G c w * forkDown k G c w = 0 := by
  by_cases hw : w + 1 ≤ c
  · -- The rung `w + 1` is the vertex `v = c - (w + 1)`, with neighbours `v - 1` and `v + 1`.
    obtain ⟨v, rfl⟩ : ∃ v, c = v + (w + 1) := ⟨c - (w + 1), by omega⟩
    have h := sum_fork_relation k hG v (by omega) {v - 1, v + 1}
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
      (fun u _ hu => by simp only [Finset.mem_insert, Finset.mem_singleton] at hu; omega)
    rw [Finset.sum_pair (by omega)] at h
    have hrung : v + (w + 1) - (w + 1) = v := by omega
    have hprev : v + (w + 1) - w = v + 1 := by omega
    simp only [forkUp, forkDown]
    rwa [hrung, hprev, Nat.add_sub_cancel]
  · -- Beyond the end of the long arm every step vanishes.
    have h0 : signlessArrow k G 0 0 = 0 := signlessArrow_fork_eq_zero k hG (by omega)
    have hrung : c - (w + 1) = 0 := by omega
    have hprev : c - w = 0 := by omega
    simp only [forkUp, forkDown, hrung, hprev, h0, mul_zero, add_zero]

/-- **The relation at a leaf**: the backtrack from a leaf `l` vanishes. -/
private theorem signlessArrow_mul_signlessArrow_leaf {l : ℕ} (hl : c < l) (hln : l < n) :
    signlessArrow k G c l * signlessArrow k G l c = 0 := by
  have h := sum_fork_relation k hG l hln {c} (by simp; omega)
    (fun u _ hu => by simp only [Finset.mem_singleton] at hu; omega)
  rwa [Finset.sum_singleton] at h

/-- **The relation at the branch node**: the backtrack into the long arm and the backtracks into
the two leaves sum to zero. -/
private theorem forkDown_mul_forkUp_add_forkTurn :
    forkDown k G c 0 * forkUp k G c 0 + (forkTurn k G c (c + 1) + forkTurn k G c (c + 2)) = 0 := by
  have h := sum_fork_relation k hG c (by omega) {c - 1, c + 1, c + 2}
    (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    (fun u hu hu' => by simp only [Finset.mem_insert, Finset.mem_singleton] at hu'; omega)
  rwa [Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega)] at h

/-- The backtracks into the leaves square to zero. -/
private theorem forkTurn_mul_self {l : ℕ} (hl : c < l) (hln : l < n) :
    forkTurn k G c l * forkTurn k G c l = 0 := by
  rw [forkTurn, mul_assoc, ← mul_assoc (signlessArrow k G c l),
    signlessArrow_mul_signlessArrow_leaf k hn hG hl hln, zero_mul, mul_zero]

/-- The backtrack into the long arm is minus the sum of the backtracks into the leaves; in
particular it lies in their span. -/
private theorem forkDown_mul_forkUp_mem_forkSpan :
    forkDown k G c 0 * forkUp k G c 0 ∈ forkSpan k G c := by
  rw [eq_neg_of_add_eq_zero_left (forkDown_mul_forkUp_add_forkTurn k hn hG)]
  exact neg_mem (add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))

/-- **Every product of `c + 2` backtracks into the leaves vanishes.** -/
private theorem forkSpan_pow_eq_bot {t : ℕ} (ht : c + 2 ≤ t) : forkSpan k G c ^ t = ⊥ := by
  -- The backtrack into the long arm is nilpotent, since the long arm has `c` rungs.
  have hq : (forkDown k G c 0 * forkUp k G c 0) ^ (c + 1) = 0 := by
    refine pow_d_mul_u_eq_zero (forkDown_mul_forkUp_add k hn hG) ?_
    exact signlessArrow_fork_eq_zero k hG (by omega)
  have hsum : (forkTurn k G c (c + 1) + forkTurn k G c (c + 2)) ^ (c + 1) = 0 := by
    rw [← neg_eq_of_add_eq_zero_right (forkDown_mul_forkUp_add_forkTurn k hn hG), neg_pow, hq,
      mul_zero]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [pow_add, forkSpan, span_pair_pow_succ_eq_bot (forkTurn_mul_self k hn hG (by omega) (by omega))
    (forkTurn_mul_self k hn hG (by omega) (by omega)) hsum, Submodule.bot_mul]

/-! ### Normal forms of paths -/

omit hn hG in
/-- A sign in the algebra is the integer sign acting by `zsmul`. -/
private theorem neg_one_pow_mul_eq_zsmul (r : ℕ)
    (a : signlessPreprojectiveAlgebra k (DoubledQuiver G)) :
    (-1) ^ r * a = ((-1 : ℤ) ^ r) • a := by
  simp [zsmul_eq_mul]

omit hn hG in
/-- The empty word in the backtracks into the leaves. -/
private theorem one_mem_forkSpan_pow_zero : 1 ∈ forkSpan k G c ^ 0 := by
  rw [pow_zero]
  exact Submodule.one_le.1 le_rfl

/-- One more arrow after a valley word on the long arm. -/
private theorem forkNormalForm_cons_valley {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hadj : j + 1 = j' ∧ j' ≤ c ∨ j' + 1 = j ∧ j ≤ c ∨ j = c ∧ c < j' ∨ j' = c ∧ c < j)
    (h : ∃ m s r : ℕ, ∃ ε : ℤ, 0 < m ∧ s + r = L ∧ m + s = c - i₀ ∧ m + r = c - j ∧
      z = ε • (ladderValley (forkUp k G c) (forkDown k G c) m s r * E)) :
    ForkNormalForm k G c i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  obtain ⟨m, s, r, ε, hm, hL, hs, hr, rfl⟩ := h
  rcases hadj with ⟨hj, hj'⟩ | ⟨hj, hjc⟩ | ⟨rfl, -⟩ | ⟨-, hj⟩
  · -- A step towards the branch node moves the bottom of the valley down by one rung.
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have harr : signlessArrow k G j j' = forkDown k G c (m + r) := by
      rw [forkDown]
      congr 1 <;> omega
    have hz : signlessArrow k G j j' *
        (ε • (ladderValley (forkUp k G c) (forkDown k G c) (m + 1) s r * E)) =
        (ε * (-1) ^ r) • (ladderValley (forkUp k G c) (forkDown k G c) m (s + 1) r * E) := by
      rw [harr, mul_smul_comm, ← mul_assoc, d_mul_ladderValley (forkDown_mul_forkUp_add k hn hG),
        mul_assoc, neg_one_pow_mul_eq_zsmul, mul_smul]
    rw [hz]
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · -- The valley reaches the branch node: a climb out of it after a descent into it.
      have hj'r : c - j' = r := by omega
      refine .inr (.inl ⟨0, s + 1, 1, (ε * (-1) ^ r) • (ladderValley (forkUp k G c)
        (forkDown k G c) 0 (s + 1) 0 * E), one_mem_forkSpan_pow_zero k, by omega, hj', by omega,
        ?_⟩)
      rw [hj'r, mul_one, mul_smul_comm, ← mul_assoc,
        ladderValley_zero_mul_ladderValley]
    · exact .inl ⟨m, s + 1, r, ε * (-1) ^ r, hm', by omega, by omega, by omega, rfl⟩
  · -- A step away from the branch node extends the climb.
    have harr : signlessArrow k G j j' = forkUp k G c (m + r) := by
      rw [forkUp]
      congr 1 <;> omega
    refine .inl ⟨m, s, r + 1, ε, hm, by omega, hs, by omega, ?_⟩
    rw [harr, mul_smul_comm, ← mul_assoc, u_mul_ladderValley]
  · omega
  · omega

/-- One more arrow after a word ending on the long arm, at or beyond the branch node. -/
private theorem forkNormalForm_cons_arm {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hadj : j + 1 = j' ∧ j' ≤ c ∨ j' + 1 = j ∧ j ≤ c ∨ j = c ∧ c < j' ∨ j' = c ∧ c < j)
    (h : ∃ t s₀ : ℕ, ∃ w D, w ∈ forkSpan k G c ^ t ∧ s₀ ≤ c + 1 ∧ j ≤ c ∧
      L = s₀ + 2 * t + (c - j) ∧
      z = ladderValley (forkUp k G c) (forkDown k G c) 0 0 (c - j) * w * D) :
    ForkNormalForm k G c i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  obtain ⟨t, s₀, w, D, hw, hs₀, hjc, hL, rfl⟩ := h
  rcases hadj with ⟨hj, hj'⟩ | ⟨hj, -⟩ | ⟨rfl, hj'⟩ | ⟨-, hj⟩
  · -- A step towards the branch node turns the climb back: one more backtrack, into the arm.
    obtain ⟨r, hr⟩ : ∃ r, c - j = r + 1 := ⟨c - j - 1, by omega⟩
    have harr : signlessArrow k G j j' = forkDown k G c r := by
      rw [forkDown]
      congr 1 <;> omega
    refine .inr (.inl ⟨t + 1, s₀, ((-1 : ℤ) ^ r) • (forkDown k G c 0 * forkUp k G c 0 * w), D,
      ?_, hs₀, hj', by omega, ?_⟩)
    · rw [pow_succ']
      exact Submodule.smul_mem _ _
        (Submodule.mul_mem_mul (forkDown_mul_forkUp_mem_forkSpan k hn hG) hw)
    · have hj'r : c - j' = r := by omega
      rw [hr, harr, hj'r, ← mul_assoc, ← mul_assoc,
        d_mul_ladderValley_zero_zero (forkDown_mul_forkUp_add k hn hG), neg_one_pow_mul_eq_zsmul]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  · -- A step away from the branch node extends the climb.
    have harr : signlessArrow k G j j' = forkUp k G c (c - j) := by
      rw [forkUp]
      congr 1 <;> omega
    have hj'r : c - j' = c - j + 1 := by omega
    refine .inr (.inl ⟨t, s₀, w, D, hw, hs₀, by omega, by omega, ?_⟩)
    rw [harr, ← mul_assoc, ← mul_assoc, hj'r, ← u_mul_ladderValley,
      zero_add]
  · -- A step from the branch node into a leaf.
    refine .inr (.inr (.inl ⟨t, s₀, w, D, hw, hs₀, hj', by omega, ?_⟩))
    simp only [Nat.sub_self, ladderValley_zero_zero, one_mul, mul_assoc]
  · omega

omit hG in
/-- One more arrow after a word ending at a leaf, after a step into it from the branch node. -/
private theorem forkNormalForm_cons_leaf {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)} (hjn : j < n)
    (hadj : j + 1 = j' ∧ j' ≤ c ∨ j' + 1 = j ∧ j ≤ c ∨ j = c ∧ c < j' ∨ j' = c ∧ c < j)
    (h : ∃ t s₀ : ℕ, ∃ w D, w ∈ forkSpan k G c ^ t ∧ s₀ ≤ c + 1 ∧ c < j ∧
      L = s₀ + 2 * t + 1 ∧ z = signlessArrow k G c j * w * D) :
    ForkNormalForm k G c i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  obtain ⟨t, s₀, w, D, hw, hs₀, hcj, hL, rfl⟩ := h
  obtain rfl : c = j' := by omega
  -- The step back to the branch node completes a backtrack into the leaf.
  have hturn : forkTurn k G c j ∈ forkSpan k G c := by
    obtain rfl | rfl : j = c + 1 ∨ j = c + 2 := by omega
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  refine .inr (.inl ⟨t + 1, s₀, forkTurn k G c j * w, D, ?_, hs₀, le_rfl, by omega, ?_⟩)
  · rw [pow_succ']
    exact Submodule.mul_mem_mul hturn hw
  · rw [Nat.sub_self, ladderValley_zero_zero, one_mul, forkTurn]
    simp only [mul_assoc]

/-- **One more arrow keeps a normal form.** -/
private theorem forkNormalForm_cons {i₀ j j' L : ℕ}
    {E z : signlessPreprojectiveAlgebra k (DoubledQuiver G)} (hjn : j < n)
    (hadj : j + 1 = j' ∧ j' ≤ c ∨ j' + 1 = j ∧ j ≤ c ∨ j = c ∧ c < j' ∨ j' = c ∧ c < j)
    (h : ForkNormalForm k G c i₀ j L E z) :
    ForkNormalForm k G c i₀ j' (L + 1) E (signlessArrow k G j j' * z) := by
  rcases h with h | h | h | ⟨rfl, hj, rfl⟩
  · exact forkNormalForm_cons_valley k hn hG hadj h
  · exact forkNormalForm_cons_arm k hn hG hadj h
  · exact forkNormalForm_cons_leaf k hn hjn hadj h
  · -- The first step from a leaf goes to the branch node.
    obtain rfl : c = j' := by omega
    refine .inr (.inl ⟨0, 1, 1, signlessArrow k G j c * z, one_mem_forkSpan_pow_zero k, by omega,
      le_rfl, by omega, ?_⟩)
    rw [Nat.sub_self, ladderValley_zero_zero, one_mul, one_mul]

/-- **Every path has a normal form**, by induction on the path. -/
private theorem forkNormalForm_ofPath {a b : DoubledQuiver G} (p : Path a b) :
    ForkNormalForm k G c ((vertexEquiv G).symm a) ((vertexEquiv G).symm b) p.length
      (signlessPreprojectiveMk k _ (ofPath ⟨a, a, .nil⟩))
      (signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩)) := by
  induction p with
  | nil =>
    -- The empty path is a valley word of length zero on the long arm, the empty word at the
    -- branch node, or the empty path at a leaf.
    rcases lt_trichotomy ((vertexEquiv G).symm a : ℕ) c with h | h | h
    · exact .inl ⟨c - (vertexEquiv G).symm a, 0, 0, 1, by omega, rfl, rfl, rfl,
        by rw [ladderValley_zero_zero, one_mul, one_smul]⟩
    · refine .inr (.inl ⟨0, 0, 1, signlessPreprojectiveMk k _ (ofPath ⟨a, a, .nil⟩),
        one_mem_forkSpan_pow_zero k, by omega, h.le,
        by rw [Path.length_nil]; omega, ?_⟩)
      rw [h, Nat.sub_self, ladderValley_zero_zero, one_mul, one_mul]
    · exact .inr (.inr (.inr ⟨rfl, h, rfl⟩))
  | @cons b b' q e ih =>
    rw [← ofArrow_mul_ofPath, map_mul, signlessPreprojectiveMk_ofArrow_eq_signlessArrow,
      Path.length_cons]
    exact forkNormalForm_cons k hn hG ((vertexEquiv G).symm b).2 ((hG _ _).1 e.down) ih

/-- **Every path of length at least `4 n` vanishes** in the signless algebra of a graph on
`Fin (c + 3)` made of a long arm `0, …, c` and two leaves `c + 1`, `c + 2` attached to `c`. -/
private theorem signlessPreprojectiveMk_ofPath_eq_zero_of_fork
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : 4 * n ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  obtain ⟨a, b, p⟩ := x
  dsimp only at hx
  have hb := ((vertexEquiv G).symm b).2
  -- A valley word on the long arm, or the empty path, is too short; otherwise the word in the
  -- backtracks into the leaves is long enough to vanish.
  rcases forkNormalForm_ofPath k hn hG p with ⟨m, s, r, ε, hm, hL, hs, hr, -⟩ |
    ⟨t, s₀, w, D, hw, hs₀, -, hL, h⟩ | ⟨t, s₀, w, D, hw, hs₀, -, hL, h⟩ | ⟨hL, -, -⟩
  · omega
  · rw [forkSpan_pow_eq_bot k hn hG (by omega), Submodule.mem_bot] at hw
    rw [h, hw, mul_zero, zero_mul]
  · rw [forkSpan_pow_eq_bot k hn hG (by omega), Submodule.mem_bot] at hw
    rw [h, hw, mul_zero, zero_mul]
  · omega

end ForkGraph

/-! ### The `Dₙ` diagram -/

/-- From rank three on, two nodes of the `Dₙ` diagram are joined exactly when they are consecutive
on the long arm `0, …, n - 3`, or one is the branch node `n - 3` and the other a leaf. -/
private theorem diagramGraph_D_adj {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (diagramGraph (DynkinType.D n).cartanMatrix : SimpleGraph (Fin n)).Adj i j ↔
      (i : ℕ) + 1 = j ∧ (j : ℕ) ≤ n - 3 ∨ (j : ℕ) + 1 = i ∧ (i : ℕ) ≤ n - 3 ∨
        (i : ℕ) = n - 3 ∧ n - 3 < j ∨ (j : ℕ) = n - 3 ∧ n - 3 < i := by
  rw [DynkinType.cartanMatrix_D, diagramGraph_adj]
  simp only [CartanMatrix.D, Matrix.of_apply, ne_eq, Fin.ext_iff]
  have := i.2
  have := j.2
  split_ifs <;> simp <;> omega

/-- Below rank three the `Dₙ` diagram has no edges. -/
private theorem not_diagramGraph_D_adj {n : ℕ} (hn : n < 3) (i j : Fin n) :
    ¬(diagramGraph (DynkinType.D n).cartanMatrix : SimpleGraph (Fin n)).Adj i j := by
  rw [DynkinType.cartanMatrix_D, diagramGraph_adj]
  rintro ⟨hij, h, -⟩
  have hn' : n ≤ 2 := by omega
  simp [CartanMatrix.D, hn', hij] at h

/-- The two-colouring of `Dₙ`: the parity along the long arm, with both leaves coloured like the
node `n - 2`. -/
private def dColoring (n : ℕ) : (diagramGraph (DynkinType.D n).cartanMatrix).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun i => decide (min (i : ℕ) (n - 2) % 2 = 0)) fun {i j} h => by
    by_cases hn : 3 ≤ n
    · have := (diagramGraph_D_adj (n := n) hn i j).1 h
      simp only [ne_eq, decide_eq_decide]
      omega
    · exact absurd h (not_diagramGraph_D_adj (n := n) (by omega) i j)

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

/-- **Every path of length at least `4 n` vanishes in the signless algebra of `Dₙ`.** -/
@[simp]
theorem signlessPreprojectiveMk_D_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (DoubledQuiver (diagramGraph (DynkinType.D n).cartanMatrix)))
    (hx : 4 * n ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  by_cases hn : 3 ≤ n
  · exact signlessPreprojectiveMk_ofPath_eq_zero_of_fork k (n := n) (c := n - 3) (by omega)
      (diagramGraph_D_adj hn) x hx
  · -- Below rank three there are no arrows, and the only empty paths are over no vertices.
    obtain ⟨a, b, p⟩ := x
    cases p with
    | nil =>
      have : _ < n := ((vertexEquiv _).symm a).2
      simp only [Path.length_nil] at hx
      omega
    | cons q e => exact absurd e.down (not_diagramGraph_D_adj (n := n) (by omega) _ _)

variable (o : Orientation (diagramGraph (DynkinType.D n).cartanMatrix))

/-- **Every path of length at least `4 n` vanishes in the preprojective algebra of `Dₙ`**, for
every orientation of the `Dₙ` graph. -/
@[simp]
theorem preprojectiveMk_D_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath
      (Symmetrify (OrientedQuiver (diagramGraph (DynkinType.D n).cartanMatrix) o)))
    (hx : 4 * n ≤ x.2.2.length) :
    preprojectiveMk k (OrientedQuiver (diagramGraph (DynkinType.D n).cartanMatrix) o)
      (ofPath x) = 0 := by
  -- Every orientation of the bipartite `Dₙ` graph is compared with the signless algebra.
  have hc : ∀ ⦃i j : OrientedQuiver (diagramGraph (DynkinType.D n).cartanMatrix) o⦄, (i ⟶ j) →
      dColoring n ((OrientedQuiver.vertexEquiv _ o).symm i) ≠
        dColoring n ((OrientedQuiver.vertexEquiv _ o).symm j) :=
    fun _ _ a => (dColoring n).valid a.1
  apply preprojectiveMk_ofPath_eq_zero_of_signless o k hc x
  exact signlessPreprojectiveMk_D_ofPath_eq_zero_of_le k _
    (by rwa [Prefunctor.length_mapTotalPath])

/-- **The preprojective relation ideal of every orientation of `Dₙ` is admissible.** It lies in
the square of the arrow ideal, and it contains every path of length at least `4 n`. -/
theorem isAdmissibleIdeal_preprojectiveIdeal_D :
    IsAdmissibleIdeal
      (preprojectiveIdeal k
        (OrientedQuiver (diagramGraph (DynkinType.D n).cartanMatrix) o)).asIdeal :=
  isAdmissibleIdeal_iff.2 ⟨⟨4 * n, fun x hx => by
    rw [TwoSidedIdeal.mem_asIdeal, ← preprojectiveMk_eq_zero_iff]
    exact preprojectiveMk_D_ofPath_eq_zero_of_le k o x hx⟩,
    preprojectiveIdeal_le_arrowIdeal_sq k⟩

end CommRing

/-! ### Finite dimensionality -/

section Field

variable (k : Type*) [Field k] {n : ℕ}

/-- **The preprojective algebra of `Dₙ` is finite-dimensional**, for every orientation of the
`Dₙ` graph and over every field. -/
instance instFiniteDimensionalPreprojectiveAlgebraD
    (o : Orientation (diagramGraph (DynkinType.D n).cartanMatrix)) :
    FiniteDimensional k
      (preprojectiveAlgebra k (OrientedQuiver (diagramGraph (DynkinType.D n).cartanMatrix) o)) :=
  (isAdmissibleIdeal_preprojectiveIdeal_D k o).finiteDimensional_quotient

/-- **The signless algebra of `Dₙ` is finite-dimensional** over every field. -/
instance instFiniteDimensionalSignlessPreprojectiveAlgebraD :
    FiniteDimensional k
      (signlessPreprojectiveAlgebra k
        (DoubledQuiver (diagramGraph (DynkinType.D n).cartanMatrix))) :=
  ((dColoring n).sourceSinkSignlessPreprojectiveAlgebraEquiv k).symm.toLinearEquiv.finiteDimensional

end Field

end TauCeti
