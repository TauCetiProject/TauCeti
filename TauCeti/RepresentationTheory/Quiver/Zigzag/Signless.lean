/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.PathAlgebra

/-!
# The signless relator of a simple graph

For the doubled quiver `TauCeti.DoubledQuiver G` of a simple graph `G`, at any vertex `v` with
finite neighbourhood the signless preprojective relator `TauCeti.signlessPreprojectiveRelator` is
`∑_{j ∼ v} (v → j → v)`, the sum of the backtracks along the edges at `v`. This is the relation
which Huerfano and Khovanov find in the quadratic dual of the zigzag algebra of `G`.

For a graph on `Fin n`, the class of the doubled arrow from `i` to `j` in the signless algebra
is recorded as a function `TauCeti.signlessArrow` of two natural numbers, zero unless they are
adjacent vertices. Products of these classes are the classes of paths, and the relator at `v`
becomes `∑ w, signlessArrow w v * signlessArrow v w = 0`; indexing by natural numbers lets the
computations along the arms of a Dynkin diagram use ordinary arithmetic on vertex labels.

A walk is recorded by the list of its vertices, latest vertex first, and
`TauCeti.signlessWord` sends it to the product of its arrow classes; prepending a vertex is left
multiplication by an arrow. These classes multiply by concatenation of walks, and every walk class
is the class of a path of the doubled quiver.

## Main definitions

* `TauCeti.signlessArrow`: the class of the doubled arrow between two vertices of a graph on
  `Fin n`, or zero.
* `TauCeti.signlessWord`: the class of the walk through a list of vertices.

## Main results

* `TauCeti.signlessPreprojectiveRelator_vertex`: at a vertex with finite neighbourhood, the
  relator is the sum of the backtracks `TauCeti.DoubledQuiver.backtrackElem` over the neighbours.
* `TauCeti.signlessPreprojectiveMk_ofArrow_eq_signlessArrow`: the class of every doubled arrow is
  a `TauCeti.signlessArrow`.
* `TauCeti.sum_signlessArrow_mul_signlessArrow`: the relation at a vertex, as a sum over all
  vertices.
* `TauCeti.signlessWord_mul_signlessWord`: walk classes multiply by concatenation.
* `TauCeti.exists_ofPath_eq_signlessWord`: the class of a walk is the class of a path through the
  same vertices.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u w

variable (k : Type w) {V : Type u} [Semiring k] (G : SimpleGraph V)

/-- **The signless relator of a simple graph** at `v` is `∑_{j ∼ v} (v → j → v)`, the sum of the
backtracks along the edges at `v`. -/
theorem signlessPreprojectiveRelator_vertex (v : V) [Fintype (G.neighborSet v)] :
    signlessPreprojectiveRelator k (DoubledQuiver.vertex G v) =
      ∑ w : G.neighborSet v, DoubledQuiver.backtrackElem G k ((G.mem_neighborSet v w).1 w.2) := by
  rw [signlessPreprojectiveRelator_def,
    ← (DoubledQuiver.starEquivNeighborSet G v).symm.sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [DoubledQuiver.starEquivNeighborSet_symm_apply, DoubledQuiver.backtrackElem_eq_ofPath,
    DoubledQuiver.backtrackPath_eq_comp, DoubledQuiver.arrowPath_eq_toPath,
    DoubledQuiver.arrowPath_eq_toPath]
  -- The reverse of the arrow along `w` is the arrow of the symmetric adjacency.
  rfl

/-! ### Arrow classes of a graph on `Fin n` -/

section FinArrow

open DoubledQuiver

variable (k : Type w) [CommRing k] {n : ℕ} (G : SimpleGraph (Fin n))
  [∀ i, Fintype (G.neighborSet i)]

open scoped Classical in
/-- The class of the doubled arrow from `i` to `j` in the signless algebra of a graph `G` on
`Fin n`, or zero if `i` and `j` are not adjacent vertices of `G`. The vertices are given as natural
numbers, so that arithmetic on vertex labels needs no bounds. -/
noncomputable def signlessArrow (i j : ℕ) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  if h : i < n ∧ j < n then
    if hij : G.Adj ⟨i, h.1⟩ ⟨j, h.2⟩ then signlessPreprojectiveMk k _ (ofArrow (arrow G hij))
    else 0
  else 0

variable {G}

/-- Between adjacent vertices, `signlessArrow` is the class of the doubled arrow. -/
@[simp] theorem signlessArrow_of_adj {i j : Fin n} (h : G.Adj i j) :
    signlessArrow k G i j = signlessPreprojectiveMk k _ (ofArrow (arrow G h)) := by
  simp [signlessArrow, h]

/-- Between non-adjacent vertices, `signlessArrow` vanishes. -/
@[simp] theorem signlessArrow_eq_zero {i j : ℕ}
    (h : ∀ (hi : i < n) (hj : j < n), ¬G.Adj ⟨i, hi⟩ ⟨j, hj⟩) :
    signlessArrow k G i j = 0 := by
  by_cases hn : i < n ∧ j < n
  · simp [signlessArrow, hn, h hn.1 hn.2]
  · simp [signlessArrow, hn]

/-- The class of an arbitrary doubled arrow of `G` is the `signlessArrow` between its endpoints. -/
theorem signlessPreprojectiveMk_ofArrow_eq_signlessArrow {i j : DoubledQuiver G} (e : i ⟶ j) :
    signlessPreprojectiveMk k _ (ofArrow e) =
      signlessArrow k G ((vertexEquiv G).symm i) ((vertexEquiv G).symm j) := by
  obtain ⟨i, rfl⟩ := exists_eq_vertex G i
  obtain ⟨j, rfl⟩ := exists_eq_vertex G j
  rw [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex,
    signlessArrow_of_adj k ((nonempty_hom_iff G).1 ⟨e⟩)]
  exact congrArg (fun e => signlessPreprojectiveMk k _ (ofArrow e)) (Subsingleton.elim _ _)

/-- Cutting an arrow class on the right selects its source vertex. -/
@[simp]
theorem signlessArrow_mul_vertexIdempotent (i j : ℕ) (v : Fin n) :
    signlessArrow k G i j * signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G v)) =
      if i = v.val then signlessArrow k G i j else 0 := by
  classical
  unfold signlessArrow
  split_ifs with h hij hv
  all_goals try simp only [zero_mul]
  · have hvi : (⟨i, h.1⟩ : Fin n) = v := Fin.ext hv
    subst v
    rw [← map_mul, ofArrow_eq_ofPath, ofPath_mul_vertexIdempotent]
  · rw [← map_mul, ofArrow_eq_ofPath, ofPath_mul_vertexIdempotent_of_ne, map_zero]
    exact fun he => hv (congrArg Fin.val (vertex_injective G he.symm))

/-- Cutting an arrow class on the left selects its target vertex. -/
@[simp]
theorem vertexIdempotent_mul_signlessArrow (v : Fin n) (i j : ℕ) :
    signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G v)) * signlessArrow k G i j =
      if j = v.val then signlessArrow k G i j else 0 := by
  classical
  unfold signlessArrow
  split_ifs with h hij hv
  all_goals try simp only [mul_zero]
  · have hvj : (⟨j, h.2⟩ : Fin n) = v := Fin.ext hv
    subst v
    rw [← map_mul, ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]
  · rw [← map_mul, ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath_of_ne, map_zero]
    exact fun he => hv (congrArg Fin.val (vertex_injective G he.symm))

variable (G) in
/-- **The signless relation at a vertex `v`**: the backtracks `v → w → v` sum to zero, the sum
running over all vertices `w`, of which only the neighbours of `v` contribute. -/
theorem sum_signlessArrow_mul_signlessArrow (v : Fin n) :
    ∑ w : Fin n, signlessArrow k G w v * signlessArrow k G v w = 0 := by
  classical
  have hrel := signlessPreprojectiveMk_signlessPreprojectiveRelator k (vertex G v)
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum] at hrel
  -- Only the neighbours of `v` contribute, and they contribute the backtracks of the relator.
  calc ∑ w : Fin n, signlessArrow k G w v * signlessArrow k G v w
      = ∑ w ∈ Finset.univ.filter (G.Adj v), signlessArrow k G w v * signlessArrow k G v w := by
        refine (Finset.sum_filter_of_ne fun w _ hw => ?_).symm
        by_contra h
        exact hw (by rw [signlessArrow_eq_zero k fun _ _ h' => h (G.adj_symm (by simpa using h')),
          zero_mul])
    _ = ∑ w : G.neighborSet v, signlessArrow k G w v * signlessArrow k G v w :=
        Finset.sum_subtype _ (fun w => by simp) _
    _ = 0 := by
        rw [← hrel]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← ofArrow_symm_mul_ofArrow _ k w.2, map_mul, ← signlessArrow_of_adj k w.2,
          ← signlessArrow_of_adj k (G.adj_symm w.2)]

/-- **The signless relation at a vertex `v` of a graph whose edges join consecutive vertices**:
the backtrack through `v + 1` cancels the backtrack through `v - 1`.
At an end vertex the missing backtrack is zero. -/
theorem signlessArrow_relation_of_consecutive
    (hconsecutive : ∀ i j : Fin n, G.Adj i j → (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) (v : ℕ) :
    signlessArrow k G (v + 1) v * signlessArrow k G v (v + 1) +
      signlessArrow k G (v - 1) v * signlessArrow k G v (v - 1) = 0 := by
  by_cases hv : v < n
  swap
  · rw [signlessArrow_eq_zero k (i := v + 1) (fun _ => by omega),
      signlessArrow_eq_zero k (i := v - 1) (fun _ _ => by omega), zero_mul, zero_mul, add_zero]
  let F : ℕ → signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
    fun w => signlessArrow k G w v * signlessArrow k G v w
  have hF (w : ℕ) (hw : ¬(w + 1 = v ∨ v + 1 = w)) : F w = 0 := by
    simp only [F, signlessArrow_eq_zero k (fun _ _ hij => hw (hconsecutive _ _ hij)), zero_mul]
  -- Only the neighbours `v - 1` and `v + 1` contribute to the relation at `v`.
  have hrel := sum_signlessArrow_mul_signlessArrow k G (⟨v, hv⟩ : Fin n)
  rw [Fin.sum_univ_eq_sum_range F n] at hrel
  rw [← hrel]
  refine (Finset.sum_eq_add (v + 1) (v - 1) (by omega) (fun w _ hw => hF w (by omega))
    (fun h => ?_) (fun h => absurd (Finset.mem_range.2 (by omega)) h)).symm
  simp only [F]
  rw [signlessArrow_eq_zero k (i := v + 1) (j := v) fun hi _ => absurd (Finset.mem_range.2 hi) h,
    zero_mul]

/-! ### Classes of walks given by their vertices -/

local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver G)

variable (G) in
/-- The class in the signless algebra of a graph `G` on `Fin n` of the walk through the vertices
`l`, **latest vertex first**: `[v]` is the vertex idempotent at `v`, and `j :: i :: r` is the
arrow class `TauCeti.signlessArrow G i j` times the class of `i :: r`. Prepending a vertex is thus
left multiplication by an arrow, in the later-factor-first convention. A list which is not a walk
has class `0`, as does the empty list. -/
noncomputable def signlessWord : List (Fin n) → Π
  | [] => 0
  | [v] => π (vertexIdempotent k (vertex G v))
  | j :: i :: r => signlessArrow k G i j * signlessWord (i :: r)

/-- The empty list has class `0`. -/
@[simp]
theorem signlessWord_nil : signlessWord k G [] = 0 := by
  rw [signlessWord]

/-- The class of a one-vertex walk is its vertex idempotent. -/
@[simp]
theorem signlessWord_singleton (v : Fin n) :
    signlessWord k G [v] = π (vertexIdempotent k (vertex G v)) := by
  rw [signlessWord]

/-- Extending a walk by a vertex multiplies its class on the left by the arrow to that vertex. -/
@[simp]
theorem signlessWord_cons_cons (j i : Fin n) (r : List (Fin n)) :
    signlessWord k G (j :: i :: r) = signlessArrow k G i j * signlessWord k G (i :: r) := by
  rw [signlessWord]

/-- `TauCeti.signlessWord_cons_cons` for a walk given together with its latest vertex. -/
theorem signlessWord_cons {j i : Fin n} {l : List (Fin n)} (hl : l.head? = some i) :
    signlessWord k G (j :: l) = signlessArrow k G i j * signlessWord k G l := by
  obtain ⟨r, rfl⟩ : ∃ r, l = i :: r := by
    cases l with
    | nil => simp at hl
    | cons i' r => exact ⟨r, by simp_all⟩
  exact signlessWord_cons_cons k j i r

/-- The vertex idempotent at the latest vertex of a walk is a left unit for its class, and the
other vertex idempotents annihilate it. -/
theorem vertexIdempotent_mul_signlessWord (v j : Fin n) (r : List (Fin n)) :
    π (vertexIdempotent k (vertex G v)) * signlessWord k G (j :: r) =
      if j = v then signlessWord k G (j :: r) else 0 := by
  cases r with
  | nil =>
    rw [signlessWord_singleton, ← map_mul]
    split_ifs with h
    · rw [h, vertexIdempotent_mul_self]
    · rw [vertexIdempotent_mul_vertexIdempotent_of_ne
        (fun h' => h (vertex_injective G h').symm), map_zero]
  | cons i r =>
    rw [signlessWord_cons_cons, ← mul_assoc, vertexIdempotent_mul_signlessArrow]
    by_cases h : j = v
    · simp [h]
    · simp [h, Fin.val_inj]

/-- An arrow class times the class of a walk extends the walk if the arrow starts at its latest
vertex, and vanishes otherwise. -/
theorem signlessArrow_mul_signlessWord (i j i' : Fin n) (r : List (Fin n)) :
    signlessArrow k G i j * signlessWord k G (i' :: r) =
      if i = i' then signlessWord k G (j :: i' :: r) else 0 := by
  have h : π (vertexIdempotent k (vertex G i')) * signlessWord k G (i' :: r) =
      signlessWord k G (i' :: r) := by
    rw [vertexIdempotent_mul_signlessWord, ite_eq_left rfl]
  rw [← h, ← mul_assoc, signlessArrow_mul_vertexIdempotent]
  by_cases hi : i = i'
  · simp [hi, signlessWord_cons_cons]
  · simp [hi, Fin.val_inj]

/-- A list of vertices which is not a walk has class `0`. -/
theorem signlessWord_eq_zero_of_not_isChain {l : List (Fin n)} (hl : ¬ l.IsChain G.Adj) :
    signlessWord k G l = 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    cases l with
    | nil => exact absurd (List.isChain_singleton j) hl
    | cons i r =>
      rw [signlessWord_cons_cons]
      by_cases h : G.Adj j i
      · rw [ih fun h' => hl (List.isChain_cons_cons.mpr ⟨h, h'⟩), mul_zero]
      · rw [signlessArrow_eq_zero k fun _ _ h' => h (G.adj_symm h'), zero_mul]

/-- The class of a walk is the class of a path of the doubled quiver through the same vertices. -/
theorem exists_ofPath_eq_signlessWord (i : Fin n) (r : List (Fin n))
    (hw : (i :: r).IsChain G.Adj) :
    ∃ (a : Fin n) (p : _root_.Quiver.Path (vertex G a) (vertex G i)),
      π (ofPath ⟨_, _, p⟩) = signlessWord k G (i :: r) ∧
        p.vertices = (i :: r).reverse.map (vertex G) := by
  induction r generalizing i with
  | nil =>
    exact ⟨i, .nil, by rw [signlessWord_singleton, vertexIdempotent_eq_ofPath], by simp⟩
  | cons i' r ih =>
    obtain ⟨hadj, hw⟩ := List.isChain_cons_cons.mp hw
    obtain ⟨a, p, hp, hv⟩ := ih i' hw
    refine ⟨a, p.cons (arrow G hadj.symm), ?_, ?_⟩
    · rw [← ofArrow_mul_ofPath, map_mul, hp, signlessWord_cons_cons,
        signlessArrow_of_adj k hadj.symm]
    · rw [_root_.Quiver.Path.vertices_cons, hv]
      simp

/-- Classes of walks multiply by concatenation, later factor first, when the earliest vertex of
the left factor is the latest vertex of the right factor; otherwise their product is `0`. -/
theorem signlessWord_mul_signlessWord (s : List (Fin n)) {j : Fin n} {t : List (Fin n)}
    (hs : s ≠ []) :
    signlessWord k G s * signlessWord k G (j :: t) =
      if s.getLast hs = j then signlessWord k G (s.dropLast ++ j :: t) else 0 := by
  induction s with
  | nil => exact absurd rfl hs
  | cons v s ih =>
    cases s with
    | nil =>
      rw [signlessWord_singleton, vertexIdempotent_mul_signlessWord]
      simp only [List.getLast_singleton, List.dropLast_singleton, List.nil_append, eq_comm]
    | cons i r =>
      rw [signlessWord_cons_cons, mul_assoc, ih (List.cons_ne_nil i r), List.getLast_cons_cons,
        List.dropLast_cons_cons, List.cons_append]
      split_ifs with h
      · rw [signlessWord_cons k (j := v) (i := i)]
        cases r with
        | nil => simpa using h.symm
        | cons _ _ => simp
      · rw [mul_zero]

end FinArrow

end TauCeti
