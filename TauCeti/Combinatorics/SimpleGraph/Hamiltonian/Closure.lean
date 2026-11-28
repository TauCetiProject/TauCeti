/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Hamiltonian.DegreeSum

/-!
# The Bondy–Chvátal closure and the theorems of Ore and Dirac

A graph `H` on `n` vertices is *degree-closed* when any two distinct nonadjacent vertices of `H`
have degree sum less than `n`. The *Bondy–Chvátal closure* of a graph `G` is the least
degree-closed graph that contains `G`. It is the graph reached from `G` by joining, one pair at a
time, two distinct nonadjacent vertices whose degree sum in the current graph is at least `n`,
until no such pair is left; the result does not depend on the order of the additions. By the
Bondy–Chvátal lemma `SimpleGraph.isHamiltonian_sup_edge_iff`, no addition changes whether the
graph is Hamiltonian, so a graph is Hamiltonian if and only if its closure is. The theorems of Ore
and Dirac follow, because under their degree conditions the closure is the complete graph.

## Main definitions

* `SimpleGraph.IsDegreeClosed`: any two distinct nonadjacent vertices have degree sum less than
  the number of vertices.
* `SimpleGraph.degreeClosure`: the Bondy–Chvátal closure, the infimum of the degree-closed graphs
  that contain `G`.

## Main results

* `SimpleGraph.isLeast_degreeClosure`: the closure is the least degree-closed graph that
  contains `G`.
* `SimpleGraph.eq_degreeClosure_iff_reflTransGen`: a graph is the closure of `G` if and only if
  it is degree-closed and is reached from `G` by a finite sequence of one-edge additions.
* `SimpleGraph.isHamiltonian_degreeClosure_iff`: a graph is Hamiltonian if and only if its
  closure is.
* `SimpleGraph.isHamiltonian_of_degreeClosure_eq_top`: a graph on at least three vertices whose
  closure is complete is Hamiltonian.
* `SimpleGraph.isHamiltonian_of_ore`: Ore's theorem.
* `SimpleGraph.isHamiltonian_of_dirac`: Dirac's theorem.

## References

* J. A. Bondy and U. S. R. Murty, *Graph Theory with Applications*, North-Holland, 1976,
  Section 4.4.
* J. A. Bondy and V. Chvátal, *A method in graph theory*, Discrete Math. 15 (1976).
* O. Ore, *Note on Hamilton circuits*, Amer. Math. Monthly 67 (1960).
* G. A. Dirac, *Some theorems on abstract graphs*, Proc. London Math. Soc. 2 (1952).
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V]

open Classical in
/-- A graph is *degree-closed* when any two distinct nonadjacent vertices have degree sum less
than the number of vertices. -/
def IsDegreeClosed (H : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → ¬H.Adj u v → H.degree u + H.degree v < Fintype.card V

/-- `SimpleGraph.IsDegreeClosed` with the degrees computed from any decidability instance. -/
theorem isDegreeClosed_iff {H : SimpleGraph V} [DecidableRel H.Adj] :
    IsDegreeClosed H ↔
      ∀ u v, u ≠ v → ¬H.Adj u v → H.degree u + H.degree v < Fintype.card V := by
  unfold IsDegreeClosed
  convert Iff.rfl

/-- The complete graph is degree-closed: it has no two distinct nonadjacent vertices. -/
@[simp]
theorem isDegreeClosed_top : IsDegreeClosed (⊤ : SimpleGraph V) :=
  fun _ _ huv h ↦ (h huv).elim

/-- The *Bondy–Chvátal closure* of `G`: the infimum of all degree-closed graphs that contain `G`.
The complete graph is one of them, and by `SimpleGraph.isLeast_degreeClosure` the closure is
itself degree-closed. -/
def degreeClosure (G : SimpleGraph V) : SimpleGraph V :=
  sInf {H | G ≤ H ∧ IsDegreeClosed H}

/-- The closure is the least degree-closed graph that contains `G`. -/
theorem isLeast_degreeClosure (G : SimpleGraph V) :
    IsLeast {H | G ≤ H ∧ IsDegreeClosed H} (degreeClosure G) := by
  classical
  refine ⟨⟨le_sInf fun H hH ↦ hH.1, fun u v huv hK ↦ ?_⟩, fun H hH ↦ sInf_le hH⟩
  -- Some degree-closed `H ≥ G` does not join `u` and `v`; its degrees bound those of the closure.
  obtain ⟨H, hGH, hH, hHuv⟩ : ∃ H, G ≤ H ∧ IsDegreeClosed H ∧ ¬H.Adj u v := by
    simpa [degreeClosure, sInf_adj, huv] using hK
  have hle : degreeClosure G ≤ H := sInf_le ⟨hGH, hH⟩
  have hu := degree_le_of_le (v := u) hle
  have hv := degree_le_of_le (v := v) hle
  have := hH u v huv hHuv
  omega

/-- The closure contains the graph. -/
theorem le_degreeClosure (G : SimpleGraph V) : G ≤ degreeClosure G :=
  (isLeast_degreeClosure G).1.1

/-- The closure is degree-closed. -/
@[simp]
theorem isDegreeClosed_degreeClosure (G : SimpleGraph V) : IsDegreeClosed (degreeClosure G) :=
  (isLeast_degreeClosure G).1.2

/-- The closure lies below every degree-closed graph that contains the graph. -/
theorem degreeClosure_le {G H : SimpleGraph V} (hGH : G ≤ H) (hH : IsDegreeClosed H) :
    degreeClosure G ≤ H :=
  (isLeast_degreeClosure G).2 ⟨hGH, hH⟩

/-- A graph is its own closure if and only if it is degree-closed. -/
theorem degreeClosure_eq_self_iff {G : SimpleGraph V} : degreeClosure G = G ↔ IsDegreeClosed G :=
  ⟨fun h ↦ h ▸ isDegreeClosed_degreeClosure G,
    fun h ↦ (degreeClosure_le le_rfl h).antisymm (le_degreeClosure G)⟩

open Classical in
/-- Each graph reached from `G` by one-edge additions contains `G` and lies below the closure. -/
private theorem le_and_le_degreeClosure_of_reflTransGen {G K : SimpleGraph V}
    (hK : Relation.ReflTransGen (fun K K' : SimpleGraph V ↦ ∃ u v, u ≠ v ∧ ¬K.Adj u v ∧
      Fintype.card V ≤ K.degree u + K.degree v ∧ K' = K ⊔ edge u v) G K) :
    G ≤ K ∧ K ≤ degreeClosure G := by
  induction hK with
  | refl => exact ⟨le_rfl, le_degreeClosure G⟩
  | tail _ hstep ih =>
    obtain ⟨u, v, huv, -, hdeg, rfl⟩ := hstep
    refine ⟨ih.1.trans le_sup_left, sup_le ih.2 ((edge_le_iff _).2 (.inr ?_))⟩
    -- The added pair has degree sum at least `n` in the closure too, so the closure joins it.
    by_contra h
    have hu := degree_le_of_le (v := u) ih.2
    have hv := degree_le_of_le (v := v) ih.2
    have := isDegreeClosed_degreeClosure G u v huv h
    omega

open Classical in
/-- From each graph, one-edge additions reach a degree-closed graph. -/
private theorem exists_isDegreeClosed_reflTransGen (K : SimpleGraph V) :
    ∃ H, IsDegreeClosed H ∧ Relation.ReflTransGen (fun K K' : SimpleGraph V ↦ ∃ u v, u ≠ v ∧
      ¬K.Adj u v ∧ Fintype.card V ≤ K.degree u + K.degree v ∧ K' = K ⊔ edge u v) K H := by
  induction K using WellFoundedGT.induction with
  | _ K ih =>
    by_cases hK : IsDegreeClosed K
    · exact ⟨K, hK, .refl⟩
    · simp only [IsDegreeClosed, not_forall, not_lt] at hK
      obtain ⟨u, v, huv, hadj, hdeg⟩ := hK
      obtain ⟨H, hH, hc⟩ := ih _ (lt_sup_edge _ _ _ huv hadj)
      exact ⟨H, hH, .head ⟨u, v, huv, hadj, hdeg, rfl⟩ hc⟩

open Classical in
/-- The closure does not depend on the order of the additions. A graph `H` is the closure of `G`
if and only if it is degree-closed and is reached from `G` by adding edges one at a time, each
between two distinct nonadjacent vertices whose degrees in the graph reached before it sum to at
least the number of vertices. -/
theorem eq_degreeClosure_iff_reflTransGen (G H : SimpleGraph V) :
    H = degreeClosure G ↔ IsDegreeClosed H ∧ Relation.ReflTransGen
      (fun K K' : SimpleGraph V ↦ ∃ u v, u ≠ v ∧ ¬K.Adj u v ∧
        Fintype.card V ≤ K.degree u + K.degree v ∧ K' = K ⊔ edge u v) G H := by
  have key : ∀ H, IsDegreeClosed H → Relation.ReflTransGen
      (fun K K' : SimpleGraph V ↦ ∃ u v, u ≠ v ∧ ¬K.Adj u v ∧
        Fintype.card V ≤ K.degree u + K.degree v ∧ K' = K ⊔ edge u v) G H →
      H = degreeClosure G := fun H hH hc ↦
    have h := le_and_le_degreeClosure_of_reflTransGen hc
    h.2.antisymm (degreeClosure_le h.1 hH)
  refine ⟨?_, fun h ↦ key H h.1 h.2⟩
  rintro rfl
  obtain ⟨H, hH, hc⟩ := exists_isDegreeClosed_reflTransGen G
  exact key H hH hc ▸ ⟨hH, hc⟩

section Hamiltonian

variable [DecidableEq V]

/-- A graph is Hamiltonian if and only if its Bondy–Chvátal closure is. -/
theorem isHamiltonian_degreeClosure_iff (G : SimpleGraph V) :
    (degreeClosure G).IsHamiltonian ↔ G.IsHamiltonian := by
  classical
  obtain ⟨-, hc⟩ := (eq_degreeClosure_iff_reflTransGen G _).1 rfl
  generalize degreeClosure G = K at hc ⊢
  induction hc with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨u, v, -, -, hdeg, rfl⟩ := hstep
    exact (isHamiltonian_sup_edge_iff hdeg).trans ih

/-- A graph on at least three vertices whose Bondy–Chvátal closure is the complete graph is
Hamiltonian. -/
theorem isHamiltonian_of_degreeClosure_eq_top {G : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    (h : degreeClosure G = ⊤) : G.IsHamiltonian :=
  (isHamiltonian_degreeClosure_iff G).1 (h ▸ isHamiltonian_top hn)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Ore's theorem.** A graph on at least three vertices in which any two distinct nonadjacent
vertices have degree sum at least the number of vertices is Hamiltonian. -/
theorem isHamiltonian_of_ore (hn : 3 ≤ Fintype.card V)
    (h : ∀ u v, u ≠ v → ¬G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  classical
  -- No two distinct vertices stay nonadjacent in the closure, so the closure is complete.
  refine isHamiltonian_of_degreeClosure_eq_top hn (eq_top_iff.2 fun u v huv ↦ ?_)
  by_contra hK
  have hu := degree_le_of_le (v := u) (le_degreeClosure G)
  have hv := degree_le_of_le (v := v) (le_degreeClosure G)
  have := h u v huv fun hG ↦ hK (le_degreeClosure G hG)
  have := isDegreeClosed_degreeClosure G u v huv hK
  omega

/-- **Dirac's theorem.** A graph on `n ≥ 3` vertices in which every vertex has degree at least
`n / 2` is Hamiltonian; the bound is written `n ≤ 2 * deg v`. -/
theorem isHamiltonian_of_dirac (hn : 3 ≤ Fintype.card V)
    (h : ∀ v, Fintype.card V ≤ 2 * G.degree v) : G.IsHamiltonian :=
  isHamiltonian_of_ore hn fun u v _ _ ↦ by have := h u; have := h v; omega

end Hamiltonian

end SimpleGraph
