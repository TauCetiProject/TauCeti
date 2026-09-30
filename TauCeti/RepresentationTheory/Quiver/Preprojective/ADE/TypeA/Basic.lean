/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.LadderValley
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# The preprojective algebra of `Aₙ` is finite-dimensional

The Bourbaki-labelled diagram of `Aₙ` is the path `0 — 1 — ⋯ — (n - 1)`
(`TauCeti.DynkinType.diagramGraph_cartanMatrix_A`). Write `u w` for the doubled arrow `w → w + 1`
and `d w` for the arrow `w + 1 → w`. In the signless algebra `TauCeti.signlessPreprojectiveAlgebra`
of the doubled graph, the relation at the vertex `w + 1` says that the two backtracks there cancel,

```text
d (w + 1) * u (w + 1) + u w * d w = 0,
```

and the relation at the end vertex `0` is the single backtrack `d 0 * u 0 = 0`. These are the ladder
relations of `TauCeti.Algebra.Ring.LadderValley`, so the class of a path from `a` to `b` is, up to
sign, a valley word descending to some vertex `m` and climbing back, or zero. Its length is then
`(a - m) + (b - m) ≤ a + b`. Reading the vertices from the other end, `w ↦ n - 1 - w`, gives the
same relations and the bound `2 (n - 1) - a - b`. Adding the two bounds, **every path of length at
least `n` vanishes**.

The signless algebra of a bipartite graph is the preprojective algebra of each of its orientations,
by an explicit sign rescaling of the arrows. Thus the same bound holds in the preprojective algebra
`Π_k(Q)` of every orientation `Q` of `Aₙ`, over every commutative ring; the relation ideal is
admissible, and `Π_k(Q)` is finite-dimensional over every field. The bound `n` is `h - 1` for the
Coxeter number `h = n + 1` of `Aₙ`; that paths of length `n - 1` survive is not proved here.

## Main results

* `TauCeti.signlessPreprojectiveMk_A_ofPath_eq_zero_of_le`: paths of length at least `n` vanish in
  the signless algebra of `Aₙ`.
* `TauCeti.preprojectiveMk_A_ofPath_eq_zero_of_le`: the same in the preprojective algebra of every
  orientation of `Aₙ`.
* `TauCeti.isAdmissibleIdeal_preprojectiveIdeal_A`: the preprojective relation ideal of every
  orientation of `Aₙ` is admissible.
* `TauCeti.instFiniteDimensionalPreprojectiveAlgebraA` and
  `TauCeti.instFiniteDimensionalSignlessPreprojectiveAlgebraA`: the preprojective algebra of every
  orientation of `Aₙ`, and the signless algebra of `Aₙ`, are finite-dimensional.

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
noncomputable local instance finiteNeighborSetFintype {V : Type*} [Finite V] (G : SimpleGraph V)
    (i : V) : Fintype (G.neighborSet i) :=
  Fintype.ofFinite _

/-! ### Graphs whose edges join consecutive vertices -/

section PathGraph

variable (k : Type*) [CommRing k] {n : ℕ} (G : SimpleGraph (Fin n))

open scoped Classical in
/-- The class of the doubled arrow from `i` to `j` in the signless algebra of `G`, or zero if `i`
and `j` are not adjacent vertices of `G`. -/
private noncomputable def finArrow (i j : ℕ) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  if h : i < n ∧ j < n then
    if hij : G.Adj ⟨i, h.1⟩ ⟨j, h.2⟩ then signlessPreprojectiveMk k _ (ofArrow (arrow G hij))
    else 0
  else 0

/-- Between adjacent vertices, `finArrow` is the class of the doubled arrow. -/
private theorem finArrow_of_adj {i j : Fin n} (h : G.Adj i j) :
    finArrow k G i j = signlessPreprojectiveMk k _ (ofArrow (arrow G h)) := by
  simp [finArrow, h]

/-- Between non-adjacent vertices, `finArrow` vanishes. -/
private theorem finArrow_eq_zero {i j : ℕ}
    (h : ∀ (hi : i < n) (hj : j < n), ¬G.Adj ⟨i, hi⟩ ⟨j, hj⟩) :
    finArrow k G i j = 0 := by
  by_cases hn : i < n ∧ j < n
  · simp [finArrow, hn, h hn.1 hn.2]
  · simp [finArrow, hn]

/-- The class of an arbitrary doubled arrow of `G`. -/
private theorem signlessPreprojectiveMk_ofArrow {i j : DoubledQuiver G} (e : i ⟶ j) :
    signlessPreprojectiveMk k _ (ofArrow e) =
      finArrow k G ((vertexEquiv G).symm i) ((vertexEquiv G).symm j) := by
  obtain ⟨i, rfl⟩ := exists_eq_vertex G i
  obtain ⟨j, rfl⟩ := exists_eq_vertex G j
  rw [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex,
    finArrow_of_adj k G ((nonempty_hom_iff G).1 ⟨e⟩)]
  exact congrArg (fun e => signlessPreprojectiveMk k _ (ofArrow e)) (Subsingleton.elim _ _)

variable {G}

/-! ### Paths as valley words -/

/-- **Every path is a valley word up to sign, or zero.** Here the vertices are read through a
height function `φ`, each doubled arrow either climbing from `φ i` to `φ i + 1`, with class
`u (φ i)`, or descending to `φ j`, with class `d (φ j)`, and the ladder relations hold. The valley
word descends from the height of the source to some height `m` and climbs to the height of the
target. -/
private theorem signlessPreprojectiveMk_ofPath_eq_ladderValley (φ : Fin n → ℕ)
    {u d : ℕ → signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hud₀ : d 0 * u 0 = 0) (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    (harr : ∀ i j : Fin n, G.Adj i j →
      (φ j = φ i + 1 ∧ finArrow k G i j = u (φ i)) ∨ (φ i = φ j + 1 ∧ finArrow k G i j = d (φ j)))
    {a b : DoubledQuiver G} (p : Path a b) :
    signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩) = 0 ∨
      ∃ m s r : ℕ, ∃ ε : ℤ, s + r = p.length ∧ m + s = φ ((vertexEquiv G).symm a) ∧
        m + r = φ ((vertexEquiv G).symm b) ∧
        signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩) =
          ε • (ladderValley u d m s r * signlessPreprojectiveMk k _ (ofPath ⟨a, a, .nil⟩)) := by
  induction p with
  | nil => exact .inr ⟨_, 0, 0, 1, rfl, add_zero _, add_zero _, by
    rw [ladderValley_zero_zero, one_mul, one_smul]⟩
  | @cons c b q e ih =>
    rw [← ofArrow_mul_ofPath, map_mul, signlessPreprojectiveMk_ofArrow]
    rcases ih with ih | ⟨m, s, r, ε, hlen, hs, hr, ih⟩
    · exact .inl (by rw [ih, mul_zero])
    rw [ih, mul_smul_comm, ← mul_assoc]
    rcases harr _ _ e.down with ⟨hup, harr⟩ | ⟨hdown, harr⟩
    · -- A climbing arrow extends the climb of the valley.
      rw [harr, ← hr, u_mul_ladderValley]
      exact .inr ⟨m, s, r + 1, ε, by rw [Path.length_cons, ← hlen, add_assoc], hs, by omega, rfl⟩
    · -- A descending arrow moves the bottom of the valley down, or kills a valley at height `0`.
      rw [harr]
      rcases m with _ | m
      · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hheight : φ ((vertexEquiv G).symm b) = r := by omega
        rw [hheight, d_mul_ladderValley_zero_eq_zero hud₀ hud, zero_mul, smul_zero]
        exact .inl rfl
      · have hheight : φ ((vertexEquiv G).symm b) = m + r := by omega
        rw [hheight, d_mul_ladderValley hud]
        refine .inr ⟨m, s + 1, r, ε * (-1) ^ r, by rw [Path.length_cons, ← hlen]; omega, by omega,
          by omega, ?_⟩
        rw [mul_smul, mul_assoc]
        congr 1
        rw [zsmul_eq_mul]
        push_cast
        rfl

/-- Paths whose length exceeds the sum of the heights of their endpoints vanish. -/
private theorem signlessPreprojectiveMk_ofPath_eq_zero_of_lt (φ : Fin n → ℕ)
    {u d : ℕ → signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hud₀ : d 0 * u 0 = 0) (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    (harr : ∀ i j : Fin n, G.Adj i j →
      (φ j = φ i + 1 ∧ finArrow k G i j = u (φ i)) ∨ (φ i = φ j + 1 ∧ finArrow k G i j = d (φ j)))
    {a b : DoubledQuiver G} (p : Path a b)
    (hp : φ ((vertexEquiv G).symm a) + φ ((vertexEquiv G).symm b) < p.length) :
    signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩) = 0 := by
  rcases signlessPreprojectiveMk_ofPath_eq_ladderValley k φ hud₀ hud harr p with
    h | ⟨m, s, r, ε, hlen, hs, hr, -⟩
  · exact h
  · omega

variable (hG : ∀ i j : Fin n, G.Adj i j ↔ (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)
include hG

/-- `finArrow` vanishes between vertices which are not consecutive. -/
private theorem finArrow_eq_zero_of_not_consecutive {i j : ℕ} (h : ¬(i + 1 = j ∨ j + 1 = i)) :
    finArrow k G i j = 0 :=
  finArrow_eq_zero k G fun _ _ hij => h ((hG _ _).1 hij)

/-- **The signless relation at a vertex `v` of a path**: the backtrack through `v + 1` cancels the
backtrack through `v - 1`. At an end vertex the missing backtrack is zero. -/
private theorem finArrow_relation (v : ℕ) :
    finArrow k G (v + 1) v * finArrow k G v (v + 1) +
      finArrow k G (v - 1) v * finArrow k G v (v - 1) = 0 := by
  by_cases hv : v < n
  swap
  · rw [finArrow_eq_zero k G (i := v + 1) (fun _ => by omega),
      finArrow_eq_zero k G (i := v - 1) (fun _ _ => by omega), zero_mul, zero_mul, add_zero]
  -- The relator at `v` is the sum of the backtracks along the edges at `v`.
  have hrel := signlessPreprojectiveMk_signlessPreprojectiveRelator k (vertex G (⟨v, hv⟩ : Fin n))
  rw [signlessPreprojectiveRelator_congr k (vertex G (⟨v, hv⟩ : Fin n)) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum] at hrel
  let F : ℕ → signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
    fun w => finArrow k G w v * finArrow k G v w
  have hF (w : ℕ) (hw : ¬(w + 1 = v ∨ v + 1 = w)) : F w = 0 := by
    simp only [F, finArrow_eq_zero_of_not_consecutive k hG hw, zero_mul]
  -- Only the neighbours `v - 1` and `v + 1` contribute to the sum over all vertices.
  have hsum : ∑ w : G.neighborSet ⟨v, hv⟩, F w = F (v + 1) + F (v - 1) := by
    classical
    rw [← Finset.sum_subtype (Finset.univ.filter fun w : Fin n => G.Adj ⟨v, hv⟩ w)
        (fun w => by simp) (fun w : Fin n => F w),
      Finset.sum_filter_of_ne (fun w _ hw => by
        by_contra h
        exact hw (hF w (by rw [hG, Fin.val_mk] at h; omega))),
      Fin.sum_univ_eq_sum_range F n]
    refine Finset.sum_eq_add (v + 1) (v - 1) (by omega) (fun w _ hw => hF w (by omega))
      (fun h => ?_) (fun h => absurd (Finset.mem_range.2 (by omega)) h)
    simp only [F]
    rw [finArrow_eq_zero k G (i := v + 1) (j := v) fun hi _ => absurd (Finset.mem_range.2 hi) h,
      zero_mul]
  rw [← hsum, ← hrel]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← ofArrow_symm_mul_ofArrow _ k w.2, map_mul, ← finArrow_of_adj k G w.2,
    ← finArrow_of_adj k G (G.adj_symm w.2)]

/-- **Every path of length at least `n` vanishes** in the signless algebra of a graph on `Fin n`
whose edges join consecutive vertices. The heights are read from both ends of the path graph. -/
private theorem signlessPreprojectiveMk_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : n ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  obtain ⟨a, b, p⟩ := x
  dsimp only at hx
  have ha := ((vertexEquiv G).symm a).2
  have hb := ((vertexEquiv G).symm b).2
  -- Heights increasing from the vertex `0`.
  by_cases hlow : ((vertexEquiv G).symm a : ℕ) + (vertexEquiv G).symm b < p.length
  · refine signlessPreprojectiveMk_ofPath_eq_zero_of_lt k (fun i => i)
      (u := fun w => finArrow k G w (w + 1)) (d := fun w => finArrow k G (w + 1) w) ?_
      (fun w => by simpa [add_comm] using finArrow_relation k hG (w + 1)) ?_ p hlow
    · simpa [finArrow_eq_zero_of_not_consecutive k hG (i := 0) (j := 0)] using
        finArrow_relation k hG 0
    · intro i j hij
      rcases (hG i j).1 hij with h | h
      · exact .inl ⟨h.symm, by rw [← h]⟩
      · exact .inr ⟨h.symm, by rw [← h]⟩
  -- Heights increasing from the vertex `n - 1`.
  refine signlessPreprojectiveMk_ofPath_eq_zero_of_lt k (fun i => n - 1 - i)
    (u := fun w => finArrow k G (n - 1 - w) (n - 1 - (w + 1)))
    (d := fun w => finArrow k G (n - 1 - (w + 1)) (n - 1 - w)) ?_ (fun w => ?_) ?_ p (by omega)
  · have h := finArrow_relation k hG (n - 1)
    rw [finArrow_eq_zero k G (i := n - 1 + 1) (fun _ => by omega), zero_mul, zero_add] at h
    simpa using h
  · by_cases hw : w + 1 ≤ n - 1
    · have h := finArrow_relation k hG (n - 1 - (w + 1))
      have hnext : n - 1 - (w + 1) + 1 = n - 1 - w := by omega
      have hprev : n - 1 - (w + 1) - 1 = n - 1 - (w + 1 + 1) := by omega
      rw [hnext, hprev, add_comm] at h
      exact h
    · have hzero : n - 1 - (w + 1) = 0 := by omega
      have hnext : n - 1 - w = 0 := by omega
      have hprev : n - 1 - (w + 1 + 1) = 0 := by omega
      rw [hzero, hnext, hprev,
        finArrow_eq_zero_of_not_consecutive k hG (i := 0) (j := 0) (by omega)]
      simp
  · intro i j hij
    have hi := i.2
    have hj := j.2
    rcases (hG i j).1 hij with h | h
    · exact .inr ⟨by omega, by congr 1 <;> omega⟩
    · exact .inl ⟨by omega, by congr 1 <;> omega⟩

end PathGraph

/-! ### The `Aₙ` diagram -/

/-- Two nodes of the `Aₙ` diagram are joined exactly when they are consecutive. -/
private theorem diagramGraph_A_adj (n : ℕ) (i j : Fin n) :
    (diagramGraph (DynkinType.A n).cartanMatrix : SimpleGraph (Fin n)).Adj i j ↔
      (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i := by
  rw [DynkinType.cartanMatrix_A, DynkinType.diagramGraph_cartanMatrix_A,
    SimpleGraph.pathGraph_adj]

/-- The two-colouring of `Aₙ` by the parity of the node, read from the path graph. -/
private def aColoring (n : ℕ) : (diagramGraph (DynkinType.A n).cartanMatrix).Coloring Bool := by
  simpa only [DynkinType.rank_A, DynkinType.cartanMatrix_A] using
    (SimpleGraph.pathGraph.bicoloring n).comp
      (SimpleGraph.Hom.ofLE (DynkinType.diagramGraph_cartanMatrix_A n).le)

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

/-- **Every path of length at least `n` vanishes in the signless algebra of `Aₙ`.** -/
@[simp]
theorem signlessPreprojectiveMk_A_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (DoubledQuiver (diagramGraph (DynkinType.A n).cartanMatrix)))
    (hx : n ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 :=
  signlessPreprojectiveMk_ofPath_eq_zero_of_le k (diagramGraph_A_adj n) x hx

variable (o : Orientation (diagramGraph (DynkinType.A n).cartanMatrix))

/-- **Every path of length at least `n` vanishes in the preprojective algebra of `Aₙ`**, for every
orientation of the `Aₙ` graph. -/
@[simp]
theorem preprojectiveMk_A_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath
      (Symmetrify (OrientedQuiver (diagramGraph (DynkinType.A n).cartanMatrix) o)))
    (hx : n ≤ x.2.2.length) :
    preprojectiveMk k (OrientedQuiver (diagramGraph (DynkinType.A n).cartanMatrix) o)
      (ofPath x) = 0 := by
  -- Every orientation of the bipartite `Aₙ` graph is compared with the signless algebra.
  have hc : ∀ ⦃i j : OrientedQuiver (diagramGraph (DynkinType.A n).cartanMatrix) o⦄, (i ⟶ j) →
      aColoring n ((OrientedQuiver.vertexEquiv _ o).symm i) ≠
        aColoring n ((OrientedQuiver.vertexEquiv _ o).symm j) :=
    fun _ _ a => (aColoring n).valid a.1
  apply preprojectiveMk_ofPath_eq_zero_of_signless o k hc x
  exact signlessPreprojectiveMk_A_ofPath_eq_zero_of_le k _
    (by rwa [Prefunctor.length_mapTotalPath])

/-- **The preprojective relation ideal of every orientation of `Aₙ` is admissible.** It lies in
the square of the arrow ideal, and it contains every path of length at least `n`. -/
theorem isAdmissibleIdeal_preprojectiveIdeal_A :
    IsAdmissibleIdeal
      (preprojectiveIdeal k
        (OrientedQuiver (diagramGraph (DynkinType.A n).cartanMatrix) o)).asIdeal :=
  isAdmissibleIdeal_iff.2 ⟨⟨n, fun x hx => by
    rw [TwoSidedIdeal.mem_asIdeal, ← preprojectiveMk_eq_zero_iff]
    exact preprojectiveMk_A_ofPath_eq_zero_of_le k o x hx⟩,
    preprojectiveIdeal_le_arrowIdeal_sq k⟩

end CommRing

/-! ### Finite dimensionality -/

section Field

variable (k : Type*) [Field k] {n : ℕ}

/-- **The preprojective algebra of `Aₙ` is finite-dimensional**, for every orientation of the
`Aₙ` graph and over every field. -/
instance instFiniteDimensionalPreprojectiveAlgebraA
    (o : Orientation (diagramGraph (DynkinType.A n).cartanMatrix)) :
    FiniteDimensional k
      (preprojectiveAlgebra k (OrientedQuiver (diagramGraph (DynkinType.A n).cartanMatrix) o)) :=
  (isAdmissibleIdeal_preprojectiveIdeal_A k o).finiteDimensional_quotient

/-- **The signless algebra of `Aₙ` is finite-dimensional** over every field. -/
instance instFiniteDimensionalSignlessPreprojectiveAlgebraA :
    FiniteDimensional k
      (signlessPreprojectiveAlgebra k
        (DoubledQuiver (diagramGraph (DynkinType.A n).cartanMatrix))) :=
  ((aColoring n).sourceSinkSignlessPreprojectiveAlgebraEquiv k).symm.toLinearEquiv.finiteDimensional

end Field

end TauCeti
