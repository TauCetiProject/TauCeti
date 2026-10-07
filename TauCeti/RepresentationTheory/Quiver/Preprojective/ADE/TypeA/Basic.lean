/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.LadderValley
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Basic
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

* `TauCeti.signlessPreprojectiveMk_A_ofPath_eq_zero_of_endpoint_bound`: the finer vanishing
  bound depending on the two endpoints.
* `TauCeti.signlessPreprojectiveMk_A_ofPath_eq_zero_or_ladderValley`: length-preserving
  reduction to a valley word.
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

variable (k : Type*) [CommRing k] {n : ℕ} {G : SimpleGraph (Fin n)}

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
      (φ j = φ i + 1 ∧ signlessArrow k G i j = u (φ i)) ∨
        (φ i = φ j + 1 ∧ signlessArrow k G i j = d (φ j)))
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
    rw [← ofArrow_mul_ofPath, map_mul, signlessPreprojectiveMk_ofArrow_eq_signlessArrow]
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
      (φ j = φ i + 1 ∧ signlessArrow k G i j = u (φ i)) ∨
        (φ i = φ j + 1 ∧ signlessArrow k G i j = d (φ j)))
    {a b : DoubledQuiver G} (p : Path a b)
    (hp : φ ((vertexEquiv G).symm a) + φ ((vertexEquiv G).symm b) < p.length) :
    signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩) = 0 := by
  rcases signlessPreprojectiveMk_ofPath_eq_ladderValley k φ hud₀ hud harr p with
    h | ⟨m, s, r, ε, hlen, hs, hr, -⟩
  · exact h
  · omega

variable (hG : ∀ i j : Fin n, G.Adj i j ↔ (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)
include hG

/-- `signlessArrow` vanishes between vertices which are not consecutive. -/
private theorem signlessArrow_eq_zero_of_not_consecutive {i j : ℕ} (h : ¬(i + 1 = j ∨ j + 1 = i)) :
    signlessArrow k G i j = 0 :=
  signlessArrow_eq_zero k fun _ _ hij => h ((hG _ _).1 hij)

/-- Paths longer than either endpoint-height bound vanish. The heights are read from both
ends of the path graph. -/
private theorem signlessPreprojectiveMk_ofPath_eq_zero_of_endpoint_bound
    (x : Quiver.TotalPath (DoubledQuiver G))
    (hx : min (((vertexEquiv G).symm x.1 : ℕ) + (vertexEquiv G).symm x.2.1)
      (2 * (n - 1) - ((vertexEquiv G).symm x.1 : ℕ) - (vertexEquiv G).symm x.2.1) <
        x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  obtain ⟨a, b, p⟩ := x
  dsimp only at hx
  have ha := ((vertexEquiv G).symm a).2
  have hb := ((vertexEquiv G).symm b).2
  -- Heights increasing from the vertex `0`.
  by_cases hlow : ((vertexEquiv G).symm a : ℕ) + (vertexEquiv G).symm b < p.length
  · refine signlessPreprojectiveMk_ofPath_eq_zero_of_lt k (fun i => i)
      (u := fun w => signlessArrow k G w (w + 1)) (d := fun w => signlessArrow k G (w + 1) w) ?_
      (fun w => by
        simpa [add_comm] using
          signlessArrow_relation_of_consecutive k
            (fun i j hij => (hG i j).mp hij) (w + 1)) ?_ p hlow
    · simpa [signlessArrow_eq_zero_of_not_consecutive k hG (i := 0) (j := 0)] using
        signlessArrow_relation_of_consecutive k (fun i j hij => (hG i j).mp hij) 0
    · intro i j hij
      rcases (hG i j).1 hij with h | h
      · exact .inl ⟨h.symm, by rw [← h]⟩
      · exact .inr ⟨h.symm, by rw [← h]⟩
  -- Heights increasing from the vertex `n - 1`.
  refine signlessPreprojectiveMk_ofPath_eq_zero_of_lt k (fun i => n - 1 - i)
    (u := fun w => signlessArrow k G (n - 1 - w) (n - 1 - (w + 1)))
    (d := fun w => signlessArrow k G (n - 1 - (w + 1)) (n - 1 - w)) ?_ (fun w => ?_) ?_ p (by omega)
  · have h := signlessArrow_relation_of_consecutive k (fun i j hij => (hG i j).mp hij) (n - 1)
    rw [signlessArrow_eq_zero k (i := n - 1 + 1) (fun _ => by omega), zero_mul, zero_add] at h
    simpa using h
  · by_cases hw : w + 1 ≤ n - 1
    · have h := signlessArrow_relation_of_consecutive k (fun i j hij => (hG i j).mp hij)
        (n - 1 - (w + 1))
      have hnext : n - 1 - (w + 1) + 1 = n - 1 - w := by omega
      have hprev : n - 1 - (w + 1) - 1 = n - 1 - (w + 1 + 1) := by omega
      rw [hnext, hprev, add_comm] at h
      exact h
    · have hzero : n - 1 - (w + 1) = 0 := by omega
      have hnext : n - 1 - w = 0 := by omega
      have hprev : n - 1 - (w + 1 + 1) = 0 := by omega
      rw [hzero, hnext, hprev,
        signlessArrow_eq_zero_of_not_consecutive k hG (i := 0) (j := 0) (by omega)]
      simp
  · intro i j hij
    have hi := i.2
    have hj := j.2
    rcases (hG i j).1 hij with h | h
    · exact .inr ⟨by omega, by congr 1 <;> omega⟩
    · exact .inl ⟨by omega, by congr 1 <;> omega⟩

end PathGraph

/-! ### The `Aₙ` diagram -/

/-- The two-colouring of `Aₙ` by the parity of the node, read from the path graph. -/
private def aColoring (n : ℕ) : (diagramGraph (DynkinType.A n).cartanMatrix).Coloring Bool := by
  simpa only [DynkinType.rank_A, DynkinType.cartanMatrix_A] using
    (SimpleGraph.pathGraph.bicoloring n).comp
      (SimpleGraph.Hom.ofLE (DynkinType.diagramGraph_cartanMatrix_A n).le)

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))

/-- The signless relation at a type-`A` vertex: the backtracks through its two neighbours
cancel. A missing neighbour contributes zero, including at the endpoints. -/
theorem signlessArrow_A_relation (v : ℕ) :
    signlessArrow k AG (v + 1) v * signlessArrow k AG v (v + 1) +
      signlessArrow k AG (v - 1) v * signlessArrow k AG v (v - 1) = 0 :=
  signlessArrow_relation_of_consecutive k
    (fun i j hij => (diagramGraph_A_adj n i j).mp hij) v

/-- A path from `a` to `b` in the signless algebra of `Aₙ` vanishes when its length exceeds
`min (a + b) (2(n - 1) - a - b)`. -/
theorem signlessPreprojectiveMk_A_ofPath_eq_zero_of_endpoint_bound
    {a b : Fin (DynkinType.A n).rank} (p : Path (vertex AG a) (vertex AG b))
    (hp : min (a.val + b.val) (2 * ((DynkinType.A n).rank - 1) - a.val - b.val) < p.length) :
    signlessPreprojectiveMk k _ (ofPath ⟨_, _, p⟩) = 0 := by
  apply signlessPreprojectiveMk_ofPath_eq_zero_of_endpoint_bound k
    (n := (DynkinType.A n).rank) (G := AG) (fun i j => diagramGraph_A_adj n i j)
  simpa only [vertexEquiv_symm_vertex] using hp

/-- Every path in the signless algebra of `Aₙ` reduces to an integer multiple of a valley word,
or to zero. The word descends from `a` to `m` and climbs to `b`, and its length is preserved. -/
theorem signlessPreprojectiveMk_A_ofPath_eq_zero_or_ladderValley
    {a b : Fin (DynkinType.A n).rank} (p : Path (vertex AG a) (vertex AG b)) :
    signlessPreprojectiveMk k _ (ofPath ⟨_, _, p⟩) = 0 ∨
      ∃ m s r : ℕ, ∃ ε : ℤ, s + r = p.length ∧ m + s = a.val ∧ m + r = b.val ∧
        signlessPreprojectiveMk k _ (ofPath ⟨_, _, p⟩) =
          ε • (ladderValley (fun w => signlessArrow k AG w (w + 1))
            (fun w => signlessArrow k AG (w + 1) w) m s r *
              signlessPreprojectiveMk k _ (vertexIdempotent k (vertex AG a))) := by
  have h := signlessPreprojectiveMk_ofPath_eq_ladderValley k
    (n := (DynkinType.A n).rank) (G := AG) (fun i => i.val)
    (u := fun w => signlessArrow k AG w (w + 1))
    (d := fun w => signlessArrow k AG (w + 1) w) ?_ ?_ ?_ p
  · simpa only [vertexEquiv_symm_vertex, vertexIdempotent_eq_ofPath] using h
  · have hzero : signlessArrow k AG 0 0 = 0 :=
      signlessArrow_eq_zero_of_not_consecutive k (n := (DynkinType.A n).rank)
        (G := AG) (fun i j => diagramGraph_A_adj n i j) (by omega)
    simpa only [Nat.zero_add, Nat.sub_self, hzero, zero_mul, add_zero] using
      signlessArrow_A_relation k (n := n) 0
  · intro w
    simpa [add_comm] using signlessArrow_A_relation k (n := n) (w + 1)
  · intro i j hij
    rcases (diagramGraph_A_adj n i j).1 hij with h | h
    · exact .inl ⟨h.symm, by rw [← h]⟩
    · exact .inr ⟨h.symm, by rw [← h]⟩

/-- **Every path of length at least `n` vanishes in the signless algebra of `Aₙ`.** -/
@[simp]
theorem signlessPreprojectiveMk_A_ofPath_eq_zero_of_le
    (x : Quiver.TotalPath (DoubledQuiver (diagramGraph (DynkinType.A n).cartanMatrix)))
    (hx : n ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 :=
  signlessPreprojectiveMk_ofPath_eq_zero_of_endpoint_bound k
    (n := (DynkinType.A n).rank) (G := diagramGraph (DynkinType.A n).cartanMatrix)
    (fun i j => diagramGraph_A_adj n i j) x (by
      have ha := ((vertexEquiv (diagramGraph (DynkinType.A n).cartanMatrix)).symm x.1).isLt
      have hb := ((vertexEquiv (diagramGraph (DynkinType.A n).cartanMatrix)).symm x.2.1).isLt
      have hn := DynkinType.rank_A n
      omega)

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
