/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The incidence graph of a relational configuration

A configuration `c` of a relational language `L` on a carrier `V` is coded by a vertex-coloured
graph, its *incidence graph*. The vertices, which do not depend on `c`, are of four sorts:

* a *point* `point a` for every `a : V`;
* a *tuple vertex* `tuple q` for every atom `q`;
* a *position vertex* `position R x j` for every atom `q = atom R x` of an `n`-ary symbol `R` and
  every argument position `j < n`;
* a *truth vertex* `truth q` for every atom `q`.

The edges join the tuple vertex of `atom R x` to each `position R x j`, join `position R x j` to
the point `x j`, and join `tuple q` to `truth q` exactly when `c` makes `q` true. Only these last
edges depend on `c`, each on a single coordinate. A vertex is coloured by a natural number
recording its sort, the index of a position vertex, and, through an injection `ι` of the relation
symbols into `ℕ`, the symbol of a tuple vertex.

The graph is bipartite, with the points and tuple vertices on one side, so it has no triangles.
The point of the coding is that it forgets nothing: two configurations are relabellings of one
another, that is, isomorphic, exactly when some colour-preserving graph isomorphism maps one
incidence graph onto the other. Combined with gadgets that make the colours visible in the
uncoloured graph, this reduces isomorphism of countable structures in any countable relational
language to isomorphism of countable graphs, as in the theorem of Friedman and Stanley that
countable graphs are Borel complete.

## Main definitions

* `TauCeti.RelationalConfiguration.IncidenceVertex L V`: the vertices of the incidence graphs.
* `TauCeti.RelationalConfiguration.IncidenceVertex.color ι`: the colouring of the vertices.
* `TauCeti.RelationalConfiguration.incidenceGraph c`: the incidence graph of `c`.
* `TauCeti.RelationalConfiguration.incidenceGraphPermSmulIso σ c`: relabelling by `σ` moves the
  incidence graph of `c` onto that of `σ • c`.

## Main results

* `TauCeti.RelationalConfiguration.isBipartite_incidenceGraph` and
  `TauCeti.RelationalConfiguration.cliqueFree_incidenceGraph`: the incidence graph is bipartite,
  hence triangle-free.
* `TauCeti.RelationalConfiguration.exists_perm_smul_eq_iff_exists_iso_incidenceGraph` and
  `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_iso_incidenceGraph`: two configurations
  are isomorphic exactly when their incidence graphs are isomorphic by a colour-preserving
  isomorphism.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), Theorem 1 (countable structures code into countable graphs).
* A. Montalbán, *Computable Structure Theory: Within the Arithmetic*, Cambridge University Press
  (2021), Theorem VI.27 (a coding of structures into graphs, with different gadgets).
-/

public section

universe u v w

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w}

/-- The vertices of the incidence graphs of configurations of `L` on `V`: a point for every
element of `V`, and for every atom `q` a tuple vertex, a position vertex for each argument
position of `q`, and a truth vertex. -/
inductive IncidenceVertex (L : Language.{u, v}) (V : Type w)
  /-- The point of an element of the carrier. -/
  | point (a : V)
  /-- The tuple vertex of an atom. -/
  | tuple (q : Atom L V)
  /-- The vertex of the argument position `j` of the atom `atom R x`. -/
  | position {n : ℕ} (R : L.Relations n) (x : Fin n → V) (j : Fin n)
  /-- The truth vertex of an atom, adjacent to its tuple vertex exactly when the atom holds. -/
  | truth (q : Atom L V)

namespace IncidenceVertex

variable {n : ℕ} {R : L.Relations n} {x : Fin n → V}

/-! ### Colours -/

/-- The colour of a vertex, given an injection `ι` of the relation symbols into `ℕ`: `0` for
points, `1` for truth vertices, `2 * j + 2` for the vertex of the argument position `j`, and
`2 * ι R + 3` for the tuple vertex of an atom with relation symbol `R`. -/
def color (ι : (Σ n, L.Relations n) → ℕ) : IncidenceVertex L V → ℕ
  | point _ => 0
  | truth _ => 1
  | position _ _ j => 2 * j + 2
  | tuple q => 2 * ι q.symbol + 3

variable {ι : (Σ n, L.Relations n) → ℕ}

@[simp]
theorem color_point (ι : (Σ n, L.Relations n) → ℕ) (a : V) :
    color ι (point (L := L) a) = 0 := (rfl)

@[simp]
theorem color_truth (ι : (Σ n, L.Relations n) → ℕ) (q : Atom L V) : color ι (truth q) = 1 :=
  (rfl)

@[simp]
theorem color_position (ι : (Σ n, L.Relations n) → ℕ) (R : L.Relations n) (x : Fin n → V)
    (j : Fin n) : color ι (position R x j) = 2 * j + 2 := (rfl)

@[simp]
theorem color_tuple (ι : (Σ n, L.Relations n) → ℕ) (q : Atom L V) :
    color ι (tuple q) = 2 * ι q.symbol + 3 := (rfl)

/-- The vertices of colour `0` are the points. -/
private theorem color_eq_zero_iff {v : IncidenceVertex L V} :
    color ι v = 0 ↔ ∃ a, v = point a := by
  cases v <;> simp

/-- The vertices of colour `1` are the truth vertices. -/
private theorem color_eq_one_iff {v : IncidenceVertex L V} :
    color ι v = 1 ↔ ∃ q, v = truth q := by
  cases v <;> simp

/-- The vertices of colour `2 * k + 2` are the vertices of the argument position `k`. -/
private theorem color_eq_two_mul_add_two_iff {v : IncidenceVertex L V} {k : ℕ} :
    color ι v = 2 * k + 2 ↔ ∃ (m : ℕ) (S : L.Relations m) (y : Fin m → V) (j : Fin m),
      v = position S y j ∧ (j : ℕ) = k := by
  cases v with
  | position S y j =>
    refine ⟨fun h => ⟨_, S, y, j, rfl, by simp only [color_position] at h; omega⟩, ?_⟩
    rintro ⟨m, S', y', j', h, rfl⟩
    cases h
    rfl
  | tuple q => simp; omega
  | _ => simp

/-- For injective `ι`, the vertices of colour `2 * ι s + 3` are the tuple vertices of the atoms
with relation symbol `s`. -/
private theorem color_eq_two_mul_add_three_iff (hι : Function.Injective ι)
    {v : IncidenceVertex L V} {s : Σ n, L.Relations n} :
    color ι v = 2 * ι s + 3 ↔
      ∃ q : Atom L V, v = tuple q ∧ q.symbol = s := by
  cases v with
  | tuple q => simp [hι.eq_iff]
  | position S y j => simp; omega
  | _ => simp

/-! ### Relabelling -/

variable {W X : Type*}

/-- Relabel a vertex along a map of carriers: each point, and the arguments of each atom, are
relabelled, and an argument position keeps its index. -/
def map (f : V → W) : IncidenceVertex L V → IncidenceVertex L W
  | point a => point (f a)
  | tuple q => tuple (q.map f)
  | position R x j => position R (f ∘ x) j
  | truth q => truth (q.map f)

@[simp]
theorem map_point (f : V → W) (a : V) : map f (point (L := L) a) = point (f a) := (rfl)

@[simp]
theorem map_tuple (f : V → W) (q : Atom L V) : map f (tuple q) = tuple (q.map f) := (rfl)

@[simp]
theorem map_position (f : V → W) (R : L.Relations n) (x : Fin n → V) (j : Fin n) :
    map f (position R x j) = position R (f ∘ x) j := (rfl)

@[simp]
theorem map_truth (f : V → W) (q : Atom L V) : map f (truth q) = truth (q.map f) := (rfl)

@[simp]
theorem map_id (v : IncidenceVertex L V) : map id v = v := by
  cases v <;> simp

theorem map_comp (g : W → X) (f : V → W) (v : IncidenceVertex L V) :
    map (g ∘ f) v = map g (map f v) := by
  cases v <;> simp [Atom.map_comp, Function.comp_assoc]

/-- Relabelling keeps the colour of every vertex. -/
@[simp]
theorem color_map (ι : (Σ n, L.Relations n) → ℕ) (f : V → W) (v : IncidenceVertex L V) :
    color ι (map f v) = color ι v := by
  cases v <;> simp

/-! ### Cardinality -/

/-- The vertices, sorted into the four kinds. -/
private def equivSum : IncidenceVertex L V ≃
    V ⊕ Atom L V ⊕ (Σ n, L.Relations n × (Fin n → V) × Fin n) ⊕ Atom L V where
  toFun
    | point a => .inl a
    | tuple q => .inr (.inl q)
    | position R x j => .inr (.inr (.inl ⟨_, R, x, j⟩))
    | truth q => .inr (.inr (.inr q))
  invFun
    | .inl a => point a
    | .inr (.inl q) => tuple q
    | .inr (.inr (.inl ⟨_, R, x, j⟩)) => position R x j
    | .inr (.inr (.inr q)) => truth q
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with _ | _ | ⟨_, _, _, _⟩ | _ <;> rfl

/-- With countably many relation symbols of each arity over a countable carrier, there are
countably many vertices. -/
instance [∀ n, Countable (L.Relations n)] [Countable V] : Countable (IncidenceVertex L V) :=
  equivSum.injective.countable

/-- Over an infinite carrier there are infinitely many vertices, the points. -/
instance [Infinite V] : Infinite (IncidenceVertex L V) :=
  .of_injective point fun _ _ h => by cases h; rfl

end IncidenceVertex

open IncidenceVertex

/-! ### The incidence graph -/

/-- The edges of the incidence graph, each listed in one direction. -/
private def IncidenceRel (c : RelationalConfiguration L V) :
    IncidenceVertex L V → IncidenceVertex L V → Prop
  | tuple q, position R x _ => q = atom R x
  | position _ x j, point a => x j = a
  | tuple q, truth r => q = r ∧ c.eval q = true
  | _, _ => False

/-- The **incidence graph** of a configuration: each tuple vertex is joined to the vertices of
the argument positions of its atom, each such vertex to the point in that position, and the tuple
vertex of an atom to its truth vertex exactly when the configuration makes the atom true. -/
def incidenceGraph (c : RelationalConfiguration L V) : SimpleGraph (IncidenceVertex L V) :=
  .fromRel (IncidenceRel c)

variable {c d : RelationalConfiguration L V} {a b : V} {q r : Atom L V} {n m : ℕ}
  {R : L.Relations n} {S : L.Relations m} {x : Fin n → V} {y : Fin m → V} {j : Fin n}
  {k : Fin m}

@[simp]
theorem incidenceGraph_adj_tuple_position :
    c.incidenceGraph.Adj (tuple q) (position R x j) ↔ q = atom R x := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem incidenceGraph_adj_position_tuple :
    c.incidenceGraph.Adj (position R x j) (tuple q) ↔ q = atom R x := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem incidenceGraph_adj_position_point :
    c.incidenceGraph.Adj (position R x j) (point a) ↔ x j = a := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem incidenceGraph_adj_point_position :
    c.incidenceGraph.Adj (point a) (position R x j) ↔ x j = a := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem incidenceGraph_adj_tuple_truth :
    c.incidenceGraph.Adj (tuple q) (truth r) ↔ q = r ∧ c.eval q = true := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem incidenceGraph_adj_truth_tuple :
    c.incidenceGraph.Adj (truth q) (tuple r) ↔ q = r ∧ c.eval q = true := by
  simp only [incidenceGraph, IncidenceRel, SimpleGraph.fromRel_adj, ne_eq, reduceCtorEq,
    not_false_eq_true, false_or, true_and]
  constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩

@[simp]
theorem not_incidenceGraph_adj_point_point : ¬c.incidenceGraph.Adj (point a) (point b) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_point_tuple : ¬c.incidenceGraph.Adj (point a) (tuple q) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_tuple_point : ¬c.incidenceGraph.Adj (tuple q) (point a) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_point_truth : ¬c.incidenceGraph.Adj (point a) (truth q) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_truth_point : ¬c.incidenceGraph.Adj (truth q) (point a) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_tuple_tuple : ¬c.incidenceGraph.Adj (tuple q) (tuple r) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_position_position :
    ¬c.incidenceGraph.Adj (position R x j) (position S y k) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_position_truth :
    ¬c.incidenceGraph.Adj (position R x j) (truth q) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_truth_position :
    ¬c.incidenceGraph.Adj (truth q) (position R x j) := by
  simp [incidenceGraph, IncidenceRel]

@[simp]
theorem not_incidenceGraph_adj_truth_truth : ¬c.incidenceGraph.Adj (truth q) (truth r) := by
  simp [incidenceGraph, IncidenceRel]

/-- The incidence graph is bipartite: points and tuple vertices form one side, position and
truth vertices the other. -/
theorem isBipartite_incidenceGraph (c : RelationalConfiguration L V) :
    c.incidenceGraph.IsBipartite :=
  (SimpleGraph.Coloring.mk
    (fun v : IncidenceVertex L V => match v with
      | point _ => false
      | tuple _ => false
      | position _ _ _ => true
      | truth _ => true)
    (by rintro (_ | _ | _ | _) (_ | _ | _ | _) <;> simp)).colorable

/-- The incidence graph has no triangles. -/
theorem cliqueFree_incidenceGraph (c : RelationalConfiguration L V) :
    c.incidenceGraph.CliqueFree 3 :=
  (isBipartite_incidenceGraph c).cliqueFree (by norm_num)

/-- An atom holds in `c` exactly when its tuple vertex has a neighbour of colour `1`, which is
then its truth vertex. -/
private theorem eval_eq_true_iff_exists_adj_color_eq_one (ι : (Σ n, L.Relations n) → ℕ) :
    c.eval q = true ↔ ∃ v, c.incidenceGraph.Adj (tuple q) v ∧ color ι v = 1 := by
  simp only [color_eq_one_iff]
  constructor
  · exact fun h => ⟨truth q, by simpa using h, q, rfl⟩
  · rintro ⟨_, hv, r, rfl⟩
    exact (incidenceGraph_adj_tuple_truth.1 hv).2

/-! ### Relabelling the incidence graph -/

/-- Relabelling vertices by `σ` maps the incidence graph of `c` onto that of `σ • c`. -/
theorem incidenceGraph_perm_smul_adj_map_iff (σ : Equiv.Perm V) {v w : IncidenceVertex L V} :
    (σ • c).incidenceGraph.Adj (v.map σ) (w.map σ) ↔ c.incidenceGraph.Adj v w := by
  have hq (q : Atom L V) : (q.map σ).map σ.symm = q := by
    rw [← Atom.map_comp, Equiv.symm_comp_self, Atom.map_id]
  have hσq {q r : Atom L V} : q.map σ = r.map σ ↔ q = r :=
    (Atom.map_injective σ.injective).eq_iff
  have hσa {q : Atom L V} {n : ℕ} {R : L.Relations n} {x : Fin n → V} :
      q.map σ = atom R (σ ∘ x) ↔ q = atom R x := by
    rw [← Atom.map_atom, hσq]
  rcases v with a | q | ⟨R, x, j⟩ | q <;> rcases w with b | r | ⟨S, y, k⟩ | r <;>
    simp [hσq, hσa, hq]

/-- Relabelling by `σ`, as an isomorphism from the incidence graph of `c` onto that of
`σ • c`. -/
def incidenceGraphPermSmulIso (σ : Equiv.Perm V) (c : RelationalConfiguration L V) :
    c.incidenceGraph ≃g (σ • c).incidenceGraph where
  toFun := map σ
  invFun := map σ.symm
  left_inv v := by rw [← map_comp, Equiv.symm_comp_self, map_id]
  right_inv v := by rw [← map_comp, Equiv.self_comp_symm, map_id]
  map_rel_iff' := incidenceGraph_perm_smul_adj_map_iff σ

@[simp]
theorem incidenceGraphPermSmulIso_apply (σ : Equiv.Perm V) (c : RelationalConfiguration L V)
    (v : IncidenceVertex L V) : incidenceGraphPermSmulIso σ c v = v.map σ := (rfl)

/-! ### Recovering a relabelling from a colour-preserving isomorphism -/

section Recover

variable {ι : (Σ n, L.Relations n) → ℕ} (f : c.incidenceGraph ≃g d.incidenceGraph)
  (hf : ∀ v, color ι (f v) = color ι v)

include hf

/-- A colour-preserving isomorphism of incidence graphs moves points to points; this is the
permutation of the carrier it induces. -/
private theorem exists_perm_apply_point :
    ∃ σ : Equiv.Perm V, ∀ a, f (point a) = point (σ a) := by
  have h a : ∃ b, f (point a) = point b := color_eq_zero_iff.1 (by rw [hf, color_point])
  choose g hg using h
  refine ⟨.ofBijective g ⟨fun a b hab => ?_, fun b => ?_⟩, hg⟩
  · exact point.inj (f.injective ((hg a).trans (hab ▸ (hg b).symm)))
  · obtain ⟨a, ha⟩ := (color_eq_zero_iff (ι := ι) (v := f.symm (point b))).1 (by
      rw [← hf, RelIso.apply_symm_apply, color_point])
    refine ⟨a, ?_⟩
    have := hg a
    rw [← ha, RelIso.apply_symm_apply] at this
    cases this
    rfl

/-- If the points move along `σ`, a colour-preserving isomorphism of incidence graphs moves the
tuple vertex of each atom to that of the relabelled atom: the symbol is read off the colour, and
each argument through the position vertex of that index. -/
private theorem apply_tuple_eq (hι : Function.Injective ι) {σ : Equiv.Perm V}
    (hσ : ∀ a, f (point a) = point (σ a)) (q : Atom L V) : f (tuple q) = tuple (q.map σ) := by
  obtain ⟨r, hr, hs⟩ := (color_eq_two_mul_add_three_iff (V := V) hι).1
    ((hf (tuple q)).trans (color_tuple ι q))
  induction q using Atom.induction_atom with | h R x =>
  induction r using Atom.induction_atom with | h S y =>
  rw [Atom.symbol_atom, Atom.symbol_atom] at hs
  cases hs
  rw [hr, Atom.map_atom]
  refine congrArg (fun z => tuple (atom R z)) (funext fun j => ?_)
  -- The vertex of position `j` goes to a position vertex of index `j`, adjacent to the image
  -- of the tuple vertex, so it is the vertex of position `j` of the image atom.
  obtain ⟨m, S, z, j', hj, hjj⟩ := (color_eq_two_mul_add_two_iff (ι := ι) (k := j)).1
    ((hf (position R x j)).trans (color_position ι R x j))
  have hadj : d.incidenceGraph.Adj (tuple (atom R y)) (position S z j') := by
    rw [← hr, ← hj, f.map_adj_iff, incidenceGraph_adj_tuple_position]
  obtain ⟨hRS, hyz⟩ := atom_eq_atom_iff.1 (incidenceGraph_adj_tuple_position.1 hadj)
  cases hRS
  cases hyz
  obtain rfl : j = j' := (Fin.ext hjj).symm
  -- The point in position `j` is adjacent to it, so goes to the point in that position.
  have hpt : d.incidenceGraph.Adj (position R y j) (point (σ (x j))) := by
    rw [← hj, ← hσ, f.map_adj_iff, incidenceGraph_adj_position_point]
  exact incidenceGraph_adj_position_point.1 hpt

/-- A colour-preserving isomorphism of incidence graphs is induced by a relabelling. -/
private theorem exists_perm_smul_eq_of_iso (hι : Function.Injective ι) :
    ∃ σ : Equiv.Perm V, σ • c = d := by
  obtain ⟨σ, hσ⟩ := exists_perm_apply_point f hf
  refine ⟨σ, ext fun q => ?_⟩
  -- An atom holds in `c` exactly when its relabelling holds in `d`: compare the truth
  -- neighbours of the two tuple vertices.
  have key (p : Atom L V) : c.eval p = d.eval (p.map σ) := by
    rw [Bool.eq_iff_iff, eval_eq_true_iff_exists_adj_color_eq_one ι,
      eval_eq_true_iff_exists_adj_color_eq_one ι, ← apply_tuple_eq f hf hι hσ]
    exact ⟨fun ⟨v, hv, h⟩ => ⟨f v, f.map_adj_iff.2 hv, (hf v).trans h⟩,
      fun ⟨v, hv, h⟩ => ⟨f.symm v, by rwa [← f.map_adj_iff, RelIso.apply_symm_apply],
        by rwa [← hf, RelIso.apply_symm_apply]⟩⟩
  rw [eval_perm_smul, key, ← Atom.map_comp, Equiv.self_comp_symm, Atom.map_id]

end Recover

/-- **Incidence graphs.** For an injection `ι` of the relation symbols into `ℕ`, two
configurations are relabellings of one another exactly when some isomorphism of their incidence
graphs preserves the colours given by `ι`. -/
theorem exists_perm_smul_eq_iff_exists_iso_incidenceGraph {ι : (Σ n, L.Relations n) → ℕ}
    (hι : Function.Injective ι) :
    (∃ σ : Equiv.Perm V, σ • c = d) ↔
      ∃ f : c.incidenceGraph ≃g d.incidenceGraph, ∀ v, color ι (f v) = color ι v := by
  refine ⟨?_, fun ⟨f, hf⟩ => exists_perm_smul_eq_of_iso f hf hι⟩
  rintro ⟨σ, rfl⟩
  exact ⟨incidenceGraphPermSmulIso σ c, fun v => by simp⟩

/-- **Incidence graphs.** For an injection `ι` of the relation symbols into `ℕ`, two
configurations of a relational language are isomorphic exactly when some isomorphism of their
incidence graphs preserves the colours given by `ι`. -/
theorem isoSetoid_iff_exists_iso_incidenceGraph [L.IsRelational]
    {ι : (Σ n, L.Relations n) → ℕ} (hι : Function.Injective ι) :
    isoSetoid L V c d ↔
      ∃ f : c.incidenceGraph ≃g d.incidenceGraph, ∀ v, color ι (f v) = color ι v := by
  rw [isoSetoid_iff_exists_perm_smul_eq, exists_perm_smul_eq_iff_exists_iso_incidenceGraph hι]

end TauCeti.RelationalConfiguration
