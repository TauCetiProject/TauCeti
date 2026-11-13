/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import TauCeti.GroupTheory.FreeGroup.Reduce
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# The Cayley graph of a free group

The Cayley graph of the free group on `α` with respect to its basis has the elements of the group
as vertices, and a dart `(g, x)` from `g` to `g * x` for every element `g` and every signed letter
`x`, that is every basis element or inverse of a basis element. The reverse of `(g, x)` is
`(g * x, x⁻¹)`.

The coordinates `SerreGraph.cayleyVertexEquiv` and `SerreGraph.cayleyDartEquiv` identify the
vertices with the elements of the free group and the darts with these pairs.

A path starting at `g` reads a word, the list of the letters of its darts
(`SerreGraph.cayleyWord`), and ends at the product of `g` with that word. The path is reduced
exactly when the word is, and every word is read along a path from every vertex. Since a reduced
word representing the identity is empty, the Cayley graph is a tree, and the distance from `g` to
`h` is the length of the reduced word of `g⁻¹ * h`.

The free group acts on its Cayley graph by left multiplication, `SerreGraph.cayleyMulLeft`.

## Main declarations

* `TauCeti.SerreGraph.cayley`: the Cayley graph of `FreeGroup α` with respect to its basis.
* `TauCeti.SerreGraph.cayleyWord`: the word read along a path, with
  `TauCeti.SerreGraph.cayleyVertexEquiv_mul_mk_cayleyWord`,
  `TauCeti.SerreGraph.isReduced_cayleyWord_iff` and `TauCeti.SerreGraph.exists_cayleyWord_eq`.
* `TauCeti.SerreGraph.cayley_isTree`: the Cayley graph is a tree.
* `TauCeti.SerreGraph.cayley_dist`: the path distance is the word metric.
* `TauCeti.SerreGraph.cayleyMulLeft`: the action by left multiplication.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §3.2.
* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, J. Algebra 248
  (2002), Introduction.
-/

public section

universe u

namespace TauCeti
namespace SerreGraph

variable {α : Type u}

/-- The Cayley graph of the free group on `α` with respect to its basis: the vertices are the
elements of the group, and the dart `(g, x)` runs from `g` to `g * x`, for a signed letter `x`.
The body is exposed because the definitions below, which compute with vertices and darts, could
not be compiled otherwise; use `cayleyVertexEquiv` and `cayleyDartEquiv` to access them. -/
@[expose] def cayley (α : Type u) : SerreGraph.{u, u} where
  V := FreeGroup α
  E := FreeGroup α × (α × Bool)
  src e := e.1
  rev e := (e.1 * FreeGroup.mk [e.2], (e.2.1, !e.2.2))
  rev_rev e := by
    refine Prod.ext ?_ (by simp)
    rw [← FreeGroup.inv_mk_singleton, mul_inv_cancel_right]
  rev_ne e h := by simpa using congrArg (fun x => x.2.2) h

/-- The vertices of the Cayley graph are the elements of the free group. -/
def cayleyVertexEquiv : (cayley α).V ≃ FreeGroup α :=
  Equiv.refl _

/-- The darts of the Cayley graph are the pairs of their source and a signed letter. -/
def cayleyDartEquiv : (cayley α).E ≃ FreeGroup α × (α × Bool) :=
  Equiv.refl _

@[simp] theorem cayleyVertexEquiv_src (e : (cayley α).E) :
    cayleyVertexEquiv ((cayley α).src e) = (cayleyDartEquiv e).1 := (rfl)

/-- The reverse of the dart `(g, x)` of the Cayley graph is `(g * x, x⁻¹)`. -/
@[simp] theorem cayleyDartEquiv_rev (e : (cayley α).E) :
    cayleyDartEquiv ((cayley α).rev e) =
      ((cayleyDartEquiv e).1 * FreeGroup.mk [(cayleyDartEquiv e).2],
        ((cayleyDartEquiv e).2.1, !(cayleyDartEquiv e).2.2)) := (rfl)

/-- The dart `(g, x)` of the Cayley graph ends at `g * x`. -/
@[simp] theorem cayleyVertexEquiv_tgt (e : (cayley α).E) :
    cayleyVertexEquiv ((cayley α).tgt e) =
      (cayleyDartEquiv e).1 * FreeGroup.mk [(cayleyDartEquiv e).2] := (rfl)

/-- A dart of the Cayley graph following another one is not its reverse exactly when their letters
do not cancel. -/
theorem cayley_ne_rev_iff {e f : (cayley α).E} (h : (cayley α).src e = (cayley α).tgt f) :
    e ≠ (cayley α).rev f ↔
      ((cayleyDartEquiv f).2.1 = (cayleyDartEquiv e).2.1 →
        (cayleyDartEquiv f).2.2 = (cayleyDartEquiv e).2.2) := by
  have h' := congrArg cayleyVertexEquiv h
  rw [cayleyVertexEquiv_src, cayleyVertexEquiv_tgt] at h'
  rw [Ne, ← cayleyDartEquiv.apply_eq_iff_eq, cayleyDartEquiv_rev]
  generalize cayleyDartEquiv e = x at h' ⊢
  generalize cayleyDartEquiv f = y at h' ⊢
  obtain ⟨g, a, b⟩ := x
  obtain ⟨g', a', b'⟩ := y
  obtain rfl : g = g' * FreeGroup.mk [(a', b')] := h'
  cases b <;> cases b' <;> simp [eq_comm]

/-! ### The word read along a path -/

/-- The word read along a path of the Cayley graph: the list of the letters of its darts. -/
def cayleyWord {v w : (cayley α).V} (p : (cayley α).Path v w) : List (α × Bool) :=
  (Path.darts (cayley α) p).map fun e => (cayleyDartEquiv e).2

@[simp] theorem cayleyWord_nil (v : (cayley α).V) :
    cayleyWord (Quiver.Path.nil : (cayley α).Path v v) = [] := by
  simp [cayleyWord]

@[simp] theorem cayleyWord_cons {a b c : (cayley α).V} (p : (cayley α).Path a b)
    (e : Quiver.Hom b c) : cayleyWord (p.cons e) = cayleyWord p ++ [(cayleyDartEquiv e.1).2] := by
  simp [cayleyWord]

@[simp] theorem cayleyWord_comp {a b c : (cayley α).V} (p : (cayley α).Path a b)
    (q : (cayley α).Path b c) : cayleyWord (p.comp q) = cayleyWord p ++ cayleyWord q := by
  simp [cayleyWord]

/-- The word read along a path has as many letters as the path has darts. -/
@[simp] theorem length_cayleyWord {v w : (cayley α).V} (p : (cayley α).Path v w) :
    (cayleyWord p).length = p.length := by
  simp [cayleyWord]

/-- A path in the Cayley graph ends at the product of its starting point with the word it
reads. -/
theorem cayleyVertexEquiv_mul_mk_cayleyWord {v w : (cayley α).V} (p : (cayley α).Path v w) :
    cayleyVertexEquiv v * FreeGroup.mk (cayleyWord p) = cayleyVertexEquiv w := by
  induction p with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    rw [cayleyWord_cons, ← FreeGroup.mul_mk, ← mul_assoc, ih, cayleyVertexEquiv_src,
      cayleyVertexEquiv_tgt]

/-- A path in the Cayley graph is reduced exactly when the word it reads is reduced. -/
@[simp] theorem isReduced_cayleyWord_iff {v w : (cayley α).V} (p : (cayley α).Path v w) :
    FreeGroup.IsReduced (cayleyWord p) ↔ Path.IsReduced (cayley α) p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    cases p with
    | nil => exact iff_of_true (by simp) (Path.isReduced_toPath _ e)
    | cons p f =>
      rw [Path.isReduced_cons_cons, ← ih, cayley_ne_rev_iff (e.2.1.trans f.2.2.symm),
        cayleyWord_cons (p.cons f) e, cayleyWord_cons p f, FreeGroup.IsReduced,
        List.isChain_append, ← FreeGroup.IsReduced]
      simp

/-- Every word is read along a path of the Cayley graph from any given vertex. -/
theorem exists_cayleyWord_eq (v : (cayley α).V) (L : List (α × Bool)) {w : (cayley α).V}
    (hL : cayleyVertexEquiv v * FreeGroup.mk L = cayleyVertexEquiv w) :
    ∃ p : (cayley α).Path v w, cayleyWord p = L := by
  induction L using List.reverseRecOn generalizing w with
  | nil =>
    obtain rfl : v = w := cayleyVertexEquiv.injective (by simpa [← FreeGroup.one_eq_mk] using hL)
    exact ⟨.nil, cayleyWord_nil v⟩
  | append_singleton L x ih =>
    obtain ⟨p, hp⟩ := ih (w := cayleyVertexEquiv.symm (cayleyVertexEquiv v * FreeGroup.mk L))
      (by simp)
    refine ⟨p.cons ⟨cayleyDartEquiv.symm (cayleyVertexEquiv v * FreeGroup.mk L, x), ?_, ?_⟩,
      by simp [hp]⟩
    · exact cayleyVertexEquiv.injective (by simp)
    · exact cayleyVertexEquiv.injective (by simp [← hL, mul_assoc, FreeGroup.mul_mk])

/-- Any two vertices `g` and `h` of the Cayley graph are joined by a path reading the reduced word
of `g⁻¹ * h`. -/
theorem exists_cayleyWord_eq_toWord [DecidableEq α] (v w : (cayley α).V) :
    ∃ p : (cayley α).Path v w,
      cayleyWord p = ((cayleyVertexEquiv v)⁻¹ * cayleyVertexEquiv w).toWord :=
  exists_cayleyWord_eq v _ (by rw [FreeGroup.mk_toWord, mul_inv_cancel_left])

/-! ### The Cayley graph is a tree -/

/-- The Cayley graph of a free group is connected. -/
theorem cayley_connected : (cayley α).Connected := by
  classical
  refine (connected_iff _).mpr ⟨⟨cayleyVertexEquiv.symm 1⟩, (preconnected_iff _).mpr fun v w => ?_⟩
  exact (exists_cayleyWord_eq_toWord v w).nonempty

/-- The Cayley graph of a free group is acyclic: a reduced closed path reads a reduced word
representing the identity, which is empty. -/
theorem cayley_isAcyclic : (cayley α).IsAcyclic := by
  refine (isAcyclic_iff _).mpr fun v p hp => Quiver.Path.eq_nil_of_length_zero p ?_
  rw [← length_cayleyWord, ((isReduced_cayleyWord_iff p).mpr hp).eq_of_mk_eq
    FreeGroup.IsReduced.nil (mul_eq_left.mp (cayleyVertexEquiv_mul_mk_cayleyWord p)),
    List.length_nil]

/-- The Cayley graph of a free group with respect to its basis is a tree. -/
theorem cayley_isTree : (cayley α).IsTree :=
  (isTree_iff _).mpr ⟨cayley_connected, cayley_isAcyclic⟩

/-- The distance between two vertices `g` and `h` of the Cayley graph of a free group is the
length of the reduced word of `g⁻¹ * h`. -/
theorem cayley_dist [DecidableEq α] (v w : (cayley α).V) :
    (cayley α).dist v w = ((cayleyVertexEquiv v)⁻¹ * cayleyVertexEquiv w).norm := by
  obtain ⟨p, hp⟩ := exists_cayleyWord_eq_toWord v w
  rw [cayley_isAcyclic.dist_eq_length
      ((isReduced_cayleyWord_iff p).mp (hp ▸ FreeGroup.isReduced_toWord)),
    ← length_cayleyWord, hp, FreeGroup.norm]

/-! ### The action by left multiplication -/

/-- The action of a free group on its Cayley graph by left multiplication. -/
def cayleyMulLeft : FreeGroup α →* (cayley α).Aut where
  toFun g :=
    { equivV := cayleyVertexEquiv.trans ((Equiv.mulLeft g).trans cayleyVertexEquiv.symm)
      equivE := cayleyDartEquiv.trans
        (((Equiv.mulLeft g).prodCongr (Equiv.refl (α × Bool))).trans cayleyDartEquiv.symm)
      map_src _ := rfl
      map_rev e := Prod.ext (mul_assoc g (cayleyDartEquiv e).1 _).symm rfl }
  -- The coordinates are identity maps, and the identity automorphism and a product of
  -- automorphisms are the identity and the composite of the underlying equivalences. So the
  -- compatibility with reversal and both laws reduce to the monoid laws of the free group.
  map_one' := Iso.ext (fun v => cayleyVertexEquiv.injective (one_mul (cayleyVertexEquiv v)))
    fun e => cayleyDartEquiv.injective (Prod.ext (one_mul (cayleyDartEquiv e).1) rfl)
  map_mul' x y := Iso.ext
    (fun v => cayleyVertexEquiv.injective (mul_assoc x y (cayleyVertexEquiv v)))
    fun e => cayleyDartEquiv.injective (Prod.ext (mul_assoc x y (cayleyDartEquiv e).1) rfl)

/-- Left multiplication acts on the vertices of the Cayley graph. -/
@[simp] theorem cayleyVertexEquiv_cayleyMulLeft_smul (g : FreeGroup α) (v : (cayley α).V) :
    cayleyVertexEquiv (cayleyMulLeft g • v) = g * cayleyVertexEquiv v := (rfl)

/-- Left multiplication moves the source of a dart of the Cayley graph and keeps its letter. -/
@[simp] theorem cayleyDartEquiv_cayleyMulLeft_smul (g : FreeGroup α) (e : (cayley α).E) :
    cayleyDartEquiv (cayleyMulLeft g • e) = (g * (cayleyDartEquiv e).1, (cayleyDartEquiv e).2) :=
  (rfl)

end SerreGraph
end TauCeti
