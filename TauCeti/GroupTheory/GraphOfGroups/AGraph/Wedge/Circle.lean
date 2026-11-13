/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.AGraph.Wedge.Basic
import all TauCeti.GroupTheory.GraphOfGroups.AGraph.Wedge.Basic

/-!
# The circles of the wedge of a family of closed paths

The wedge of a family `p` of closed alternating `𝔸`-paths at `v₀`, the `S`-wedge of Kapovich,
Weidmann and Myasnikov, has a base vertex and, for every path `p i = g₀, e₁, g₁, …, e_k, g_k` of
length `k ≥ 1`, a circle through the base vertex subdivided into `k` edges. This file describes
these circles. The edge at position `j < k` of the circle of `p i` runs from the vertex at position
`j` to the vertex at position `j + 1`, the last one back to the base vertex; it has as type the
dart `e_{j+1}` and as start label the element `g_j`, read in the vertex group of the vertex `c_j`
of `p i` (`TauCeti.GraphOfGroups.AlternatingPath.vertex`,
`TauCeti.GraphOfGroups.AlternatingPath.elem`); its end label is `1`, except for the last edge,
whose end label is `g_k`. Distinct positions give
distinct edges, every dart of the wedge is an edge of a circle or the reverse of one, and the loop
around the circle of `p i` reads `p i`.

## Main definitions

* `TauCeti.GraphOfGroups.AGraph.wedgeVertex`, `TauCeti.GraphOfGroups.AGraph.wedgeDart`,
  `TauCeti.GraphOfGroups.AGraph.wedgeLoop`: the vertices, the edges and the loop of the circle of a
  path of positive length.

## Main results

* `TauCeti.GraphOfGroups.AGraph.src_wedgeDart`, `TauCeti.GraphOfGroups.AGraph.tgt_wedgeDart_of_lt`,
  `TauCeti.GraphOfGroups.AGraph.exists_eq_wedgeDart_or_eq_rev`: the edges of a circle join its
  consecutive vertices, and the circles cover the wedge.
* `TauCeti.GraphOfGroups.AGraph.wedgeDart_eq_wedgeDart_iff`,
  `TauCeti.GraphOfGroups.AGraph.wedgeVertex_eq_wedgeVertex_iff`: the edges and the vertices other
  than the base vertex are determined by their circle and position.
* `TauCeti.GraphOfGroups.AGraph.typ_mapE_wedgeDart`,
  `TauCeti.GraphOfGroups.AGraph.typ_mapV_wedgeVertex`,
  `TauCeti.GraphOfGroups.AGraph.cast_labelα_wedgeDart`,
  `TauCeti.GraphOfGroups.AGraph.cast_labelω_wedgeDart_of_add_one_eq`: the types and labels of the
  circle of `p i` read `p i`.
* `TauCeti.GraphOfGroups.AGraph.π₁Hom_mk_wedgeLoop`: the loop around the circle of a path
  represents the class of the path.
* `TauCeti.GraphOfGroups.AGraph.isFinite_wedge_iff`: the wedge is a finite `𝔸`-graph exactly when
  finitely many paths have positive length and its base vertex group is finitely generated.

## Implementation notes

The wedge is built in `TauCeti.GroupTheory.GraphOfGroups.AGraph.Wedge.Basic` from private circles
indexed from the base vertex. The vertices, edges and labels are read here through these private
declarations, which this file imports with `import all`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §5, Definition 5.1 and Lemma 5.3.
-/

public section

universe u v w x u'

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ}

/-- Transporting an element of a vertex group along an equality of vertices does not change it as
an element of the sigma type of the vertex groups. -/
private theorem sigma_mk_cast {a b : Γ.V} (h : a = b) (g : 𝔸.vertexGroup a) :
    (⟨b, MulEquiv.cast (M := 𝔸.vertexGroup) h g⟩ : Σ c, 𝔸.vertexGroup c) = ⟨a, g⟩ := by
  subst h
  rfl

/-- Elements of vertex groups which are equal in the sigma type of the vertex groups agree after
transport. -/
private theorem cast_eq_of_sigma_eq {a b : Γ.V} (h : a = b) {g : 𝔸.vertexGroup a}
    {g' : 𝔸.vertexGroup b} (e : (⟨a, g⟩ : Σ c, 𝔸.vertexGroup c) = ⟨b, g'⟩) :
    MulEquiv.cast (M := 𝔸.vertexGroup) h g = g' := by
  subst h
  rw [MulEquiv.cast_apply, cast_eq]
  exact eq_of_heq (Sigma.mk.inj e).2

/-! ### Positions of the paths indexed from the front -/

namespace IndexedPath

variable {x y z : Γ.V} {n : ℕ}

/-- The vertex group elements of an indexed path `g₀, e₀, …, g_n, e_n, h` with their vertices, by
position: `g_k` at `k ≤ n` and `h` after. -/
private def get (t : IndexedPath 𝔸 x y n) (k : ℕ) : Σ c, 𝔸.vertexGroup c :=
  if hk : k < n then ⟨_, t.lab ⟨k, hk⟩⟩ else if k = n then ⟨_, t.lastLab⟩ else ⟨y, t.endLab⟩

private theorem get_castSucc (t : IndexedPath 𝔸 x y n) (j : Fin n) : t.get j = ⟨_, t.lab j⟩ :=
  dite_eq_left j.2

private theorem get_self (t : IndexedPath 𝔸 x y n) : t.get n = ⟨_, t.lastLab⟩ :=
  (dite_eq_right (lt_irrefl n)).trans (ite_eq_left rfl)

private theorem get_of_lt (t : IndexedPath 𝔸 x y n) {k : ℕ} (hk : n < k) :
    t.get k = ⟨y, t.endLab⟩ :=
  (dite_eq_right (by omega)).trans (ite_eq_right (by omega))

/-- The vertex at position `k ≤ n` of an indexed path is `c_k`. -/
private theorem fst_get (t : IndexedPath 𝔸 x y n) (k : Fin (n + 1)) :
    (t.get k).1 = (Fin.cons x t.vt : Fin (n + 1) → Γ.V) k := by
  cases k using Fin.lastCases with
  | last => rw [Fin.val_last, get_self]
  | cast j => rw [Fin.val_castSucc, get_castSucc]

private theorem get_single (g : 𝔸.vertexGroup x) (e : x ⟶ y) (h : 𝔸.vertexGroup y) (k : ℕ) :
    (single g e h).get k = if k = 0 then ⟨x, g⟩ else ⟨y, h⟩ := by
  unfold get
  split_ifs <;> first | omega | rfl

private theorem get_step_zero (g : 𝔸.vertexGroup x) (e : x ⟶ z) (t : IndexedPath 𝔸 z y n) :
    (step g e t).get 0 = ⟨x, g⟩ :=
  dite_eq_left (Nat.succ_pos n)

private theorem get_step_succ (g : 𝔸.vertexGroup x) (e : x ⟶ z) (t : IndexedPath 𝔸 z y n)
    (k : ℕ) : (step g e t).get (k + 1) = t.get k := by
  unfold get
  -- The entries of `Fin.cons` at a successor are those of the tail, by definition.
  split_ifs <;> first | omega | rfl

/-- The positions of `prepend p t` are those of `p` before its last position, followed by those of
`t`. -/
private theorem get_prepend (p : 𝔸.AlternatingPath x z) (t : IndexedPath 𝔸 z y n) (k : ℕ) :
    (prepend p t).2.get k =
      if k < p.length then ⟨p.vertex k, p.elem k⟩ else t.get (k - p.length) := by
  induction p generalizing n k with
  | single g => simp [prepend]
  | cons p e g ih =>
    rw [prepend, ih, AlternatingPath.length_cons]
    rcases lt_trichotomy k p.length with hk | rfl | hk
    · rw [ite_eq_left hk, ite_eq_left (by omega), AlternatingPath.elem_cons_of_le p e g hk.le,
        sigma_mk_cast]
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), Nat.sub_self,
        get_step_zero, AlternatingPath.elem_cons_of_le p e g le_rfl, sigma_mk_cast,
        AlternatingPath.elem_length, sigma_mk_cast]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        show k - p.length = k - (p.length + 1) + 1 by omega, get_step_succ]

/-- The positions of the indexed path of an alternating path are those of the alternating
path. -/
private theorem get_ofAlternatingPath (p : 𝔸.AlternatingPath x y) (h : p.length ≠ 0) (k : ℕ) :
    (ofAlternatingPath p h).2.get k = ⟨p.vertex k, p.elem k⟩ := by
  cases p with
  | single g => exact absurd (AlternatingPath.length_single g) h
  | cons q e g =>
    rw [ofAlternatingPath, get_prepend, get_single]
    rcases lt_trichotomy k q.length with hk | rfl | hk
    · rw [ite_eq_left hk, AlternatingPath.elem_cons_of_le q e g hk.le, sigma_mk_cast]
    · rw [ite_eq_right (lt_irrefl _), Nat.sub_self, ite_eq_left rfl,
        AlternatingPath.elem_cons_of_le q e g le_rfl, sigma_mk_cast, AlternatingPath.elem_length,
        sigma_mk_cast]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        AlternatingPath.elem_cons_of_lt q e g hk, sigma_mk_cast]

/-- The initial segment of length `k` has `k` darts. -/
private theorem length_darts_pre (t : IndexedPath 𝔸 x y n) (k : Fin (n + 1)) :
    (SerreGraph.Path.darts Γ (t.pre k).edgePath).length = k := by
  induction k using Fin.induction with
  | zero =>
    rw [Fin.val_zero]
    exact congrArg List.length ((congrArg (SerreGraph.Path.darts Γ)
      ((congrArg Path.edgePath (pre_zero t)).trans Path.edgePath_nil)).trans
        (SerreGraph.Path.darts_nil Γ x))
  | succ k ih => simp [pre_succ, ih]

/-- The darts of the initial segment of length `k` are `e_0, …, e_{k-1}`. -/
private theorem getElem?_darts_pre (t : IndexedPath 𝔸 x y n) (k : Fin (n + 1)) (j : Fin n)
    (hj : (j : ℕ) < k) :
    (SerreGraph.Path.darts Γ (t.pre k).edgePath)[(j : ℕ)]? = some (t.dt j).1 := by
  induction k using Fin.induction with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    rw [pre_succ, Path.edgePath_cons_dart, Path.edgePath_cons_vertex, SerreGraph.Path.darts_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Fin.val_succ k ▸ hj) with hj | hj
    · rw [List.getElem?_append_left (by rwa [length_darts_pre]), ih hj]
    · obtain rfl := Fin.ext hj
      rw [List.getElem?_append_right (by rw [length_darts_pre]; exact le_rfl), length_darts_pre,
        Fin.val_castSucc, Nat.sub_self]
      rfl

/-- The darts of the path spelled by an indexed path are `e_0, …, e_n`. -/
private theorem getElem?_darts_toPath (t : IndexedPath 𝔸 x y n) (k : Fin (n + 1)) :
    (SerreGraph.Path.darts Γ t.toPath.edgePath)[(k : ℕ)]? =
      some (Fin.lastCases (motive := fun _ => Γ.E) t.lastDart.1 (fun j => (t.dt j).1) k) := by
  rw [toPath, Path.edgePath_cons_vertex, Path.edgePath_cons_dart, Path.edgePath_cons_vertex,
    SerreGraph.Path.darts_cons]
  cases k using Fin.lastCases with
  | last =>
    rw [Fin.lastCases_last, List.getElem?_append_right (by rw [length_darts_pre]),
      length_darts_pre, Nat.sub_self]
    rfl
  | cast j =>
    rw [Fin.lastCases_castSucc, Fin.val_castSucc,
      List.getElem?_append_left (by rw [length_darts_pre]; exact j.2),
      getElem?_darts_pre t _ j (by rw [Fin.val_last]; exact j.2)]

/-- The edge path of `prepend p t` is that of `p` followed by that of `t`. -/
private theorem edgePath_toPath_prepend (p : 𝔸.AlternatingPath x z) (t : IndexedPath 𝔸 z y n) :
    (prepend p t).2.toPath.edgePath = p.toPath.edgePath.comp t.toPath.edgePath := by
  induction p generalizing n with
  | single g => simp [prepend]
  | cons p e g ih =>
    rw [prepend, ih, toPath_step, AlternatingPath.toPath_cons]
    simp [← Quiver.Path.comp_toPath_eq_cons]

/-- The indexed path of an alternating path has the same edge path. -/
private theorem edgePath_toPath_ofAlternatingPath (p : 𝔸.AlternatingPath x y)
    (h : p.length ≠ 0) : (ofAlternatingPath p h).2.toPath.edgePath = p.toPath.edgePath := by
  cases p with
  | single g => exact absurd (AlternatingPath.length_single g) h
  | cons q e g =>
    rw [ofAlternatingPath, edgePath_toPath_prepend, toPath_single]
    simp

end IndexedPath

/-! ### Positions on the circles -/

namespace AGraph

variable {v₀ : Γ.V} {ι : Type u'}

section

variable (n : ι → ℕ)

/-- The position of a dart of the wedge on its circle: `j` for `⟨i, some j⟩` and `n i` for
`⟨i, none⟩`. -/
private def dartPos : (Σ i, Option (Fin (n i))) → ℕ
  | ⟨_, some j⟩ => j
  | ⟨i, none⟩ => n i

/-- The position of a vertex of the wedge on its circle: `0` for the base vertex `none` and `j + 1`
for `some ⟨i, j⟩`. -/
private def vertexPos : Option (Σ i, Fin (n i)) → ℕ
  | none => 0
  | some ⟨_, j⟩ => j + 1

/-- The vertex at position `k` of a circle has position `k`. -/
private theorem vertexPos_wedgePos (i : ι) (k : Fin (n i + 1)) :
    vertexPos n (wedgePos n i k) = k := by
  cases k using Fin.cases <;> rfl

end

variable {n : ι → ℕ}

/-- The reverse of the last dart of the `i`-th circle starts with the label `h⁻¹`, by definition of
`wedgeLabel`. -/
private theorem labelα_rev_circleWedge_none (t : ∀ i, IndexedPath 𝔸 v₀ v₀ (n i))
    (K : Subgroup (𝔸.vertexGroup v₀)) (i : ι) :
    (circleWedge t K).labelα ((circleWedge t K).graph.rev (⟨i, none⟩, true)) =
      MulEquiv.cast (M := 𝔸.vertexGroup) ((t i).lastDart.2.2.symm.trans (Γ.src_rev _).symm :
        v₀ = Γ.src ((circleWedge t K).typ.mapE ((circleWedge t K).graph.rev (⟨i, none⟩, true))))
        (t i).endLab⁻¹ :=
  rfl

/-- The last dart of the `i`-th circle ends with the label `h`. -/
private theorem labelω_circleWedge_none (t : ∀ i, IndexedPath 𝔸 v₀ v₀ (n i))
    (K : Subgroup (𝔸.vertexGroup v₀)) (i : ι) :
    (⟨_, (circleWedge t K).labelω (⟨i, none⟩, true)⟩ : Σ c, 𝔸.vertexGroup c) =
      ⟨v₀, (t i).endLab⟩ := by
  rw [labelω_def, labelα_rev_circleWedge_none, map_inv, map_inv, inv_inv, sigma_mk_cast,
    sigma_mk_cast]

/-! ### The circles of the wedge -/

-- The vertices and darts of the wedge live in its unexposed carrier, hence `noncomputable`.
/-- The vertex at position `k` of the circle of a path `p i` of positive length: the base vertex
at position `0`, and the end of the first `k` edges of the circle, the target of
`wedgeDart p i (k - 1)`, at a position `k ≠ 0`. -/
noncomputable def wedgeVertex (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    (k : Fin (p i).length) : (wedge p).graph.V :=
  wedgePos _ i (Fin.cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2).symm k)

/-- The edge from position `k` to position `k + 1` of the circle of a path `p i` of positive
length, the last one back to the base vertex. Its type is the `(k + 1)`-th dart of `p i`. -/
noncomputable def wedgeDart (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    (k : Fin (p i).length) : (wedge p).graph.E :=
  (⟨i, Fin.lastCases none some
    (Fin.cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2).symm k)⟩, true)

/-- The loop at the base vertex of the wedge around the circle of a path `p i` of positive
length. -/
def wedgeLoop (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0}) :
    (wedge p).toGraphOfGroups.Path ⟨(wedge p).base⟩ ⟨(wedge p).base⟩ :=
  circleLoop _ _ i

/-- The positions of a circle, read on its indexed path. -/
private theorem wedgeVertex_cast (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin ((IndexedPath.ofAlternatingPath (p i) i.2).1 + 1)) :
    wedgeVertex p i (Fin.cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2) k) =
      wedgePos _ i k := by
  simp only [wedgeVertex, Fin.cast_cast, Fin.cast_eq_self]
  rfl

/-- The edges of a circle before the last one, read on its indexed path. -/
private theorem wedgeDart_cast_castSucc (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (j : Fin (IndexedPath.ofAlternatingPath (p i) i.2).1) :
    wedgeDart p i (Fin.cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2) j.castSucc) =
      (⟨i, some j⟩, true) := by
  simp only [wedgeDart, Fin.cast_cast, Fin.cast_eq_self, Fin.lastCases_castSucc]
  rfl

/-- The last edge of a circle, read on its indexed path. -/
private theorem wedgeDart_cast_last (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) :
    wedgeDart p i (Fin.cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)
      (Fin.last _)) = (⟨i, none⟩, true) := by
  simp only [wedgeDart, Fin.cast_cast, Fin.cast_eq_self, Fin.lastCases_last]
  rfl

/-- The vertex at position `k` of a circle is the base vertex exactly when `k = 0`. -/
@[simp] theorem wedgeVertex_eq_base_iff (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin (p i).length) :
    wedgeVertex p i k = (wedge p).base ↔ (k : ℕ) = 0 := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  rw [wedgeVertex_cast]
  cases k using Fin.cases <;> simp [wedgePos, wedge]

/-- The edge at position `k` of a circle starts at the vertex at position `k`. -/
@[simp] theorem src_wedgeDart (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    (k : Fin (p i).length) : (wedge p).graph.src (wedgeDart p i k) = wedgeVertex p i k := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  rw [wedgeVertex_cast]
  cases k using Fin.lastCases with
  | last => rw [wedgeDart_cast_last]; rfl
  | cast j => rw [wedgeDart_cast_castSucc]; rfl

/-- The edge at position `k` of a circle, for `k + 1` less than its length, ends at the vertex at
position `k + 1`. -/
theorem tgt_wedgeDart_of_lt (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    {k : Fin (p i).length} (hk : (k : ℕ) + 1 < (p i).length) :
    (wedge p).graph.tgt (wedgeDart p i k) = wedgeVertex p i ⟨k + 1, hk⟩ := by
  have h := IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2
  obtain ⟨k, rfl⟩ := (Fin.rightInverse_cast h).surjective k
  cases k using Fin.lastCases with
  | last => simp only [Fin.val_cast, Fin.val_last] at hk; omega
  | cast j =>
    rw [wedgeDart_cast_castSucc, show (⟨_ + 1, hk⟩ : Fin (p i).length) = Fin.cast h j.succ from
      Fin.ext (by simp), wedgeVertex_cast]
    rfl

/-- The edge at the last position of a circle ends at the base vertex. -/
theorem tgt_wedgeDart_of_add_one_eq (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) {k : Fin (p i).length} (hk : (k : ℕ) + 1 = (p i).length) :
    (wedge p).graph.tgt (wedgeDart p i k) = (wedge p).base := by
  have h := IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2
  obtain ⟨k, rfl⟩ := (Fin.rightInverse_cast h).surjective k
  cases k using Fin.lastCases with
  | last => rw [wedgeDart_cast_last]; rfl
  | cast j => simp only [Fin.val_cast, Fin.val_castSucc] at hk; omega

/-- Every dart of the wedge is an edge of a circle or the reverse of one. -/
theorem exists_eq_wedgeDart_or_eq_rev (p : ι → 𝔸.AlternatingPath v₀ v₀) (f : (wedge p).graph.E) :
    ∃ i k, f = wedgeDart p i k ∨ f = (wedge p).graph.rev (wedgeDart p i k) := by
  have h (i : {i // (p i).length ≠ 0}) := IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2
  obtain ⟨⟨i, _ | j⟩, b⟩ := f
  · refine ⟨i, Fin.cast (h i) (Fin.last _), ?_⟩
    rw [wedgeDart_cast_last]
    cases b
    exacts [.inr rfl, .inl rfl]
  · refine ⟨i, Fin.cast (h i) j.castSucc, ?_⟩
    rw [wedgeDart_cast_castSucc]
    cases b
    exacts [.inr rfl, .inl rfl]

/-- Every vertex of the wedge other than the base vertex lies on a circle. -/
theorem exists_eq_wedgeVertex (p : ι → 𝔸.AlternatingPath v₀ v₀) {u : (wedge p).graph.V}
    (hu : u ≠ (wedge p).base) : ∃ i k, u = wedgeVertex p i k := by
  obtain _ | ⟨i, j⟩ := u
  · exact absurd rfl hu
  · exact ⟨i, _, (wedgeVertex_cast p i j.succ).symm⟩

/-- The vertex groups at the positions `k ≠ 0` of the circles are trivial. -/
theorem grp_wedgeVertex_of_ne_zero (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    {k : Fin (p i).length} (hk : (k : ℕ) ≠ 0) : (wedge p).grp (wedgeVertex p i k) = ⊥ :=
  grp_wedge_of_ne_base p (mt (wedgeVertex_eq_base_iff p i k).1 hk)

/-- The edges of a circle other than the last one have the end label `1`. -/
theorem labelω_wedgeDart_of_lt (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    {k : Fin (p i).length} (hk : (k : ℕ) + 1 < (p i).length) :
    (wedge p).labelω (wedgeDart p i k) = 1 := by
  have h := IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2
  obtain ⟨k, rfl⟩ := (Fin.rightInverse_cast h).surjective k
  cases k using Fin.lastCases with
  | last => simp only [Fin.val_cast, Fin.val_last] at hk; omega
  | cast j =>
    -- The reverse of the edge has the start label `1`, by definition of `wedgeLabel`.
    rw [wedgeDart_cast_castSucc]
    exact (labelω_def _ _).trans (inv_eq_one.2 (map_one _))

/-- The path read along the loop around the circle of a path `p i` of positive length represents
the class of `p i`. -/
theorem π₁Hom_mk_wedgeLoop (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) : (wedge p).π₁Hom (π₁.mk (wedgeLoop p i)) = π₁.mk (p i).toPath :=
  (π₁Hom_mk_circleLoop _ _ i).trans
    (π₁.mk_eq_mk_iff.2 (IndexedPath.toPath_ofAlternatingPath_homotopic _ i.2))

/-- The vertex at position `0` of a circle is the base vertex. -/
@[simp] theorem wedgeVertex_zero (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    (h : 0 < (p i).length) : wedgeVertex p i ⟨0, h⟩ = (wedge p).base :=
  (wedgeVertex_eq_base_iff p i _).2 rfl

/-- The vertex at position `k` of a circle has position `k`. -/
private theorem vertexPos_wedgeVertex (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin (p i).length) :
    vertexPos _ (wedgeVertex p i k) = k := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  rw [wedgeVertex_cast]
  exact vertexPos_wedgePos
    (fun c : {i // (p i).length ≠ 0} => (IndexedPath.ofAlternatingPath (p c) c.2).1) i k

/-- The vertex at a position `k ≠ 0` of the circle of `p i` lies on that circle. -/
private theorem map_fst_wedgeVertex (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) {k : Fin (p i).length} (hk : (k : ℕ) ≠ 0) :
    Option.map Sigma.fst (wedgeVertex p i k) = some i := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  rw [wedgeVertex_cast]
  cases k using Fin.cases with
  | zero => exact absurd rfl hk
  | succ j => rfl

/-- Two vertices of the circles are equal exactly when both are the base vertex or they are at the
same position of the same circle. -/
@[simp] theorem wedgeVertex_eq_wedgeVertex_iff (p : ι → 𝔸.AlternatingPath v₀ v₀)
    {i₁ i₂ : {i // (p i).length ≠ 0}} {k₁ : Fin (p i₁).length} {k₂ : Fin (p i₂).length} :
    wedgeVertex p i₁ k₁ = wedgeVertex p i₂ k₂ ↔
      (k₁ : ℕ) = 0 ∧ (k₂ : ℕ) = 0 ∨ i₁ = i₂ ∧ (k₁ : ℕ) = k₂ := by
  refine ⟨fun h => ?_, ?_⟩
  · have hk : (k₁ : ℕ) = k₂ := by
      rw [← vertexPos_wedgeVertex p i₁ k₁, h, vertexPos_wedgeVertex]
    by_cases h₁ : (k₁ : ℕ) = 0
    · exact .inl ⟨h₁, hk ▸ h₁⟩
    · refine .inr ⟨Option.some_injective _ ?_, hk⟩
      rw [← map_fst_wedgeVertex p i₁ h₁, h, map_fst_wedgeVertex p i₂ (hk ▸ h₁)]
  · rintro (⟨h₁, h₂⟩ | ⟨rfl, h⟩)
    · rw [(wedgeVertex_eq_base_iff p i₁ k₁).2 h₁, (wedgeVertex_eq_base_iff p i₂ k₂).2 h₂]
    · rw [Fin.ext h]

/-- The edge at position `k` of a circle has position `k`. -/
private theorem dartPos_wedgeDart (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin (p i).length) :
    dartPos _ (wedgeDart p i k).1 = k := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  cases k using Fin.lastCases with
  | last => rw [wedgeDart_cast_last]; rfl
  | cast j => rw [wedgeDart_cast_castSucc]; rfl

/-- Two edges of the circles are equal exactly when they are at the same position of the same
circle. -/
@[simp] theorem wedgeDart_eq_wedgeDart_iff (p : ι → 𝔸.AlternatingPath v₀ v₀)
    {i₁ i₂ : {i // (p i).length ≠ 0}} {k₁ : Fin (p i₁).length} {k₂ : Fin (p i₂).length} :
    wedgeDart p i₁ k₁ = wedgeDart p i₂ k₂ ↔ i₁ = i₂ ∧ (k₁ : ℕ) = k₂ := by
  refine ⟨fun h => ⟨congrArg (fun f => f.1.1) h, ?_⟩, ?_⟩
  · rw [← dartPos_wedgeDart p i₁ k₁, h, dartPos_wedgeDart]
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

/-- No edge of a circle is the reverse of an edge of a circle. -/
theorem wedgeDart_ne_rev (p : ι → 𝔸.AlternatingPath v₀ v₀) (i₁ i₂ : {i // (p i).length ≠ 0})
    (k₁ : Fin (p i₁).length) (k₂ : Fin (p i₂).length) :
    wedgeDart p i₁ k₁ ≠ (wedge p).graph.rev (wedgeDart p i₂ k₂) :=
  -- The edges of the circles are the darts `(d, true)` and their reverses are the darts
  -- `(d, false)`, by definition.
  fun h => Bool.noConfusion (congrArg Prod.snd h : true = false)

/-- The edge path of the path to position `0` of a circle is empty. -/
private theorem edgePath_circlePath_zero (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) :
    (circlePath (wedgeCircles p) (wedgeGroup p) i 0).edgePath =
      (Quiver.Path.nil : (wedge p).graph.Path _ _) :=
  -- The path to position `0` is empty, by definition of `circlePath`.
  Path.edgePath_nil

/-- The edge path of the path to position `k + 1` of a circle is that of the path to position `k`
followed by the dart `⟨i, some k⟩`. -/
private theorem edgePath_circlePath_succ (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin (IndexedPath.ofAlternatingPath (p i) i.2).1) :
    (circlePath (wedgeCircles p) (wedgeGroup p) i k.succ).edgePath =
      Quiver.Path.cons (V := (wedge p).graph.V)
        (circlePath (wedgeCircles p) (wedgeGroup p) i k.castSucc).edgePath
        ((wedge p).graph.dart (⟨i, some k⟩, true)) :=
  (congrArg Path.edgePath (circlePath_succ (wedgeCircles p) (wedgeGroup p) i k)).trans
    (Path.edgePath_cons_dart _ _)

/-- The edge path of the loop around a circle is that of the path to its last position followed by
the dart `⟨i, none⟩`. -/
private theorem edgePath_wedgeLoop (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) :
    (wedgeLoop p i).edgePath =
      Quiver.Path.cons (V := (wedge p).graph.V)
        (circlePath (wedgeCircles p) (wedgeGroup p) i (Fin.last _)).edgePath
        ((wedge p).graph.dart (⟨i, none⟩, true)) :=
  -- The loop is the path to the last position followed by the dart `⟨i, none⟩`, by definition of
  -- `circleLoop`.
  Path.edgePath_cons_dart _ _

/-- The darts along the circle of `p i` up to position `k` are its first `k` darts. -/
private theorem darts_edgePath_circlePath (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin ((IndexedPath.ofAlternatingPath (p i) i.2).1 + 1)) :
    SerreGraph.Path.darts (wedge p).graph
      (circlePath (wedgeCircles p) (wedgeGroup p) i k).edgePath =
        (List.ofFn fun j => ((⟨i, some j⟩, true) : (wedge p).graph.E)).take k := by
  induction k using Fin.induction with
  | zero =>
    rw [Fin.val_zero, List.take_zero]
    exact (congrArg (SerreGraph.Path.darts (wedge p).graph) (edgePath_circlePath_zero p i)).trans
      (SerreGraph.Path.darts_nil _ _)
  | succ k ih =>
    refine ((congrArg (SerreGraph.Path.darts (wedge p).graph)
      (edgePath_circlePath_succ p i k)).trans (SerreGraph.Path.darts_cons _ _ _)).trans ?_
    rw [ih, Fin.val_succ, List.take_add_one, Fin.val_castSucc, List.getElem?_ofFn,
      dite_eq_left k.2, Option.toList_some]
    -- The dart `⟨i, some k⟩`, read through the quiver of the wedge, is `⟨i, some k⟩`.
    exact congrArg (HAppend.hAppend _) (congrArg (fun f => [f]) (SerreGraph.dart_val _ _))

/-- The path along the circle of `p i` is read from its darts. -/
private theorem mapPath_edgePath_circlePath (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin ((IndexedPath.ofAlternatingPath (p i) i.2).1 + 1)) :
    (dartPrefunctor (wedge p).toGraphOfGroups).mapPath
      (circlePath (wedgeCircles p) (wedgeGroup p) i k).edgePath =
        circlePath (wedgeCircles p) (wedgeGroup p) i k := by
  induction k using Fin.induction with
  | zero =>
    -- The path to position `0` is empty, by definition of `circlePath`.
    exact (congrArg _ (edgePath_circlePath_zero p i)).trans (Prefunctor.mapPath_nil _ _)
  | succ k ih =>
    -- The path to position `k + 1` is the path to position `k` followed by the dart `⟨i, some k⟩`,
    -- by definition of `circlePath`.
    exact (congrArg _ (edgePath_circlePath_succ p i k)).trans ((Prefunctor.mapPath_cons _ _ _).trans
      (congrArg (fun q => q.cons (Letter.dart ((wedge p).graph.dart (⟨i, some k⟩, true)))) ih))

/-- The edges read along the loop around a circle are the edges of the circle, in order. -/
@[simp] theorem darts_edgePath_wedgeLoop (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) :
    SerreGraph.Path.darts _ (wedgeLoop p i).edgePath = List.ofFn (wedgeDart p i) := by
  have h := IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2
  refine ((congrArg (SerreGraph.Path.darts (wedge p).graph) (edgePath_wedgeLoop p i)).trans
    ((SerreGraph.Path.darts_cons _ _ _).trans
      (congrArg (· ++ _) (darts_edgePath_circlePath p i _)))).trans ?_
  rw [Fin.val_last, List.take_of_length_le (by simp),
    List.ofFn_congr h.symm, List.ofFn_succ', List.concat_eq_append]
  simp only [wedgeDart_cast_castSucc, wedgeDart_cast_last]
  -- The dart `⟨i, none⟩`, read through the quiver of the wedge, is `⟨i, none⟩`.
  exact congrArg (HAppend.hAppend _) (congrArg (fun f => [f]) (SerreGraph.dart_val _ _))

/-- The loop around a circle is the edge path of its edges, read as a path of the graph of groups
of the wedge. -/
@[simp] theorem mapPath_edgePath_wedgeLoop (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) :
    (dartPrefunctor _).mapPath (wedgeLoop p i).edgePath = wedgeLoop p i := by
  -- The loop is the path along the circle followed by its last edge, by definition.
  exact (congrArg _ (edgePath_wedgeLoop p i)).trans ((Prefunctor.mapPath_cons _ _ _).trans
    (congrArg (fun q => q.cons (Letter.dart ((wedge p).graph.dart (⟨i, none⟩, true))))
      (mapPath_edgePath_circlePath p i _)))

/-- The edge at position `k` of the circle of `p i` has as type the dart `e_{k+1}` of `p i`. -/
theorem typ_mapE_wedgeDart (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    (k : Fin (p i).length) :
    (wedge p).typ.mapE (wedgeDart p i k) =
      (SerreGraph.Path.darts Γ (p i).toPath.edgePath)[(k : ℕ)]'(by simp) := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  rw [← Option.some_inj, ← List.getElem?_eq_getElem,
    ← IndexedPath.edgePath_toPath_ofAlternatingPath (p i) i.2, Fin.val_cast,
    IndexedPath.getElem?_darts_toPath]
  cases k using Fin.lastCases with
  | last => rw [wedgeDart_cast_last, Fin.lastCases_last]; rfl
  | cast j => rw [wedgeDart_cast_castSucc, Fin.lastCases_castSucc]; rfl

/-- The vertex at position `k` of the circle of `p i` has as type the vertex `c_k` of `p i`. -/
@[simp] theorem typ_mapV_wedgeVertex (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) (k : Fin (p i).length) :
    (wedge p).typ.mapV (wedgeVertex p i k) = (p i).vertex k := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  rw [wedgeVertex_cast]
  -- The type of the vertex at position `k` is `c_k`, by definition of `wedge` and `wedgeTyp`.
  exact (wedgeTyp_wedgePos (wedgeCircles p) i k).trans ((IndexedPath.fst_get _ k).symm.trans
    (congrArg Sigma.fst (IndexedPath.get_ofAlternatingPath (p i) i.2 k)))

/-- The start label of the edge at position `k` of the circle of `p i`, read in the vertex group of
the vertex `c_k` of `p i`, is the element `g_k` of `p i`. -/
theorem cast_labelα_wedgeDart (p : ι → 𝔸.AlternatingPath v₀ v₀) (i : {i // (p i).length ≠ 0})
    (k : Fin (p i).length) :
    MulEquiv.cast (M := 𝔸.vertexGroup) (((wedge p).typ.map_src _).trans
      ((congrArg _ (src_wedgeDart p i k)).trans (typ_mapV_wedgeVertex p i k)))
        ((wedge p).labelα (wedgeDart p i k)) = (p i).elem k := by
  obtain ⟨k, rfl⟩ :=
    (Fin.rightInverse_cast (IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2)).surjective k
  apply cast_eq_of_sigma_eq
  rw [Fin.val_cast, ← IndexedPath.get_ofAlternatingPath (p i) i.2]
  -- The start labels of the edges are the transported elements of the indexed path, by
  -- definition of `wedgeLabel`.
  cases k using Fin.lastCases with
  | last => rw [wedgeDart_cast_last, Fin.val_last, IndexedPath.get_self]; exact sigma_mk_cast _ _
  | cast j =>
    rw [wedgeDart_cast_castSucc, Fin.val_castSucc, IndexedPath.get_castSucc]
    exact sigma_mk_cast _ _

/-- The end label of the last edge of the circle of `p i`, read in `A_{v₀}`, is the last element
`g_k` of `p i`. -/
theorem cast_labelω_wedgeDart_of_add_one_eq (p : ι → 𝔸.AlternatingPath v₀ v₀)
    (i : {i // (p i).length ≠ 0}) {k : Fin (p i).length} (hk : (k : ℕ) + 1 = (p i).length) :
    MulEquiv.cast (M := 𝔸.vertexGroup)
      (by rw [SerreGraph.Hom.map_tgt, tgt_wedgeDart_of_add_one_eq p i hk, typ_base])
      ((wedge p).labelω (wedgeDart p i k)) = (p i).last := by
  have h := IndexedPath.ofAlternatingPath_fst_add_one (p i) i.2
  obtain ⟨k, rfl⟩ := (Fin.rightInverse_cast h).surjective k
  apply cast_eq_of_sigma_eq
  cases k using Fin.lastCases with
  | cast j => simp only [Fin.val_cast, Fin.val_castSucc] at hk; omega
  | last =>
    rw [wedgeDart_cast_last]
    refine (labelω_circleWedge_none (wedgeCircles p) (wedgeGroup p) i).trans ?_
    rw [← IndexedPath.get_of_lt _ (Nat.lt_add_one _), IndexedPath.get_ofAlternatingPath, h,
      AlternatingPath.elem_length, sigma_mk_cast]

/-- The wedge is a finite `𝔸`-graph exactly when finitely many paths have positive length and its
base vertex group is finitely generated. -/
theorem isFinite_wedge_iff (p : ι → 𝔸.AlternatingPath v₀ v₀) :
    (wedge p).IsFinite ↔ Finite {i // (p i).length ≠ 0} ∧ (wedgeGroup p).FG := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · have := h.finite_E
    exact Finite.of_injective (fun i => wedgeDart p i ⟨0, Nat.pos_of_ne_zero i.2⟩)
      fun _ _ hi => ((wedgeDart_eq_wedgeDart_iff p).1 hi).1
  · rw [← map_grp_wedge_base]
    have : Group.FG ((wedge p).grp (wedge p).base) := (Group.fg_iff_subgroup_fg _).2 (h.fg _)
    exact (Group.fg_iff_subgroup_fg _).1 inferInstance
  · have : Group.FG (wedgeGroup p) := (Group.fg_iff_subgroup_fg _).2 h
    exact isFinite_wedge p

end AGraph

end GraphOfGroups

end TauCeti
