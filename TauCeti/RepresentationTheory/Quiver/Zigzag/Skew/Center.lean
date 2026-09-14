/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Subalgebra.Center
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basis

/-!
# The centre of a skew-zigzag algebra

For a finite connected simple graph without isolated vertices, the centre of every skew-zigzag
relation quotient is spanned by the unit and one volume class at each vertex. Thus its dimension is
independent of the skew parameter and equals the number of vertices plus one.

The volume at a vertex is defined relative to a chosen incident edge. Changing that choice rescales
the corresponding basis vector by a unit, so it does not change the central subspace or its
dimension. The proof uses the vertex--arrow--volume basis: centrality kills every off-diagonal
corner, while commuting with an arrow forces the coefficients of the vertex idempotents to agree
along its edge.

## Main results

* `TauCeti.mem_center_skewZigzagQuotient_iff`: characterizes all central elements.
* `TauCeti.skewZigzagCenterBasis`: the unit and chosen volume classes form a basis of the centre.
* `TauCeti.finrank_center_skewZigzagQuotient`: the centre has dimension `|V| + 1`.

## References

See C. Couture, *Skew-Zigzag Algebras*, Sections 3 and 4,
https://arxiv.org/abs/1509.08405. The proof follows the ordinary zigzag-centre calculation already
formalized in `TauCeti.RepresentationTheory.Quiver.Zigzag.Center`, with the parameter-dependent
volume basis from `TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basis`.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (c : SkewZigzagParameter k G) (t : ∀ i : V, {j : V // G.Adj i j})

/-! ### Multiplication used by the centre calculation -/

private theorem skewZigzagMk_vertexIdempotent_mul_self (i : V) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G i)) =
      skewZigzagMk k G c (vertexIdempotent k (vertex G i)) := by
  rw [← map_mul, vertexIdempotent_mul_self]

private theorem skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne
    {i j : V} (h : i ≠ j) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G j)) = 0 := by
  rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne ((vertex_injective G).ne h),
    map_zero]

private theorem skewZigzagMk_vertexIdempotent_mul_ofArrow (d : G.Dart) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G d.snd)) *
        skewZigzagMk k G c (ofArrow (arrow G d.adj)) =
      skewZigzagMk k G c (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow]

private theorem skewZigzagMk_vertexIdempotent_mul_ofArrow_of_ne
    {v : V} (d : G.Dart) (h : v ≠ d.snd) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G v)) *
        skewZigzagMk k G c (ofArrow (arrow G d.adj)) = 0 := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow_of_ne _ _ d.adj h, map_zero]

private theorem skewZigzagMk_ofArrow_mul_vertexIdempotent (d : G.Dart) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G d.fst)) =
      skewZigzagMk k G c (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent]

private theorem skewZigzagMk_ofArrow_mul_vertexIdempotent_of_ne
    {v : V} (d : G.Dart) (h : v ≠ d.fst) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G v)) = 0 := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent_of_ne _ _ d.adj h, map_zero]

private theorem skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume (i : V) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) *
      skewZigzagVolume k G c (t i) = skewZigzagVolume k G c (t i) := by
  rw [skewZigzagVolume_def, ← map_mul, vertexIdempotent_mul_backtrackElem]

private theorem skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume_of_ne
    {v i : V} (h : v ≠ i) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G v)) *
        skewZigzagVolume k G c (t i) = 0 := by
  rw [skewZigzagVolume_def, ← map_mul,
    vertexIdempotent_mul_backtrackElem_of_ne _ _ (t i).2 h, map_zero]

private theorem skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent (i : V) :
    skewZigzagVolume k G c (t i) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G i)) =
      skewZigzagVolume k G c (t i) := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_mul_vertexIdempotent]

private theorem skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent_of_ne
    {i v : V} (h : v ≠ i) :
    skewZigzagVolume k G c (t i) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G v)) = 0 := by
  rw [skewZigzagVolume_def, ← map_mul,
    backtrackElem_mul_vertexIdempotent_of_ne _ _ (t i).2 h, map_zero]

private theorem skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le
    (x y : Quiver.TotalPath (DoubledQuiver G))
    (h : 3 ≤ x.2.2.length + y.2.2.length) :
    skewZigzagMk k G c (ofPath x * ofPath y) = 0 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨d, e, q⟩ := y
  rcases eq_or_ne e a with rfl | hea
  · rw [ofPath_mul_ofPath_of_comp]
    exact skewZigzagMk_ofPath_eq_zero_of_three_le k G c _
      (by simpa only [_root_.Quiver.Path.length_comp, Nat.add_comm] using h)
  · rw [ofPath_mul_ofPath_of_not_composable hea, map_zero]

private theorem skewZigzagMk_ofArrow_mul_skewZigzagVolume (d : G.Dart) (i : V) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) * skewZigzagVolume k G c (t i) = 0 := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_eq_ofPath,
    ofArrow_eq_ofPath_arrowPath]
  exact skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G c _ _
    (by simp [length_backtrackPath, length_arrowPath])

private theorem skewZigzagVolume_mul_skewZigzagMk_ofArrow (i : V) (d : G.Dart) :
    skewZigzagVolume k G c (t i) * skewZigzagMk k G c (ofArrow (arrow G d.adj)) = 0 := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_eq_ofPath,
    ofArrow_eq_ofPath_arrowPath]
  exact skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G c _ _
    (by simp [length_backtrackPath, length_arrowPath])

private theorem skewZigzagVolume_mul_skewZigzagVolume (i j : V) :
    skewZigzagVolume k G c (t i) * skewZigzagVolume k G c (t j) = 0 := by
  rw [skewZigzagVolume_def, skewZigzagVolume_def, ← map_mul, backtrackElem_eq_ofPath,
    backtrackElem_eq_ofPath]
  exact skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G c _ _
    (by simp [length_backtrackPath])

/-! ### A criterion for centrality -/

/-- An element commuting with every vertex idempotent, every arrow and every volume class is
central: those classes span the zigzag relation quotient. -/
theorem mem_center_of_commute_skewZigzagBasisFun {z : skewZigzagQuotient k G c}
    (h : ∀ b, z * skewZigzagBasisFun k G c t b = skewZigzagBasisFun k G c t b * z) :
    z ∈ Subalgebra.center k (skewZigzagQuotient k G c) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  exact (Commute.span_right (s := Set.range (skewZigzagBasisFun k G c t))
    (fun _ ⟨b, hb⟩ => by rw [← hb]; exact h b) y (by
    rw [span_range_skewZigzagBasisFun_eq_top]
    exact Submodule.mem_top)).eq.symm

/-- A scalar annihilating a member of the vertex, arrow and volume family is zero: that family is
a basis when no vertex is isolated. -/
private theorem smul_skewZigzagBasisFun_eq_zero
    {b : ZigzagBasisIndex G} {a : k} (h : a • skewZigzagBasisFun k G c t b = 0) : a = 0 := by
  have h0 : (skewZigzagBasis k G c t).repr (a • skewZigzagBasisFun k G c t b) = 0 := by
    rw [h, map_zero]
  rw [map_smul, ← skewZigzagBasis_apply k G c t b, Module.Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h0
  exact Finsupp.single_eq_zero.mp h0

/-! ### The volume classes are central -/

/-- **The volume class of a vertex is central.** The idempotent at its base is a two-sided unit for
it, the other idempotents kill it on both sides, and the arrows and the other volume classes
annihilate it on both sides. -/
@[simp]
theorem skewZigzagVolume_mem_center (i : V) :
    skewZigzagVolume k G c (t i) ∈ Subalgebra.center k (skewZigzagQuotient k G c) := by
  refine mem_center_of_commute_skewZigzagBasisFun k G c t fun b => ?_
  rcases b with j | d | j
  · rw [skewZigzagBasisFun_inl]
    rcases eq_or_ne j i with rfl | hji
    · rw [skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent,
        skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume]
    · rw [skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent_of_ne k G c t hji,
        skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume_of_ne k G c t hji]
  · rw [skewZigzagBasisFun_inr_inl, skewZigzagVolume_mul_skewZigzagMk_ofArrow,
      skewZigzagMk_ofArrow_mul_skewZigzagVolume]
  · rw [skewZigzagBasisFun_inr_inr, skewZigzagVolume_mul_skewZigzagVolume,
      skewZigzagVolume_mul_skewZigzagVolume]

/-! ### Combinations of vertex idempotents -/

/-- A combination of vertex idempotents meets an idempotent through the coefficient at its
vertex. -/
private theorem sum_smul_vertexIdempotent_mul_vertexIdempotent [Fintype V] (f : V → k) (j : V) :
    (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
        * skewZigzagMk k G c (vertexIdempotent k (vertex G j))
      = f j • skewZigzagMk k G c (vertexIdempotent k (vertex G j)) := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, skewZigzagMk_vertexIdempotent_mul_self]
  · intro i _ hij
    rw [smul_mul_assoc,
      skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G c hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A combination of vertex idempotents meets an idempotent through the coefficient at its vertex,
on the other side. -/
private theorem vertexIdempotent_mul_sum_smul_vertexIdempotent [Fintype V] (f : V → k) (j : V) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G j))
        * ∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i))
      = f j • skewZigzagMk k G c (vertexIdempotent k (vertex G j)) := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, skewZigzagMk_vertexIdempotent_mul_self]
  · intro i _ hij
    rw [mul_smul_comm, skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G c (Ne.symm hij),
      smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A combination of vertex idempotents meets an arrow through the coefficient at its head. -/
private theorem sum_smul_vertexIdempotent_mul_ofArrow [Fintype V] (f : V → k) (d : G.Dart) :
    (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
        * skewZigzagMk k G c (ofArrow (arrow G d.adj))
      = f d.snd • skewZigzagMk k G c (ofArrow (arrow G d.adj)) := by
  rw [Finset.sum_mul, Finset.sum_eq_single d.snd]
  · rw [smul_mul_assoc, skewZigzagMk_vertexIdempotent_mul_ofArrow]
  · intro i _ hij
    rw [smul_mul_assoc, skewZigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G c d hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ d.snd) hj

/-- A combination of vertex idempotents meets an arrow through the coefficient at its tail, on the
other side. -/
private theorem ofArrow_mul_sum_smul_vertexIdempotent [Fintype V] (f : V → k) (d : G.Dart) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj))
        * ∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i))
      = f d.fst • skewZigzagMk k G c (ofArrow (arrow G d.adj)) := by
  rw [Finset.mul_sum, Finset.sum_eq_single d.fst]
  · rw [mul_smul_comm, skewZigzagMk_ofArrow_mul_vertexIdempotent]
  · intro i _ hij
    rw [mul_smul_comm, skewZigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G c d hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ d.fst) hj

/-- A combination of vertex idempotents meets a volume class through the coefficient at its base
vertex. -/
private theorem sum_smul_vertexIdempotent_mul_zigzagVolume [Fintype V] (f : V → k) (j : V) :
    (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i))) * skewZigzagVolume k G c (t j)
      = f j • skewZigzagVolume k G c (t j) := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume]
  · intro i _ hij
    rw [smul_mul_assoc,
      skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume_of_ne k G c t hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A combination of vertex idempotents meets a volume class through the coefficient at its base
vertex, on the other side. -/
private theorem skewZigzagVolume_mul_sum_smul_vertexIdempotent [Fintype V] (f : V → k) (j : V) :
    skewZigzagVolume k G c (t j) * ∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i))
      = f j • skewZigzagVolume k G c (t j) := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent]
  · intro i _ hij
    rw [mul_smul_comm,
      skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent_of_ne k G c t hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **A combination of vertex idempotents whose coefficients are constant along the edges is
central.** An arrow sees the coefficient at its head on one side and the coefficient at its tail on
the other, and an idempotent or a volume class sees the coefficient at its own vertex on both
sides. -/
theorem sum_smul_skewZigzagMk_vertexIdempotent_mem_center [Fintype V]
    (t : ∀ i : V, {j : V // G.Adj i j}) (f : V → k)
    (hf : ∀ ⦃i j : V⦄, G.Adj i j → f i = f j) :
    (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
      ∈ Subalgebra.center k (skewZigzagQuotient k G c) := by
  refine mem_center_of_commute_skewZigzagBasisFun k G c t fun b => ?_
  rcases b with j | d | j
  · rw [skewZigzagBasisFun_inl, sum_smul_vertexIdempotent_mul_vertexIdempotent,
      vertexIdempotent_mul_sum_smul_vertexIdempotent]
  · rw [skewZigzagBasisFun_inr_inl, sum_smul_vertexIdempotent_mul_ofArrow,
      ofArrow_mul_sum_smul_vertexIdempotent, hf d.adj]
  · rw [skewZigzagBasisFun_inr_inr, sum_smul_vertexIdempotent_mul_zigzagVolume,
      skewZigzagVolume_mul_sum_smul_vertexIdempotent]

/-- **A combination of vertex idempotents is central exactly when its coefficients are constant
along the edges.** The converse of
`TauCeti.sum_smul_skewZigzagMk_vertexIdempotent_mem_center` needs the arrows to be independent,
hence the hypothesis that no vertex is isolated. -/
@[simp]
theorem sum_smul_skewZigzagMk_vertexIdempotent_mem_center_iff [Fintype V]
    (t : ∀ i : V, {j : V // G.Adj i j}) (f : V → k) :
    (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
        ∈ Subalgebra.center k (skewZigzagQuotient k G c)
      ↔ ∀ ⦃i j : V⦄, G.Adj i j → f i = f j := by
  refine ⟨fun hz i j hij => ?_, sum_smul_skewZigzagMk_vertexIdempotent_mem_center k G c t f⟩
  have hcomm := (Subalgebra.mem_center_iff.mp hz)
    (skewZigzagMk k G c (ofArrow (arrow G (⟨(i, j), hij⟩ : G.Dart).adj)))
  rw [sum_smul_vertexIdempotent_mul_ofArrow k G c f ⟨(i, j), hij⟩,
    ofArrow_mul_sum_smul_vertexIdempotent k G c f ⟨(i, j), hij⟩] at hcomm
  have hzero : (f i - f j) • skewZigzagBasisFun k G c t (.inr (.inl ⟨(i, j), hij⟩)) = 0 := by
    rw [skewZigzagBasisFun_inr_inl, sub_smul, sub_eq_zero]
    exact hcomm
  exact sub_eq_zero.mp (smul_skewZigzagBasisFun_eq_zero k G c t hzero)

/-! ### The diagonal corners of a central element -/

/-- The unit of the zigzag relation quotient is the sum of the vertex idempotents. -/
private theorem one_eq_sum_skewZigzagMk_vertexIdempotent [Fintype V] :
    (1 : skewZigzagQuotient k G c)
      = ∑ i, skewZigzagMk k G c (vertexIdempotent k (vertex G i)) := by
  rw [← map_one (skewZigzagMk k G c), PathAlgebra.one_def, map_sum]
  exact (Fintype.sum_equiv (vertexEquiv G)
    (fun i : V => skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
    (fun v : DoubledQuiver G => skewZigzagMk k G c (vertexIdempotent k v))
    fun i => by rw [vertexEquiv_apply]).symm

/-- **A diagonal corner is spanned by the idempotent and the volume class of its vertex.** An
arrow has distinct endpoints, so it does not survive a corner, and the idempotents away from the
corner vertex are killed on one side or the other. -/
private theorem corner_mem_span (i : V) (y : skewZigzagQuotient k G c) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) * y
        * skewZigzagMk k G c (vertexIdempotent k (vertex G i))
      ∈ Submodule.span k
        {skewZigzagMk k G c (vertexIdempotent k (vertex G i)), skewZigzagVolume k G c (t i)} := by
  have hy : y ∈ Submodule.span k (Set.range (skewZigzagBasisFun k G c t)) := by
    rw [span_range_skewZigzagBasisFun_eq_top]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rcases b with j | d | j
    · rw [skewZigzagBasisFun_inl]
      rcases eq_or_ne i j with rfl | hij
      · rw [skewZigzagMk_vertexIdempotent_mul_self, skewZigzagMk_vertexIdempotent_mul_self]
        exact Submodule.subset_span (by simp)
      · rw [skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G c hij, zero_mul]
        exact Submodule.zero_mem _
    · rw [skewZigzagBasisFun_inr_inl]
      rcases eq_or_ne i d.snd with rfl | hne
      · rw [skewZigzagMk_vertexIdempotent_mul_ofArrow,
          skewZigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G c d d.adj.ne']
        exact Submodule.zero_mem _
      · rw [skewZigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G c d hne, zero_mul]
        exact Submodule.zero_mem _
    · rw [skewZigzagBasisFun_inr_inr]
      rcases eq_or_ne i j with rfl | hij
      · rw [skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume,
          skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent]
        exact Submodule.subset_span (by simp)
      · rw [skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume_of_ne k G c t hij, zero_mul]
        exact Submodule.zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

/-- **A central element is the sum of its diagonal corners.** An off-diagonal corner
`e_i * z * e_j` of a central element is `z * e_i * e_j`, and distinct vertex idempotents are
orthogonal. -/
private theorem sum_corner_eq_self [Fintype V] {z : skewZigzagQuotient k G c}
    (hz : z ∈ Subalgebra.center k (skewZigzagQuotient k G c)) :
    ∑ i, skewZigzagMk k G c (vertexIdempotent k (vertex G i)) * z
        * skewZigzagMk k G c (vertexIdempotent k (vertex G i)) = z := by
  have hcomm := Subalgebra.mem_center_iff.mp hz
  calc ∑ i, skewZigzagMk k G c (vertexIdempotent k (vertex G i)) * z
          * skewZigzagMk k G c (vertexIdempotent k (vertex G i))
      = ∑ i, ∑ j, skewZigzagMk k G c (vertexIdempotent k (vertex G i)) * z
          * skewZigzagMk k G c (vertexIdempotent k (vertex G j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        symm
        refine Finset.sum_eq_single i ?_ ?_
        · intro j _ hji
          rw [mul_assoc, ← hcomm, ← mul_assoc,
            skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G c (Ne.symm hji), zero_mul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
    _ = (∑ i, skewZigzagMk k G c (vertexIdempotent k (vertex G i))) * z
          * ∑ j, skewZigzagMk k G c (vertexIdempotent k (vertex G j)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = z := by
        rw [← one_eq_sum_skewZigzagMk_vertexIdempotent k G c, one_mul, mul_one]

/-! ### The centre -/

/-- **The centre of a skew-zigzag algebra.** For a finite simple graph with no isolated vertex, an
element is central exactly when it is the sum of a combination of vertex idempotents whose
coefficients are constant along the edges and a combination of volume classes. -/
theorem mem_center_skewZigzagQuotient_iff [Fintype V] (t : ∀ i : V, {j : V // G.Adj i j})
    {z : skewZigzagQuotient k G c} :
    z ∈ Subalgebra.center k (skewZigzagQuotient k G c) ↔
      ∃ f g : V → k, (∀ ⦃i j : V⦄, G.Adj i j → f i = f j) ∧
        z = (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
          + ∑ i, g i • skewZigzagVolume k G c (t i) := by
  constructor
  · intro hz
    have hcorner : ∀ i : V, ∃ a b : k,
        skewZigzagMk k G c (vertexIdempotent k (vertex G i)) * z
            * skewZigzagMk k G c (vertexIdempotent k (vertex G i))
          = a • skewZigzagMk k G c (vertexIdempotent k (vertex G i))
            + b • skewZigzagVolume k G c (t i) :=
      fun i => by
        obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (corner_mem_span k G c t i z)
        exact ⟨a, b, hab.symm⟩
    choose f g hfg using hcorner
    have hzsum : z = (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
        + ∑ i, g i • skewZigzagVolume k G c (t i) := by
      rw [← Finset.sum_add_distrib, ← sum_corner_eq_self k G c hz]
      exact Finset.sum_congr rfl fun i _ => hfg i
    have hvol : (∑ i, g i • skewZigzagVolume k G c (t i))
        ∈ Subalgebra.center k (skewZigzagQuotient k G c) :=
      sum_mem fun i _ => Subalgebra.smul_mem _ (skewZigzagVolume_mem_center k G c t i) _
    have hidem : (∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i)))
        ∈ Subalgebra.center k (skewZigzagQuotient k G c) := by
      have := sub_mem hz hvol
      rwa [hzsum, add_sub_cancel_right] at this
    exact ⟨f, g,
      (sum_smul_skewZigzagMk_vertexIdempotent_mem_center_iff k G c t f).mp hidem, hzsum⟩
  · rintro ⟨f, g, hf, rfl⟩
    exact add_mem (sum_smul_skewZigzagMk_vertexIdempotent_mem_center k G c t f hf)
      (sum_mem fun i _ => Subalgebra.smul_mem _ (skewZigzagVolume_mem_center k G c t i) _)

/-! ### The centre of a connected zigzag algebra -/

omit [Finite V] in
/-- A preconnected graph with at least two vertices has no isolated vertex. -/
private theorem exists_adj_of_preconnected [Nontrivial V] (hconn : G.Preconnected) (i : V) :
    ∃ j, G.Adj i j :=
  SimpleGraph.exists_adj_iff_not_isIsolated.mpr (hconn.not_isIsolated i)

omit [CommRing k] [Finite V] in
/-- A family of scalars constant along the edges is constant along reachability: induct along a
walk. -/
private theorem eq_of_reachable {f : V → k} (hf : ∀ ⦃i j : V⦄, G.Adj i j → f i = f j) {i j : V}
    (h : G.Reachable i j) : f i = f j := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf hadj).trans ih

/-- The family consisting of the unit and one volume class per vertex, indexed by `Option V`. For
a connected graph it is a basis of the centre: the unit takes the place of the sum of the vertex
idempotents, which is, up to a scalar, the only edge-constant combination of them. -/
noncomputable def skewZigzagCenterFun : Option V → skewZigzagQuotient k G c
  | none => 1
  | some i => skewZigzagVolume k G c (t i)

@[simp]
theorem skewZigzagCenterFun_none : skewZigzagCenterFun k G c t none = 1 := (rfl)

@[simp]
theorem skewZigzagCenterFun_some (i : V) :
    skewZigzagCenterFun k G c t (some i) = skewZigzagVolume k G c (t i) := (rfl)

/-- The unit and the volume classes are central. -/
@[simp]
theorem skewZigzagCenterFun_mem_center (o : Option V) :
    skewZigzagCenterFun k G c t o ∈ Subalgebra.center k (skewZigzagQuotient k G c) := by
  cases o with
  | none => rw [skewZigzagCenterFun_none]; exact one_mem _
  | some i => rw [skewZigzagCenterFun_some]; exact skewZigzagVolume_mem_center k G c t i

/-- **The unit and the volume classes span the centre of a connected skew-zigzag algebra.** The
coefficients of a central combination of vertex idempotents are constant along the edges, hence
constant, so that combination is a multiple of `1 = ∑ i, e_i`. -/
theorem span_range_skewZigzagCenterFun_eq_center [Nontrivial V] (hconn : G.Preconnected) :
    Submodule.span k (Set.range (skewZigzagCenterFun k G c t))
      = Subalgebra.toSubmodule (Subalgebra.center k (skewZigzagQuotient k G c)) := by
  have : Fintype V := Fintype.ofFinite V
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨o, rfl⟩
    exact skewZigzagCenterFun_mem_center k G c t o
  · intro z hz
    obtain ⟨f, g, hf, rfl⟩ := (mem_center_skewZigzagQuotient_iff k G c t).mp hz
    obtain ⟨i₀⟩ := (inferInstance : Nonempty V)
    have hidem : ∑ i, f i • skewZigzagMk k G c (vertexIdempotent k (vertex G i))
        = f i₀ • (1 : skewZigzagQuotient k G c) := by
      rw [one_eq_sum_skewZigzagMk_vertexIdempotent k G c, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [eq_of_reachable k G hf (hconn i i₀)]
    rw [hidem]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨some i, rfl⟩))

/-- **The unit and the volume classes are independent.** Their coordinates against
`TauCeti.skewZigzagBasis` at one fixed vertex and at the volume classes are the standard basis of
`Option V → k`. -/
theorem linearIndependent_skewZigzagCenterFun [Nonempty V] (t : ∀ i : V, {j : V // G.Adj i j}) :
    LinearIndependent k (skewZigzagCenterFun k G c t) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨i₀⟩ := (inferInstance : Nonempty V)
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (ZigzagBasisIndex G) k (skewZigzagQuotient k G c),
      ∀ b, B b = skewZigzagBasisFun k G c t b :=
    ⟨skewZigzagBasis k G c t, skewZigzagBasis_apply k G c t⟩
  have hone : (1 : skewZigzagQuotient k G c) = ∑ i, B (Sum.inl i) := by
    rw [one_eq_sum_skewZigzagMk_vertexIdempotent k G c]
    exact Finset.sum_congr rfl fun i _ => by rw [hB, skewZigzagBasisFun_inl]
  have h1l : B.repr 1 (Sum.inl i₀) = 1 := by
    rw [hone, map_sum, Finset.sum_apply', Finset.sum_eq_single i₀]
    · rw [Module.Basis.repr_self, Finsupp.single_eq_same]
    · intro i _ hi
      rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne (by simpa using hi.symm)]
    · intro hi
      exact absurd (Finset.mem_univ i₀) hi
  have h1r : ∀ j : V, B.repr 1 (Sum.inr (Sum.inr j)) = 0 := fun j => by
    rw [hone, map_sum, Finset.sum_apply']
    exact Finset.sum_eq_zero fun i _ => by
      rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne (by simp)]
  have hvol_eq (i : V) : skewZigzagVolume k G c (t i) = B (Sum.inr (Sum.inr i)) := by
    rw [hB, skewZigzagBasisFun_inr_inr]
  have hvol : ∀ (i : V) (b : ZigzagBasisIndex G), B.repr (skewZigzagVolume k G c (t i)) b
      = if (Sum.inr (Sum.inr i) : ZigzagBasisIndex G) = b then (1 : k) else 0 := fun i b => by
    rw [hvol_eq, Module.Basis.repr_self, Finsupp.single_apply]
  refine LinearIndependent.of_comp (LinearMap.pi fun o : Option V =>
    B.coord (Option.elim o (Sum.inl i₀) fun i => Sum.inr (Sum.inr i))) ?_
  have hfun : ⇑(LinearMap.pi fun o : Option V =>
      B.coord (Option.elim o (Sum.inl i₀) fun i => Sum.inr (Sum.inr i)))
        ∘ skewZigzagCenterFun k G c t
      = ⇑(Pi.basisFun k (Option V)) := by
    funext o o'
    rw [Pi.basisFun_apply, Pi.single_apply]
    rcases o with _ | i <;> rcases o' with _ | j <;>
      simp only [Function.comp_apply, LinearMap.pi_apply, Module.Basis.coord_apply,
        skewZigzagCenterFun_none, skewZigzagCenterFun_some, Option.elim]
    · rw [h1l]
      simp
    · rw [h1r]
      simp
    · rw [hvol]
      simp
    · rw [hvol]
      simp [eq_comm (a := i) (b := j)]
  rw [hfun]
  exact Module.Basis.linearIndependent _

/-- **The basis of the centre of a connected skew-zigzag algebra.** For a preconnected finite simple
graph with at least two vertices the unit and the volume classes are a basis of the centre of the
zigzag relation quotient. -/
noncomputable def skewZigzagCenterBasis [Nontrivial V] (hconn : G.Preconnected) :
    Module.Basis (Option V) k (Subalgebra.center k (skewZigzagQuotient k G c)) :=
  (Module.Basis.span (linearIndependent_skewZigzagCenterFun k G c t)).map
      ((LinearEquiv.ofEq _ _ (span_range_skewZigzagCenterFun_eq_center k G c t hconn)).trans
        (Subalgebra.toSubmoduleEquiv _))

@[simp]
theorem skewZigzagCenterBasis_apply [Nontrivial V] (hconn : G.Preconnected) (o : Option V) :
    (skewZigzagCenterBasis k G c t hconn o : skewZigzagQuotient k G c)
      = skewZigzagCenterFun k G c t o := by
  rw [skewZigzagCenterBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/-- **The dimension of the centre of a skew-zigzag algebra.** A preconnected finite simple graph
with at least two vertices has centre of dimension `|V| + 1`: the unit, together with one volume
class at each vertex. -/
theorem finrank_center_skewZigzagQuotient [Nontrivial k] [Fintype V] [Nontrivial V]
    (hconn : G.Preconnected) :
    Module.finrank k (Subalgebra.center k (skewZigzagQuotient k G c))
      = Fintype.card V + 1 := by
  let t : ∀ i : V, {j : V // G.Adj i j} := fun i =>
    ⟨(exists_adj_of_preconnected G hconn i).choose,
      (exists_adj_of_preconnected G hconn i).choose_spec⟩
  rw [Module.finrank_eq_card_basis (skewZigzagCenterBasis k G c t hconn),
    Fintype.card_option]

end TauCeti
