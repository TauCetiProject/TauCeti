/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Neighbours along a copy, and extending edge data by zero

Let `f` be a copy of a graph `H` in a graph `G`, that is an injective graph homomorphism, not
necessarily induced. A family `β x y` of values on the ordered pairs of vertices of `H` extends by
zero to `G`: the extended family takes the value `β x y` on `(f x, f y)` for every edge `x ∼ y` of
`H`, and zero on every other pair, including the pairs of `G`-adjacent vertices of the copy which
are not edges of `H`.

When the values form an additive commutative monoid and carry a multiplication with
`0 * 0 = 0` for its zero (as in any semiring), the local sums over the neighbours of a vertex are
preserved for `β' = f.extendByZero β`: at a vertex `f x` of the copy with finitely many neighbours
in `G` and `x` with finitely many neighbours in `H`, the extended sum
`∑_{w ∼ f x} β' w (f x) * β' (f x) w` equals `∑_{y ∼ x} β y x * β x y`. So when `H`
is locally finite and the local sums of `β` vanish at every vertex, so do those of the extension
at every vertex of `G` with finitely many neighbours, also away from the copy. These are the
local relations of the signless preprojective algebra: for finite graphs, extending by zero the
edge-block family of a block-matrix representation of the signless preprojective algebra of `H`
gives a block-matrix representation of that of `G` (`TauCeti.signlessMatrixRepresentation`).

Along a copy, the neighbours of a vertex map to neighbours of its image, so a weight on `G` that is
nonnegative at the extra neighbours sums to at least as much over the neighbours of `f x` as over
the images of those of `x`.

## Main definitions

* `SimpleGraph.Copy.extendByZero`: the extension by zero of a family on the vertex pairs of `H`
  along a copy of `H` in `G`.

## Main results

* `SimpleGraph.Copy.map_neighborFinset_subset` and `SimpleGraph.Copy.sum_neighborFinset_comp_le`:
  neighbours map to neighbours along a copy, and the resulting bound on neighbour sums of a
  weight that is nonnegative at the extra neighbours.
* `SimpleGraph.Copy.extendByZero_apply_apply`: along the copy, the extension is the original
  family on edges of `H` and zero elsewhere.
* `SimpleGraph.Copy.extendByZero_ne_zero_iff`: the extension is nonzero at an ordered pair of
  vertices of `G` exactly when it is `(f x, f y)` for an edge `x ∼ y` of `H` with `β x y ≠ 0`.
* `SimpleGraph.Copy.extendByZero_eq_iff`: a family on the vertex pairs of `G` is the extension
  exactly when it agrees with `β` on the images of the edges of `H` and vanishes on every other
  pair.
* `SimpleGraph.Copy.extendByZero_mul_extendByZero`: the product of the extension in the two orders
  of a pair is the extension of the product of `β` in the two orders, when `0 * 0 = 0`.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero_apply`: at a vertex `f x` of the copy with
  finitely many neighbours in `G`, where `x` has finitely many neighbours in `H`, the local sum
  `∑_{w ∼ f x} f.extendByZero β w (f x) * f.extendByZero β (f x) w` equals
  `∑_{y ∼ x} β y x * β x y`.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero`: for locally finite `H`, the local sums
  of the extension vanish at every vertex of `G` with finitely many neighbours when those of the
  original family vanish at every vertex of `H`.
-/

public section

namespace SimpleGraph.Copy

variable {V W M : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

section neighborFinset

/-- Along a copy `f`, not necessarily induced, the neighbours of `x` map to neighbours of `f x`. -/
theorem map_neighborFinset_subset (f : H.Copy G) (x : W) [Fintype (G.neighborSet (f x))]
    [Fintype (H.neighborSet x)] :
    (H.neighborFinset x).map f.toEmbedding ⊆ G.neighborFinset (f x) := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hw
  rw [mem_neighborFinset] at hy ⊢
  exact f.toHom.map_adj hy

/-- Along a copy `f`, not necessarily induced, a weight on `G` that is nonnegative at the neighbours
of `f x` outside the image of those of `x` sums to at least as much over the neighbours of `f x` as
over the images of the neighbours of `x`. -/
theorem sum_neighborFinset_comp_le [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (f : H.Copy G) {a : V → M} {x : W} [Fintype (G.neighborSet (f x))]
    [Fintype (H.neighborSet x)]
    (ha0 : ∀ w ∈ G.neighborFinset (f x), w ∉ (H.neighborFinset x).map f.toEmbedding → 0 ≤ a w) :
    ∑ y ∈ H.neighborFinset x, a (f y) ≤ ∑ w ∈ G.neighborFinset (f x), a w := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f.map_neighborFinset_subset x) ha0
  rwa [Finset.sum_map] at h

end neighborFinset

section Zero

variable [Zero M]

/-- The **extension by zero** of a family `β` on the vertex pairs of `H` along a copy `f` of `H` in
`G`: the pair `(f x, f y)` of an edge `x ∼ y` of `H` carries `β x y`, and every other pair carries
zero.

This specializes Mathlib's `Function.extend` along `Prod.map f f`, with zero as the fallback, to
the indicator (`Set.indicator`) of the edges of `H` applied to the family. -/
noncomputable def extendByZero (f : H.Copy G) (β : W → W → M) (v w : V) : M :=
  Function.extend (Prod.map f f) ({p : W × W | H.Adj p.1 p.2}.indicator fun p => β p.1 p.2) 0
    (v, w)

variable (f : H.Copy G) (β : W → W → M)

/-- Along the copy, the extension is the original family on edges of `H`, and zero elsewhere. -/
theorem extendByZero_apply_apply [DecidableRel H.Adj] (x y : W) :
    f.extendByZero β (f x) (f y) = if H.Adj x y then β x y else 0 := by
  have hf : Function.Injective (Prod.map f f) := f.injective.prodMap f.injective
  rw [extendByZero, ← Prod.map_apply, hf.extend_apply]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- Along an edge of `H`, the extension is the original family. -/
@[simp]
theorem extendByZero_apply_apply_of_adj {x y : W} (h : H.Adj x y) :
    f.extendByZero β (f x) (f y) = β x y := by
  classical
  simp [extendByZero_apply_apply, h]

/-- Along a pair of vertices of the copy which is not an edge of `H`, the extension vanishes. -/
@[simp]
theorem extendByZero_apply_apply_of_not_adj {x y : W} (h : ¬H.Adj x y) :
    f.extendByZero β (f x) (f y) = 0 := by
  classical
  simp [extendByZero_apply_apply, h]

/-- Away from the image of the copy, the extension vanishes. -/
@[simp]
theorem extendByZero_eq_zero_of_notMem_range_left {v : V} (hv : v ∉ Set.range f) (w : V) :
    f.extendByZero β v w = 0 := by
  have h : (v, w) ∉ Set.range (Prod.map f f) := by
    rw [Set.range_prodMap, Set.mem_prod]
    exact fun h => hv h.1
  rw [extendByZero, Function.extend_apply' _ _ _ h, Pi.zero_apply]

/-- Away from the image of the copy, the extension vanishes. -/
@[simp]
theorem extendByZero_eq_zero_of_notMem_range_right (v : V) {w : V} (hw : w ∉ Set.range f) :
    f.extendByZero β v w = 0 := by
  have h : (v, w) ∉ Set.range (Prod.map f f) := by
    rw [Set.range_prodMap, Set.mem_prod]
    exact fun h => hw h.2
  rw [extendByZero, Function.extend_apply' _ _ _ h, Pi.zero_apply]

/-- The extension is nonzero at an ordered pair `(v, w)` of vertices of `G` exactly when
`(v, w) = (f x, f y)` for an edge `x ∼ y` of `H` with `β x y ≠ 0`. Only this order of the edge is
asserted: the value `β y x` at `(f y, f x)` may vanish. -/
theorem extendByZero_ne_zero_iff {v w : V} :
    f.extendByZero β v w ≠ 0 ↔ ∃ x y, f x = v ∧ f y = w ∧ H.Adj x y ∧ β x y ≠ 0 := by
  have hf : Function.Injective (Prod.map f f) := f.injective.prodMap f.injective
  rw [extendByZero, ← Function.mem_support, Function.support_extend_zero hf,
    Set.support_indicator]
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support,
    Prod.exists, Prod.map_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, ⟨hxy, hβ⟩, hx, hy⟩
    exact ⟨x, y, hx, hy, hxy, hβ⟩
  · rintro ⟨x, y, hx, hy, hxy, hβ⟩
    exact ⟨x, y, ⟨hxy, hβ⟩, hx, hy⟩

/-- The extension vanishes at every ordered pair `(v, w)` of vertices of `G` which is not the image
`(f x, f y)` of an edge `x ∼ y` of `H`. -/
theorem extendByZero_eq_zero_of_forall_not_adj {v w : V}
    (h : ∀ x y, f x = v → f y = w → ¬H.Adj x y) : f.extendByZero β v w = 0 := by
  by_contra hne
  obtain ⟨x, y, hx, hy, hxy, -⟩ := (extendByZero_ne_zero_iff f β).1 hne
  exact h x y hx hy hxy

/-- **Uniqueness of the extension by zero**: a family `γ` on the vertex pairs of `G` is the
extension of `β` exactly when it agrees with `β` on the images `(f x, f y)` of the edges `x ∼ y` of
`H` and vanishes on every other ordered pair. -/
theorem extendByZero_eq_iff {γ : V → V → M} :
    f.extendByZero β = γ ↔ (∀ x y, H.Adj x y → γ (f x) (f y) = β x y) ∧
      ∀ v w, (∀ x y, f x = v → f y = w → ¬H.Adj x y) → γ v w = 0 := by
  constructor
  · rintro rfl
    exact ⟨fun x y => extendByZero_apply_apply_of_adj f β,
      fun v w => extendByZero_eq_zero_of_forall_not_adj f β⟩
  · rintro ⟨hadj, hzero⟩
    funext v w
    by_cases h : ∀ x y, f x = v → f y = w → ¬H.Adj x y
    · rw [extendByZero_eq_zero_of_forall_not_adj f β h, hzero v w h]
    · push Not at h
      obtain ⟨x, y, rfl, rfl, hxy⟩ := h
      rw [extendByZero_apply_apply_of_adj f β hxy, hadj x y hxy]

/-- Extending the zero family by zero yields the zero family. -/
@[simp]
theorem extendByZero_zero : f.extendByZero (0 : W → W → M) = 0 :=
  (extendByZero_eq_iff f 0).2
    ⟨fun _ _ _ => by simp only [Pi.zero_apply], fun _ _ _ => by simp only [Pi.zero_apply]⟩

/-- The product of the extension in the two orders of an ordered pair `(v, w)` is the extension of
the product `β y x * β x y` of `β` in the two orders of an edge `x ∼ y`. Of the multiplication only
`0 * 0 = 0` is used: off the images of the edges of `H` both factors vanish. -/
theorem extendByZero_mul_extendByZero [Mul M] (hmul : (0 : M) * 0 = 0) (v w : V) :
    f.extendByZero β w v * f.extendByZero β v w =
      f.extendByZero (fun x y => β y x * β x y) v w := by
  have h : f.extendByZero (fun x y => β y x * β x y) =
      fun v w => f.extendByZero β w v * f.extendByZero β v w := by
    rw [extendByZero_eq_iff]
    refine ⟨fun x y hxy => ?_, fun v w h => ?_⟩
    · rw [extendByZero_apply_apply_of_adj f β hxy.symm, extendByZero_apply_apply_of_adj f β hxy]
    · rw [extendByZero_eq_zero_of_forall_not_adj f β fun y x hy hx hyx => h x y hx hy hyx.symm,
        extendByZero_eq_zero_of_forall_not_adj f β h, hmul]
  exact (congrFun (congrFun h v) w).symm

end Zero

/-- Extending a pointwise sum of families by zero is the pointwise sum of their extensions. -/
@[simp]
theorem extendByZero_add [AddZeroClass M] (f : H.Copy G) (β γ : W → W → M) :
    f.extendByZero (β + γ) = f.extendByZero β + f.extendByZero γ := by
  rw [extendByZero_eq_iff]
  refine ⟨fun x y hxy => ?_, fun v w h => ?_⟩
  · simp only [Pi.add_apply, extendByZero_apply_apply_of_adj f _ hxy]
  · simp only [Pi.add_apply, extendByZero_eq_zero_of_forall_not_adj f _ h, add_zero]

section Mul

variable [AddCommMonoid M] [Mul M] (f : H.Copy G) (β : W → W → M)

/-- At a vertex `f x` of the copy with finitely many neighbours in `G`, where `x` has finitely many
neighbours in `H`, the local sum `∑_{w ∼ f x} f.extendByZero β w (f x) * f.extendByZero β (f x) w`
over the neighbours in `G` is the local sum `∑_{y ∼ x} β y x * β x y` of `β` over the neighbours
in `H`. Off the image of the neighbours of `x` both factors vanish, so of the multiplication only
`0 * 0 = 0` for the additive zero is used: it need neither distribute over the addition nor have
zero as an absorbing element (`a * 0 = 0` may fail, as for `a * b = a`). -/
theorem sum_extendByZero_mul_extendByZero_apply (hmul : (0 : M) * 0 = 0) (x : W)
    [Fintype (G.neighborSet (f x))] [Fintype (H.neighborSet x)] :
    ∑ w ∈ G.neighborFinset (f x), f.extendByZero β w (f x) * f.extendByZero β (f x) w =
      ∑ y ∈ H.neighborFinset x, β y x * β x y := by
  have hemb : ⇑f.toEmbedding = f := rfl
  -- Only the images of the neighbours of `x` in `H` contribute, and they contribute the sum of
  -- `H` at `x`.
  rw [Finset.sum_congr rfl fun w _ => extendByZero_mul_extendByZero f β hmul (f x) w,
    ← Finset.sum_subset (f.map_neighborFinset_subset x), Finset.sum_map]
  · refine Finset.sum_congr rfl fun y hy => ?_
    rw [hemb]
    exact extendByZero_apply_apply_of_adj f _ ((mem_neighborFinset _ _ _).1 hy)
  · -- Off the image of the neighbours of `x`, the extended product vanishes.
    intro w _ hw
    refine extendByZero_eq_zero_of_forall_not_adj f _ fun a b ha hb hab => hw ?_
    rw [f.injective ha] at hab
    rw [← hb, ← hemb]
    exact Finset.mem_map_of_mem _ ((mem_neighborFinset _ _ _).2 hab)

/-- **Local relations extend by zero along a copy**: for locally finite `H`, if the sums
`∑_{y ∼ x} β y x * β x y` over the neighbours in `H` vanish at every vertex of `H`, then so do the
corresponding sums of the extension by zero at every vertex of `G` with finitely many
neighbours. As for `sum_extendByZero_mul_extendByZero_apply`, of the multiplication only
`0 * 0 = 0` is used. -/
theorem sum_extendByZero_mul_extendByZero [H.LocallyFinite] (hmul : (0 : M) * 0 = 0)
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0) (v : V)
    [Fintype (G.neighborSet v)] :
    ∑ w ∈ G.neighborFinset v, f.extendByZero β w v * f.extendByZero β v w = 0 := by
  by_cases hv : v ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hv
    exact (sum_extendByZero_mul_extendByZero_apply f β hmul x).trans (hβ x)
  · exact Finset.sum_eq_zero fun w _ => by
      rw [extendByZero_eq_zero_of_notMem_range_right f β w hv,
        extendByZero_eq_zero_of_notMem_range_left f β hv, hmul]

end Mul

end SimpleGraph.Copy
