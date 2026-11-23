/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Extending edge data by zero along a copy

Let `f` be a copy of a graph `H` in a graph `G`, that is an injective graph homomorphism, not
necessarily induced. A family `β x y` of values on the ordered pairs of vertices of `H` extends by
zero to `G`: the extended family takes the value `β x y` on `(f x, f y)` for every edge `x ∼ y` of
`H`, and zero on every other pair, including the pairs of `G`-adjacent vertices of the copy which
are not edges of `H`.

When the values form an additive commutative monoid and carry a multiplication with
`0 * 0 = 0` for its zero (as in any semiring), the local sums
`∑_{w ∼ v} β w v * β v w` over the neighbours of a vertex are preserved: at a vertex `f x` of the
copy with finitely many neighbours in `G` and `x` with finitely many neighbours in `H`, the
extended sum is the sum of `H` at `x`. So when `H`
is locally finite and the local sums of `β` vanish at every vertex, so do those of the extension
at every vertex of `G` with finitely many neighbours, also away from the copy. These are the
local relations of the signless preprojective algebra, so for finite graphs a block-matrix
representation of the signless preprojective algebra of `H` given by such a family extends by zero
to one of `G` (`TauCeti.signlessMatrixRepresentation`).

## Main definitions

* `SimpleGraph.Copy.extendByZero`: the extension by zero of a family on the vertex pairs of `H`
  along a copy of `H` in `G`.

## Main results

* `SimpleGraph.Copy.extendByZero_apply_apply`: along the copy, the extension is the original
  family on edges of `H` and zero elsewhere.
* `SimpleGraph.Copy.extendByZero_ne_zero_iff`: the extension is nonzero at an ordered pair of
  vertices of `G` exactly when it is `(f x, f y)` for an edge `x ∼ y` of `H` with `β x y ≠ 0`.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero_apply`: at a vertex `f x` of the copy with
  finitely many neighbours in `G`, where `x` has finitely many neighbours in `H`, the local sum
  `∑_{w ∼ f x} β w (f x) * β (f x) w` of the extension is the local sum of `β` at `x`.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero`: for locally finite `H`, the local sums
  of the extension vanish at every vertex of `G` with finitely many neighbours when those of the
  original family vanish at every vertex of `H`.
-/

public section

namespace SimpleGraph.Copy

variable {V W M : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

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
  rw [extendByZero, ← Prod.map_apply, hf.extend_apply, Set.indicator_apply]
  rfl

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
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hxy, hβ⟩, h⟩
    simp only [Prod.map_apply, Prod.mk.injEq] at h
    exact ⟨x, y, h.1, h.2, hxy, hβ⟩
  · rintro ⟨x, y, rfl, rfl, hxy, hβ⟩
    exact ⟨(x, y), ⟨hxy, hβ⟩, rfl⟩

end Zero

section Mul

variable [AddCommMonoid M] [Mul M] (f : H.Copy G) (β : W → W → M)

/-- At a vertex `f x` of the copy with finitely many neighbours in `G`, where `x` has finitely many
neighbours in `H`, the local sum `∑_{w ∼ f x} β w (f x) * β (f x) w` of the extension by zero over
the neighbours in `G` is the local sum `∑_{y ∼ x} β y x * β x y` of `β` over the neighbours in
`H`. Off the image of the neighbours of `x` both factors vanish, so of the multiplication only
`0 * 0 = 0` for the additive zero is used: it need neither distribute over the addition nor have
zero as an absorbing element (`a * 0 = 0` may fail, as for `a * b = a`). -/
theorem sum_extendByZero_mul_extendByZero_apply (hmul : (0 : M) * 0 = 0) (x : W)
    [Fintype (G.neighborSet (f x))] [Fintype (H.neighborSet x)] :
    ∑ w ∈ G.neighborFinset (f x), f.extendByZero β w (f x) * f.extendByZero β (f x) w =
      ∑ y ∈ H.neighborFinset x, β y x * β x y := by
  -- Only the images of the neighbours of `x` in `H` contribute, and they contribute the sum of
  -- `H` at `x`.
  have hsub : (H.neighborFinset x).map f.toEmbedding ⊆ G.neighborFinset (f x) := by
    rw [← Finset.coe_subset, Finset.coe_map, coe_neighborFinset, coe_neighborFinset]
    exact f.toHom.image_neighborSet_subset x
  rw [← Finset.sum_subset hsub, Finset.sum_map]
  · refine Finset.sum_congr rfl fun y hy => ?_
    rw [mem_neighborFinset] at hy
    exact congrArg₂ (· * ·) (extendByZero_apply_apply_of_adj f β hy.symm)
      (extendByZero_apply_apply_of_adj f β hy)
  · -- Off the image of the neighbours of `x`, both factors vanish.
    intro w _ hw
    have hl : f.extendByZero β w (f x) = 0 := by
      by_contra h
      obtain ⟨a, b, rfl, hb, hab, -⟩ := (extendByZero_ne_zero_iff f β).1 h
      rw [f.injective hb] at hab
      exact hw (Finset.mem_map_of_mem _ ((mem_neighborFinset _ _ _).2 hab.symm))
    have hr : f.extendByZero β (f x) w = 0 := by
      by_contra h
      obtain ⟨a, b, ha, rfl, hab, -⟩ := (extendByZero_ne_zero_iff f β).1 h
      rw [f.injective ha] at hab
      exact hw (Finset.mem_map_of_mem _ ((mem_neighborFinset _ _ _).2 hab))
    rw [hl, hr, hmul]

/-- **Local relations extend by zero along a copy**: if the sums `∑_{y ∼ x} β y x * β x y` over
the neighbours in `H` vanish at every vertex of `H`, then so do the corresponding sums of the
extension by zero at every vertex of `G` with finitely many neighbours. As for
`sum_extendByZero_mul_extendByZero_apply`, of the multiplication only `0 * 0 = 0` is used. -/
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
