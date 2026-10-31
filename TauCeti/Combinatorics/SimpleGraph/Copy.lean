/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Extending edge data by zero along a copy

Let `f` be a copy of a graph `H` in a graph `G`, that is an injective graph homomorphism, not
necessarily induced. A family `β x y` of values on the ordered pairs of vertices of `H` extends by
zero to `G`: the extended family takes the value `β x y` on `(f x, f y)` for every edge `x ∼ y` of
`H`, and zero on every other pair, including the pairs of `G`-adjacent vertices of the copy which
are not edges of `H`.

When the values lie in a semiring, the local sums `∑_{w ∼ v} β w v * β v w` over the neighbours of
a vertex are preserved: at a vertex `f x` of the copy the extended sum is the sum of `H` at `x`,
and away from the copy it is zero. These are the local relations of the signless preprojective
algebra, so a representation of the signless preprojective algebra of `H` by such a family extends
by zero to one of `G`.

## Main definitions

* `SimpleGraph.Copy.extendByZero`: the extension by zero of a family on the vertex pairs of `H`
  along a copy of `H` in `G`.

## Main results

* `SimpleGraph.Copy.extendByZero_apply_apply`: along the copy, the extension is the original
  family on edges of `H` and zero elsewhere.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero`: the local sums
  `∑_{w ∼ v} β w v * β v w` vanish for the extension when they vanish for the original family.
-/

public section

namespace SimpleGraph.Copy

variable {V W M : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

section AddCommMonoid

variable [AddCommMonoid M] [Fintype W] [DecidableEq V] [DecidableRel H.Adj]

/-- The **extension by zero** of a family `β` on the vertex pairs of `H` along a copy `f` of `H` in
`G`: the pair `(f x, f y)` of an edge `x ∼ y` of `H` carries `β x y`, and every other pair carries
zero. -/
def extendByZero (f : H.Copy G) (β : W → W → M) : V → V → M :=
  fun v w => ∑ x, ∑ y, if f x = v ∧ f y = w ∧ H.Adj x y then β x y else 0

variable (f : H.Copy G) (β : W → W → M)

/-- Along the copy, the extension is the original family on edges of `H`, and zero elsewhere. -/
theorem extendByZero_apply_apply (x y : W) :
    f.extendByZero β (f x) (f y) = if H.Adj x y then β x y else 0 := by
  classical
  have hf : Function.Injective f := f.injective
  simp only [extendByZero, hf.eq_iff]
  rw [Finset.sum_eq_single x (fun _ _ hx => Finset.sum_eq_zero fun _ _ => by simp [hx])
      (by simp),
    Finset.sum_eq_single y (fun _ _ hy => by simp [hy]) (by simp)]
  simp

/-- Along an edge of `H`, the extension is the original family. -/
@[simp]
theorem extendByZero_apply_apply_of_adj {x y : W} (h : H.Adj x y) :
    f.extendByZero β (f x) (f y) = β x y := by
  simp [extendByZero_apply_apply, h]

/-- Along a pair of vertices of the copy which is not an edge of `H`, the extension vanishes. -/
theorem extendByZero_apply_apply_of_not_adj {x y : W} (h : ¬H.Adj x y) :
    f.extendByZero β (f x) (f y) = 0 := by
  simp [extendByZero_apply_apply, h]

/-- Away from the image of the copy, the extension vanishes. -/
theorem extendByZero_eq_zero_of_notMem_range_left {v : V} (hv : v ∉ Set.range f) (w : V) :
    f.extendByZero β v w = 0 :=
  Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun _ _ =>
    ite_eq_right_iff.2 fun h => absurd ⟨x, h.1⟩ hv

/-- Away from the image of the copy, the extension vanishes. -/
theorem extendByZero_eq_zero_of_notMem_range_right (v : V) {w : V} (hw : w ∉ Set.range f) :
    f.extendByZero β v w = 0 :=
  Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun y _ =>
    ite_eq_right_iff.2 fun h => absurd ⟨y, h.2.1⟩ hw

end AddCommMonoid

section Semiring

variable [NonUnitalNonAssocSemiring M] [Fintype W] [DecidableEq V] [DecidableRel H.Adj]
  (f : H.Copy G) (β : W → W → M)

/-- **Local relations extend by zero along a copy**: if the sums `∑_{y ∼ x} β y x * β x y` over
the neighbours in `H` vanish at every vertex of `H`, then so do the corresponding sums of the
extension by zero at every vertex of `G`. -/
theorem sum_extendByZero_mul_extendByZero [Fintype V] [DecidableRel G.Adj]
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0) (v : V) :
    ∑ w ∈ G.neighborFinset v, f.extendByZero β w v * f.extendByZero β v w = 0 := by
  by_cases hv : v ∈ Set.range f
  swap
  · exact Finset.sum_eq_zero fun w _ => by
      rw [extendByZero_eq_zero_of_notMem_range_left f β hv, mul_zero]
  obtain ⟨x, rfl⟩ := hv
  -- Only the images of the neighbours of `x` in `H` contribute, and they contribute the sum of
  -- `H` at `x`.
  have hsub : (H.neighborFinset x).map f.toEmbedding ⊆ G.neighborFinset (f x) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hw
    rw [mem_neighborFinset] at hy ⊢
    exact f.toHom.map_adj hy
  rw [← Finset.sum_subset hsub, Finset.sum_map]
  · refine (Finset.sum_congr rfl fun y hy => ?_).trans (hβ x)
    rw [mem_neighborFinset] at hy
    exact congrArg₂ (· * ·) (extendByZero_apply_apply_of_adj f β hy.symm)
      (extendByZero_apply_apply_of_adj f β hy)
  · intro w _ hw
    by_cases hwr : w ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hwr
      have hxy : ¬H.Adj x y := fun hxy =>
        hw (Finset.mem_map_of_mem _ ((mem_neighborFinset _ _ _).2 hxy))
      rw [extendByZero_apply_apply_of_not_adj f β hxy, mul_zero]
    · rw [extendByZero_eq_zero_of_notMem_range_right f β _ hwr, mul_zero]

end Semiring

end SimpleGraph.Copy
