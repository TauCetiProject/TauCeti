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

When the values carry an addition and a multiplication for which zero is right-absorbing
(`a * 0 = 0`, as in any semiring), the local sums `∑_{w ∼ v} β w v * β v w` over the neighbours
of a vertex are preserved: at a vertex `f x` of the copy with finitely many neighbours in `G` and
`x` with finitely many neighbours in `H`, the extended sum is the sum of `H` at `x`. So when `H`
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
* `SimpleGraph.Copy.extendByZero_ne_zero_iff`: the extension is nonzero exactly on the images of
  the edges of `H` on which the family is nonzero.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero_apply`: at a vertex of the copy, the local
  sum `∑_{w ∼ v} β w v * β v w` of the extension is the local sum of the original family.
* `SimpleGraph.Copy.sum_extendByZero_mul_extendByZero`: for locally finite `H`, the local sums
  of the extension vanish at every vertex of `G` with finitely many neighbours when those of the
  original family vanish at every vertex of `H`.
-/

public section

namespace SimpleGraph.Copy

variable {V W M : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

section Zero

variable [Zero M]

open Classical in
/-- The **extension by zero** of a family `β` on the vertex pairs of `H` along a copy `f` of `H` in
`G`: the pair `(f x, f y)` of an edge `x ∼ y` of `H` carries `β x y`, and every other pair carries
zero.

This specializes Mathlib's `Function.extend` along `Prod.map f f`, with zero as the fallback, to
the family that is first set to zero on the pairs which are not edges of `H`. -/
noncomputable def extendByZero (f : H.Copy G) (β : W → W → M) (v w : V) : M :=
  Function.extend (Prod.map f f) (fun p => if H.Adj p.1 p.2 then β p.1 p.2 else 0) 0 (v, w)

variable (f : H.Copy G) (β : W → W → M)

/-- Along the copy, the extension is the original family on edges of `H`, and zero elsewhere. -/
theorem extendByZero_apply_apply [DecidableRel H.Adj] (x y : W) :
    f.extendByZero β (f x) (f y) = if H.Adj x y then β x y else 0 := by
  have hf : Function.Injective (Prod.map f f) := f.injective.prodMap f.injective
  rw [extendByZero, ← Prod.map_apply, hf.extend_apply]
  congr

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
  rw [extendByZero, Function.extend_apply' _ _ _ fun ⟨p, hp⟩ =>
    hv ⟨p.1, by simpa only [Prod.map_fst] using congrArg Prod.fst hp⟩, Pi.zero_apply]

/-- Away from the image of the copy, the extension vanishes. -/
@[simp]
theorem extendByZero_eq_zero_of_notMem_range_right (v : V) {w : V} (hw : w ∉ Set.range f) :
    f.extendByZero β v w = 0 := by
  rw [extendByZero, Function.extend_apply' _ _ _ fun ⟨p, hp⟩ =>
    hw ⟨p.2, by simpa only [Prod.map_snd] using congrArg Prod.snd hp⟩, Pi.zero_apply]

/-- The extension is nonzero exactly on the images of the edges of `H` on which the family is
nonzero. -/
theorem extendByZero_ne_zero_iff {v w : V} :
    f.extendByZero β v w ≠ 0 ↔ ∃ x y, f x = v ∧ f y = w ∧ H.Adj x y ∧ β x y ≠ 0 := by
  refine ⟨fun h => ?_, fun ⟨x, y, hx, hy, hxy, hβ⟩ => ?_⟩
  · obtain ⟨x, rfl⟩ : v ∈ Set.range f := by_contra fun hv =>
      h (extendByZero_eq_zero_of_notMem_range_left f β hv w)
    obtain ⟨y, rfl⟩ : w ∈ Set.range f := by_contra fun hw =>
      h (extendByZero_eq_zero_of_notMem_range_right f β _ hw)
    have hxy : H.Adj x y := by_contra fun hxy =>
      h (extendByZero_apply_apply_of_not_adj f β hxy)
    exact ⟨x, y, rfl, rfl, hxy, by rwa [extendByZero_apply_apply_of_adj f β hxy] at h⟩
  · rwa [← hx, ← hy, extendByZero_apply_apply_of_adj f β hxy]

end Zero

section Mul

variable [AddCommMonoid M] [Mul M] (f : H.Copy G) (β : W → W → M)

/-- At a vertex `f x` of the copy, the local sum `∑_{w ∼ f x} β w (f x) * β (f x) w` of the
extension by zero over the neighbours in `G` is the local sum `∑_{y ∼ x} β y x * β x y` of `β`
over the neighbours in `H`. Only right absorption `a * 0 = 0` by the additive zero is used, so
the multiplication need not distribute over the addition. -/
theorem sum_extendByZero_mul_extendByZero_apply (hmul : ∀ a : M, a * 0 = 0) (x : W)
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
  · intro w _ hw
    by_cases hwr : w ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hwr
      have hxy : ¬H.Adj x y := fun hxy =>
        hw (Finset.mem_map_of_mem _ ((mem_neighborFinset _ _ _).2 hxy))
      rw [extendByZero_apply_apply_of_not_adj f β hxy, hmul]
    · rw [extendByZero_eq_zero_of_notMem_range_right f β _ hwr, hmul]

/-- **Local relations extend by zero along a copy**: if the sums `∑_{y ∼ x} β y x * β x y` over
the neighbours in `H` vanish at every vertex of `H`, then so do the corresponding sums of the
extension by zero at every vertex of `G` with finitely many neighbours. As for
`sum_extendByZero_mul_extendByZero_apply`, only right absorption `a * 0 = 0` is used. -/
theorem sum_extendByZero_mul_extendByZero [H.LocallyFinite] (hmul : ∀ a : M, a * 0 = 0)
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0) (v : V)
    [Fintype (G.neighborSet v)] :
    ∑ w ∈ G.neighborFinset v, f.extendByZero β w v * f.extendByZero β v w = 0 := by
  by_cases hv : v ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hv
    exact (sum_extendByZero_mul_extendByZero_apply f β hmul x).trans (hβ x)
  · exact Finset.sum_eq_zero fun w _ => by
      rw [extendByZero_eq_zero_of_notMem_range_left f β hv, hmul]

end Mul

end SimpleGraph.Copy
