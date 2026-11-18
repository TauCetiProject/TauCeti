/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Abel

/-!
# Transversality of iterated linear fibre products

Let `a : U → P`, `b : V → P`, `c : V → Q` and `d : W → Q` be linear maps. The fibre product of
`a` and `b` consists of the pairs `(u, v)` with `a u = b v`; the vectors `v` occurring in it form
the submodule `b⁻¹(range a)`. So `c` maps the fibre product of `a` and `b` onto
`c (b⁻¹(range a))`, and the second iterated fibre product, of this map with `d`, is transverse
when

`c (b⁻¹(range a)) + range d = Q`.

Regrouping the three spaces the other way, the map `b` sends the fibre product of `c` and `d`
onto `b (c⁻¹(range d))`, and the other iterated fibre product is transverse when

`range a + b (c⁻¹(range d)) = P`.

If `a` and `b` are transverse, `range a + range b = P`, the first condition implies the second
(`LinearMap.range_sup_map_comap_range_eq_top`). So when both inner pairs are transverse, the two
outer conditions are equivalent (`LinearMap.map_comap_range_sup_range_eq_top_iff`): each says
that `(u, v, w) ↦ (a u - b v, c v - d w)` is onto `P × Q`. This is the tangent-space content of
the associativity of transverse composition of correspondences.

## Main results

* `LinearMap.range_sup_map_comap_range_eq_top`: transversality of the iterated fibre product in
  one grouping gives it in the other, when the first pair is transverse.
* `LinearMap.map_comap_range_sup_range_eq_top_iff`: the two groupings are equivalent when both
  inner pairs are transverse.
-/

public section

namespace LinearMap

variable {R U V W P Q : Type*} [Ring R] [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup P] [AddCommGroup Q] [Module R U] [Module R V] [Module R W] [Module R P]
  [Module R Q]

/-- **Regrouping a transverse iterated fibre product.** Let `a : U → P`, `b : V → P`,
`c : V → Q` and `d : W → Q` be linear maps with `range a + range b = P`. If
`c (b⁻¹(range a)) + range d = Q`, then `range a + b (c⁻¹(range d)) = P`. -/
theorem range_sup_map_comap_range_eq_top (a : U →ₗ[R] P) (b : V →ₗ[R] P) (c : V →ₗ[R] Q)
    (d : W →ₗ[R] Q) (hab : range a ⊔ range b = ⊤)
    (h : ((range a).comap b).map c ⊔ range d = ⊤) :
    range a ⊔ ((range d).comap c).map b = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  -- Write `x = a u + b v₀`, then split `c v₀ = c v₁ + d w` with `b v₁ = a u₁`.
  obtain ⟨_, ⟨u, rfl⟩, _, ⟨v₀, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hab ▸ Submodule.mem_top (x := x))
  obtain ⟨_, ⟨v₁, ⟨u₁, hu₁⟩, rfl⟩, _, ⟨w, rfl⟩, hc⟩ :=
    Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := c v₀))
  -- Then `v₀ - v₁` is matched by `w`, and `x = a (u + u₁) + b (v₀ - v₁)`.
  refine Submodule.mem_sup.2 ⟨a (u + u₁), mem_range_self a _, b (v₀ - v₁),
    Submodule.mem_map_of_mem ⟨w, ?_⟩, ?_⟩
  · rw [map_sub, ← hc]
    abel
  · rw [map_add, map_sub, hu₁]
    abel

/-- **The transversality of an iterated linear fibre product is independent of the grouping.**
For linear maps `a : U → P`, `b : V → P`, `c : V → Q` and `d : W → Q` with
`range a + range b = P` and `range c + range d = Q`, the condition
`c (b⁻¹(range a)) + range d = Q` holds exactly when `range a + b (c⁻¹(range d)) = P`. -/
theorem map_comap_range_sup_range_eq_top_iff {a : U →ₗ[R] P} {b : V →ₗ[R] P} {c : V →ₗ[R] Q}
    {d : W →ₗ[R] Q} (hab : range a ⊔ range b = ⊤) (hcd : range c ⊔ range d = ⊤) :
    ((range a).comap b).map c ⊔ range d = ⊤ ↔ range a ⊔ ((range d).comap c).map b = ⊤ :=
  ⟨range_sup_map_comap_range_eq_top a b c d hab, fun h ↦ by
    rw [sup_comm] at hcd h ⊢
    exact range_sup_map_comap_range_eq_top d c b a hcd h⟩

end LinearMap
