/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Transverse lines and affine subspaces

A line whose direction is outside an affine subspace's direction meets that
subspace at most once, counted by its affine parameter. More generally, the
affine span of finitely many points meets an affine subspace at most once when
the edge vectors from the first point are linearly independent modulo the
subspace's direction. Any two affine subspaces with disjoint directions also
meet in at most one point. For a line transverse to a level hyperplane, the
contact parameter is the height difference divided by the normal velocity.

## Main results

* `AffineSubspace.subsingleton_inter_of_disjoint_direction`: affine subspaces with disjoint
  directions meet in at most one point.
* `AffineSubspace.subsingleton_preimage_lineMap`: a line whose direction is not in the direction
  of `S` meets `S` for at most one parameter.
* `AffineSubspace.subsingleton_affineSpan_range_inter`: the affine span of finitely many points
  whose edge vectors are independent modulo the direction of `S` meets `S` at most once.
* `LinearMap.eq_div_of_apply_add_smul_eq`: the contact parameter of a transverse line with a
  level hyperplane.

In particular, a segment whose direction is outside the affine direction of a wall meets the
wall in at most one point.

## Attribution

Adapted from `Mei/Geometry/Affine/Transverse.lean` in Mei at commit
`68536122a97fed8e87bc6870b9427151971b9ab2`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/68536122a97fed8e87bc6870b9427151971b9ab2/Mei/Geometry/Affine/Transverse.lean
-/

public section

namespace LinearMap

/-- A transverse line meets a level hyperplane at the height difference divided
by its normal velocity. -/
theorem eq_div_of_apply_add_smul_eq {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] K) {c t : K} {y v : V} (hv : f v ≠ 0)
    (ht : f (y + t • v) = c) : t = (c - f y) / f v := by
  apply (eq_div_iff hv).mpr
  exact eq_sub_of_add_eq' (by simpa only [map_add, map_smul, smul_eq_mul] using ht)

end LinearMap

namespace AffineSubspace

/-- Affine subspaces with disjoint directions meet in at most one point.
Neither affine subspace is required to be nonempty. -/
theorem subsingleton_inter_of_disjoint_direction
    {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    (S T : AffineSubspace k P)
    (hST : Disjoint S.direction T.direction) :
    ((S : Set P) ∩ T).Subsingleton := by
  intro x hx y hy
  apply vsub_eq_zero_iff_eq.mp
  exact Submodule.disjoint_def.mp hST _
    (S.vsub_mem_direction hx.1 hy.1) (T.vsub_mem_direction hx.2 hy.2)

section Ring

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- If the edge vectors `p j.succ -ᵥ p 0` of a finite family of points remain linearly
independent modulo the direction of `S`, then the affine span of the points meets `S` in at most
one point. -/
theorem subsingleton_affineSpan_range_inter (S : AffineSubspace k P) {n : ℕ}
    {p : Fin (n + 1) → P}
    (hp : LinearIndependent k (S.direction.mkQ ∘ fun j : Fin n => p j.succ -ᵥ p 0)) :
    ((affineSpan k (Set.range p) : Set P) ∩ S).Subsingleton := by
  intro x hx y hy
  have hxy : x -ᵥ y ∈ Submodule.span k (Set.range fun j : Fin n => p j.succ -ᵥ p 0) := by
    have hmem := (affineSpan k (Set.range p)).vsub_mem_direction hx.1 hy.1
    rw [direction_affineSpan, vectorSpan_range_eq_span_range_vsub_right_ne k p 0] at hmem
    convert hmem using 2
    ext w
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.succ, Fin.succ_ne_zero j⟩, rfl⟩
    · rintro ⟨⟨l, hl⟩, rfl⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hl
      exact ⟨j, rfl⟩
  apply vsub_eq_zero_iff_eq.mp
  refine Submodule.disjoint_def.mp (Submodule.range_ker_disjoint hp) _ hxy ?_
  rw [Submodule.ker_mkQ]
  exact S.vsub_mem_direction hx.2 hy.2

end Ring

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

/-- The inverse image of an affine subspace under a scalar-parametrized affine
map has at most one point if at least one parameter avoids the subspace. -/
theorem subsingleton_preimage_of_notMem
    (S : AffineSubspace k P) (f : k →ᵃ[k] P) {t₀ : k} (ht₀ : f t₀ ∉ S) :
    (f ⁻¹' (S : Set P)).Subsingleton := by
  let A := S.comap f
  have hA : A ≠ ⊤ := by
    intro he
    have hmem : t₀ ∈ A := he.symm ▸ AffineSubspace.mem_top k k t₀
    exact ht₀ (mem_comap.mp hmem)
  intro s hs t ht
  have hsA : s ∈ A := mem_comap.mpr hs
  have htA : t ∈ A := mem_comap.mpr ht
  rcases eq_bot_or_eq_top A.direction with hd | hd
  · exact (direction_eq_bot_iff.mp hd) hsA htA
  · exact (hA ((direction_eq_top_iff_of_nonempty ⟨s, hsA⟩).mp hd)).elim

/-- The parameters at which a transverse line meets an affine subspace form
a subsingleton. No codimension or nonemptiness assumption is needed. -/
theorem subsingleton_preimage_lineMap (S : AffineSubspace k P) {x y : P}
    (h : y -ᵥ x ∉ S.direction) :
    ((AffineMap.lineMap x y : k →ᵃ[k] P) ⁻¹' (S : Set P)).Subsingleton := by
  classical
  intro s hs t ht
  by_contra hst
  have hd := S.vsub_mem_direction hs ht
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply,
    vadd_vsub_vadd_cancel_right, ← sub_smul] at hd
  exact h ((S.direction.smul_mem_iff (sub_ne_zero.mpr hst)).mp hd)

end AffineSubspace
