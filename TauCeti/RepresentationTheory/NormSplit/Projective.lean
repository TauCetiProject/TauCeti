/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.NormSplit.Basic
import TauCeti.RepresentationTheory.Rep.Free
import TauCeti.RepresentationTheory.Rep.Projective

/-!
# Higman's criterion for projectivity

Let `A` be a representation of a finite group `G` over a commutative ring `k`, and let `G` act on
`End_k(A)` by conjugation (`Representation.linHom A.ρ A.ρ`). **Higman's criterion** (at the trivial
subgroup) says that, when `A` is projective over `k`, `A` is a projective representation exactly
when the identity of `A` is a norm for this action: `id_A = ∑ g, A.ρ g ∘ α ∘ A.ρ g⁻¹` for some
`k`-linear `α`.

`TauCeti/RepresentationTheory/NormSplit/Basic.lean` proves that a norm identity gives
projectivity (`Rep.projective_of_id_mem_range_norm_linHom`). This file proves the converse, with
no hypothesis on `k`. On the free representation on a type `ι`, the identity is the norm of the
projection `α₀` to the coefficients at `1 ∈ G`
(`Rep.id_mem_range_norm_linHom_free`), and a norm identity passes to retracts
(`Rep.id_mem_range_norm_linHom_of_retract`); a projective representation is a retract of the free
representation on its underlying set (`Rep.retractFree`).

## Main results

* `Rep.id_mem_range_norm_linHom_of_projective`: the identity of a projective representation is a
  norm.
* `Rep.projective_iff_id_mem_range_norm_linHom`,
  `Rep.moduleProjective_iff_id_mem_range_norm_linHom`: Higman's criterion, for a representation
  projective over `k`, in `Rep k G` and as a `k[G]`-module.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 11.3.4, pp. 198–199
  (the case `H = 1`).
-/

public section

universe u v w

namespace Rep

open CategoryTheory

section

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]

/-- **A norm identity passes to retracts.** If `r ∘ s = id_A` for morphisms of representations
`s : A ⟶ B` and `r : B ⟶ A`, and `id_B = ∑ g, B.ρ g ∘ β ∘ B.ρ g⁻¹`, then
`id_A = ∑ g, A.ρ g ∘ (r ∘ β ∘ s) ∘ A.ρ g⁻¹`. -/
theorem id_mem_range_norm_linHom_of_retract {A B : Rep.{w} k G} (s : A ⟶ B) (r : B ⟶ A)
    (hsr : s ≫ r = 𝟙 A)
    (h : LinearMap.id ∈ LinearMap.range (Representation.linHom B.ρ B.ρ).norm) :
    LinearMap.id ∈ LinearMap.range (Representation.linHom A.ρ A.ρ).norm := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨r.hom.toLinearMap ∘ₗ β ∘ₗ s.hom.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  have hx : r.hom (s.hom x) = x := congr($(hsr).hom x)
  have hβx := LinearMap.congr_fun hβ (s.hom x)
  rw [Representation.norm_linHom_apply, LinearMap.id_apply] at hβx
  rw [Representation.norm_linHom_apply, LinearMap.id_apply]
  conv_rhs => rw [← hx, ← hβx]
  simp [map_sum, hom_comm_apply]

/-- **The identity of a free representation is a norm**: it is the norm of the projection to the
coefficients at `1 ∈ G`, `f ↦ single 1 (f 1)` in each coordinate. -/
theorem id_mem_range_norm_linHom_free (ι : Type w) :
    LinearMap.id ∈ LinearMap.range
      (Representation.linHom (free k G ι).ρ (free k G ι).ρ).norm := by
  classical
  refine ⟨Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle (R := k) (1 : G) ∘ₗ
    Finsupp.lapply 1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap), ?_⟩
  refine Finsupp.lhom_ext' fun i ↦ MonoidAlgebra.lhom_ext' fun h ↦ LinearMap.ext_ring ?_
  simp +contextual [Representation.norm_linHom_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, inv_mul_eq_one, Fintype.sum_eq_single h]

/-- **The identity of a projective representation is a norm**: `id_A = ∑ g, A.ρ g ∘ α ∘ A.ρ g⁻¹`
for some `k`-linear `α`. -/
theorem id_mem_range_norm_linHom_of_projective (A : Rep.{max u v} k G) [Projective A] :
    LinearMap.id ∈ LinearMap.range (Representation.linHom A.ρ A.ρ).norm :=
  id_mem_range_norm_linHom_of_retract (retractFree A).i (retractFree A).r (retractFree A).retract
    (id_mem_range_norm_linHom_free _)

end

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- **Higman's criterion.** A representation projective over `k` is projective exactly when its
identity is a norm for the conjugation action on its `k`-linear endomorphisms. -/
theorem projective_iff_id_mem_range_norm_linHom (A : Rep.{u} k G) [Module.Projective k A.V] :
    Projective A ↔ LinearMap.id ∈ LinearMap.range (Representation.linHom A.ρ A.ρ).norm :=
  ⟨fun _ ↦ id_mem_range_norm_linHom_of_projective A, projective_of_id_mem_range_norm_linHom A⟩

/-- **Higman's criterion** for `k[G]`-modules: a representation projective over `k` is a projective
`k[G]`-module exactly when its identity is a norm for the conjugation action on its `k`-linear
endomorphisms. -/
theorem moduleProjective_iff_id_mem_range_norm_linHom (A : Rep.{u} k G)
    [Module.Projective k A.V] :
    Module.Projective (MonoidAlgebra k G) A.ρ.asModule ↔
      LinearMap.id ∈ LinearMap.range (Representation.linHom A.ρ A.ρ).norm :=
  (projective_iff_moduleProjective A).symm.trans (projective_iff_id_mem_range_norm_linHom A)

end Rep
