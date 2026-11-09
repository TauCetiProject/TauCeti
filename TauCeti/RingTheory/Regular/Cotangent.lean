/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.Ideal.Cotangent.Basic
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# The conormal module of a weakly regular sequence

Let `f₁, …, f_r` be a weakly regular sequence on `R`, generating the ideal `I`. The conormal module
`I ⧸ I²` (Mathlib's `Ideal.Cotangent`) is free over `R ⧸ I` with basis the classes of
`f₁, …, f_r`. A relation `∑ aᵢ fᵢ ∈ I²` can be rewritten as `∑ (aᵢ - bᵢ) fᵢ = 0` with `bᵢ ∈ I`, so
every `aᵢ` lies in `I` by `RingTheory.Sequence.IsWeaklyRegular.mem_ofList_smul_top_of_sum_eq_zero`.

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.cotangentBasis`: for a weakly regular sequence on `R`, the
  basis of `I ⧸ I²` over `R ⧸ I` given by the classes of the elements of the sequence.

## References

* [The Stacks Project, Tags 062F and 062I](https://stacks.math.columbia.edu/tag/062I)
-/

public section

open RingTheory.Sequence

variable {R : Type*} [CommRing R]

namespace RingTheory.Sequence.IsWeaklyRegular

section Cotangent

variable {rs : List R}

/-- The class of the `i`-th element of `rs` in `(rs) ⧸ (rs)²`. -/
private noncomputable abbrev cotangentVec (rs : List R) (i : Fin rs.length) :
    (Ideal.ofList rs).Cotangent :=
  (Ideal.ofList rs).toCotangent ⟨rs[i], Ideal.subset_span (List.getElem_mem _)⟩

/-- The classes of the elements of a weakly regular sequence are linearly independent in the
conormal module. -/
private theorem linearIndependent_cotangentVec (h : IsWeaklyRegular R rs) :
    LinearIndependent (R ⧸ Ideal.ofList rs) (cotangentVec rs) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective.comp_left g
  simp only [Function.comp_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul,
    ← map_smul, ← map_sum, Ideal.toCotangent_eq_zero, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, smul_eq_mul] at hg
  -- `∑ aⱼ rsⱼ ∈ I² = I • (rs)` is also `∑ bⱼ rsⱼ` with `bⱼ ∈ I`.
  rw [sq, ← Ideal.smul_eq_mul] at hg
  nth_rw 2 [Ideal.ofList_eq_span_range_getElem] at hg
  obtain ⟨b, hb, hab⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp hg
  rw [Finsupp.sum_fintype _ _ (by simp)] at hab
  have hrel : ∑ j : Fin rs.length, rs[j] • (a j - b j) = 0 := by
    simp only [smul_eq_mul] at hab
    simp only [smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_comm _ (a _), mul_comm _ (b _),
      hab, sub_self]
  have := h.mem_ofList_smul_top_of_sum_eq_zero hrel i
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
  simpa [Ideal.Quotient.eq_zero_iff_mem] using (sub_add_cancel (a i) (b i)) ▸
    add_mem this (hb i)

/-- **The conormal module of a weakly regular sequence is free.** If `rs` is weakly regular on `R`
and `I = (rs)`, the classes of the elements of `rs` form a basis of `I ⧸ I²` over `R ⧸ I`. -/
noncomputable def cotangentBasis (h : IsWeaklyRegular R rs) :
    Module.Basis (Fin rs.length) (R ⧸ Ideal.ofList rs) (Ideal.ofList rs).Cotangent :=
  .mk (linearIndependent_cotangentVec h) (Ideal.span_range_toCotangent_eq_top
    (f := fun i ↦ ⟨rs[i], Ideal.subset_span (List.getElem_mem _)⟩)
    (Ideal.ofList_eq_span_range_getElem rs).symm).ge

/-- The `i`-th vector of `IsWeaklyRegular.cotangentBasis` is the class of the `i`-th element. -/
@[simp]
theorem cotangentBasis_apply (h : IsWeaklyRegular R rs) (i : Fin rs.length) :
    h.cotangentBasis i =
      (Ideal.ofList rs).toCotangent ⟨rs[i], Ideal.subset_span (List.getElem_mem _)⟩ :=
  Module.Basis.mk_apply _ _ _

end Cotangent

end RingTheory.Sequence.IsWeaklyRegular
