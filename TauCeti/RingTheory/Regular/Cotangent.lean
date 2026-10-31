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
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# The conormal module of a weakly regular sequence

Let `f₁, …, f_r` be a weakly regular sequence on an `R`-module `M`, generating the ideal `I`. Every
relation `∑ fᵢ mᵢ = 0` with `mᵢ ∈ M` has all its coefficients in `I M`. Dividing the last element
out first, `f_r m_r ∈ (f₁, …, f_{r-1}) M` forces `m_r = ∑_{i<r} fᵢ nᵢ`, and the relation
`∑_{i<r} fᵢ (mᵢ + f_r nᵢ) = 0` among the first `r - 1` elements finishes the induction.

For `M = R` this computes the conormal module `I ⧸ I²` (Mathlib's `Ideal.Cotangent`): it is free
over `R ⧸ I` with basis the classes of `f₁, …, f_r`. A relation `∑ aᵢ fᵢ ∈ I²` can be rewritten as
`∑ (aᵢ - bᵢ) fᵢ = 0` with `bᵢ ∈ I`, so every `aᵢ` lies in `I`.

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.mem_ofList_smul_top_of_sum_eq_zero`: the coefficients of a
  relation among a weakly `M`-regular sequence lie in `(f₁, …, f_r) M`.
* `RingTheory.Sequence.IsWeaklyRegular.cotangentBasis`: for a weakly regular sequence on `R`, the
  basis of `I ⧸ I²` over `R ⧸ I` given by the classes of the elements of the sequence.

## References

* [The Stacks Project, Tags 062F and 062I](https://stacks.math.columbia.edu/tag/062I)
-/

public section

open RingTheory.Sequence

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace RingTheory.Sequence.IsWeaklyRegular

/-- The relation statement for a sequence indexed by `Fin n`, by induction on `n`. -/
private theorem mem_smul_top_of_sum_eq_zero_aux :
    ∀ {n : ℕ} {rs : Fin n → R}, IsWeaklyRegular M (List.ofFn rs) → ∀ {m : Fin n → M},
      ∑ i, rs i • m i = 0 → ∀ i, m i ∈ Ideal.span (Set.range rs) • (⊤ : Submodule R M) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ i ↦ i.elim0
  | succ n ih =>
    intro rs h m hm
    rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff,
      isWeaklyRegular_singleton_iff, Ideal.ofList_ofFn] at h
    obtain ⟨h₁, h₂⟩ := h
    set I' := Ideal.span (Set.range fun i : Fin n ↦ rs i.castSucc)
    rw [Fin.sum_univ_castSucc] at hm
    -- The last element is regular modulo `I' M`, so its coefficient lies in `I' M`.
    have hlast : m (Fin.last n) ∈ I' • (⊤ : Submodule R M) := by
      have : rs (Fin.last n) • m (Fin.last n) ∈ I' • (⊤ : Submodule R M) := by
        rw [eq_neg_of_add_eq_zero_right hm]
        exact neg_mem (sum_mem fun i _ ↦ Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩)
          Submodule.mem_top)
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul] at this
      rw [← Submodule.Quotient.mk_eq_zero]
      exact h₂.right_eq_zero_of_smul this
    -- Writing it as `∑ rsᵢ cᵢ` gives a relation among the first `n` elements.
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_smul_top_iff_exists_fun.mp hlast
    have hrel := ih h₁ (m := fun i ↦ m i.castSucc + rs (Fin.last n) • c i) (by
      simpa [smul_add, Finset.sum_add_distrib, smul_comm (rs _) (rs (Fin.last n)),
        ← Finset.smul_sum, hc] using hm)
    have hle : I' ≤ Ideal.span (Set.range rs) :=
      Ideal.span_mono (Set.range_comp_subset_range Fin.castSucc rs)
    refine Fin.lastCases (Submodule.smul_mono_left hle hlast) fun i ↦ ?_
    simpa using sub_mem (Submodule.smul_mono_left hle (hrel i)) (Submodule.smul_mem_smul
      (Ideal.subset_span ⟨Fin.last n, rfl⟩) (Submodule.mem_top (x := c i)))

/-- **Relations among a weakly regular sequence have coefficients in the ideal it generates.** If
`rs` is weakly regular on `M` and `∑ rsᵢ • mᵢ = 0`, then every `mᵢ` lies in `(rs) M`. -/
theorem mem_ofList_smul_top_of_sum_eq_zero {rs : List R} (h : IsWeaklyRegular M rs)
    {m : Fin rs.length → M} (hm : ∑ i, rs[i] • m i = 0) (i : Fin rs.length) :
    m i ∈ Ideal.ofList rs • (⊤ : Submodule R M) := by
  rw [← List.ofFn_getElem (xs := rs)] at h
  exact Ideal.ofList_eq_span_range_getElem rs ▸ mem_smul_top_of_sum_eq_zero_aux h hm i

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
