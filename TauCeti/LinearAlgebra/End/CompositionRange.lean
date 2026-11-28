/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.LinearAlgebra.Exact

/-!
# Ranges and kernel dimensions of products of endomorphisms

A commuting factor whose kernel complements its range contributes an intersection to the
range of a product. Independently of commutativity or splitting, the kernel dimension of
a product is bounded by the sum of the kernel dimensions of its factors.
-/

public section

open LinearMap

namespace Module.End

/-- If `f` splits the module as its kernel plus its range, composing with a commuting
endomorphism `g` has range `range f ⊓ range g`. No splitting for `g` is needed. -/
theorem range_mul_eq_inf_of_isCompl_ker_range {R M : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (f : End R M) {g : End R M} (hfg : Commute f g)
    (hf : IsCompl (ker f) (range f)) : range (f * g) = range f ⊓ range g := by
  have hgf : f * g = g * f := hfg.eq
  refine le_antisymm (le_inf (range_comp_le_range _ _) ?_) ?_
  · rw [hgf]
    exact range_comp_le_range _ _
  · intro x hx
    obtain ⟨hx, hx'⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx'
    have hy : y ∈ ker f ⊔ range f := by rw [hf.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp hy
    have hcomm (z : M) : f (g z) = g (f z) := LinearMap.congr_fun hgf z
    obtain ⟨v, rfl⟩ := mem_range.mp hr
    have hgk : g k ∈ ker f := mem_ker.mpr (by rw [hcomm, mem_ker.mp hk, map_zero])
    have hgkr : g k ∈ range f := by
      obtain ⟨w, hw⟩ := mem_range.mp hx
      exact mem_range.mpr ⟨w - g v, by
        rw [map_sub, hw, hcomm v, map_add, add_sub_cancel_right]⟩
    have hzero : g k = 0 := hf.disjoint.le_bot ⟨hgk, hgkr⟩
    exact mem_range.mpr ⟨v, by rw [mul_apply_eq_comp, map_add, hzero, zero_add]; exact hcomm v⟩

end Module.End

namespace List

open Module.End

/-- The range of a product of commuting endomorphisms whose kernels complement their ranges is
the intersection of their ranges. The empty product has the full range. -/
theorem range_map_prod_eq_iInf_range {R M ι : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] (s : List ι) (f : ι → Module.End R M)
    (hcomm : s.Pairwise fun i j ↦ Commute (f i) (f j))
    (hs : ∀ i ∈ s, IsCompl (ker (f i)) (f i).range) :
    (s.map f).prod.range = ⨅ i ∈ s, (f i).range := by
  induction s with
  | nil => simp [one_eq_id]
  | cons i s ih =>
    rcases List.pairwise_cons.mp hcomm with ⟨hi, ht⟩
    have hprod : Commute (f i) (s.map f).prod := by
      apply Commute.list_prod_right
      rintro _ h
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      exact hi j hj
    rw [List.map_cons, List.prod_cons,
      (f i).range_mul_eq_inf_of_isCompl_ker_range hprod (hs i List.mem_cons_self),
      ih ht (fun j hj ↦ hs j (List.mem_cons_of_mem _ hj))]
    simp only [List.mem_cons, iInf_or, iInf_iInf_eq_left, iInf_inf_eq]

/-- The dimension lost by a product of endomorphisms is at most the sum of the
individual losses in a finite-dimensional space. -/
theorem finrank_ker_map_prod_le_sum {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (s : List ι) (f : ι → Module.End K V) :
    Module.finrank K (ker (s.map f).prod) ≤ (s.map fun i ↦ Module.finrank K (ker (f i))).sum := by
  induction s with
  | nil => simp [one_eq_id]
  | cons i s ih =>
    rw [List.map_cons, List.prod_cons, mul_eq_comp, finrank_ker_comp_eq_finrank_ker_add,
      List.map_cons, List.sum_cons]
    exact (add_le_add ih ((s.map f).prod.kerCompToKer (f i)).range.finrank_le).trans_eq
      (add_comm ..)

end List
