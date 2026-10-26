/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Minkowski's convex body theorem for the integer lattice

Mathlib states Minkowski's convex body theorem for an arbitrary discrete subgroup with a
fundamental domain. This file records its most common instance: the integer lattice `ℤ^η` in
`η → ℝ` with Lebesgue measure, whose unit cube has volume one. The statement produces an
integer vector directly, which is the form used in Diophantine approximation.

## Main results

* `MeasureTheory.exists_ne_zero_int_vec_mem_of_two_pow_le_volume`: a compact convex symmetric
  set `s ⊆ η → ℝ` of volume at least `2 ^ |η|` contains a nonzero integer vector.
-/

public section

open Module

namespace MeasureTheory

/-- **Minkowski's convex body theorem for the integer lattice.** A compact convex set
`s ⊆ η → ℝ`, symmetric about the origin, of volume at least `2 ^ |η|` contains a nonzero integer
vector. -/
theorem exists_ne_zero_int_vec_mem_of_two_pow_le_volume {η : Type*} [Fintype η] [Nonempty η]
    {s : Set (η → ℝ)} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : 2 ^ Fintype.card η ≤ volume s) :
    ∃ z : η → ℤ, z ≠ 0 ∧ (fun k ↦ (z k : ℝ)) ∈ s := by
  set b := Pi.basisFun ℝ η
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨⟨v, hv⟩, hv0, hvs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (ZSpan.isAddFundamentalDomain' b volume) h_symm h_conv h_cpt (by
      rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico, finrank_fintype_fun_eq_card]
      simpa using h)
  choose z hz using fun k ↦ by simpa [b] using (b.mem_span_iff_repr_mem ℤ v).1 hv k
  have hvz : v = fun k ↦ (z k : ℝ) := funext fun k ↦ (hz k).symm
  subst hvz
  exact ⟨z, fun h0 ↦ hv0 (Subtype.ext (funext fun k ↦ by simp [h0])), hvs⟩

end MeasureTheory
