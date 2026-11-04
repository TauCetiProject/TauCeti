/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Ring.Rat
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational spans of additive subgroups

An element of a `ℚ`-module lies in the rational span of an additive subgroup `Q` exactly when some
positive integer multiple of it lies in `Q`. This denominator-clearing result is used to pass
from rational spans back to integer lattices.
-/

public section

namespace TauCeti

/-- An element `x` of a `ℚ`-module lies in the rational span of an additive subgroup `Q` exactly
when `n • x ∈ Q` for some positive integer `n`. -/
theorem _root_.AddSubgroup.mem_rat_span_iff_exists_nsmul_mem {V : Type*} [AddCommGroup V]
    [Module ℚ V] (Q : AddSubgroup V) {x : V} :
    x ∈ Submodule.span ℚ (Q : Set V) ↔ ∃ n : ℕ, 0 < n ∧ n • x ∈ Q := by
  refine ⟨fun hx => ?_, fun ⟨n, hn, hnx⟩ => ?_⟩
  · obtain ⟨⟨t, ht⟩, htx⟩ :=
      multiple_mem_span_of_mem_localization_span (Submonoid.pos ℤ) ℚ _ x hx
    rw [Submonoid.mem_pos] at ht
    lift t to ℕ using ht.le
    refine ⟨t, by omega, ?_⟩
    rwa [← Q.coe_toIntSubmodule, Submodule.span_eq, Submonoid.smul_def, natCast_zsmul] at htx
  · have := Submodule.smul_mem _ (n⁻¹ : ℚ) (Submodule.subset_span (R := ℚ) hnx)
    rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this

end TauCeti
