/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic

import Mathlib.RingTheory.Ideal.Nonunits

/-!
# Non-units of a subring of a division ring and elements outside the subring

In a subring `S` of a division ring `F`, whenever neither `b : S` nor `1 - b` is a unit of `S`,
the element `t = 1 - b⁻¹` lies outside `S`, its inverse `t⁻¹ = 1 - (1 - b)⁻¹` also lies outside
`S`, and `(b : F) * (1 - t) = 1`. In the splitting argument for subrings of an algebraically
closed field, this produces a non-valuation element `t` witnessing a non-trivial cover by `S[t]`
and `S[t⁻¹]`.

## Main results

* `Subring.exists_notMem_and_inv_notMem_of_not_isUnit`: if `b : S` satisfies `¬IsUnit b` and
  `¬IsUnit (1 - b)`, then there exists `t : F` with `t ∉ S`, `t⁻¹ ∉ S`, and
  `(b : F) * (1 - t) = 1`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/ProperBaseChange/SubringSplitting.lean`
(`Subring.exists_notMem_and_inv_notMem_of_not_isUnit`), generalized from fields to division rings.
-/

@[expose] public section

namespace Subring

/-- Let `b` be an element of a subring `S` of a division ring `F` such that neither `b` nor `1 - b`
is a unit of `S`. Then `t = 1 - b⁻¹` satisfies `t ∉ S`, `t⁻¹ ∉ S`, and `(b : F) * (1 - t) = 1`. -/
theorem exists_notMem_and_inv_notMem_of_not_isUnit {F : Type*} [DivisionRing F] {S : Subring F}
    (b : S) (hb : ¬IsUnit b) (h_one_sub : ¬IsUnit (1 - b)) :
    ∃ t : F, t ∉ S ∧ t⁻¹ ∉ S ∧ (b : F) * (1 - t) = 1 := by
  have hb_ne : (b : F) ≠ 0 := fun h ↦ h_one_sub (by simp [ZeroMemClass.coe_eq_zero.mp h])
  have hsub_ne : 1 - (b : F) ≠ 0 := fun h ↦
    hb (by simp [show b = 1 from Subtype.ext (sub_eq_zero.mp h).symm])
  refine ⟨1 - (b : F)⁻¹, fun h_mem ↦ hb ?_, fun h_mem ↦ h_one_sub ?_, ?_⟩
  · exact (Submonoid.isUnit_iff_of_ne_zero hb_ne).mpr (by simpa using S.sub_mem S.one_mem h_mem)
  · have h_mul : (1 - (b : F)⁻¹) * (1 - (1 - (b : F))⁻¹) = 1 := by
      have h1 : (1 - (b : F)⁻¹) = ((b : F) - 1) * (b : F)⁻¹ := by
        rw [sub_mul, one_mul, mul_inv_cancel₀ hb_ne]
      have h2 : (1 - (1 - (b : F))⁻¹) = -(b : F) * (1 - (b : F))⁻¹ := by
        calc 1 - (1 - (b : F))⁻¹
            = (1 - (b : F)) * (1 - (b : F))⁻¹ - 1 * (1 - (b : F))⁻¹ := by
              rw [mul_inv_cancel₀ hsub_ne, one_mul]
          _ = -(b : F) * (1 - (b : F))⁻¹ := by rw [← sub_mul, sub_sub_cancel_left]
      rw [h1, h2, mul_assoc, ← mul_assoc (b : F)⁻¹, mul_neg, inv_mul_cancel₀ hb_ne, neg_mul,
        one_mul, mul_neg, ← neg_mul, neg_sub, mul_inv_cancel₀ hsub_ne]
    have h_inv : (1 - (b : F))⁻¹ = 1 - (1 - (b : F)⁻¹)⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right h_mul, sub_sub_cancel]
    have h_inv_mem : (1 - (b : F))⁻¹ ∈ S := by
      simpa only [h_inv] using S.sub_mem S.one_mem h_mem
    exact (Submonoid.isUnit_iff_of_ne_zero (a := 1 - b) hsub_ne).mpr h_inv_mem
  · rw [sub_sub_cancel, mul_inv_cancel₀ hb_ne]

end Subring
