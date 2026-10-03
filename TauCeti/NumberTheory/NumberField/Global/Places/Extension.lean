/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion

/-!
# Normalized archimedean absolute values under field extension

For infinite places `w ∣ v`, the completion map raises the normalized absolute value to the
local degree `[L_w : K_v]`. The underlying ordinary norms agree, but a complex place above a
real place doubles the normalization exponent. Multiplying over all places above `v` gives
the global degree `[L : K]`. These are the archimedean factors in the degree formula for
extension of ideles.

The formulas are in `TauCeti.GlobalNumberFields`, alongside
`infiniteCompletionNormalizedAbsValue`. For the ordinary norm, use
`TauCeti.GlobalNumberFields.norm_completionMap (w := w) x`. For the normalized value, use
`infiniteCompletionNormalizedAbsValue_completionMap (w := w) x` for a completion element,
and `prod_infiniteCompletionNormalizedAbsValue_completionMap (L := L) v x` for the product
over places above `v`. Both are pre-simplification rules: `simp` applies them before
expanding the normalized absolute value into a power of the norm.

The degree and multiplicity identities are Mathlib's
`NumberField.InfinitePlace.mult_mul_finrank` and
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
-/

public section
noncomputable section

open NumberField
open scoped NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Extension of archimedean completions preserves the ordinary norm. -/
@[simp]
theorem norm_completionMap
    {v : InfinitePlace K} {w : InfinitePlace L} [w.LiesOver v] (x : v.Completion) :
    ‖LiesOver.completionMap (w := w) x‖ = ‖x‖ := by
  -- `completionMap` has an unexposed body, so use its public continuity and coercion lemmas
  -- to transport Mathlib's norm preservation from the dense base field.
  induction x using InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (continuous_norm.comp (LiesOver.continuous_completionMap (v := v) (w := w)))
      continuous_norm
  | ih y =>
    rw [LiesOver.completionMap_coe]
    simpa only [InfinitePlace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
      WithAbs.equiv_apply, InfinitePlace.coe_apply] using
      (InfinitePlace.LiesOver.isometry_algebraMap w v).norm_map_of_map_zero (map_zero _) y

/-- Under extension of archimedean completions the normalized absolute value is raised to the
local degree. This includes the real-to-complex case and the value at zero. -/
@[simp↓]
theorem infiniteCompletionNormalizedAbsValue_completionMap
    {v : InfinitePlace K} {w : InfinitePlace L} [w.LiesOver v] (x : v.Completion) :
    infiniteCompletionNormalizedAbsValue w (LiesOver.completionMap x) =
      infiniteCompletionNormalizedAbsValue v x ^ Module.finrank v.Completion w.Completion := by
  rw [infiniteCompletionNormalizedAbsValue_apply, norm_completionMap,
    infiniteCompletionNormalizedAbsValue_apply, ← pow_mul, InfinitePlace.mult_mul_finrank]

variable [NumberField K] [NumberField L]

open Classical in
/-- The product of normalized absolute values over the infinite places above `v` is the
normalized absolute value at `v` raised to the global degree. -/
@[simp↓]
theorem prod_infiniteCompletionNormalizedAbsValue_completionMap
    (v : InfinitePlace K) (x : v.Completion) :
    ∏ w : {w : InfinitePlace L // w.LiesOver v}, infiniteCompletionNormalizedAbsValue w.1
        (@LiesOver.completionMap K L _ _ _ v w.1 w.2 x) =
      infiniteCompletionNormalizedAbsValue v x ^ Module.finrank K L := by
  classical
  have h (w : {w : InfinitePlace L // w.LiesOver v}) :
      infiniteCompletionNormalizedAbsValue w.1
        (@LiesOver.completionMap K L _ _ _ v w.1 w.2 x) =
        infiniteCompletionNormalizedAbsValue v x ^ v.inertiaDeg w.1 := by
    let := w.2
    rw [infiniteCompletionNormalizedAbsValue_completionMap,
      InfinitePlace.inertiaDeg_eq_finrank]
  simp_rw [h]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Finset.sum_set_coe (f := fun w ↦ v.inertiaDeg w) (v.placesOver L)).trans
    (InfinitePlace.sum_inertiaDeg_eq_finrank K L v)

end TauCeti.GlobalNumberFields
