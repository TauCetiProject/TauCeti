/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Normalized archimedean absolute values under field extension

For infinite places `w ∣ v`, the completion map raises the normalized absolute value to the
local degree `[L_w : K_v]`. The underlying ordinary norms agree, but a complex place above a
real place doubles the normalization exponent. Multiplying over all places above `v` gives
the global degree `[L : K]`. These are the archimedean factors in the degree formula for
extension of ideles.

Throughout, `L_w` carries Mathlib's `K_v`-algebra structure
`AbsoluteValue.Completion.algebraOfLiesOver` as a local instance whenever `w` lies over `v`.
Completed extensions at infinite places are finite dimensional, with degree one or two. A place
indexed by the places above `v` carries its proof of lying over `v` as an instance.

The formulas are in `NumberField.InfinitePlace`, alongside
`completionNormalizedAbsValue`. For the ordinary norm, use
`AbsoluteValue.Completion.norm_map x`. For the normalized value, use
`completionNormalizedAbsValue_completionMap (w := w) x` for a completion element,
and `prod_completionNormalizedAbsValue_completionMap (L := L) v x` for the product
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

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A place indexed by the places above `v` carries its proof of lying over `v` as an instance. -/
instance instLiesOverSubtype (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.LiesOver v}) : w.1.LiesOver v := w.2

/-- A completed extension at an infinite place is finite dimensional: its degree is one or two. -/
instance (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] :
    FiniteDimensional v.Completion w.Completion := by
  apply Module.finite_of_finrank_pos
  have h := mult_ne_zero (w := w)
  rw [← mult_mul_finrank v w, mul_ne_zero_iff] at h
  exact Nat.pos_of_ne_zero h.2

/-- Under extension of archimedean completions the normalized absolute value is raised to the
local degree. This includes the real-to-complex case and the value at zero. -/
@[simp↓]
theorem completionNormalizedAbsValue_completionMap
    {v : InfinitePlace K} {w : InfinitePlace L} [w.LiesOver v] (x : v.Completion) :
    completionNormalizedAbsValue w (AbsoluteValue.Completion.map v.1 w.1 x) =
      completionNormalizedAbsValue v x ^ Module.finrank v.Completion w.Completion := by
  rw [completionNormalizedAbsValue_apply, AbsoluteValue.Completion.norm_map,
    completionNormalizedAbsValue_apply, ← pow_mul, InfinitePlace.mult_mul_finrank]

variable [NumberField K] [NumberField L]

omit [NumberField K] in
open Classical in
/-- The product of normalized absolute values over the infinite places above `v` is the
normalized absolute value at `v` raised to the global degree. -/
@[simp↓]
theorem prod_completionNormalizedAbsValue_completionMap
    (v : InfinitePlace K) (x : v.Completion) :
    ∏ w : {w : InfinitePlace L // w.LiesOver v}, completionNormalizedAbsValue w.1
        (@AbsoluteValue.Completion.map K L _ _ _ v.1 w.1.1 w.2 x) =
      completionNormalizedAbsValue v x ^ Module.finrank K L := by
  classical
  have : CharZero K := (algebraMap K L).charZero
  have : NumberField K := NumberField.of_tower ℚ L K
  have h (w : {w : InfinitePlace L // w.LiesOver v}) :
      completionNormalizedAbsValue w.1
        (@AbsoluteValue.Completion.map K L _ _ _ v.1 w.1.1 w.2 x) =
        completionNormalizedAbsValue v x ^ v.inertiaDeg w.1 := by
    let := w.2
    rw [completionNormalizedAbsValue_completionMap,
      InfinitePlace.inertiaDeg_eq_finrank]
  simp_rw [h]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Finset.sum_set_coe (f := fun w ↦ v.inertiaDeg w) (v.placesOver L)).trans
    (InfinitePlace.sum_inertiaDeg_eq_finrank K L v)

end NumberField.InfinitePlace
