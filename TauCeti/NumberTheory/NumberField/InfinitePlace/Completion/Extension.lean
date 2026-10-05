/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

Completed extensions at infinite places are finite dimensional, with degree one or two. A place
indexed by the places above `v` carries its proof of lying over `v` as an instance.

The formulas are in `NumberField.InfinitePlace`, alongside
`completionNormalizedAbsValue`. For the ordinary norm, use
`NumberField.InfinitePlace.Completion.norm_completionMap (w := w) x`. For the normalized value, use
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
open scoped NumberField.LiesOver

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

/-- Canonical maps between archimedean completions compose in a tower of fields. -/
@[simp]
theorem _root_.NumberField.LiesOver.completionMap_comp
    {M : Type*} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {v : InfinitePlace K} {w : InfinitePlace L} {u : InfinitePlace M}
    [w.LiesOver v] [u.LiesOver w] :
    (LiesOver.completionMap (v := w) (w := u)).comp
        (LiesOver.completionMap (v := v) (w := w)) =
      @LiesOver.completionMap K M _ _ _ v u (InfinitePlace.LiesOver.trans u w v) := by
  let _ : u.LiesOver v := InfinitePlace.LiesOver.trans u w v
  apply DFunLike.coe_injective
  apply (InfinitePlace.Completion.denseRange_coe v).equalizer
    (LiesOver.continuous_completionMap.comp LiesOver.continuous_completionMap)
    LiesOver.continuous_completionMap
  funext x
  simp [Function.comp_apply, LiesOver.completionMap_coe,
    WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
    ← IsScalarTower.algebraMap_apply]

/-- Extension of archimedean completions preserves the ordinary norm. -/
@[simp]
theorem Completion.norm_completionMap
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
theorem completionNormalizedAbsValue_completionMap
    {v : InfinitePlace K} {w : InfinitePlace L} [w.LiesOver v] (x : v.Completion) :
    completionNormalizedAbsValue w (LiesOver.completionMap x) =
      completionNormalizedAbsValue v x ^ Module.finrank v.Completion w.Completion := by
  rw [completionNormalizedAbsValue_apply, Completion.norm_completionMap,
    completionNormalizedAbsValue_apply, ← pow_mul, InfinitePlace.mult_mul_finrank]

variable [NumberField K] [NumberField L]

open Classical in
/-- The product of normalized absolute values over the infinite places above `v` is the
normalized absolute value at `v` raised to the global degree. -/
@[simp↓]
theorem prod_completionNormalizedAbsValue_completionMap
    (v : InfinitePlace K) (x : v.Completion) :
    ∏ w : {w : InfinitePlace L // w.LiesOver v}, completionNormalizedAbsValue w.1
        (@LiesOver.completionMap K L _ _ _ v w.1 w.2 x) =
      completionNormalizedAbsValue v x ^ Module.finrank K L := by
  classical
  have h (w : {w : InfinitePlace L // w.LiesOver v}) :
      completionNormalizedAbsValue w.1
        (@LiesOver.completionMap K L _ _ _ v w.1 w.2 x) =
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
