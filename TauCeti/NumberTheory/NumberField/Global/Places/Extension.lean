/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Places.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Norm

/-!
# Normalized absolute values under a finite extension

Let `L / K` be an extension of number fields and let `w` be a place of `L` lying over the place
`v` of `K`. On the image of `K` in `L`, the normalized absolute value at `w` is the normalized
absolute value at `v` raised to the local degree `[L_w : K_v]`:

`‖x‖_w = ‖x‖_v ^ [L_w : K_v]`  for `x ∈ K`.

At a finite place the local degree is `e(w ∣ v) f(w ∣ v)`
(`IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion`). At an infinite place it is `1`,
unless `w` is complex and `v` is real, where it is `2`; this is the factor by which the squared
absolute value at a complex place differs from the absolute value at the real place below it.

The same formulas on the completions themselves are
`IsDedekindDomain.HeightOneSpectrum.norm_adicCompletionExtension` and
`NumberField.InfinitePlace.completionNormalizedAbsValue_completionMap`; this file states them for
the normalized absolute value `TauCeti.GlobalNumberFields.normalizedAbsValue` on `K` and `L`,
indexed by `TauCeti.GlobalNumberFields.Place`.

Since the local degrees above a fixed place `v` add up to `[L : K]`, multiplying over the places
`w ∣ v` gives `∏_{w ∣ v} ‖x‖_w = ‖x‖_v ^ [L : K]`. Read through the product formula, this is the
compatibility of the normalizations of `K` and `L` with one another.

## Main results

* `TauCeti.GlobalNumberFields.normalizedAbsValue_inl_algebraMap` and
  `TauCeti.GlobalNumberFields.normalizedAbsValue_inr_algebraMap`: at a finite, respectively
  infinite, place `w ∣ v`, the normalized absolute value of `x ∈ K` at `w` is its normalized
  absolute value at `v` raised to the local degree.
* `TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inl_algebraMap` and
  `TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inr_algebraMap`: the product over the
  places above `v` is the `[L : K]`-th power of the normalized absolute value at `v`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8 and Chapter III, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §11.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace Module
open scoped NumberField AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

/-- **Normalized absolute values at a finite place under extension.** If the finite place `w` of
`L` lies over the finite place `v` of `K`, then `‖x‖_w = ‖x‖_v ^ [L_w : K_v]` for `x ∈ K`. -/
theorem normalizedAbsValue_inl_algebraMap (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : K) :
    normalizedAbsValue (Sum.inl w) (algebraMap K L x) =
      normalizedAbsValue (Sum.inl v) x ^ finrank (v.adicCompletion K) (w.adicCompletion L) := by
  rw [normalizedAbsValue_inl_eq_norm_coe, normalizedAbsValue_inl_eq_norm_coe,
    ← HeightOneSpectrum.adicCompletionExtension_coe K L v w,
    HeightOneSpectrum.norm_adicCompletionExtension]

attribute [local instance] Fintype.ofFinite in
/-- The product over the finite places `w ∣ v` of `L` of the normalized absolute values of
`x ∈ K` is `‖x‖_v ^ [L : K]`. -/
@[simp↓]
theorem finprod_normalizedAbsValue_inl_algebraMap (x : K) :
    ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        normalizedAbsValue (Sum.inl w.1) (algebraMap K L x) =
      normalizedAbsValue (Sum.inl v) x ^ finrank K L := by
  simp_rw [finprod_eq_prod_of_fintype, normalizedAbsValue_inl_eq_norm_coe,
    ← HeightOneSpectrum.adicCompletionExtension_coe K L v,
    TauCeti.prod_norm_adicCompletionExtension_eq_norm_pow]

end Finite

section Infinite

variable (v : InfinitePlace K)

omit [NumberField K] in
/-- At an infinite place `w ∣ v`, the normalized absolute value of `x ∈ K` is the normalized
absolute value on `L_w` of the image of `x` under `K_v → L_w`. -/
private theorem normalizedAbsValue_inr_algebraMap_eq_completionMap (w : InfinitePlace L)
    [w.LiesOver v] (x : K) :
    normalizedAbsValue (Sum.inr w) (algebraMap K L x) =
      completionNormalizedAbsValue w
        (LiesOver.completionMap v w (algebraMap K v.Completion x)) := by
  rw [normalizedAbsValue_inr, ← completionNormalizedAbsValue_algebraMap,
    ← IsScalarTower.algebraMap_apply K L w.Completion,
    IsScalarTower.algebraMap_apply K v.Completion w.Completion]
  rfl

/-- **Normalized absolute values at an infinite place under extension.** If the infinite place `w`
of `L` lies over the infinite place `v` of `K`, then `‖x‖_w = ‖x‖_v ^ [L_w : K_v]` for `x ∈ K`.
The exponent is `2` exactly when `w` is complex and `v` is real, and `1` otherwise. -/
theorem normalizedAbsValue_inr_algebraMap (w : InfinitePlace L) [w.LiesOver v] (x : K) :
    normalizedAbsValue (Sum.inr w) (algebraMap K L x) =
      normalizedAbsValue (Sum.inr v) x ^ finrank v.Completion w.Completion := by
  rw [normalizedAbsValue_inr_algebraMap_eq_completionMap v,
    completionNormalizedAbsValue_completionMap, completionNormalizedAbsValue_algebraMap,
    normalizedAbsValue_inr]

open scoped Classical in
/-- The product over the infinite places `w ∣ v` of `L` of the normalized absolute values of
`x ∈ K` is `‖x‖_v ^ [L : K]`. -/
@[simp↓]
theorem finprod_normalizedAbsValue_inr_algebraMap (x : K) :
    ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        normalizedAbsValue (Sum.inr w.1) (algebraMap K L x) =
      normalizedAbsValue (Sum.inr v) x ^ finrank K L := by
  rw [finprod_eq_prod_of_fintype,
    Finset.prod_congr rfl fun w _ ↦ normalizedAbsValue_inr_algebraMap_eq_completionMap v w.1 x,
    prod_completionNormalizedAbsValue_completionMap, completionNormalizedAbsValue_algebraMap,
    normalizedAbsValue_inr]

end Infinite

end TauCeti.GlobalNumberFields
