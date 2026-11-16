/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.ENat.BigOperators
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Holomorphic infinite products and additivity of analytic zero orders

Let `u : ι → ℂ → ℂ` be a family of functions holomorphic on an open set `U ⊆ ℂ` such that on every
compact subset `K ⊆ U` the norms `‖u i z‖` admit a summable cofinite majorant — for instance when
`∑' i, sup_{z ∈ K} ‖u i z‖ < ∞` on every compact `K ⊆ U`. Building on Mathlib's
`Summable.hasProdUniformlyOn_one_add` (`Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn`)
and `tprod_one_add_ne_zero_of_summable` (`Mathlib.Analysis.SpecialFunctions.Log.Summable`),
together with the general normed-ring and locally uniform product infrastructure in
`TauCeti.Analysis.Normed.Ring.InfiniteProd` and
`TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn`, this module proves holomorphy and
additivity of analytic zero orders for unordered products `∏' i, (1 + u i z)` over arbitrary index
types `ι`.

Extracting any finite set `s` of factors containing the ones that vanish at `z ∈ U` expresses the
product near `z` as `(∏ i ∈ s, (1 + u i ·))` times a holomorphic tail product nonvanishing at `z`,
yielding `analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z = ∑ᶠ i, analyticOrderAt (1 + u i ·) z`.
The factor-extraction and zero-order arguments generalize the genus-one case in
`TauCeti.Analysis.Complex.CanonicalProduct.Convergence`.

## Main results

* `TauCeti.differentiableOn_tprod_one_add`, `TauCeti.differentiableOn_tprod_one_add_subtype`:
  holomorphy of `∏' i, (1 + u i z)` and its subtype restrictions on an open set `U ⊆ ℂ`.
* `TauCeti.analyticOrderAt_tprod_one_add_of_finset`, `TauCeti.analyticOrderAt_tprod_one_add`,
  `TauCeti.analyticOrderNatAt_tprod_one_add`: additivity of analytic orders of vanishing for
  locally uniformly convergent holomorphic infinite products.
* `TauCeti.differentiableOn_tprod_one_add_of_summable_sSup`,
  `TauCeti.analyticOrderAt_tprod_one_add_of_summable_sSup`: Rudin's compact-supremum criterion
  (Theorem 15.6) for holomorphy and zero multiplicities.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorem 15.6.
-/

public section

open Complex Filter Function Metric Set Topology
open scoped BigOperators

namespace TauCeti

variable {ι : Type*} {U : Set ℂ} {u : ι → ℂ → ℂ}

/-- If `u i` are holomorphic on an open set `U ⊆ ℂ` and admit a summable cofinite majorant on
every compact subset of `U`, then `∏' i, (1 + u i z)` is holomorphic on `U`. -/
theorem differentiableOn_tprod_one_add (hU : IsOpen U) (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) :
    DifferentiableOn ℂ (fun z ↦ ∏' i, (1 + u i z)) U := by
  refine (hasProdLocallyUniformlyOn_one_add_of_forall_compact hU
    (fun i ↦ (hu i).continuousOn) hsum).differentiableOn ?_ hU
  exact Eventually.of_forall fun s ↦ by fun_prop

/-- Restricting the index family to any subtype preserves holomorphy of `∏' i, (1 + u i z)`
on `U`. -/
theorem differentiableOn_tprod_one_add_subtype (hU : IsOpen U)
    (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) (p : ι → Prop) :
    DifferentiableOn ℂ (fun z ↦ ∏' i : Subtype p, (1 + u i z)) U :=
  differentiableOn_tprod_one_add hU (fun i ↦ hu i) (exists_summable_cofinite_subtype hsum p)

/-- Extracting any finite set `s` containing all factors that vanish at `z ∈ U` reduces the
analytic order of `∏' i, (1 + u i ·)` at `z` to the finite sum over `s` of the factor orders. -/
theorem analyticOrderAt_tprod_one_add_of_finset (hU : IsOpen U)
    (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i)
    {s : Finset ι} {z : ℂ} (hz : z ∈ U) (hs : ∀ i, 1 + u i z = 0 → i ∈ s) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑ i ∈ s, analyticOrderAt (fun w ↦ 1 + u i w) z := by
  have hfac (i : ι) : AnalyticAt ℂ (fun w ↦ 1 + u i w) z :=
    ((differentiableOn_const (1 : ℂ)).add (hu i)).analyticAt (hU.mem_nhds hz)
  have hfin : AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, (1 + u i w)) z :=
    s.analyticAt_fun_prod fun i _ ↦ hfac i
  have htail : AnalyticAt ℂ (fun w ↦ ∏' i : {i // i ∉ s}, (1 + u i w)) z :=
    (differentiableOn_tprod_one_add_subtype hU hu hsum _).analyticAt (hU.mem_nhds hz)
  have hev : (fun w ↦ ∏' i, (1 + u i w)) =ᶠ[𝓝 z]
      ((fun w ↦ ∏ i ∈ s, (1 + u i w)) * fun w ↦ ∏' i : {i // i ∉ s}, (1 + u i w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact tprod_one_add_eq_prod_mul_tprod_compl (summable_norm_of_forall_compact hsum hw) s
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hfin htail,
    htail.analyticOrderAt_eq_zero.mpr (tprod_one_add_compl_ne_zero hsum hz hs), add_zero,
    ← Finset.prod_fn, analyticOrderAt_prod (fun i _ ↦ hfac i)]

/-- **Additivity of analytic order for locally uniform holomorphic infinite products.** At each
`z ∈ U`, the analytic order of `∏' i, (1 + u i ·)` equals the finitely supported sum of the
analytic orders of its factors. -/
theorem analyticOrderAt_tprod_one_add (hU : IsOpen U) (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑ᶠ i, analyticOrderAt (fun w ↦ 1 + u i w) z := by
  have hf := finite_one_add_eq_zero hsum hz
  rw [analyticOrderAt_tprod_one_add_of_finset hU hu hsum hz (fun i hi ↦ hf.mem_toFinset.mpr hi)]
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ hf.mem_toFinset.mpr ?_).symm
  exact apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun w ↦ 1 + u i w) hi

/-- Natural-number form of `analyticOrderAt_tprod_one_add` when no factor vanishes identically
near `z`. -/
theorem analyticOrderNatAt_tprod_one_add (hU : IsOpen U) (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i)
    {z : ℂ} (hz : z ∈ U) (htop : ∀ i, analyticOrderAt (fun w ↦ 1 + u i w) z ≠ ⊤) :
    analyticOrderNatAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑ᶠ i, analyticOrderNatAt (fun w ↦ 1 + u i w) z := by
  have hf := finite_one_add_eq_zero hsum hz
  have hord := analyticOrderAt_tprod_one_add_of_finset hU hu hsum hz
    (fun i hi ↦ hf.mem_toFinset.mpr hi)
  rw [analyticOrderNatAt, hord, ENat.toNat_sum (fun i _ ↦ htop i)]
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ hf.mem_toFinset.mpr ?_).symm
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun w ↦ 1 + u i w) hi

/-- Rudin's compact-supremum criterion (Theorem 15.6): if `u i` are holomorphic on an open set
`U ⊆ ℂ` and `∑' i, sup_{z ∈ K} ‖u i z‖ < ∞` on every compact `K ⊆ U`, then `∏' i, (1 + u i z)`
is holomorphic on `U`. -/
theorem differentiableOn_tprod_one_add_of_summable_sSup (hU : IsOpen U)
    (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → Summable fun i ↦ sSup ((fun z ↦ ‖u i z‖) '' K)) :
    DifferentiableOn ℂ (fun z ↦ ∏' i, (1 + u i z)) U :=
  differentiableOn_tprod_one_add hU hu
    (exists_summable_cofinite_of_summable_sSup (fun i ↦ (hu i).continuousOn) hsum)

/-- Rudin's compact-supremum criterion (Theorem 15.6) for zero multiplicities: under
`∑' i, sup_{z ∈ K} ‖u i z‖ < ∞` on every compact `K ⊆ U`, the analytic order of
`∏' i, (1 + u i ·)` at `z ∈ U` equals the sum of the analytic orders of its factors. -/
theorem analyticOrderAt_tprod_one_add_of_summable_sSup (hU : IsOpen U)
    (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → Summable fun i ↦ sSup ((fun z ↦ ‖u i z‖) '' K))
    {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑ᶠ i, analyticOrderAt (fun w ↦ 1 + u i w) z :=
  analyticOrderAt_tprod_one_add hU hu
    (exists_summable_cofinite_of_summable_sSup (fun i ↦ (hu i).continuousOn) hsum) hz

end TauCeti
