/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Analytic.Order

/-!
# Locally uniform holomorphic infinite products and their zero multiplicities

Let `u : ι → ℂ → ℂ` be a family of functions holomorphic on an open set `U ⊆ ℂ` such that on every
compact subset `K ⊆ U` the norms `‖u i z‖` admit a summable cofinite majorant — for instance when
`∑' i, sup_{z ∈ K} ‖u i z‖ < ∞` on every compact `K ⊆ U`. Then the unordered product
`∏' i, (1 + u i z)` converges locally uniformly on `U` to a holomorphic function on `U`, vanishes
at `z ∈ U` if and only if some factor `1 + u i z` vanishes, and has only finitely many vanishing
factors at each point of `U`. Extracting any finite set `s` of factors containing the ones that
vanish at `z` expresses the product on `U` as `(∏ i ∈ s, (1 + u i ·))` times a holomorphic tail
product nonvanishing at `z`, so the analytic order of vanishing is additive across the infinite
product: `analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z = ∑ᶠ i, analyticOrderAt (1 + u i ·) z`.

No countability or enumeration assumption is imposed on the index type `ι`. The convergence,
pointwise vanishing, finiteness of vanishing factors, and finite-set extraction lemmas are stated
first in their natural normed-ring and topological generality before specializing to holomorphic
families on open subsets of `ℂ`.

## Main results

* `TauCeti.tprod_one_add_eq_zero_iff_of_summable`, `TauCeti.finite_one_add_eq_zero_of_summable`,
  `TauCeti.tprod_one_add_eq_prod_mul_tprod_compl`: pointwise vanishing, finiteness of vanishing
  factors, and finite-set extraction for `∏' i, (1 + f i)` under `Summable fun i ↦ ‖f i‖`.
* `TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_compact`,
  `TauCeti.hasProdLocallyUniformlyOn_one_add_of_summable_sSup`: locally uniform convergence of
  `∏' i, (1 + u i x)` on an open set from compact-set majorants or compact-supremum summability.
* `TauCeti.differentiableOn_tprod_one_add`, `TauCeti.analyticOnNhd_tprod_one_add`: holomorphy and
  analyticity of the infinite product on an open set `U ⊆ ℂ`.
* `TauCeti.tprod_one_add_compl_ne_zero`: after extracting a finite set containing all factors that
  vanish at `z ∈ U`, the complementary product is nonzero at `z` (hence a holomorphic unit germ).
* `TauCeti.analyticOrderAt_tprod_one_add_of_finset`, `TauCeti.analyticOrderAt_tprod_one_add`,
  `TauCeti.analyticOrderNatAt_tprod_one_add`: additivity of analytic orders of vanishing for
  locally uniformly convergent holomorphic infinite products.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorem 15.6.
-/

public section

open Complex Filter Function Metric Set Topology
open scoped BigOperators

namespace TauCeti

section NormedRing

variable {ι α R : Type*}

/-- Under absolute summability of `f`, the product `∏' i, (1 + f i)` in a complete normed
commutative ring with multiplicative norm vanishes if and only if one of its factors vanishes. -/
theorem tprod_one_add_eq_zero_iff_of_summable [NormedCommRing R] [NormOneClass R] [NormMulClass R]
    [CompleteSpace R] {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    (∏' i, (1 + f i)) = 0 ↔ ∃ i, 1 + f i = 0 := by
  refine ⟨fun h ↦ ?_, tprod_of_exists_eq_zero⟩
  by_contra! hne
  exact tprod_one_add_ne_zero_of_summable hne hf h

/-- Under summability of `‖f i‖` in a normed commutative ring with `‖(1 : R)‖ = 1`, only finitely
many factors `1 + f i` can vanish. -/
theorem finite_one_add_eq_zero_of_summable [NormedCommRing R] [NormOneClass R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) : {i | 1 + f i = 0}.Finite := by
  have hev : ∀ᶠ i in cofinite, 1 + f i ≠ 0 := by
    filter_upwards [hf.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)] with i hi hzero
    have hnorm : ‖f i‖ = 1 := by
      rw [← norm_neg, ← eq_neg_of_add_eq_zero_left hzero, norm_one]
    exact lt_irrefl (1 : ℝ) (hnorm ▸ hi)
  simpa only [Filter.Eventually, mem_cofinite, Set.compl_ofPred, not_not] using hev

/-- Under summability of `‖f i‖` in a complete normed commutative ring, any finite set `s` of
factors splits off from `∏' i, (1 + f i)` leaving the complementary subtype product. -/
theorem tprod_one_add_eq_prod_mul_tprod_compl [NormedCommRing R] [NormOneClass R]
    [CompleteSpace R] {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) (s : Finset ι) :
    (∏' i, (1 + f i)) = (∏ i ∈ s, (1 + f i)) * ∏' i : {i // i ∉ s}, (1 + f i) := by
  have htail : Multipliable fun i : {i // i ∉ s} ↦ 1 + f i :=
    multipliable_one_add_of_summable (hf.subtype _)
  have hsplit := Multipliable.tprod_mul_tprod_compl (s := (s : Set ι)) (f := fun i ↦ 1 + f i)
    Multipliable.of_finite htail
  rw [s.tprod_subtype' (fun i ↦ 1 + f i)] at hsplit
  exact hsplit.symm

/-- Passing to any subtype of the index type preserves the existence of summable cofinite majorants
on compact subsets. -/
theorem exists_summable_cofinite_subtype [TopologicalSpace α] [SeminormedAddCommGroup R]
    {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i) (p : ι → Prop) :
    ∀ K ⊆ U, IsCompact K → ∃ v : Subtype p → ℝ, Summable v ∧
      ∀ᶠ i : Subtype p in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i := by
  intro K hKU hK
  obtain ⟨v, hv, hbound⟩ := hsum K hKU hK
  exact ⟨fun i ↦ v i, hv.subtype p, Subtype.val_injective.tendsto_cofinite.eventually hbound⟩

/-- Compact-set cofinite majorants imply pointwise absolute summability at every point of `U`. -/
theorem summable_norm_of_forall_compact [TopologicalSpace α] [SeminormedAddCommGroup R]
    {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i) {x : α} (hx : x ∈ U) :
    Summable fun i ↦ ‖u i x‖ := by
  obtain ⟨v, hv, hbound⟩ := hsum {x} (singleton_subset_iff.mpr hx) isCompact_singleton
  refine hv.of_norm_bounded_eventually ?_
  filter_upwards [hbound] with i hi
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact hi x (mem_singleton x)

/-- If continuous functions `u i` on an open set `U` in a locally compact space admit a summable
cofinite majorant on every compact subset of `U`, then `∏' i, (1 + u i x)` converges locally
uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_add_of_forall_compact [TopologicalSpace α]
    [LocallyCompactSpace α] [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {U : Set α} (hU : IsOpen U) {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) U := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hU
  intro K hKU hK
  obtain ⟨v, hv, hbound⟩ := hsum K hKU hK
  exact hv.hasProdUniformlyOn_one_add hK hbound fun i ↦ (hcts i).mono hKU

/-- Summability of `sSup ((fun x ↦ ‖u i x‖) '' K)` for continuous `u i` on a compact set `K`
gives uniform convergence of `∏' i, (1 + u i x)` on `K`. -/
theorem hasProdUniformlyOn_one_add_of_summable_sSup [TopologicalSpace α]
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {K : Set α} (hK : IsCompact K)
    {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) K)
    (hsum : Summable fun i ↦ sSup ((fun x ↦ ‖u i x‖) '' K)) :
    HasProdUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) K :=
  hsum.hasProdUniformlyOn_one_add hK
    (Eventually.of_forall fun i _ hx ↦
      le_csSup (hK.image_of_continuousOn (hcts i).norm).bddAbove (mem_image_of_mem _ hx))
    hcts

/-- Summability of `sSup ((fun x ↦ ‖u i x‖) '' K)` on every compact subset `K ⊆ U` supplies a
summable majorant on every compact subset of `U`. -/
theorem exists_summable_cofinite_of_summable_sSup [TopologicalSpace α]
    [SeminormedAddCommGroup R] {U : Set α} {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → Summable fun i ↦ sSup ((fun x ↦ ‖u i x‖) '' K)) :
    ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i :=
  fun K hKU hK ↦ ⟨_, hsum K hKU hK, Eventually.of_forall fun i _ hx ↦
    le_csSup (hK.image_of_continuousOn ((hcts i).mono hKU).norm).bddAbove (mem_image_of_mem _ hx)⟩

/-- If continuous functions `u i` on an open set `U` in a locally compact space satisfy
`∑' i, sup_{x ∈ K} ‖u i x‖ < ∞` on every compact `K ⊆ U`, then `∏' i, (1 + u i x)` converges
locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_add_of_summable_sSup [TopologicalSpace α]
    [LocallyCompactSpace α] [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {U : Set α} (hU : IsOpen U) {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → Summable fun i ↦ sSup ((fun x ↦ ‖u i x‖) '' K)) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) U :=
  hasProdLocallyUniformlyOn_one_add_of_forall_compact hU hcts
    (exists_summable_cofinite_of_summable_sSup hcts hsum)

end NormedRing

section Holomorphic

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

/-- Under the hypotheses of `differentiableOn_tprod_one_add`, the infinite product is analytic on
a neighborhood of every point of `U`. -/
theorem analyticOnNhd_tprod_one_add (hU : IsOpen U) (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) :
    AnalyticOnNhd ℂ (fun z ↦ ∏' i, (1 + u i z)) U :=
  (differentiableOn_tprod_one_add hU hu hsum).analyticOnNhd hU

/-- Restricting the index family to any subtype preserves holomorphy of `∏' i, (1 + u i z)`
on `U`. -/
theorem differentiableOn_tprod_one_add_subtype (hU : IsOpen U)
    (hu : ∀ i, DifferentiableOn ℂ (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) (p : ι → Prop) :
    DifferentiableOn ℂ (fun z ↦ ∏' i : Subtype p, (1 + u i z)) U :=
  differentiableOn_tprod_one_add hU (fun i ↦ hu i) (exists_summable_cofinite_subtype hsum p)

/-- At each point `z ∈ U`, the product `∏' i, (1 + u i z)` vanishes if and only if some factor
`1 + u i z` vanishes. -/
theorem tprod_one_add_eq_zero_iff
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) {z : ℂ} (hz : z ∈ U) :
    (∏' i, (1 + u i z)) = 0 ↔ ∃ i, 1 + u i z = 0 :=
  tprod_one_add_eq_zero_iff_of_summable (summable_norm_of_forall_compact hsum hz)

/-- At each point `z ∈ U`, only finitely many factors `1 + u i z` vanish. -/
theorem finite_one_add_eq_zero
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i) {z : ℂ} (hz : z ∈ U) :
    {i | 1 + u i z = 0}.Finite :=
  finite_one_add_eq_zero_of_summable (summable_norm_of_forall_compact hsum hz)

/-- After extracting a finite set `s` containing all indices whose factor vanishes at `z ∈ U`, the
complementary product is nonzero at `z`. Together with `differentiableOn_tprod_one_add_subtype`,
this shows that the complementary tail defines a holomorphic unit germ at `z`. -/
theorem tprod_one_add_compl_ne_zero
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖u i z‖ ≤ v i)
    {s : Finset ι} {z : ℂ} (hz : z ∈ U) (hs : ∀ i, 1 + u i z = 0 → i ∈ s) :
    (∏' i : {i // i ∉ s}, (1 + u i z)) ≠ 0 := by
  rw [ne_eq, tprod_one_add_eq_zero_iff (exists_summable_cofinite_subtype hsum _) hz]
  rintro ⟨i, hi⟩
  exact i.property (hs i hi)

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
  have hfin : AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, (1 + u i w)) z := by
    have heq : (fun w ↦ ∏ i ∈ s, (1 + u i w)) = ∏ i ∈ s, (fun w ↦ 1 + u i w) := by ext; simp
    rw [heq]
    exact Finset.analyticAt_prod _ fun i _ ↦ hfac i
  have htail : AnalyticAt ℂ (fun w ↦ ∏' i : {i // i ∉ s}, (1 + u i w)) z :=
    (differentiableOn_tprod_one_add_subtype hU hu hsum _).analyticAt (hU.mem_nhds hz)
  have hev : (fun w ↦ ∏' i, (1 + u i w)) =ᶠ[𝓝 z]
      ((fun w ↦ ∏ i ∈ s, (1 + u i w)) * fun w ↦ ∏' i : {i // i ∉ s}, (1 + u i w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact tprod_one_add_eq_prod_mul_tprod_compl (summable_norm_of_forall_compact hsum hw) s
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hfin htail,
    htail.analyticOrderAt_eq_zero.mpr (tprod_one_add_compl_ne_zero hsum hz hs), add_zero]
  have heq : (fun w ↦ ∏ i ∈ s, (1 + u i w)) = ∏ i ∈ s, (fun w ↦ 1 + u i w) := by ext; simp
  rw [heq, analyticOrderAt_prod (fun i _ ↦ hfac i)]

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
  have hfac : AnalyticAt ℂ (fun w ↦ 1 + u i w) z :=
    ((differentiableOn_const (1 : ℂ)).add (hu i)).analyticAt (hU.mem_nhds hz)
  exact hfac.analyticOrderAt_ne_zero.mp hi

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
  have hcast : ∑ i ∈ hf.toFinset, analyticOrderAt (fun w ↦ 1 + u i w) z =
      ((∑ i ∈ hf.toFinset, analyticOrderNatAt (fun w ↦ 1 + u i w) z : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.cast_analyticOrderNatAt (htop i)).symm
  rw [analyticOrderNatAt, hord, hcast, ENat.toNat_natCast]
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ hf.mem_toFinset.mpr ?_).symm
  have hfac : AnalyticAt ℂ (fun w ↦ 1 + u i w) z :=
    ((differentiableOn_const (1 : ℂ)).add (hu i)).analyticAt (hU.mem_nhds hz)
  refine hfac.analyticOrderAt_ne_zero.mp ?_
  rw [← Nat.cast_analyticOrderNatAt (htop i)]
  exact_mod_cast hi

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

end Holomorphic

end TauCeti
