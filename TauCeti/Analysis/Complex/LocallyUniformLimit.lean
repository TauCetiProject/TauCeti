/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Instances.ENat
public import TauCeti.Analysis.Analytic.Order
public import TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn

import Mathlib.Data.ENat.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Holomorphicity and germ orders of locally uniformly convergent infinite products

This file connects locally uniform convergence of infinite products on open subsets `Ω ⊆ ℂ`
(including empty and disconnected `Ω`) to holomorphicity and `analyticOrderAt`:

* `HasProdLocallyUniformlyOn.differentiableOn` and `HasSumLocallyUniformlyOn.differentiableOn`:
  per-factor holomorphicity passes to locally uniformly convergent products and sums on open sets
  in `ℂ`.
* `TauCeti.differentiableOn_tprod_one_add` and
  `TauCeti.differentiableOn_tprod_nat_one_add_of_tail`: holomorphicity of `∏' i, (1 + u i z)` on
  an arbitrary open set `Ω ⊆ ℂ` under compact uniform-tail hypotheses.
* `TauCeti.exists_finset_closedBall_tprod_one_add_eq_prod_mul`: around every `z ∈ Ω`, a closed disk
  splits `∏' i, (1 + u i w)` into a finite product `(∏ i ∈ I, (1 + u i w))` times a holomorphic
  nowhere-zero tail `∏' i : {i // i ∉ I}, (1 + u i w)`.
* `TauCeti.hasSum_analyticOrderAt_one_add`, `TauCeti.analyticOrderAt_tprod_one_add`, and
  `TauCeti.analyticOrderAt_tprod_nat_one_add_of_tail`: the exact germ-order sum formula
  `analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z = ∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z`
  in `ℕ∞` for every `z ∈ Ω`, valid both when all factor orders are finite and when a factor has
  zero germ (`analyticOrderAt = ⊤`), together with the `analyticOrderNatAt` specialization and the
  compact-sup-summability corollary `TauCeti.analyticOrderAt_tprod_one_add_of_locally_summable`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 14.3, pp. 35–36.
-/

public section

open Filter Function Metric Set
open scoped Topology

section LocallyUniformClosure

/-- A locally uniformly convergent infinite product of holomorphic functions on an open subset
`Ω ⊆ ℂ` is holomorphic on `Ω`. -/
theorem HasProdLocallyUniformlyOn.differentiableOn {ι : Type*} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {Ω : Set ℂ} (h : HasProdLocallyUniformlyOn f g Ω) (hf : ∀ i, DifferentiableOn ℂ (f i) Ω)
    (hΩ : IsOpen Ω) : DifferentiableOn ℂ g Ω :=
  TendstoLocallyUniformlyOn.differentiableOn h
    (.of_forall fun _ ↦ by
      simpa only [Finset.prod_fn] using DifferentiableOn.finsetProd fun i _ ↦ hf i)
    hΩ

/-- If a family of holomorphic functions on an open subset `Ω ⊆ ℂ` is locally uniformly
multipliable on `Ω`, then its pointwise product `∏' i, f i z` is holomorphic on `Ω`. -/
theorem MultipliableLocallyUniformlyOn.differentiableOn_tprod {ι : Type*} {f : ι → ℂ → ℂ}
    {Ω : Set ℂ} (h : MultipliableLocallyUniformlyOn f Ω) (hf : ∀ i, DifferentiableOn ℂ (f i) Ω)
    (hΩ : IsOpen Ω) : DifferentiableOn ℂ (fun z ↦ ∏' i, f i z) Ω :=
  h.hasProdLocallyUniformlyOn.differentiableOn hf hΩ

/-- A locally uniformly convergent infinite sum of holomorphic functions on an open subset `Ω ⊆ ℂ`
with values in a complete complex normed space is holomorphic on `Ω`. -/
theorem HasSumLocallyUniformlyOn.differentiableOn {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {g : ℂ → E} {Ω : Set ℂ}
    (h : HasSumLocallyUniformlyOn f g Ω) (hf : ∀ i, DifferentiableOn ℂ (f i) Ω)
    (hΩ : IsOpen Ω) : DifferentiableOn ℂ g Ω :=
  TendstoLocallyUniformlyOn.differentiableOn h
    (.of_forall fun _ ↦ DifferentiableOn.fun_sum fun i _ ↦ hf i) hΩ

/-- If a family of holomorphic functions on an open subset `Ω ⊆ ℂ` into a complete complex normed
space is locally uniformly summable on `Ω`, then `∑' i, f i z` is holomorphic on `Ω`. -/
theorem SummableLocallyUniformlyOn.differentiableOn_tsum {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {Ω : Set ℂ}
    (h : SummableLocallyUniformlyOn f Ω) (hf : ∀ i, DifferentiableOn ℂ (f i) Ω)
    (hΩ : IsOpen Ω) : DifferentiableOn ℂ (fun z ↦ ∑' i, f i z) Ω :=
  h.hasSumLocallyUniformlyOn.differentiableOn hf hΩ

end LocallyUniformClosure

namespace TauCeti

section HolomorphicProduct

variable {ι : Type*} {u : ι → ℂ → ℂ} {Ω : Set ℂ}

/-- **Holomorphicity of uniform-tail infinite products.** If `Ω ⊆ ℂ` is open, each `u i` is
holomorphic on `Ω`, and `fun i z ↦ ‖u i z‖` is uniformly summable on every compact subset of `Ω`,
then `∏' i, (1 + u i z)` is holomorphic on `Ω`. -/
theorem differentiableOn_tprod_one_add
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K) :
    DifferentiableOn ℂ (fun z ↦ ∏' i, (1 + u i z)) Ω :=
  (hasProdLocallyUniformlyOn_one_add_of_forall_isCompact (fun i ↦ (hu i).continuousOn) hΩ
    hsum).differentiableOn (fun i ↦ (hu i).const_add 1) hΩ

/-- Analytic-on-neighborhoods form of `TauCeti.differentiableOn_tprod_one_add`. -/
theorem analyticOnNhd_tprod_one_add
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K) :
    AnalyticOnNhd ℂ (fun z ↦ ∏' i, (1 + u i z)) Ω :=
  (Complex.analyticOnNhd_iff_differentiableOn hΩ).2 (differentiableOn_tprod_one_add hu hΩ hsum)

/-- **Sequential holomorphic uniform-tail product theorem.** If `Ω ⊆ ℂ` is open, each `u n` is
holomorphic on `Ω`, `∑' n, ‖u n z‖` converges on `Ω`, and the tails `∑' k, ‖u (N + k) z‖` vanish
uniformly on every compact subset of `Ω`, then `∏' n, (1 + u n z)` is holomorphic on `Ω`. -/
theorem differentiableOn_tprod_nat_one_add_of_tail {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, DifferentiableOn ℂ (u n) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ z ∈ Ω, Summable fun n ↦ ‖u n z‖)
    (htail : ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, (∑' k, ‖u (N + k) z‖) < ε) :
    DifferentiableOn ℂ (fun z ↦ ∏' n, (1 + u n z)) Ω :=
  (hasProdLocallyUniformlyOn_nat_one_add_of_tail (fun n ↦ (hu n).continuousOn) hΩ hsum
    htail).differentiableOn (fun n ↦ (hu n).const_add 1) hΩ

/-- **Local unit-tail splitting on a closed disk.** At every point `z` of an open set `Ω ⊆ ℂ`,
there exist a radius `r > 0` with `closedBall z r ⊆ Ω` and a finite index set `I` such that every
omitted factor `1 + u i` is nonvanishing on `closedBall z r`, the complement infinite product
`w ↦ ∏' i : {i // i ∉ I}, (1 + u i w)` is holomorphic on `ball z r`, analytic at `z`, and nowhere
zero on `closedBall z r`, and `∏' i, (1 + u i w)` factors on `closedBall z r` as the finite product
over `I` times the complement product. -/
theorem exists_finset_closedBall_tprod_one_add_eq_prod_mul
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    ∃ r > 0, ∃ I : Finset ι,
      closedBall z r ⊆ Ω ∧
      (∀ i ∉ I, ∀ w ∈ closedBall z r, 1 + u i w ≠ 0) ∧
      DifferentiableOn ℂ (fun w ↦ ∏' i : {i // i ∉ I}, (1 + u i w)) (ball z r) ∧
      AnalyticAt ℂ (fun w ↦ ∏' i : {i // i ∉ I}, (1 + u i w)) z ∧
      (∀ w ∈ closedBall z r, (∏' i : {i // i ∉ I}, (1 + u i w)) ≠ 0) ∧
      ∀ w ∈ closedBall z r, ∏' i, (1 + u i w) =
        (∏ i ∈ I, (1 + u i w)) * ∏' i : {i // i ∉ I}, (1 + u i w) := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩ z hz
  set r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hKΩ : closedBall z r ⊆ Ω := (closedBall_subset_ball (half_lt_self hR)).trans hRΩ
  have hK : IsCompact (closedBall z r) := isCompact_closedBall z r
  have hbd : ∀ i, Bornology.IsBounded (u i '' closedBall z r) := fun i ↦
    (hK.image_of_continuousOn ((hu i).continuousOn.mono hKΩ)).isBounded
  obtain ⟨I, -, hfac_ne, htail_prod, htail_ne, hsplit⟩ :=
    (hsum _ hKΩ hK).exists_finset_tprod_one_add_eq_prod_mul_ne_zero hbd
  have hballΩ : ball z r ⊆ Ω := ball_subset_closedBall.trans hKΩ
  have htail_diff : DifferentiableOn ℂ (fun w ↦ ∏' i : {i // i ∉ I}, (1 + u i w)) (ball z r) :=
    ((htail_prod.mono ball_subset_closedBall).hasProdLocallyUniformlyOn).differentiableOn
      (fun i ↦ ((hu i).mono hballΩ).const_add 1) isOpen_ball
  exact ⟨r, hr, I, hKΩ, hfac_ne, htail_diff, htail_diff.analyticAt (ball_mem_nhds z hr),
    htail_ne, hsplit⟩

/-- At every point `z ∈ Ω`, only finitely many factors `1 + u i` have nonzero analytic order at
`z`. -/
theorem finite_analyticOrderAt_one_add_ne_zero
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    {i : ι | analyticOrderAt (fun w ↦ 1 + u i w) z ≠ 0}.Finite := by
  obtain ⟨r, hr, I, -, hfac_ne, -, -, -, -⟩ :=
    exists_finset_closedBall_tprod_one_add_eq_prod_mul hu hΩ hsum hz
  refine I.finite_toSet.subset fun i hi ↦ ?_
  by_contra hiI
  have han : AnalyticAt ℂ (fun w ↦ 1 + u i w) z :=
    ((hu i).const_add 1).analyticAt (hΩ.mem_nhds hz)
  exact hi (han.analyticOrderAt_eq_zero.2 (hfac_ne i hiI z (mem_closedBall_self hr.le)))

/-- **`HasSum` form of the infinite-product germ-order formula in `ℕ∞`.** For `z ∈ Ω`, the family
of factor orders `i ↦ analyticOrderAt (fun w ↦ 1 + u i w) z` has finite support and sums to
`analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z`, including `⊤` when some factor vanishes
identically near `z`. -/
theorem hasSum_analyticOrderAt_one_add
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    HasSum (fun i ↦ analyticOrderAt (fun w ↦ 1 + u i w) z)
      (analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z) := by
  obtain ⟨r, hr, I, -, hfac_ne, -, htail_an, htail_ne, hsplit⟩ :=
    exists_finset_closedBall_tprod_one_add_eq_prod_mul hu hΩ hsum hz
  have han : ∀ i, AnalyticAt ℂ (fun w ↦ 1 + u i w) z := fun i ↦
    ((hu i).const_add 1).analyticAt (hΩ.mem_nhds hz)
  have hzero_off : ∀ i ∉ I, analyticOrderAt (fun w ↦ 1 + u i w) z = 0 := fun i hiI ↦
    (han i).analyticOrderAt_eq_zero.2 (hfac_ne i hiI z (mem_closedBall_self hr.le))
  have hev : (fun w ↦ ∏' i, (1 + u i w)) =ᶠ[𝓝 z]
      ((∏ i ∈ I, fun w ↦ 1 + u i w) * fun w ↦ ∏' i : {i // i ∉ I}, (1 + u i w)) := by
    filter_upwards [closedBall_mem_nhds z hr] with w hw
    simp [Finset.prod_apply, hsplit w hw]
  have hord_eq : analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑ i ∈ I, analyticOrderAt (fun w ↦ 1 + u i w) z := by
    rw [analyticOrderAt_congr hev,
      analyticOrderAt_mul (Finset.analyticAt_prod I fun i _ ↦ han i) htail_an,
      analyticOrderAt_prod fun i _ ↦ han i,
      htail_an.analyticOrderAt_eq_zero.2 (htail_ne z (mem_closedBall_self hr.le)), add_zero]
  rw [hord_eq]
  exact hasSum_sum_of_ne_finset_zero hzero_off

/-- **Germ-order identity for uniform-tail infinite products in `ℕ∞`.** At every `z ∈ Ω`,
`analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z` equals `∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z`
in `ℕ∞`, including infinite order `⊤` when some factor has zero germ at `z`. -/
theorem analyticOrderAt_tprod_one_add
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z :=
  (hasSum_analyticOrderAt_one_add hu hΩ hsum hz).tsum_eq.symm

/-- **Sequential `ℕ`-indexed germ-order identity in `ℕ∞`.** Under pointwise absolute summability on
`Ω` and uniformly vanishing tails on every compact `K ⊆ Ω`, the analytic order of
`∏' n, (1 + u n w)` at `z ∈ Ω` is `∑' n, analyticOrderAt (fun w ↦ 1 + u n w) z`. -/
theorem analyticOrderAt_tprod_nat_one_add_of_tail {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, DifferentiableOn ℂ (u n) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ z ∈ Ω, Summable fun n ↦ ‖u n z‖)
    (htail : ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, (∑' k, ‖u (N + k) z‖) < ε)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' n, (1 + u n w)) z =
      ∑' n, analyticOrderAt (fun w ↦ 1 + u n w) z := by
  refine analyticOrderAt_tprod_one_add hu hΩ (fun K hKΩ hK ↦ ?_) hz
  exact (summableUniformlyOn_nat_of_nonneg_iff fun _ _ _ ↦ norm_nonneg _).2
    ⟨fun w hw ↦ hsum w (hKΩ hw), htail K hKΩ hK⟩

/-- Under the hypotheses of `TauCeti.analyticOrderAt_tprod_one_add`, the infinite product has
infinite analytic order (`⊤`) at `z ∈ Ω` if and only if some factor `1 + u i` has infinite analytic
order at `z`. -/
theorem analyticOrderAt_tprod_one_add_eq_top_iff
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z = ⊤ ↔
      ∃ i, analyticOrderAt (fun w ↦ 1 + u i w) z = ⊤ := by
  have hfin := finite_analyticOrderAt_one_add_ne_zero hu hΩ hsum hz
  have hzero : ∀ i ∉ hfin.toFinset, analyticOrderAt (fun w ↦ 1 + u i w) z = 0 := by
    intro i hi
    simpa [Set.Finite.mem_toFinset] using hi
  rw [analyticOrderAt_tprod_one_add hu hΩ hsum hz, tsum_eq_sum hzero, ENat.sum_eq_top]
  refine ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, ?_, hi⟩⟩
  rw [Set.Finite.mem_toFinset, mem_ofPred_eq, hi]
  exact ENat.top_ne_zero

/-- Finite-order characterization: `∏' i, (1 + u i w)` has finite analytic order at `z ∈ Ω` if and
only if every factor `1 + u i` has finite analytic order at `z`. -/
theorem analyticOrderAt_tprod_one_add_ne_top_iff
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z ≠ ⊤ ↔
      ∀ i, analyticOrderAt (fun w ↦ 1 + u i w) z ≠ ⊤ := by
  rw [ne_eq, analyticOrderAt_tprod_one_add_eq_top_iff hu hΩ hsum hz, not_exists]

/-- When no factor vanishes identically near `z ∈ Ω`, the natural-number analytic order
`analyticOrderNatAt` of `∏' i, (1 + u i w)` at `z` is the (finitely supported) sum of the factor
orders `analyticOrderNatAt (fun w ↦ 1 + u i w) z`. -/
theorem analyticOrderNatAt_tprod_one_add
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i w ↦ ‖u i w‖) K)
    {z : ℂ} (hz : z ∈ Ω) (hne : ∀ i, analyticOrderAt (fun w ↦ 1 + u i w) z ≠ ⊤) :
    analyticOrderNatAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑' i, analyticOrderNatAt (fun w ↦ 1 + u i w) z := by
  have hfin := finite_analyticOrderAt_one_add_ne_zero hu hΩ hsum hz
  have hzero_enat : ∀ i ∉ hfin.toFinset, analyticOrderAt (fun w ↦ 1 + u i w) z = 0 := by
    intro i hi
    simpa [Set.Finite.mem_toFinset] using hi
  have hzero_nat : ∀ i ∉ hfin.toFinset, analyticOrderNatAt (fun w ↦ 1 + u i w) z = 0 := by
    intro i hi
    simp [analyticOrderNatAt, hzero_enat i hi]
  have hprod_ne : analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z ≠ ⊤ :=
    (analyticOrderAt_tprod_one_add_ne_top_iff hu hΩ hsum hz).2 hne
  apply Nat.cast_injective (R := ℕ∞)
  rw [Nat.cast_analyticOrderNatAt hprod_ne, analyticOrderAt_tprod_one_add hu hΩ hsum hz,
    tsum_eq_sum hzero_enat, tsum_eq_sum hzero_nat, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (Nat.cast_analyticOrderNatAt (hne i)).symm

/-- **Germ-order identity under compact-sup summability.** If on every compact `K ⊆ Ω` the norms
`‖u i w‖` are eventually dominated by a summable sequence `M : ι → ℝ`, then
`analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z = ∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z` for
every `z ∈ Ω`. -/
theorem analyticOrderAt_tprod_one_add_of_locally_summable
    (hu : ∀ i, DifferentiableOn ℂ (u i) Ω) (hΩ : IsOpen Ω)
    (hM : ∀ K ⊆ Ω, IsCompact K →
      ∃ M : ι → ℝ, Summable M ∧ ∀ᶠ i in cofinite, ∀ w ∈ K, ‖u i w‖ ≤ M i)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z := by
  refine analyticOrderAt_tprod_one_add hu hΩ (fun K hKΩ hK ↦ ?_) hz
  obtain ⟨M, hM_sum, hM_le⟩ := hM K hKΩ hK
  refine (HasSumUniformlyOn.of_norm_le_summable_eventually hM_sum ?_).summableUniformlyOn
  filter_upwards [hM_le] with i hi w hw
  simpa using hi w hw

end HolomorphicProduct

end TauCeti
