/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENat
public import TauCeti.Analysis.Analytic.Order
public import TauCeti.Analysis.Calculus.LogDerivUniformlyOn
public import TauCeti.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn
import TauCeti.Analysis.Normed.Ring.InfiniteProd.Basic

/-!
# Holomorphic infinite products on plane domains

Let `Ω ⊆ ℂ` be an open set and `u : ι → ℂ → ℂ` a family of holomorphic functions on `Ω` whose norm
series `∑' i, ‖u i z‖` converges uniformly on every compact subset `K ⊆ Ω`. This file establishes
the function-theoretic properties of the infinite product `z ↦ ∏' i, (1 + u i z)` on `Ω`:

1. **Holomorphy and analyticity**: `z ↦ ∏' i, (1 + u i z)` converges locally uniformly on `Ω`
   (both unordered and sequentially, via
   `TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_isCompact` and
   `TauCeti.tendstoLocallyUniformlyOn_prod_range_one_add_of_tail_lt`) and is holomorphic, hence
   `AnalyticOnNhd`, on `Ω`.
2. **Local analytic unit-tail factorization**: for every compact `K ⊆ Ω`, outside a finite set
   `t : Finset ι` the complementary product `g w = ∏' i : {i // i ∉ t}, (1 + u i w)` is analytic on
   `Ω` and nowhere vanishing on `K`, with `∏' i, (1 + u i w) = (∏ i ∈ t, (1 + u i w)) * g w` on `Ω`.
3. **Additivity of analytic orders and divisors**: for every `z ∈ Ω`, only finitely many factors
   have nonzero `analyticOrderAt` at `z`, and
   `analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z = ∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z`
   in `ℕ∞` unconditionally (including `⊤` when some factor vanishes on a neighborhood of `z`). When
   no factor has infinite analytic order at `z`, `analyticOrderNatAt` and `MeromorphicOn.divisor` on
   `Ω` are likewise additive across the infinite product.
4. **Logarithmic derivative**: on any subset `V ⊆ Ω` where no factor `1 + u i` vanishes, the series
   `∑' i, deriv (u i) z / (1 + u i z)` converges locally uniformly on `V` to
   `logDeriv (fun z ↦ ∏' i, (1 + u i z))`.

## Main results

* `TauCeti.differentiableOn_tprod_one_add`, `TauCeti.analyticOnNhd_tprod_one_add`: holomorphy and
  analyticity of `∏' i, (1 + u i z)` on `Ω`.
* `TauCeti.exists_finset_tprod_one_add_eq_prod_mul_compl`: finite-head times zero-free analytic-tail
  factorization on any compact subset `K ⊆ Ω`.
* `TauCeti.finite_analyticOrderAt_one_add_ne_zero`, `TauCeti.analyticOrderAt_tprod_one_add`,
  `TauCeti.analyticOrderNatAt_tprod_one_add`, `TauCeti.divisor_tprod_one_add_apply`: finiteness of
  factor vanishing orders and additivity of `analyticOrderAt`, `analyticOrderNatAt`, and
  `MeromorphicOn.divisor` at `z ∈ Ω`.
* `TauCeti.hasSumLocallyUniformlyOn_logDeriv_one_add`, `TauCeti.logDeriv_tprod_one_add`: locally
  uniform and pointwise logarithmic-derivative expansion off the factor zeros.
* `TauCeti.differentiableOn_tprod_nat_one_add_of_tail_lt`,
  `TauCeti.analyticOrderAt_tprod_nat_one_add_of_tail_lt`: specialization to `ℕ`-indexed products
  with uniformly vanishing sequential norm tails on compact subsets of `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 14.3 and Remark 15.4.
* R. Remmert, *Classical Topics in Complex Function Theory*, Graduate Texts in Mathematics **172**,
  Springer, 1998, Chapter 1.
-/

public section

open Complex Filter Finset Function Metric Set Topology
open scoped BigOperators

namespace TauCeti

section GeneralIndex

variable {ι : Type*} {u : ι → ℂ → ℂ} {Ω V K : Set ℂ}

/-- Under compact-uniform norm summability on an open set `Ω ⊆ ℂ`, the infinite product
`z ↦ ∏' i, (1 + u i z)` of holomorphic factors is holomorphic on `Ω`. -/
theorem differentiableOn_tprod_one_add (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K) :
    DifferentiableOn ℂ (fun z ↦ ∏' i, (1 + u i z)) Ω :=
  (hasProdLocallyUniformlyOn_one_add_of_forall_isCompact hΩ htail
    fun i ↦ (hd i).continuousOn).differentiableOn (.of_forall fun _ ↦ by fun_prop) hΩ

/-- Under compact-uniform norm summability on an open set `Ω ⊆ ℂ`, the infinite product
`z ↦ ∏' i, (1 + u i z)` is analytic on a neighborhood of every point of `Ω`. -/
theorem analyticOnNhd_tprod_one_add (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K) :
    AnalyticOnNhd ℂ (fun z ↦ ∏' i, (1 + u i z)) Ω :=
  (differentiableOn_tprod_one_add hΩ hd htail).analyticOnNhd hΩ

/-- **Holomorphic head times zero-free tail factorization.** For every compact subset `K ⊆ Ω`,
there is a finite index set `t : Finset ι` such that the complementary infinite product
`w ↦ ∏' i : {i // i ∉ t}, (1 + u i w)` is analytic on all of `Ω`, neither it nor any factor
`1 + u i` (`i ∉ t`) vanishes on `K`, and on `Ω` the full product factors as the finite product over
`t` times this analytic tail. -/
theorem exists_finset_tprod_one_add_eq_prod_mul_compl (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ t : Finset ι,
      AnalyticOnNhd ℂ (fun w ↦ ∏' i : {i // i ∉ t}, (1 + u i w)) Ω ∧
        (∀ i ∉ t, ∀ w ∈ K, 1 + u i w ≠ 0) ∧
        (∀ w ∈ K, (∏' i : {i // i ∉ t}, (1 + u i w)) ≠ 0) ∧
        ∀ w ∈ Ω, ∏' i, (1 + u i w) =
          (∏ i ∈ t, (1 + u i w)) * ∏' i : {i // i ∉ t}, (1 + u i w) := by
  obtain ⟨t, hfac, hprod⟩ := (htail K hKΩ hK).exists_finset_tprod_compl_one_add_ne_zero
  have htail_compl :
      ∀ L ⊆ Ω, IsCompact L → SummableUniformlyOn (fun (i : {i // i ∉ t}) z ↦ ‖u i z‖) L :=
    fun L hLΩ hL ↦ Summable.subtype (htail L hLΩ hL) (· ∉ t)
  refine ⟨t, analyticOnNhd_tprod_one_add hΩ (fun i ↦ hd i) htail_compl, hfac, hprod, fun w hw ↦ ?_⟩
  exact (prod_mul_tprod_compl_one_add
    ((htail {w} (singleton_subset_iff.mpr hw) isCompact_singleton).summable (mem_singleton w))
    t).symm

/-- At every point `z ∈ Ω`, at most finitely many factors `1 + u i` have nonzero `analyticOrderAt`
at `z`. -/
theorem finite_analyticOrderAt_one_add_ne_zero (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    {i : ι | analyticOrderAt (fun w ↦ 1 + u i w) z ≠ 0}.Finite := by
  obtain ⟨t, _, hfac, _, _⟩ := exists_finset_tprod_one_add_eq_prod_mul_compl hΩ hd htail
    (singleton_subset_iff.mpr hz) isCompact_singleton
  refine t.finite_toSet.subset fun i hi ↦ ?_
  by_contra hit
  have hana : AnalyticAt ℂ (fun w ↦ 1 + u i w) z :=
    analyticAt_const.add ((hd i).analyticOnNhd hΩ z hz)
  exact hi (hana.analyticOrderAt_eq_zero.mpr (hfac i hit z (mem_singleton z)))

/-- **Additivity of `analyticOrderAt` for holomorphic infinite products.** At every point `z ∈ Ω`,
the `ℕ∞`-valued analytic order of `w ↦ ∏' i, (1 + u i w)` at `z` equals the infinite sum of the
analytic orders of its factors, unconditionally (including `⊤` when some factor vanishes on a
neighborhood of `z`). -/
theorem analyticOrderAt_tprod_one_add (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑' i, analyticOrderAt (fun w ↦ 1 + u i w) z := by
  obtain ⟨t, hana_compl, hfac, hprod, hsplit⟩ :=
    exists_finset_tprod_one_add_eq_prod_mul_compl hΩ hd htail
      (singleton_subset_iff.mpr hz) isCompact_singleton
  have heq : (fun w ↦ ∏' i, (1 + u i w)) =ᶠ[𝓝 z]
      ((∏ i ∈ t, fun w ↦ 1 + u i w) * fun w ↦ ∏' i : {i // i ∉ t}, (1 + u i w)) := by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    simp [Finset.prod_apply, hsplit w hw]
  have hfac_ana (i : ι) : AnalyticAt ℂ (fun w ↦ 1 + u i w) z :=
    analyticAt_const.add ((hd i).analyticOnNhd hΩ z hz)
  have hhead_ana : AnalyticAt ℂ (∏ i ∈ t, fun w ↦ 1 + u i w) z :=
    Finset.analyticAt_prod _ fun i _ ↦ hfac_ana i
  have htail_ana : AnalyticAt ℂ (fun w ↦ ∏' i : {i // i ∉ t}, (1 + u i w)) z := hana_compl z hz
  have htail_ord : analyticOrderAt (fun w ↦ ∏' i : {i // i ∉ t}, (1 + u i w)) z = 0 :=
    htail_ana.analyticOrderAt_eq_zero.mpr (hprod z (mem_singleton z))
  have hfac_ord : ∀ i ∉ t, analyticOrderAt (fun w ↦ 1 + u i w) z = 0 := fun i hi ↦
    (hfac_ana i).analyticOrderAt_eq_zero.mpr (hfac i hi z (mem_singleton z))
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hhead_ana htail_ana, htail_ord, add_zero,
    analyticOrderAt_prod fun i _ ↦ hfac_ana i, tsum_eq_sum hfac_ord]

/-- If no factor `1 + u i` vanishes identically near `z ∈ Ω`, then neither does the infinite
product `∏' i, (1 + u i ·)`. -/
theorem analyticOrderAt_tprod_one_add_ne_top (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    {z : ℂ} (hz : z ∈ Ω) (htop : ∀ i, analyticOrderAt (fun w ↦ 1 + u i w) z ≠ ⊤) :
    analyticOrderAt (fun w ↦ ∏' i, (1 + u i w)) z ≠ ⊤ := by
  classical
  have hfin := finite_analyticOrderAt_one_add_ne_zero hΩ hd htail hz
  rw [analyticOrderAt_tprod_one_add hΩ hd htail hz,
    tsum_eq_sum (s := hfin.toFinset) fun i hi ↦ not_ne_iff.mp (by simpa using hi)]
  have hcast : ∑ i ∈ hfin.toFinset, analyticOrderAt (fun w ↦ 1 + u i w) z =
      ((∑ i ∈ hfin.toFinset, analyticOrderNatAt (fun w ↦ 1 + u i w) z : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.cast_analyticOrderNatAt (htop i)).symm
  rw [hcast]
  exact ENat.natCast_ne_top _

/-- Additivity of `analyticOrderNatAt` for a holomorphic infinite product at `z ∈ Ω` when no factor
vanishes identically near `z`. -/
theorem analyticOrderNatAt_tprod_one_add (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    {z : ℂ} (hz : z ∈ Ω) (htop : ∀ i, analyticOrderAt (fun w ↦ 1 + u i w) z ≠ ⊤) :
    analyticOrderNatAt (fun w ↦ ∏' i, (1 + u i w)) z =
      ∑' i, analyticOrderNatAt (fun w ↦ 1 + u i w) z := by
  classical
  have hfin := finite_analyticOrderAt_one_add_ne_zero hΩ hd htail hz
  have hzero_ord : ∀ i ∉ hfin.toFinset, analyticOrderAt (fun w ↦ 1 + u i w) z = 0 :=
    fun i hi ↦ not_ne_iff.mp (by simpa using hi)
  have hzero_nat : ∀ i ∉ hfin.toFinset, analyticOrderNatAt (fun w ↦ 1 + u i w) z = 0 := by
    intro i hi
    simp [analyticOrderNatAt, hzero_ord i hi]
  have hord := analyticOrderAt_tprod_one_add hΩ hd htail hz
  rw [tsum_eq_sum hzero_ord] at hord
  have hcast : ∑ i ∈ hfin.toFinset, analyticOrderAt (fun w ↦ 1 + u i w) z =
      ((∑ i ∈ hfin.toFinset, analyticOrderNatAt (fun w ↦ 1 + u i w) z : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.cast_analyticOrderNatAt (htop i)).symm
  rw [analyticOrderNatAt, hord, hcast, ENat.toNat_natCast, tsum_eq_sum hzero_nat]

/-- **Additivity of `MeromorphicOn.divisor` for holomorphic infinite products.** At any `z ∈ Ω`
where no factor `1 + u i` vanishes identically nearby, the divisor multiplicity of
`w ↦ ∏' i, (1 + u i w)` at `z` equals the finitely supported sum of the factor multiplicities. -/
theorem divisor_tprod_one_add_apply (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    {z : ℂ} (hz : z ∈ Ω) (htop : ∀ i, analyticOrderAt (fun w ↦ 1 + u i w) z ≠ ⊤) :
    MeromorphicOn.divisor (fun w ↦ ∏' i, (1 + u i w)) Ω z =
      ∑ᶠ i, MeromorphicOn.divisor (fun w ↦ 1 + u i w) Ω z := by
  classical
  have hana_prod := analyticOnNhd_tprod_one_add hΩ hd htail
  have hana_fac (i : ι) : AnalyticOnNhd ℂ (fun w ↦ 1 + u i w) Ω :=
    fun w hw ↦ analyticAt_const.add ((hd i).analyticOnNhd hΩ w hw)
  have hdiv_fac (i : ι) : MeromorphicOn.divisor (fun w ↦ 1 + u i w) Ω z =
      (analyticOrderNatAt (fun w ↦ 1 + u i w) z : ℤ) :=
    (hana_fac i).meromorphicOn.divisor_eq_analyticOrderNatAt (hana_fac i z hz) hz
  have hfin := finite_analyticOrderAt_one_add_ne_zero hΩ hd htail hz
  have hzero_nat : ∀ i ∉ hfin.toFinset, analyticOrderNatAt (fun w ↦ 1 + u i w) z = 0 := by
    intro i hi
    have h0 : analyticOrderAt (fun w ↦ 1 + u i w) z = 0 := not_ne_iff.mp (by simpa using hi)
    simp [analyticOrderNatAt, h0]
  have hsupp : Function.support (fun i ↦ MeromorphicOn.divisor (fun w ↦ 1 + u i w) Ω z) ⊆
      (hfin.toFinset : Set ι) := by
    intro i hi
    by_contra hit
    exact hi (by simp [hdiv_fac i, hzero_nat i hit])
  rw [hana_prod.meromorphicOn.divisor_eq_analyticOrderNatAt (hana_prod z hz) hz,
    analyticOrderNatAt_tprod_one_add hΩ hd htail hz htop,
    tsum_eq_sum hzero_nat, finsum_eq_sum_of_support_subset _ hsupp, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (hdiv_fac i).symm

/-- **Locally uniform logarithmic derivative of `∏' i, (1 + u i z)`.** On any subset `V ⊆ Ω` where
every factor `1 + u i` is nonzero, the series `∑' i, deriv (u i) z / (1 + u i z)` converges locally
uniformly on `V` to `logDeriv (fun z ↦ ∏' i, (1 + u i z))`. Nonvanishing of the infinite product on
`V` is automatic from `SummableUniformlyOn.tprod_one_add_eq_zero_iff`. -/
theorem hasSumLocallyUniformlyOn_logDeriv_one_add (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    (hVΩ : V ⊆ Ω) (hu₀ : ∀ i, ∀ z ∈ V, 1 + u i z ≠ 0) :
    HasSumLocallyUniformlyOn (fun i z ↦ deriv (u i) z / (1 + u i z))
      (logDeriv (fun z ↦ ∏' i, (1 + u i z))) V := by
  have hprod := hasProdLocallyUniformlyOn_one_add_of_forall_isCompact hΩ htail
    fun i ↦ (hd i).continuousOn
  have hd1 : ∀ i, DifferentiableOn ℂ (fun z ↦ 1 + u i z) Ω := fun i ↦ (hd i).const_add 1
  have hF₀ : ∀ z ∈ V, (∏' i, (1 + u i z)) ≠ 0 := by
    intro z hz hzero
    obtain ⟨i, hi⟩ :=
      ((htail {z} (singleton_subset_iff.mpr (hVΩ hz)) isCompact_singleton)
        |>.tprod_one_add_eq_zero_iff (mem_singleton z)).mp hzero
    exact hu₀ i z hz hi
  have hsum := hprod.hasSumLocallyUniformlyOn_logDeriv hΩ hd1 hVΩ hu₀ hF₀
  have hfun : (fun i ↦ logDeriv (fun z ↦ 1 + u i z)) = fun i z ↦ deriv (u i) z / (1 + u i z) := by
    ext i z
    rw [logDeriv_apply, deriv_const_add]
  rwa [hfun] at hsum

/-- Pointwise logarithmic-derivative expansion
`logDeriv (fun w ↦ ∏' i, (1 + u i w)) z = ∑' i, deriv (u i) z / (1 + u i z)` at any `z ∈ Ω` where
all factors `1 + u i z` are nonzero. -/
theorem logDeriv_tprod_one_add (hΩ : IsOpen Ω)
    (hd : ∀ i, DifferentiableOn ℂ (u i) Ω)
    (htail : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i z ↦ ‖u i z‖) K)
    {z : ℂ} (hz : z ∈ Ω) (hu₀ : ∀ i, 1 + u i z ≠ 0) :
    logDeriv (fun w ↦ ∏' i, (1 + u i w)) z = ∑' i, deriv (u i) z / (1 + u i z) :=
  ((hasSumLocallyUniformlyOn_logDeriv_one_add hΩ hd htail (singleton_subset_iff.mpr hz)
    fun i _ hw ↦ mem_singleton_iff.mp hw ▸ hu₀ i).hasSum (mem_singleton z)).tsum_eq.symm

end GeneralIndex

section SequentialNat

variable {u : ℕ → ℂ → ℂ} {Ω : Set ℂ}

/-- If `u n` is holomorphic on an open set `Ω ⊆ ℂ`, `∑' n, ‖u n z‖` converges on `Ω`, and the
sequential tails `∑' k, ‖u (k + N) z‖` vanish uniformly on every compact subset `K ⊆ Ω`, then
`z ↦ ∏' n, (1 + u n z)` is holomorphic on `Ω`. -/
theorem differentiableOn_tprod_nat_one_add_of_tail_lt (hΩ : IsOpen Ω)
    (hd : ∀ n, DifferentiableOn ℂ (u n) Ω)
    (hsum : ∀ z ∈ Ω, Summable fun n ↦ ‖u n z‖)
    (htail : ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, ∑' k, ‖u (k + N) z‖ < ε) :
    DifferentiableOn ℂ (fun z ↦ ∏' n, (1 + u n z)) Ω :=
  differentiableOn_tprod_one_add hΩ hd fun K hKΩ hK ↦
    (summableUniformlyOn_nat_iff_tail_tsum_lt fun _ _ _ ↦ norm_nonneg _).mpr
      ⟨fun z hz ↦ hsum z (hKΩ hz), htail K hKΩ hK⟩

/-- Sequential-tail version of `TauCeti.analyticOrderAt_tprod_one_add` for `ℕ`-indexed holomorphic
products on an open set `Ω ⊆ ℂ`. -/
theorem analyticOrderAt_tprod_nat_one_add_of_tail_lt (hΩ : IsOpen Ω)
    (hd : ∀ n, DifferentiableOn ℂ (u n) Ω)
    (hsum : ∀ z ∈ Ω, Summable fun n ↦ ‖u n z‖)
    (htail : ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, ∑' k, ‖u (k + N) z‖ < ε)
    {z : ℂ} (hz : z ∈ Ω) :
    analyticOrderAt (fun w ↦ ∏' n, (1 + u n w)) z =
      ∑' n, analyticOrderAt (fun w ↦ 1 + u n w) z :=
  analyticOrderAt_tprod_one_add hΩ hd
    (fun K hKΩ hK ↦ (summableUniformlyOn_nat_iff_tail_tsum_lt fun _ _ _ ↦ norm_nonneg _).mpr
      ⟨fun w hw ↦ hsum w (hKΩ hw), htail K hKΩ hK⟩) hz

end SequentialNat

end TauCeti

/-! ### Degenerate zero-factor check

When one factor `1 + u 0` vanishes identically (`u 0 = -1`, `u (n + 1) = 0`), the infinite product
vanishes identically on `ℂ` and `TauCeti.analyticOrderAt_tprod_one_add` evaluates to `⊤ = ⊤` in
`ℕ∞`. -/

example (z : ℂ) :
    let u : ℕ → ℂ → ℂ := fun n _ ↦ if n = 0 then -1 else 0
    analyticOrderAt (fun w ↦ ∏' n, (1 + u n w)) z = ⊤ ∧
      (∑' n, analyticOrderAt (fun w ↦ 1 + u n w) z) = ⊤ := by
  intro u
  have hd : ∀ n, DifferentiableOn ℂ (u n) Set.univ := fun n ↦ by
    by_cases h : n = 0 <;> simp [u, h, differentiableOn_const]
  have hsum : ∀ w ∈ (Set.univ : Set ℂ), Summable fun n ↦ ‖u n w‖ := by
    refine fun _ _ ↦ summable_of_ne_finset_zero (s := {0}) fun n hn ↦ ?_
    simp only [Finset.mem_singleton] at hn
    simp [u, hn]
  have htail : ∀ K ⊆ (Set.univ : Set ℂ), IsCompact K →
      ∀ ε > 0, ∃ N : ℕ, ∀ w ∈ K, ∑' k, ‖u (k + N) w‖ < ε :=
    fun _ _ _ _ hε ↦ ⟨1, fun _ _ ↦ by simpa [u] using hε⟩
  have h0 : analyticOrderAt (fun w ↦ 1 + u 0 w) z = ⊤ := by
    have hzero : (fun w : ℂ ↦ 1 + u 0 w) = 0 := by ext w; simp [u]
    simp [hzero]
  have hsucc (n : ℕ) : analyticOrderAt (fun w ↦ 1 + u (n + 1) w) z = 0 := by
    have hone : (fun w : ℂ ↦ 1 + u (n + 1) w) = fun _ ↦ (1 : ℂ) := by ext w; simp [u]
    rw [hone]
    exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  have htsum : (∑' n, analyticOrderAt (fun w ↦ 1 + u n w) z) = ⊤ := by
    rw [tsum_eq_single 0]
    · exact h0
    · rintro (_ | n) hn
      · exact (hn rfl).elim
      · exact hsucc n
  exact ⟨(TauCeti.analyticOrderAt_tprod_nat_one_add_of_tail_lt isOpen_univ hd hsum htail
      (mem_univ z)).trans htsum, htsum⟩
