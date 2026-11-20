/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Locally uniform convergence of logarithmic derivatives

Mathlib's `Complex.logDeriv_tendsto` and `logDeriv_tprod_eq_tsum` establish only *pointwise*
convergence of logarithmic derivatives of locally uniformly convergent holomorphic sequences and
infinite products, and `logDeriv_tprod_eq_tsum` additionally assumes that the termwise
logarithmic-derivative series is already `Summable`.

This file upgrades both results to locally uniform convergence on any zero-free subset `V` of the
open domain `U ⊆ ℂ` (and uniform convergence on compact zero-free subsets `K ⊆ U`), while removing
the redundant summability hypothesis on termwise logarithmic derivatives.

## Main results

* `TendstoLocallyUniformlyOn.logDeriv`: if holomorphic functions `F n` converge locally uniformly to
  `f` on an open set `U ⊆ ℂ`, then `logDeriv (F n)` converges locally uniformly to `logDeriv f` on
  every subset `V ⊆ U` where `f` has no zeros.
* `TendstoLocallyUniformlyOn.tendstoUniformlyOn_logDeriv_of_isCompact`: uniform convergence of
  `logDeriv (F n)` to `logDeriv f` on compact zero-free subsets `K ⊆ U`.
* `TendstoLocallyUniformlyOn.sum_logDeriv`: for finite partial products indexed along an arbitrary
  filter (covering both sequential/symmetric partial products and unordered finite-subset products),
  the finite sums of logarithmic derivatives converge locally uniformly to `logDeriv F` on subsets
  `V ⊆ U` where the factors and limit do not vanish.
* `HasProdLocallyUniformlyOn.hasSumLocallyUniformlyOn_logDeriv`: for an unordered holomorphic
  infinite product `HasProdLocallyUniformlyOn f F U`, the series `∑' i, logDeriv (f i)` converges
  locally uniformly to `logDeriv F` on any `V ⊆ U` where all `f i` and `F` are nonzero.
* `HasProdLocallyUniformlyOn.hasSum_logDeriv`, `HasProdLocallyUniformlyOn.summable_logDeriv`,
  `HasProdLocallyUniformlyOn.logDeriv_eq_tsum`, and
  `MultipliableLocallyUniformlyOn.logDeriv_tprod_eq_tsum`: unconditional pointwise `HasSum`,
  `Summable`, and `tsum` identities at any point `z ∈ U` where the factors and product are nonzero.

## References

* A. Rainer, *Advanced Complex Analysis* (lecture notes, University of Vienna, 2022), Remark 15.4.
* J. B. Conway, *Functions of One Complex Variable I*, 2nd ed., Springer, 1978, §VII.5.
-/

public section

open Complex Filter Set Topology
open scoped BigOperators

namespace TendstoLocallyUniformlyOn

variable {ι κ : Type*} {l : Filter κ}

/-- **Locally uniform convergence of logarithmic derivatives.** If `F a` converges locally uniformly
to `f` on an open set `U ⊆ ℂ` and `F a` is eventually holomorphic on `U`, then `logDeriv (F a)`
converges locally uniformly to `logDeriv f` on any subset `V ⊆ U` (not necessarily open) where `f`
does not vanish. -/
protected theorem logDeriv {F : κ → ℂ → ℂ} {f : ℂ → ℂ} {U V : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f l U) (hU : IsOpen U)
    (hd : ∀ᶠ a in l, DifferentiableOn ℂ (F a) U) (hVU : V ⊆ U) (hf₀ : ∀ z ∈ V, f z ≠ 0) :
    TendstoLocallyUniformlyOn (fun a ↦ logDeriv (F a)) (logDeriv f) l V := by
  rcases l.eq_or_neBot with rfl | _
  · intro u _ x _
    exact ⟨V, self_mem_nhdsWithin, eventually_bot⟩
  · have hdf : DifferentiableOn ℂ f U := hF.differentiableOn hd hU
    exact ((hF.deriv hd hU).mono hVU).div₀ (hF.mono hVU)
      ((hdf.deriv hU).continuousOn.mono hVU) (hdf.continuousOn.mono hVU) hf₀

/-- **Uniform convergence of logarithmic derivatives on compact zero-free subsets.** -/
theorem tendstoUniformlyOn_logDeriv_of_isCompact {F : κ → ℂ → ℂ} {f : ℂ → ℂ} {U K : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f l U) (hU : IsOpen U)
    (hd : ∀ᶠ a in l, DifferentiableOn ℂ (F a) U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf₀ : ∀ z ∈ K, f z ≠ 0) :
    TendstoUniformlyOn (fun a ↦ logDeriv (F a)) (logDeriv f) l K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hF.logDeriv hU hd hKU hf₀)

/-- **Locally uniform logarithmic differentiation of finite partial products.** Let
`I : κ → Finset ι` be any family of finite index sets (for instance `Finset.range` for sequential
partial products, symmetric intervals for paired products, or `id` for unordered products). If the
partial products `∏ i ∈ I a, f i z` of holomorphic functions on an open set `U ⊆ ℂ` converge locally
uniformly on `U` to `F`, then `∑ i ∈ I a, logDeriv (f i) z` converges locally uniformly to
`logDeriv F` on any subset `V ⊆ U` where all factors `f i` and the limit `F` are nonzero. -/
theorem sum_logDeriv {I : κ → Finset ι} {f : ι → ℂ → ℂ} {F : ℂ → ℂ} {U V : Set ℂ}
    (hF : TendstoLocallyUniformlyOn (fun a z ↦ ∏ i ∈ I a, f i z) F l U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) (hVU : V ⊆ U)
    (hf₀ : ∀ i, ∀ z ∈ V, f i z ≠ 0) (hF₀ : ∀ z ∈ V, F z ≠ 0) :
    TendstoLocallyUniformlyOn (fun a z ↦ ∑ i ∈ I a, logDeriv (f i) z)
      (logDeriv F) l V := by
  have hd_prod : ∀ᶠ a in l, DifferentiableOn ℂ (fun z ↦ ∏ i ∈ I a, f i z) U :=
    .of_forall fun _ ↦ by fun_prop
  refine (hF.logDeriv hU hd_prod hVU hF₀).congr fun a z hz ↦ ?_
  exact logDeriv_fun_prod (fun i _ ↦ hf₀ i z hz)
    fun i _ ↦ (hd i).differentiableAt (hU.mem_nhds (hVU hz))

end TendstoLocallyUniformlyOn

namespace HasProdLocallyUniformlyOn

variable {ι : Type*} {f : ι → ℂ → ℂ} {F : ℂ → ℂ} {U V K : Set ℂ}

/-- **Term-by-term logarithmic differentiation of locally uniformly convergent holomorphic
products.** If `HasProdLocallyUniformlyOn f F U` holds on an open set `U ⊆ ℂ` with each `f i`
holomorphic on `U`, then `∑' i, logDeriv (f i)` converges locally uniformly to `logDeriv F` on any
subset `V ⊆ U` where every factor `f i` and the limit `F` are nonzero. -/
theorem hasSumLocallyUniformlyOn_logDeriv (hF : HasProdLocallyUniformlyOn f F U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) (hVU : V ⊆ U)
    (hf₀ : ∀ i, ∀ z ∈ V, f i z ≠ 0) (hF₀ : ∀ z ∈ V, F z ≠ 0) :
    HasSumLocallyUniformlyOn (fun i ↦ logDeriv (f i)) (logDeriv F) V :=
  TendstoLocallyUniformlyOn.sum_logDeriv (I := id) hF hU hd hVU hf₀ hF₀

/-- Uniform convergence of `∑' i, logDeriv (f i)` to `logDeriv F` on a compact subset `K ⊆ U` on
which every `f i` and `F` are nonzero. -/
theorem hasSumUniformlyOn_logDeriv_of_isCompact (hF : HasProdLocallyUniformlyOn f F U)
    (hU : IsOpen U) (hd : ∀ i, DifferentiableOn ℂ (f i) U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf₀ : ∀ i, ∀ z ∈ K, f i z ≠ 0) (hF₀ : ∀ z ∈ K, F z ≠ 0) :
    HasSumUniformlyOn (fun i ↦ logDeriv (f i)) (logDeriv F) K := by
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
  exact hF.hasSumLocallyUniformlyOn_logDeriv hU hd hKU hf₀ hF₀

/-- Pointwise `HasSum` for the logarithmic derivative of a locally uniformly convergent holomorphic
product at a single point `z ∈ U` where all `f i z` and `F z` are nonzero, with no prior summability
assumption on `fun i ↦ logDeriv (f i) z`. -/
theorem hasSum_logDeriv (hF : HasProdLocallyUniformlyOn f F U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) {z : ℂ} (hz : z ∈ U)
    (hf₀ : ∀ i, f i z ≠ 0) (hF₀ : F z ≠ 0) :
    HasSum (fun i ↦ logDeriv (f i) z) (logDeriv F z) :=
  (hF.hasSumLocallyUniformlyOn_logDeriv hU hd (singleton_subset_iff.mpr hz)
    (fun i _ hw ↦ mem_singleton_iff.mp hw ▸ hf₀ i)
    (fun _ hw ↦ mem_singleton_iff.mp hw ▸ hF₀)).hasSum (mem_singleton z)

/-- Pointwise summability of `fun i ↦ logDeriv (f i) z` for a locally uniformly convergent
holomorphic product at `z ∈ U` where all `f i z` and `F z` are nonzero. -/
theorem summable_logDeriv (hF : HasProdLocallyUniformlyOn f F U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) {z : ℂ} (hz : z ∈ U)
    (hf₀ : ∀ i, f i z ≠ 0) (hF₀ : F z ≠ 0) :
    Summable fun i ↦ logDeriv (f i) z :=
  (hF.hasSum_logDeriv hU hd hz hf₀ hF₀).summable

/-- Pointwise `tsum` formula `logDeriv F z = ∑' i, logDeriv (f i) z` for a locally uniformly
convergent holomorphic product, without assuming `Summable fun i ↦ logDeriv (f i) z`. -/
theorem logDeriv_eq_tsum (hF : HasProdLocallyUniformlyOn f F U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) {z : ℂ} (hz : z ∈ U)
    (hf₀ : ∀ i, f i z ≠ 0) (hF₀ : F z ≠ 0) :
    logDeriv F z = ∑' i, logDeriv (f i) z :=
  (hF.hasSum_logDeriv hU hd hz hf₀ hF₀).tsum_eq.symm

end HasProdLocallyUniformlyOn

namespace MultipliableLocallyUniformlyOn

variable {ι : Type*} {f : ι → ℂ → ℂ} {U V : Set ℂ}

/-- Existential-product form of `HasProdLocallyUniformlyOn.hasSumLocallyUniformlyOn_logDeriv`. -/
theorem hasSumLocallyUniformlyOn_logDeriv (h : MultipliableLocallyUniformlyOn f U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) (hVU : V ⊆ U)
    (hf₀ : ∀ i, ∀ z ∈ V, f i z ≠ 0) (hF₀ : ∀ z ∈ V, (∏' i, f i z) ≠ 0) :
    HasSumLocallyUniformlyOn (fun i ↦ logDeriv (f i)) (logDeriv (∏' i, f i ·)) V :=
  h.hasProdLocallyUniformlyOn.hasSumLocallyUniformlyOn_logDeriv hU hd hVU hf₀ hF₀

/-- Strengthening of Mathlib's `logDeriv_tprod_eq_tsum` that drops the redundant hypothesis
`Summable fun i ↦ logDeriv (f i) z`. -/
theorem logDeriv_tprod_eq_tsum (h : MultipliableLocallyUniformlyOn f U) (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) {z : ℂ} (hz : z ∈ U)
    (hf₀ : ∀ i, f i z ≠ 0) (hF₀ : (∏' i, f i z) ≠ 0) :
    logDeriv (∏' i, f i ·) z = ∑' i, logDeriv (f i) z :=
  h.hasProdLocallyUniformlyOn.logDeriv_eq_tsum hU hd hz hf₀ hF₀

end MultipliableLocallyUniformlyOn
