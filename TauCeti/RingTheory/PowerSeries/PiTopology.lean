/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Infinite products and the `(X)`-adic topology on power series

If all but finitely many factors agree with `1` to each prescribed degree, their product
converges coefficientwise. Each coefficient is computed from any finite cutoff containing all
factors that can affect it. Over a discrete commutative ring, the coefficientwise topology on
`R⟦X⟧` coincides with the `(X)`-adic topology.

## Main results

* `PowerSeries.WithPiTopology.hasProd_of_X_pow_dvd_sub_one`: convergence and finite-cutoff
  coefficients for products whose factors approach `1` modulo increasing powers of `X`.
* `PowerSeries.WithPiTopology.isAdic_span_X`: over a discrete commutative ring, the
  coefficientwise topology on `R⟦X⟧` is `(X)`-adic.
-/

public section

open Finset

namespace PowerSeries.WithPiTopology

open scoped PowerSeries.WithPiTopology Topology

variable {R ι : Type*} [CommRing R] [TopologicalSpace R]

/-- **Infinite products through finite cutoffs.** If, for each `n`, every factor `g i` with
`i ∉ F n` is congruent to `1` modulo `X ^ (n + 1)`, then the product of all the `g i` converges
in the coefficientwise topology, and its `n`-th coefficient is that of `∏ i ∈ F n, g i`. -/
theorem hasProd_of_X_pow_dvd_sub_one {g : ι → R⟦X⟧} (F : ℕ → Finset ι)
    (hF : ∀ n i, i ∉ F n → X ^ (n + 1) ∣ g i - 1) :
    HasProd g (mk fun n ↦ coeff n (∏ i ∈ F n, g i)) := by
  classical
  rw [HasProd, tendsto_iff_coeff_tendsto]
  refine fun n ↦ tendsto_atTop_of_eventually_const (i₀ := F n) fun s hs ↦ ?_
  rw [coeff_mk]
  exact coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one hs fun i hi ↦ hF n i (mem_sdiff.1 hi).2

/-- **The coefficientwise topology over a discrete ring is `(X)`-adic.** -/
theorem isAdic_span_X [DiscreteTopology R] :
    IsAdic (Ideal.span {(X : R⟦X⟧)}) := by
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have hset : ((Ideal.span {(X : R⟦X⟧)} ^ n : Ideal R⟦X⟧) : Set R⟦X⟧) =
        ⋂ d ∈ Finset.range n, (coeff (R := R) d) ⁻¹' {0} := by
      ext f
      simp only [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        X_pow_dvd_iff, Set.mem_iInter, Finset.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hset]
    exact isOpen_biInter_finset fun d _ ↦
      (isOpen_discrete _).preimage (continuous_coeff R d)
  · let f : ℕ → Set R⟦X⟧ := fun n ↦ ((Ideal.span {(X : R⟦X⟧)} ^ n : Ideal R⟦X⟧) : Set R⟦X⟧)
    have hf_anti : Antitone f := fun _ _ h ↦ Ideal.pow_le_pow_right h
    have hle : (⨅ n, Filter.principal (f n)) ≤ 𝓝 (0 : R⟦X⟧) := by
      rw [← Filter.tendsto_id', tendsto_iff_coeff_tendsto]
      intro d
      rw [map_zero, nhds_discrete, Filter.tendsto_pure]
      refine Filter.mem_iInf_of_mem (d + 1) (Filter.mem_principal.mpr fun g hg ↦ ?_)
      rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        X_pow_dvd_iff] at hg
      exact hg d (Nat.lt_succ_self d)
    have hdir : Directed (· ≥ ·) (fun n ↦ Filter.principal (f n)) := fun i j ↦
      ⟨max i j, Filter.principal_mono.mpr (hf_anti (le_max_left _ _)),
        Filter.principal_mono.mpr (hf_anti (le_max_right _ _))⟩
    simpa only [Filter.mem_principal] using (Filter.mem_iInf_of_directed hdir s).mp (hle hs)

end PowerSeries.WithPiTopology
