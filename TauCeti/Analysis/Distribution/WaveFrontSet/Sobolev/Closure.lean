/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.RapidDecay

/-!
# The wave front set as the closure of the Sobolev wave front sets

A complex distribution `T` on an open set `Ω` that is microlocally smooth at `(x, ξ)` is
microlocally `H^s` there for every real `s`
(`Distribution.IsMicrolocallySmoothAt.isMicrolocallySobolevAt`). This file proves the converse,
which needs a neighbourhood independent of `s`: `T` is microlocally smooth at `(x, ξ)` exactly
when, for every `s`, it is microlocally `H^s` at every point of a neighbourhood of `(x, ξ)` that
does not depend on `s`
(`Distribution.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt`).
Equivalently, the wave front set is the closure of the union of the `H^s` wave front sets inside
`Ω × (E \ {0})`:

`WF(T) = (Ω × (E \ {0})) ∩ closure (⋃ s, WF_s(T))`

(`Distribution.waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet`). The closure is needed:
covectors at which `T` has singularities of ever higher Sobolev regularity can accumulate at a
covector `(x, ξ)` at which `T` is microlocally `H^s` for every `s`. In particular `T` has empty
wave front set exactly when every `H^s` wave front set is empty
(`Distribution.waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty`).

This is how microlocal regularity on the Sobolev scale yields microlocal smoothness: combined with
a microlocal elliptic regularity estimate `WF_{s+m}(u) ⊆ WF_s(P u) ∪ Char(P)` valid for every `s`,
it gives `WF(u) ⊆ WF(P u) ∪ Char(P)`, since `WF(P u) ∪ Char(P)` is closed in `Ω × (E \ {0})`.

## The argument

Suppose `T` is microlocally `H^s` for every `s` on a neighbourhood of `(x, ξ)`, which contains
`closedBall x r ×ˢ closedBall ξ r` for some `r > 0`.

* **One cutoff and one cone for every order.** Fix `s`. The neighbourhoods and cones provided by
  `Distribution.IsMicrolocallySobolevAt.exists_nhds_cone` at the points of this compact set have
  finite subcovers, first in the frequency and then in the position. A partition of unity then
  shows that every cutoff supported in `ball x r` has weighted localized Fourier transform
  `⟨η⟩ ^ s T (ψ e_η)` square integrable on the open cone `Γ` over `ball ξ r`. Neither `ball x r`
  nor `Γ` depends on `s`
  (`Distribution.exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt`).
* **From square integrability of every order to rapid decay.** The localized Fourier transform
  `F = T (φ e_·)` is Lipschitz with a polynomially growing constant:
  `‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`
  (`Distribution.exists_norm_localFourier_sub_le`), because `φ e_η - φ e_ζ` is `φ (1 - e_(ζ - η))`
  times `e_η`. On the closed ball of radius `δ = (1 + ‖η‖) ^ (-M)` about `η` the value `F η` is
  therefore within `A (1 + ‖η‖) ^ (k - M)` of `F`, and averaging `‖F‖ ^ 2` over that ball, which
  lies in `Γ` for `η` in a smaller cone, bounds `‖F η‖ ^ 2` by
  `δ ^ (-n) (1 + ‖η‖) ^ (-2 s)` times the weighted `L²` norm, plus `A² (1 + ‖η‖) ^ (2 (k - M))`.
  For `M` and then `s` large both terms are `O((1 + ‖η‖) ^ (-2 N))`
  (`TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp`).

## Main results

* `Distribution.exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt`: one
  neighbourhood and one cone serve for every Sobolev order.
* `Distribution.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt`,
  `Distribution.waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet`,
  `Distribution.waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty`: the wave front set
  from the Sobolev wave front sets.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex Filter Function Metric MeasureTheory Module Set TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff RealInnerProductSpace

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **One cutoff and one cone for every Sobolev order.** If `T` is microlocally `H^s` for every
`s` at every point of a neighbourhood of `(x, ξ)`, then there are a neighbourhood `U` of `x` and an
open cone `Γ` containing `ξ`, both independent of `s`, such that for every `s` and every cutoff `ψ`
supported in `U` the weighted localized Fourier transform `⟨η⟩ ^ s T (ψ e_η)` is square integrable
on `Γ`. -/
theorem exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : ∀ᶠ p in 𝓝 (x, ξ), ∀ s, T.IsMicrolocallySobolevAt s p.1 p.2) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ s : ℝ, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
        MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 (volume.restrict Γ) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 h
  set r := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hreg : ∀ y ∈ closedBall x r, ∀ η ∈ closedBall ξ r, ∀ s,
      T.IsMicrolocallySobolevAt s y η := fun y hy η hη ↦ hball (show (y, η) ∈ ball (x, ξ) ρ by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (lt_of_le_of_lt hy (half_lt_self hρ)) (lt_of_le_of_lt hη (half_lt_self hρ)))
  -- `Γ` is the open cone over `ball ξ r`.
  obtain ⟨Γ, hΓ, hξΓ, hcone, hmem⟩ :=
    IsOpen.exists_cone_exists_smul_mem (isOpen_ball (x := ξ)) (mem_ball_self hr)
  refine ⟨ball x r, ball_mem_nhds x hr, Γ, hΓ, hξΓ, hcone, fun s ↦ ?_⟩
  -- Over each point of `closedBall x r`: finitely many cones cover `closedBall ξ r`, hence `Γ`.
  have hinner : ∀ y ∈ closedBall x r, ∃ V ∈ 𝓝 y, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ V →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 (volume.restrict Γ) := by
    intro y hy
    choose U hU Γ' hΓ' hηΓ' hcone' hL using fun η : closedBall ξ r ↦
      (hreg y hy η η.property s).exists_nhds_cone
    obtain ⟨t, ht⟩ := (isCompact_closedBall ξ r).elim_finite_subcover
      (fun η : closedBall ξ r ↦ Γ' η) hΓ' fun η hη ↦ mem_iUnion.2 ⟨⟨η, hη⟩, hηΓ' _⟩
    refine ⟨⋂ η ∈ t, U η, (biInter_finset_mem t).2 fun η _ ↦ hU η, fun ψ hψ ↦ ?_⟩
    refine MemLp.restrict_of_subset_iUnion (t := fun η : t ↦ Γ' η) (fun ζ hζ ↦ ?_)
      fun η ↦ hL η ψ (hψ.trans (biInter_subset_of_mem η.property))
    obtain ⟨u, hu, huζ⟩ := hmem ζ hζ
    obtain ⟨η, hηt, hη⟩ := mem_iUnion₂.1 (ht (ball_subset_closedBall huζ))
    refine mem_iUnion.2 ⟨⟨η, hηt⟩, ?_⟩
    simpa [smul_smul, inv_mul_cancel₀ hu.ne'] using hcone' η u⁻¹ (inv_pos.2 hu) _ hη
  choose! V hV hVL using hinner
  -- A partition of unity reduces a cutoff supported in `ball x r` to these neighbourhoods.
  intro ψ hψ
  have hcover : tsupport ψ ⊆ ⋃ y : closedBall x r, interior (V y) := fun z hz ↦
    have hz' : z ∈ closedBall x r := ball_subset_closedBall (hψ hz)
    mem_iUnion.2 ⟨⟨z, hz'⟩, mem_interior_iff_mem_nhds.2 (hV z hz')⟩
  obtain ⟨t, ψ', hψ'supp, hψ'sum, -⟩ :=
    ψ.exists_sum_subordinate _ (fun _ ↦ isOpen_interior) hcover
  have hsum : ∀ η, T.localFourier ψ η = ∑ i, T.localFourier (ψ' i) η := fun η ↦ by
    rw [← hψ'sum, localFourier_sum_cutoff]
  simp_rw [hsum, Finset.smul_sum]
  exact memLp_finsetSum _ fun i _ ↦ hVL _ i.val.property _ ((hψ'supp i).trans interior_subset)

/-- **Microlocal smoothness from every Sobolev order.** If `T` is microlocally `H^s` for every
`s` at every point of a neighbourhood of `(x, ξ)`, then `T` is microlocally smooth at `(x, ξ)`. -/
theorem isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} (h : ∀ᶠ p in 𝓝 (x, ξ), ∀ s, T.IsMicrolocallySobolevAt s p.1 p.2) :
    T.IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 (h.self_of_nhds 0)
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hL⟩ :=
    exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  obtain ⟨A, k, hLip⟩ := exists_norm_localFourier_sub_le T φ
  exact isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ', hΓ'o, hξ', hcone', fun N ↦
    TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp hLip hc hΓ'
      (fun s ↦ hL s φ (hφ.trans inter_subset_left)) N⟩

/-- A complex distribution is microlocally smooth at `(x, ξ)` exactly when, for every `s`, it is
microlocally `H^s` at every point of a neighbourhood of `(x, ξ)` that does not depend on `s`. -/
theorem isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} :
    T.IsMicrolocallySmoothAt x ξ ↔ ∀ᶠ p in 𝓝 (x, ξ), ∀ s, T.IsMicrolocallySobolevAt s p.1 p.2 :=
  ⟨fun h ↦ Filter.mem_of_superset
    (T.isOpen_setOf_isMicrolocallySmoothAt.mem_nhds (x := (x, ξ)) h) fun _ hp s ↦
      hp.isMicrolocallySobolevAt s,
    isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt⟩

/-- **The wave front set is the closure of the union of the `H^s` wave front sets** inside
`Ω × (E \ {0})`. The closure is needed, because covectors at which `T` has singularities of ever
higher Sobolev regularity can accumulate. -/
theorem waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet = ((Ω : Set E) ×ˢ {0}ᶜ) ∩ closure (⋃ s, T.sobolevWaveFrontSet s) := by
  ext ⟨x, ξ⟩
  rw [mem_waveFrontSet_iff, mem_inter_iff, mem_prod, mem_compl_singleton_iff]
  refine ⟨fun ⟨hx, hξ, hT⟩ ↦ ⟨⟨hx, hξ⟩, mem_closure_iff_nhds.2 fun W hW ↦ ?_⟩,
    fun ⟨⟨hx, hξ⟩, hcl⟩ ↦ ⟨hx, hξ, fun hT ↦ ?_⟩⟩
  · -- Otherwise `T` is microlocally `H^s` for every `s` on a neighbourhood of `(x, ξ)`.
    by_contra hW'
    refine hT (isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt ?_)
    filter_upwards [hW, (Ω.isOpen.prod isOpen_compl_singleton).mem_nhds (mem_prod.2 ⟨hx, hξ⟩)]
      with ⟨y, η⟩ hpW hp s
    by_contra hs
    rw [mem_prod, mem_compl_singleton_iff] at hp
    exact hW' ⟨(y, η), hpW, mem_iUnion.2 ⟨s, mem_sobolevWaveFrontSet_iff.2 ⟨hp.1, hp.2, hs⟩⟩⟩
  · obtain ⟨p, hp, hpS⟩ := mem_closure_iff_nhds.1 hcl _
      (isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt.1 hT)
    obtain ⟨s, hs⟩ := mem_iUnion.1 hpS
    exact (mem_sobolevWaveFrontSet_iff.1 hs).2.2 (hp s)

/-- A complex distribution has empty wave front set exactly when all its `H^s` wave front sets are
empty. -/
theorem waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet = ∅ ↔ ∀ s, T.sobolevWaveFrontSet s = ∅ := by
  refine ⟨fun h s ↦ subset_empty_iff.1 (h ▸ T.sobolevWaveFrontSet_subset_waveFrontSet s),
    fun h ↦ ?_⟩
  rw [waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet]
  simp [h]

end Distribution
