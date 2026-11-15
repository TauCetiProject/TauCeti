/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Hermite
public import TauCeti.Probability.Process.DyadicGrid
import TauCeti.Probability.BrownianMotion.RightContinuity

/-!
# Density of dyadic Hermite products for Brownian claims

For a Brownian motion `W` and a positive time `T`, consider the standardized increments
`(W_{t_{k+1}} - W_{t_k}) / √(t_{k+1} - t_k)` over the dyadic grid `t_k = k T / 2 ^ n` of
`[0, T]`. Their normalized Hermite products
`∏ₖ H_{a_k}((W_{t_{k+1}} - W_{t_k}) / √(t_{k+1} - t_k)) / √(a_k!)`, over all levels `n` and
multi-indices `a`, span a dense subspace of the square-integrable claims measurable for the
natural filtration of `W` at `T`. Claims measurable for the usual augmentation of that
filtration, which also contains all null events and is right-continuous, are included: they
have the same square-integrable classes.

On any strictly increasing finite grid starting at zero, the Hermite products form a Hilbert
basis of the square-integrable claims measurable for the observations at the grid times. This
only uses the Gaussian law of the increments and `W 0 = 0` almost surely, not path continuity.
Passing to all levels uses almost sure path continuity, through the convergence of conditional
expectations on the dyadic observations, and the right continuity of the null-augmented
natural filtration.

This is the cylinder-functional density underlying the martingale representation theorem for
the Brownian filtration: a closed space of claims that contains every dyadic Hermite product
contains every square-integrable claim measurable for the Brownian filtration at `T`.

## Main results

The density results are in the namespace `ProbabilityTheory`.

* `IsPreBrownianReal.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_iSup_comap`:
  the finite-grid basis identification for any strictly increasing grid starting at zero.
* `IsPreBrownianReal.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_dyadicNatural`:
  the closed span of the level-`n` Hermite products is the space of square-integrable claims
  measurable for the level-`n` dyadic observations.
* `IsBrownianReal.mem_topologicalClosure_span_gaussianVectorHermite`:
  claims measurable for the usual augmented natural filtration at `T` lie in the closed span
  of the Hermite products of all levels.
* `IsBrownianReal.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_natural`:
  this closed span is the space of square-integrable claims measurable for the natural
  filtration at `T`.
* `IsBrownianReal.lpMeas_rightCont_nullAugment_natural_eq_lpMeas_natural`:
  the usual augmentation has the same `Lᵖ` claims, at every exponent and time, as the natural
  filtration (in `TauCeti.Probability.BrownianMotion.RightContinuity`).

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4.
-/

public section

noncomputable section

open MeasureTheory Filter Set TauCeti
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

namespace ProbabilityTheory

namespace IsPreBrownianReal

/-- On any strictly increasing finite grid starting at zero, the closed linear span of the
normalized Hermite products of the standardized increments of a pre-Brownian motion is exactly the
space of square-integrable claims measurable for its observations at the grid times. These
products are orthonormal (`ProbabilityTheory.HasLaw.orthonormal_gaussianVectorHermite`), so
they form a Hilbert basis of that space. The initial observation is discarded because `W 0 = 0`
almost surely; no path regularity is needed. -/
theorem topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_iSup_comap
    (hW : IsPreBrownianReal W P) (hmeas : ∀ s, Measurable (W s))
    {k : ℕ} {t : Fin (k + 1) → ℝ≥0} (ht : StrictMono t) (ht0 : t 0 = 0) :
    (Submodule.span ℝ (range (HasLaw.gaussianVectorHermite
      (hW.hasLaw_normalizedBrownianIncrements ht)
      (measurable_normalizedBrownianIncrements fun i ↦ hmeas (t i))))).topologicalClosure =
      lpMeas ℝ ℝ (⨆ j, (inferInstance : MeasurableSpace ℝ).comap (W (t j))) 2 P := by
  have hX := hW.hasLaw_normalizedBrownianIncrements ht
  have hY := measurable_normalizedBrownianIncrements (t := t) fun i ↦ hmeas (t i)
  have hobs : Measurable (fun ω i ↦ W (t i) ω) := Measurable.of_eval fun i ↦ hmeas (t i)
  rw [← MeasurableSpace.comap_process_pi]
  refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_
    (isClosed_aestronglyMeasurable hobs.comap_le)) fun u hu ↦ ?_
  · -- Each Hermite product is a function of the observations at the grid times.
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [← HasLaw.gaussianVectorL2Isometry_gaussianHermitePiBasis hX hY,
      SetLike.mem_coe, mem_lpMeas_iff_aestronglyMeasurable]
    exact (hW.mem_range_gaussianVectorL2Isometry_iff ht ht0 hY _).1
      ⟨gaussianHermitePiBasis ℝ (Fin k) a, rfl⟩
  -- The upstream finite-grid Hermite expansion puts every observation-measurable claim
  -- in the closed span.
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto
    (hW.hasSum_gaussianVectorHermite_of_aestronglyMeasurable_comap ht ht0 hY u
      (mem_lpMeas_iff_aestronglyMeasurable.1 hu))
    (Eventually.of_forall fun s ↦ Submodule.sum_mem _
      fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

/-- At each dyadic level of a positive horizon, the closed span of the normalized Hermite
products is exactly the space of square-integrable claims measurable for that level's
observations. -/
theorem topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_dyadicNatural
    (hW : IsPreBrownianReal W P) (hmeas : ∀ t, Measurable (W t)) (hT : 0 < T) (n : ℕ) :
    (Submodule.span ℝ (range (HasLaw.gaussianVectorHermite
      (hW.hasLaw_normalizedBrownianIncrements (strictMono_dyadicTime hT n))
      (measurable_normalizedBrownianIncrements fun i ↦
        hmeas (dyadicTime T n i))))).topologicalClosure =
      lpMeas ℝ ℝ (Filtration.dyadicNatural W hmeas T n) 2 P := by
  rw [Filtration.dyadicNatural_eq_iSup]
  exact hW.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_iSup_comap hmeas
    (strictMono_dyadicTime hT n) (dyadicTime_zero T n)

end IsPreBrownianReal

namespace IsBrownianReal

/-- Every square-integrable claim measurable for the usual augmented natural filtration of a
Brownian motion at a positive time `T` lies in the closed linear span of the normalized Hermite
products of its standardized increments over the dyadic grids `k T / 2 ^ n` of `[0, T]`, of all
levels `n`. -/
theorem mem_topologicalClosure_span_gaussianVectorHermite (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (hT : 0 < T) {ξ : Lp ℝ 2 P}
    (hξ : AEStronglyMeasurable[((Filtration.natural W hmeas).nullAugment P).rightCont T] ξ P) :
    ξ ∈ (Submodule.span ℝ (⋃ n, range (HasLaw.gaussianVectorHermite
      (hW.hasLaw_normalizedBrownianIncrements (strictMono_dyadicTime hT n))
      (measurable_normalizedBrownianIncrements fun i ↦
        (hmeas (dyadicTime T n i)).measurable)))).topologicalClosure := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  set G := Filtration.dyadicNatural W (fun t ↦ (hmeas t).measurable) T
  -- Right continuity of the null-augmented natural filtration removes the right limit.
  have hξ' : AEStronglyMeasurable[(Filtration.natural W hmeas).nullAugment P T] ξ P :=
    hξ.mono ((hW.isRightContinuous_nullAugment_natural hmeas).RC T)
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (W · ω) (Iic T) := hW.cont.mono fun _ hω ↦ hω.continuousOn
  -- Conditional expectations on the dyadic observations converge to the claim in `L²`.
  have hmem (n : ℕ) : MemLp (P[ξ | G n]) 2 P := (Lp.memLp ξ).condExp one_le_two
  have hlim : Tendsto (fun n ↦ (hmem n).toLp (P[ξ | G n])) atTop (𝓝 ξ) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hmem _ (Lp.memLp ξ)).2
      (Filtration.tendsto_eLpNorm_condExp_dyadicNatural hmeas hcont one_le_two
        ENNReal.ofNat_ne_top (Lp.memLp ξ) hξ')
    rwa [Lp.toLp_coeFn] at h
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall fun n ↦ ?_)
  -- Each of them lies in the closed span of the Hermite products of its level.
  refine Submodule.topologicalClosure_mono (Submodule.span_mono (subset_iUnion_of_subset n
    subset_rfl)) ((hW.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_dyadicNatural
      _ hT n).ge (mem_lpMeas_iff_aestronglyMeasurable.2
        ⟨P[ξ | G n], stronglyMeasurable_condExp, (hmem n).coeFn_toLp⟩))

/-- For a Brownian motion and a positive time `T`, the closed linear span of the normalized
Hermite products of the standardized increments over all dyadic grids of `[0, T]` is exactly the
space of square-integrable claims measurable for the natural filtration at `T`. -/
theorem topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (hT : 0 < T) :
    (Submodule.span ℝ (⋃ n, range (HasLaw.gaussianVectorHermite
      (hW.hasLaw_normalizedBrownianIncrements (strictMono_dyadicTime hT n))
      (measurable_normalizedBrownianIncrements fun i ↦
        (hmeas (dyadicTime T n i)).measurable)))).topologicalClosure =
      lpMeas ℝ ℝ (Filtration.natural W hmeas T) 2 P := by
  refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_
    (isClosed_aestronglyMeasurable ((Filtration.natural W hmeas).le T))) fun ξ hξ ↦ ?_
  · -- The Hermite products of each level are measurable for observations before `T`.
    refine Submodule.span_le.2 (iUnion_subset fun n ↦ ?_)
    intro u hu
    have hu' := (hW.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_dyadicNatural
      (fun t ↦ (hmeas t).measurable) hT n).le
      (Submodule.le_topologicalClosure _ (Submodule.subset_span hu))
    exact mem_lpMeas_iff_aestronglyMeasurable.2 ((mem_lpMeas_iff_aestronglyMeasurable.1 hu').mono
      (Filtration.dyadicNatural_le_natural hmeas T n))
  · exact hW.mem_topologicalClosure_span_gaussianVectorHermite hmeas hT
      (((mem_lpMeas_iff_aestronglyMeasurable.1 hξ).mono
        ((Filtration.natural W hmeas).le_nullAugment P T)).mono
        (((Filtration.natural W hmeas).nullAugment P).le_rightCont T))

end IsBrownianReal

end ProbabilityTheory
