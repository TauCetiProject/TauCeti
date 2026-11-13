/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.NormalizedIncrements
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Pi.Pullback
public import TauCeti.Probability.Process.DyadicGrid
import TauCeti.MeasureTheory.Function.ConditionalExpectation.Completion
import TauCeti.Probability.BrownianMotion.RightContinuity
import TauCeti.Probability.Process.FiniteGrid

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

At a single dyadic level, the Hermite products of that level form a Hilbert basis of the
square-integrable claims measurable for the observations at the grid times. This only uses the
Gaussian law of the increments and `W 0 = 0` almost surely, not path continuity. Passing to
all levels uses almost sure path continuity, through the convergence of conditional
expectations on the dyadic observations, and the right continuity of the null-augmented
natural filtration.

This is the cylinder-functional density underlying the martingale representation theorem for
the Brownian filtration: a closed space of claims that contains every dyadic Hermite product
contains every square-integrable claim measurable for the Brownian filtration at `T`.

## Main results

The density results are in the namespace `ProbabilityTheory`.

* `IsPreBrownianReal.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_dyadicNatural`:
  the closed span of the level-`n` Hermite products is the space of square-integrable claims
  measurable for the level-`n` dyadic observations.
* `IsBrownianReal.mem_topologicalClosure_span_gaussianVectorHermite`:
  claims measurable for the usual augmented natural filtration at `T` lie in the closed span
  of the Hermite products of all levels.
* `IsBrownianReal.topologicalClosure_span_gaussianVectorHermite_eq_lpMeas`:
  this closed span is the space of square-integrable claims measurable for the natural
  filtration at `T`.
* `IsBrownianReal.lpMeas_rightCont_nullAugment_natural_eq_lpMeas_natural`:
  the usual augmentation has the same square-integrable claims as the natural filtration.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4.
-/

public section

noncomputable section

open MeasureTheory Filter Set TauCeti
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

namespace TauCeti

/-- The standardized increments over a dyadic grid are measurable for the observations at the
grid times. -/
theorem measurable_normalizedBrownianIncrements_dyadicTime (hmeas : ∀ t, Measurable (W t))
    (T : ℝ≥0) (n : ℕ) : Measurable[Filtration.dyadicNatural W hmeas T n]
      (normalizedBrownianIncrements W (dyadicTime T n)) := by
  -- Measurability lemmas for differences and vectors take the source σ-algebra as an
  -- instance, so make the observation σ-algebra the ambient one locally.
  let : MeasurableSpace Ω := Filtration.dyadicNatural W hmeas T n
  have hW (k : Fin (2 ^ n + 1)) : Measurable (W (dyadicTime T n k)) :=
    measurable_iff_comap_le.2 (Filtration.comap_le_dyadicNatural T n k)
  have heq : normalizedBrownianIncrements W (dyadicTime T n) = fun ω (i : Fin (2 ^ n)) ↦
      (W (dyadicTime T n i.succ) ω - W (dyadicTime T n i.castSucc) ω) /
        Real.sqrt ((dyadicTime T n i.succ : ℝ) - dyadicTime T n i.castSucc) :=
    funext fun ω ↦ funext fun i ↦ normalizedBrownianIncrements_apply ω i
  rw [heq]
  exact Measurable.of_eval fun i ↦ ((hW _).sub (hW _)).div_const _

end TauCeti

namespace ProbabilityTheory

namespace IsPreBrownianReal

/-- At each dyadic level of a positive horizon, the closed linear span of the normalized Hermite
products of the standardized increments of a pre-Brownian motion over the grid is exactly the
space of square-integrable claims measurable for its observations at the grid times. These
products are orthonormal (`ProbabilityTheory.HasLaw.orthonormal_gaussianVectorHermite`), so
they form a Hilbert basis of that space. The initial observation is discarded because `W 0 = 0`
almost surely; no path regularity is needed. -/
theorem topologicalClosure_span_gaussianVectorHermite_eq_lpMeas_dyadicNatural
    (hW : IsPreBrownianReal W P) (hmeas : ∀ t, Measurable (W t)) (hT : 0 < T) (n : ℕ) :
    (Submodule.span ℝ (range (HasLaw.gaussianVectorHermite
      (hW.hasLaw_normalizedBrownianIncrements (strictMono_dyadicTime hT n))
      (measurable_normalizedBrownianIncrements hmeas)))).topologicalClosure =
      lpMeas ℝ ℝ (Filtration.dyadicNatural W hmeas T n) 2 P := by
  set t := dyadicTime T n
  have hX := hW.hasLaw_normalizedBrownianIncrements (strictMono_dyadicTime hT n)
  have hY := measurable_normalizedBrownianIncrements (t := t) hmeas
  refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_
    (isClosed_aestronglyMeasurable ((Filtration.dyadicNatural W hmeas T).le n))) fun u hu ↦ ?_
  · -- Each Hermite product is a function of the observations at the grid times.
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    set f := gaussianHermitePiBasis ℝ (Fin (2 ^ n)) a
    have hYG := measurable_normalizedBrownianIncrements_dyadicTime hmeas T n
    rw [← HasLaw.gaussianVectorL2Isometry_gaussianHermitePiBasis hX hY,
      SetLike.mem_coe, mem_lpMeas_iff_aestronglyMeasurable]
    refine ⟨(Lp.aestronglyMeasurable f).mk f ∘ normalizedBrownianIncrements W t,
      (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.comp_measurable hYG, ?_⟩
    exact (HasLaw.coeFn_gaussianVectorL2Isometry hX hY f).trans
      ((hX.measurePreserving hY).quasiMeasurePreserving.ae_eq_comp
        (Lp.aestronglyMeasurable f).ae_eq_mk)
  -- Conversely, write an observation-measurable claim as a Borel function of the
  -- standardized increments.
  obtain ⟨g₀, hg₀, hug₀⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 hu
  rw [Filtration.dyadicNatural_apply] at hg₀
  have ha (i : Fin (2 ^ n)) : Real.sqrt ((t i.succ : ℝ) - t i.castSucc) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (sub_pos.2 (NNReal.coe_lt_coe.2
      (strictMono_dyadicTime hT n Fin.castSucc_lt_succ)))
  have h0 : ∀ᵐ ω ∂P, W (t 0) ω = 0 := by
    simpa only [t, dyadicTime_zero] using hW.eval_zero_ae_eq_zero
  obtain ⟨g, hg, hg₀g⟩ := exists_measurable_comp_increments_ae (fun ω k ↦ W (t k) ω)
    _ ha 0 h0 hg₀.measurable
  have hug : (u : Ω → ℝ) =ᵐ[P] g ∘ normalizedBrownianIncrements W t :=
    hug₀.trans (hg₀g.trans (EventuallyEq.of_eq (funext fun ω ↦ congrArg g
      (funext fun i ↦ (normalizedBrownianIncrements_apply ω i).symm))))
  -- The Borel function is square-integrable for the Gaussian law of the increments.
  have hgLp : MemLp g 2 (Measure.pi fun _ : Fin (2 ^ n) ↦ gaussianReal 0 1) := by
    rw [← hX.map_eq]
    exact (memLp_map_measure_iff hg.aestronglyMeasurable hY.aemeasurable).2
      ((Lp.memLp u).ae_eq hug)
  -- So the claim is the Gaussian pullback of its class, which has a Hermite expansion.
  have hpull : HasLaw.gaussianVectorL2Isometry hX hY (hgLp.toLp g) = u := by
    refine Lp.ext ((HasLaw.coeFn_gaussianVectorL2Isometry hX hY _).trans ?_)
    exact ((hX.measurePreserving hY).quasiMeasurePreserving.ae_eq_comp
      hgLp.coeFn_toLp).trans hug.symm
  rw [← hpull, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto (HasLaw.hasSum_gaussianVectorHermite hX hY (hgLp.toLp g))
    (Eventually.of_forall fun s ↦ Submodule.sum_mem _
      fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

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
      (measurable_normalizedBrownianIncrements fun t ↦
        (hmeas t).measurable)))).topologicalClosure := by
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
theorem topologicalClosure_span_gaussianVectorHermite_eq_lpMeas (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (hT : 0 < T) :
    (Submodule.span ℝ (⋃ n, range (HasLaw.gaussianVectorHermite
      (hW.hasLaw_normalizedBrownianIncrements (strictMono_dyadicTime hT n))
      (measurable_normalizedBrownianIncrements fun t ↦
        (hmeas t).measurable)))).topologicalClosure =
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

/-- The usual augmentation of the natural filtration of a Brownian motion has the same `Lᵖ`
claims, `1 ≤ p`, at every time as the natural filtration itself. -/
theorem lpMeas_rightCont_nullAugment_natural_eq_lpMeas_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) {p : ℝ≥0∞} (hp : 1 ≤ p) (T : ℝ≥0) :
    lpMeas ℝ ℝ (((Filtration.natural W hmeas).nullAugment P).rightCont T) p P =
      lpMeas ℝ ℝ (Filtration.natural W hmeas T) p P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  ext ξ
  simp only [mem_lpMeas_iff_aestronglyMeasurable]
  refine ⟨fun hξ ↦ ?_, fun hξ ↦ (hξ.mono ((Filtration.natural W hmeas).le_nullAugment P T)).mono
    (((Filtration.natural W hmeas).nullAugment P).le_rightCont T)⟩
  -- Right continuity leaves only the null events, which conditional expectation discards.
  have hξ' : AEStronglyMeasurable[(Filtration.natural W hmeas).nullAugment P T] ξ P :=
    hξ.mono ((hW.isRightContinuous_nullAugment_natural hmeas).RC T)
  rw [Filtration.nullAugment_apply] at hξ'
  exact stronglyMeasurable_condExp.aestronglyMeasurable.congr
    (TauCeti.MeasureTheory.condExp_of_aestronglyMeasurable_eventuallyMeasurableSpace
      ((Filtration.natural W hmeas).le T) hξ' ((Lp.memLp ξ).integrable hp))

end IsBrownianReal

end ProbabilityTheory
