/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.OptimalTransport.Existence.Finite
import TauCeti.MeasureTheory.OptimalTransport.Stability
import TauCeti.Topology.Order.OrderClosed

/-!
# Existence of couplings with cyclically monotone support

For a continuous cost of finite optimal value,
`TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support` shows that the topological support of
every optimal coupling is `c`-cyclically monotone. When the optimal value is `∞`, every coupling is
trivially Kantorovich-optimal, so Kantorovich optimality alone no longer selects plans with
cyclically monotone support.

Following Gangbo and McCann (Theorem 2.3), this file constructs couplings with `c`-cyclically
monotone support between finite measures of equal mass for an arbitrary continuous real cost
`c : X × Y → ℝ` on Polish spaces, with no lower bound or finite-moment assumption on `c`: after
normalizing nonzero marginals to probability measures, the cost is clamped to `[-k, k]`, shifted by
`+ k` to become nonnegative and bounded (hence of finite optimal cost), and a weak cluster point of
the resulting optimal plans inherits `c`-cyclical monotonicity of its support by
`TauCeti.isCyclicallyMonotone_support_of_tendsto`. When `c` is nonnegative, combining the finite
and infinite total-cost regimes yields an optimal coupling whose support is `c`-cyclically
monotone regardless of whether `transportCost` is finite.

## Main statements

* `TauCeti.exists_isCoupling_isCyclicallyMonotone_support` — for any continuous real cost on Polish
  spaces, any two finite measures of equal mass admit a coupling with `c`-cyclically monotone
  support;
* `TauCeti.exists_isOptimalCoupling_isCyclicallyMonotone_support` — when `0 ≤ c`, finite measures
  of equal mass admit an optimal coupling for `ENNReal.ofReal ∘ c` whose support is `c`-cyclically
  monotone, even when the optimal transport cost is `∞`.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, Theorem 2.3.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.20.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

private theorem exists_isCoupling_isCyclicallyMonotone_support_prob (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {c : X × Y → ℝ} (hc : Continuous c) :
    ∃ π, IsCoupling π μ ν ∧ IsCyclicallyMonotone c π.support := by
  let b : ℕ → X × Y → ℝ := fun k z ↦ max (-(k : ℝ)) (min (c z) k)
  let cPos : ℕ → X × Y → ℝ≥0∞ := fun k z ↦ ENNReal.ofReal (b k z + k)
  have hcPos_cont : ∀ k, Continuous (cPos k) := fun k ↦
    ENNReal.continuous_ofReal.comp ((continuous_const.max (hc.min continuous_const)).add
      continuous_const)
  have hb_nonneg : ∀ k z, 0 ≤ b k z + k := fun k z ↦ by
    linarith [le_max_left (-(k : ℝ)) (min (c z) k)]
  have hcPos_le : ∀ k z, cPos k z ≤ ENNReal.ofReal (2 * k) := fun k z ↦
    ENNReal.ofReal_le_ofReal (by
      linarith [max_le (by linarith [Nat.cast_nonneg (α := ℝ) k] : -(k : ℝ) ≤ k)
        (min_le_right (c z) k)])
  choose πs hπs using fun k ↦ exists_isOptimalCoupling μ ν (hcPos_cont k).lowerSemicontinuous
  have hcm : ∀ k, IsCyclicallyMonotone (b k) (πs k).support := fun k ↦ by
    have : IsProbabilityMeasure (πs k) := (hπs k).toIsCoupling.isProbabilityMeasure
    have hfin : transportCost (cPos k) μ ν ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top <|
        (transportCost_le_lintegral (hπs k).toIsCoupling _).trans <|
          (lintegral_mono (hcPos_le k)).trans_eq (by rw [lintegral_const, measure_univ, mul_one])
    have hcm_shift : IsCyclicallyMonotone (fun z ↦ b k z + k) (πs k).support :=
      (isCyclicallyMonotone_ofReal_iff (hb_nonneg k)).1
        ((hπs k).isCyclicallyMonotone_support (hcPos_cont k) hfin)
    exact (isCyclicallyMonotone_add_add_iff (b k) (fun _ ↦ (k : ℝ)) (fun _ ↦ (0 : ℝ))).1
      (by simpa only [add_zero] using hcm_shift)
  have hK : IsCompact {p : ProbabilityMeasure (X × Y) | IsCoupling p.toMeasure μ ν} :=
    isCompact_setOfPred_isCoupling_of_polishSpace ⟨μ, ‹_›⟩ ⟨ν, ‹_›⟩
  obtain ⟨p, hpK, hcl⟩ := hK.exists_mapClusterPt_of_frequently
    (f := fun k ↦ ⟨πs k, (hπs k).toIsCoupling.isProbabilityMeasure⟩)
    (Frequently.of_forall (f := atTop) fun k ↦ (hπs k).toIsCoupling)
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have : (U : Filter ℕ).NeBot := U.neBot
  refine ⟨p.toMeasure, hpK, isCyclicallyMonotone_support_of_tendsto hUtend
    (Eventually.of_forall hcm) fun z ↦ ?_⟩
  have hcast : Tendsto (fun q : ℕ × (X × Y) ↦ (q.1 : ℝ)) (U ×ˢ 𝓝 z) atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_fst.mono_left (Filter.prod_mono_left _ hUle))
  exact (tendsto_neg_atTop_atBot.comp hcast).atBot_max
    (((hc.tendsto z).comp tendsto_snd).min_atTop hcast)

variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

/-- **Existence of a coupling with cyclically monotone support** (Gangbo–McCann, Theorem 2.3).
On Polish Borel spaces, for any continuous cost `c : X × Y → ℝ` and any two finite measures `μ`
and `ν` of equal mass, there exists a coupling `π` of `μ` and `ν` whose topological support is
`c`-cyclically monotone. Neither nonnegativity of `c` nor finiteness of any cost integral is
required. -/
theorem exists_isCoupling_isCyclicallyMonotone_support (hmass : μ univ = ν univ)
    {c : X × Y → ℝ} (hc : Continuous c) :
    ∃ π, IsCoupling π μ ν ∧ IsCyclicallyMonotone c π.support := by
  have : IsFiniteMeasure ν := ⟨hmass ▸ measure_lt_top μ univ⟩
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (by simpa using hmass.symm)
    subst ν
    exact ⟨0, isCoupling_zero, by simp [Measure.support_zero]⟩
  have hμ0 : μ univ ≠ 0 := fun h ↦ hμ (Measure.measure_univ_eq_zero.mp h)
  have hν : ν ≠ 0 := fun h ↦ hμ0 (by simpa [h] using hmass)
  let : NeZero μ := ⟨hμ⟩
  let : NeZero ν := ⟨hν⟩
  obtain ⟨π, hπ, hcm⟩ :=
    exists_isCoupling_isCyclicallyMonotone_support_prob ((μ univ)⁻¹ • μ) ((ν univ)⁻¹ • ν) hc
  refine ⟨μ univ • π, ?_, by rwa [Measure.support_smul_measure _ _ hμ0]⟩
  simpa only [← hmass, smul_smul, ENNReal.mul_inv_cancel hμ0 (measure_ne_top μ univ),
    one_smul] using hπ.smul (μ univ)

/-- **Existence of an optimal coupling with cyclically monotone support.** On Polish Borel spaces,
for any continuous nonnegative cost `c : X × Y → ℝ` and any two finite measures `μ` and `ν` of
equal mass, there exists an optimal coupling `π` for `ENNReal.ofReal ∘ c` whose topological support
is `c`-cyclically monotone. Unlike `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`, this
requires no finiteness assumption on `transportCost`. -/
theorem exists_isOptimalCoupling_isCyclicallyMonotone_support (hmass : μ univ = ν univ)
    {c : X × Y → ℝ} (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) :
    ∃ π, IsOptimalCoupling (fun z ↦ ENNReal.ofReal (c z)) π μ ν ∧
      IsCyclicallyMonotone c π.support := by
  by_cases hfin : transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν = ∞
  · obtain ⟨π, hπ, hcm⟩ := exists_isCoupling_isCyclicallyMonotone_support hmass hc
    exact ⟨π, ⟨hπ, le_antisymm (hfin ▸ le_top) (transportCost_le_lintegral hπ _)⟩, hcm⟩
  · have hc' : Continuous fun z ↦ ENNReal.ofReal (c z) := ENNReal.continuous_ofReal.comp hc
    obtain ⟨π, hπ⟩ := (exists_isOptimalCoupling_iff hc'.lowerSemicontinuous).2 hmass
    exact ⟨π, hπ,
      (isCyclicallyMonotone_ofReal_iff hc0).1 (hπ.isCyclicallyMonotone_support hc' hfin)⟩

end TauCeti
