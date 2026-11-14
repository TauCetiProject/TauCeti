/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
public import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic
import TauCeti.MeasureTheory.OptimalTransport.Stability

/-!
# Existence of couplings with cyclically monotone support

For a continuous cost of finite optimal value,
`TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support` shows that the topological support of
every optimal coupling is `c`-cyclically monotone. When the optimal value is `∞`, every coupling is
trivially Kantorovich-optimal, so Kantorovich optimality alone no longer selects plans with
cyclically monotone support.

Following Gangbo and McCann (Theorem 2.3), this file constructs couplings with `c`-cyclically
monotone support for an arbitrary continuous real cost `c : X × Y → ℝ` on Polish spaces, with no
lower bound or finite-moment assumption on `c`: the cost is clamped to `[-k, k]`, shifted by `+ k`
to become nonnegative and bounded (hence of finite optimal cost), and a weak cluster point of the
resulting optimal plans inherits `c`-cyclical monotonicity of its support by
`TauCeti.isCyclicallyMonotone_support_of_tendsto`. When `c` is nonnegative, combining the finite
and infinite total-cost regimes yields an optimal coupling whose support is `c`-cyclically
monotone regardless of whether `transportCost` is finite.

## Main statements

* `TauCeti.exists_isCoupling_isCyclicallyMonotone_support` — for any continuous real cost on Polish
  spaces, any two probability measures admit a coupling with `c`-cyclically monotone support;
* `TauCeti.exists_isOptimalCoupling_isCyclicallyMonotone_support` — when `0 ≤ c`, there is an
  optimal coupling for `ENNReal.ofReal ∘ c` whose support is `c`-cyclically monotone, even when the
  optimal transport cost is `∞`.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, Theorem 2.3.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.20.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

private theorem tendsto_uncurry_clamp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {c : X × Y → ℝ} (hc : Continuous c) (z : X × Y) :
    Tendsto (Function.uncurry fun (k : ℕ) w ↦ max (-(k : ℝ)) (min (c w) k))
      (atTop ×ˢ 𝓝 z) (𝓝 (c z)) := by
  refine ((hc.tendsto z).comp tendsto_snd).congr' ?_
  have hW : {w : X × Y | |c w - c z| < 1} ∈ 𝓝 z :=
    isOpen_lt (hc.sub continuous_const).abs continuous_const |>.mem_nhds (by simp)
  filter_upwards [(eventually_ge_atTop (⌈|c z|⌉₊ + 1)).prod_mk hW] with ⟨k, w⟩ ⟨hk, hw⟩
  have hk' : |c z| + 1 ≤ (k : ℝ) := by
    have hceil : |c z| ≤ ⌈|c z|⌉₊ := Nat.le_ceil _
    have hnat : (⌈|c z|⌉₊ + 1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcw : |c w| < (k : ℝ) := by
    have htri := abs_sub_abs_le_abs_sub (c w) (c z)
    linarith [abs_lt.1 hw]
  obtain ⟨hlo, hhi⟩ := abs_lt.1 hcw
  simp only [Function.uncurry, Function.comp_apply, min_eq_left hhi.le, max_eq_right hlo.le]

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Existence of a coupling with cyclically monotone support** (Gangbo–McCann, Theorem 2.3).
On Polish Borel spaces, for any continuous cost `c : X × Y → ℝ` and any two probability measures
`μ` and `ν`, there exists a coupling `π` of `μ` and `ν` whose topological support is `c`-cyclically
monotone. Neither nonnegativity of `c` nor finiteness of any cost integral is required. -/
theorem exists_isCoupling_isCyclicallyMonotone_support (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] {c : X × Y → ℝ} (hc : Continuous c) :
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
  exact ⟨p.toMeasure, hpK, isCyclicallyMonotone_support_of_tendsto hUtend
    (Eventually.of_forall hcm) fun z ↦
      (tendsto_uncurry_clamp hc z).mono_left (Filter.prod_mono_left _ hUle)⟩

/-- **Existence of an optimal coupling with cyclically monotone support.** On Polish Borel spaces,
for any continuous nonnegative cost `c : X × Y → ℝ` and any two probability measures `μ` and `ν`,
there exists an optimal coupling `π` for `ENNReal.ofReal ∘ c` whose topological support is
`c`-cyclically monotone. Unlike `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`, this
requires no finiteness assumption on `transportCost`. -/
theorem exists_isOptimalCoupling_isCyclicallyMonotone_support (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {c : X × Y → ℝ} (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) :
    ∃ π, IsOptimalCoupling (fun z ↦ ENNReal.ofReal (c z)) π μ ν ∧
      IsCyclicallyMonotone c π.support := by
  by_cases hfin : transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν = ∞
  · obtain ⟨π, hπ, hcm⟩ := exists_isCoupling_isCyclicallyMonotone_support μ ν hc
    exact ⟨π, ⟨hπ, le_antisymm (hfin ▸ le_top) (transportCost_le_lintegral hπ _)⟩, hcm⟩
  · have hc' : Continuous fun z ↦ ENNReal.ofReal (c z) := ENNReal.continuous_ofReal.comp hc
    obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ ν hc'.lowerSemicontinuous
    exact ⟨π, hπ,
      (isCyclicallyMonotone_ofReal_iff hc0).1 (hπ.isCyclicallyMonotone_support hc' hfin)⟩

end TauCeti
