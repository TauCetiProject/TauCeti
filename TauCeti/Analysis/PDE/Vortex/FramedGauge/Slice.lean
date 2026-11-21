/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.Gauge.Slice
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Local uniqueness of the Coulomb gauge for the Sobolev gauge group

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts on the continuous fields of the affine space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`). At a field `x` the Coulomb
slice is cut out by the gauge-fixing condition `d₀* (y - x) = 0`, with `d₀* = gaugeAdjoint x` the
formal adjoint of the infinitesimal gauge action at `x`.

This file proves the uniqueness half of the slice theorem at `x`: the Coulomb slice meets every
gauge orbit near `x` at most once near the identity. There are a neighbourhood `U` of `x` in
`A_m^k` and a neighbourhood `N` of `1` in `G_(k+1)` such that if `y ∈ U` and `u ∈ N` satisfy
`d₀* (u · y) = d₀* y`, then `u = 1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_smul_eq`). In
particular a field of `U` in the Coulomb slice of `x` is carried out of that slice by every gauge
of `N` other than `1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero`).

The gauges near `1` are the exponentials `exp (i F)` of small real phases
(`TauCeti.Vortex.isOpenEmbedding_expGauge`), and a small phase in `H^(k+1)` is uniformly small and
of class `C²` by the Sobolev embedding. Fields near `x` in `A_m^k` are uniformly close to `x`
(`TauCeti.Vortex.SobolevFieldSpace.tendstoUniformly_of_tendsto`) and of class `C¹`. The pointwise
statement for such fields and phases is
`TauCeti.Vortex.exists_pos_forall_eq_zero_of_gaugeAdjoint_phaseGauge_eq`.

The existence half of the slice theorem, which moves every field near `x` into the Coulomb slice
by a gauge near `1`, is not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter Topology BesselPotentialSpace TemperedDistribution

namespace SobolevFieldSpace

open SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

variable (hs) in
/-- **Local uniqueness of the Coulomb gauge.** Let `x` be a continuous field of `A_m^k`, `k ≥ 3`.
There are a neighbourhood `U` of `x` and a neighbourhood `N` of `1` in the Sobolev gauge group
`G_(k+1)` such that for `y ∈ U` and `u ∈ N`, if `u · y` and `y` have the same Coulomb defect at
`x`, `d₀* (u · y) = d₀* y`, then `u = 1`. -/
theorem exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_smul_eq (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U ∈ 𝓝 x, ∃ N ∈ 𝓝 (1 : SobolevTopologicalGaugeGroup hs), ∀ y ∈ U, ∀ u ∈ N,
      (∀ z, gaugeAdjoint x ⇑(u • y) z = gaugeAdjoint x y z) → u = 1 := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  obtain ⟨ε, hε, huniq⟩ :=
    exists_pos_forall_eq_zero_of_gaugeAdjoint_phaseGauge_eq hk1 x.mem_framedFieldSpace x.continuous
  -- Fields near `x` are uniformly close to `x`.
  have hU : ∀ᶠ y in 𝓝 x, ∀ z, |y z 2 - x z 2| ≤ ε ∧ |y z 3 - x z 3| ≤ ε := by
    have hT := tendstoUniformly_of_tendsto hk1 (tendsto_id (x := 𝓝 x))
    rw [Metric.tendstoUniformly_iff] at hT
    filter_upwards [hT ε hε] with y hy z
    have hd := (hy z).le
    rw [dist_comm, dist_eq_norm] at hd
    have hi (i : Fin 4) : |y z i - x z i| ≤ ε := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (y z - x z) i).trans hd
    exact ⟨hi 2, hi 3⟩
  -- Gauges near `1` are exponentials of uniformly small phases.
  have hN : ∀ᶠ u in 𝓝 (1 : SobolevTopologicalGaugeGroup hs),
      ∃ F, expGauge hs F = u ∧ ∀ z, |continuousRep F z| ≤ ε := by
    rw [← AddChar.map_zero_eq_one (expGauge hs), ← (isOpenEmbedding_expGauge hs).map_nhds_eq,
      eventually_map]
    have hT := tendstoUniformly_continuousRep (finrank_real_complex_lt_two_mul hs)
      (0 : realSubmodule ℂ (zero_le_one.trans hs.le))
    rw [Metric.tendstoUniformly_iff] at hT
    filter_upwards [hT ε hε] with F hF
    refine ⟨F, rfl, fun z ↦ ?_⟩
    simpa [Real.dist_eq, abs_sub_comm] using (hF z).le
  refine ⟨_, hU, _, hN, fun y hy u hu hcoul ↦ ?_⟩
  obtain ⟨F, rfl, hF⟩ := hu
  have hd := finrank_real_complex_lt_two_mul hs
  have hφ := continuousRep_mem_realSobolevFunctions hd F
  -- The phase `F` is `C²` and square integrable, and the field `y` is `C¹`.
  have hφ2 : ContDiff ℝ 2 (continuousRep F) := by
    refine contDiff_of_mem_realSobolevFunctions ?_ hφ (continuous_continuousRep hd F)
    rw [Complex.finrank_real_complex]
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith
  have hy1 : ContDiff ℝ 1 y := y.contDiff (by exact_mod_cast (by omega : 1 + 1 < k))
  have hy₀ : Differentiable ℝ fun w ↦ y w 0 :=
    (differentiable_euclidean.1 (hy1.differentiable one_ne_zero)) 0
  have hy₁ : Differentiable ℝ fun w ↦ y w 1 :=
    (differentiable_euclidean.1 (hy1.differentiable one_ne_zero)) 1
  have hact : ⇑(expGauge hs F • y) = phaseGauge y (continuousRep F) := by
    rw [coe_smul, toSubgroup_expGauge]
    exact gaugeTransform_exp (hφ2.differentiable two_ne_zero) y
  have h0 := huniq y.continuous hy₀ hy₁ hy hφ2 (memLp_of_mem_realSobolevFunctions hφ) hF
    (by simpa only [hact] using hcoul)
  rw [continuousRep_injective hd (h0.trans (map_zero _).symm), AddChar.map_zero_eq_one]

variable (hs) in
/-- **The Coulomb slice meets nearby gauge orbits once.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`. There are a neighbourhood `U` of `x` and a neighbourhood `N` of `1` in `G_(k+1)` such
that if `y ∈ U` and `u · y`, `u ∈ N`, both lie in the Coulomb slice `d₀* (· - x) = 0` of `x`, then
`u = 1`. -/
theorem exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U ∈ 𝓝 x, ∃ N ∈ 𝓝 (1 : SobolevTopologicalGaugeGroup hs), ∀ y ∈ U, ∀ u ∈ N,
      (∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0) → (∀ z, gaugeAdjoint x (⇑(u • y) - ⇑x) z = 0) →
        u = 1 := by
  obtain ⟨U, hU, N, hN, h⟩ := exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_smul_eq hs hk x
  refine ⟨U, hU, N, hN, fun y hy u hu hy0 huy0 ↦ h y hy u hu fun z ↦ ?_⟩
  -- Fields of `A_m^k`, `k ≥ 3`, are `C¹`, so `d₀*` is additive on them.
  have hC (w : SobolevFieldSpace f m k) : ContDiff ℝ 1 w :=
    w.contDiff (by exact_mod_cast (by omega : 1 + 1 < k))
  have hd (w : SobolevFieldSpace f m k) (i : Fin 4) : DifferentiableAt ℝ (fun v ↦ w v i) z :=
    (differentiable_euclidean.1 ((hC w).differentiable one_ne_zero)) i z
  have e₁ := hy0 z
  have e₂ := huy0 z
  rw [gaugeAdjoint_sub _ (hd y 0) (hd y 1) (hd x 0) (hd x 1)] at e₁
  rw [gaugeAdjoint_sub _ (hd (u • y) 0) (hd (u • y) 1) (hd x 0) (hd x 1)] at e₂
  linarith

end SobolevFieldSpace

end TauCeti.Vortex
