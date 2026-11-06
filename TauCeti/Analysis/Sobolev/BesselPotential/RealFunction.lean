/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Real functions in the Bessel-potential spaces

Mathlib's Bessel-potential space `H^{s,p}` consists of tempered distributions, and
`TemperedDistribution.realSobolevSubmodule` collects the real `Lᵖ` classes whose complexification
lies in it. Nonlinear constructions such as gauge groups and the coefficients of field equations
are written with actual functions instead, whose values can be multiplied and evaluated at points.
This file packages the real functions on `E` that agree almost everywhere with an element of
`realSobolevSubmodule E s p` as a real submodule of `E → ℝ`
(`TemperedDistribution.realSobolevFunctions`), and transfers to it the facts about `L²` classes
that such constructions use:

* membership decreases as the order increases (`TemperedDistribution.realSobolevFunctions_mono`);
* smooth compactly supported functions belong for every order
  (`TemperedDistribution.mem_realSobolevFunctions_of_hasCompactSupport`);
* for `s > dim E / 2` the space is closed under pointwise multiplication
  (`TemperedDistribution.mul_mem_realSobolevFunctions`), by the algebra property
  `TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`;
* for `s > dim E / 2` a continuous member tends to zero at infinity
  (`TemperedDistribution.tendsto_cocompact_of_mem_realSobolevFunctions`), by the Sobolev
  embedding `TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology
open scoped ENNReal ContDiff

namespace TemperedDistribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (E) in
/-- The real functions on `E` that agree almost everywhere with a real `Lᵖ` function whose
complexification lies in the Bessel-potential space `H^{s,p}`, as a real submodule of `E → ℝ`. -/
def realSobolevFunctions (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (E → ℝ) where
  carrier := {g | ∃ u : Lp ℝ p (volume : Measure E), u =ᵐ[volume] g ∧
    u ∈ realSobolevSubmodule E s p}
  add_mem' := by
    rintro g₁ g₂ ⟨u₁, hu₁, hs₁⟩ ⟨u₂, hu₂, hs₂⟩
    refine ⟨u₁ + u₂, ?_, add_mem hs₁ hs₂⟩
    filter_upwards [Lp.coeFn_add u₁ u₂, hu₁, hu₂] with z h h₁ h₂
    rw [h, Pi.add_apply, h₁, h₂, Pi.add_apply]
  zero_mem' := ⟨0, Lp.coeFn_zero ℝ p volume, zero_mem _⟩
  smul_mem' := by
    rintro c g ⟨u, hu, hs⟩
    refine ⟨c • u, ?_, Submodule.smul_mem _ c hs⟩
    filter_upwards [Lp.coeFn_smul c u, hu] with z h h'
    rw [h, Pi.smul_apply, h', Pi.smul_apply]

/-- Membership in `realSobolevFunctions`: almost everywhere equality with a real `Lᵖ` function
whose complexification lies in `H^{s,p}`. -/
theorem mem_realSobolevFunctions {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℝ} :
    g ∈ realSobolevFunctions E s p ↔ ∃ u : Lp ℝ p (volume : Measure E), u =ᵐ[volume] g ∧
      MemSobolev s p (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) :=
  exists_congr fun _ ↦ and_congr_right' mem_realSobolevSubmodule

/-- The real `L²` Sobolev function spaces decrease as the order increases. -/
theorem realSobolevFunctions_mono {s s' : ℝ} (h : s' ≤ s) :
    realSobolevFunctions E s 2 ≤ realSobolevFunctions E s' 2 :=
  fun _ hg ↦ mem_realSobolevFunctions.2 <|
    (mem_realSobolevFunctions.1 hg).imp fun _ hu ↦ ⟨hu.1, hu.2.mono h⟩

/-- A smooth compactly supported real function lies in every Bessel-potential space. -/
theorem mem_realSobolevFunctions_of_hasCompactSupport {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    g ∈ realSobolevFunctions E s p := by
  have hm : MemLp g p volume := hg.continuous.memLp_of_hasCompactSupport hc
  refine mem_realSobolevFunctions.2 ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  refine memSobolev_of_ae_eq_of_hasCompactSupport (u := fun z ↦ (g z : ℂ))
    (Complex.ofRealCLM.contDiff.comp hg) (hc.comp_left Complex.ofReal_zero) ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (hm.toLp _), hm.coeFn_toLp] with z h₁ h₂
  simp [h₁, h₂]

/-- **The real Sobolev functions of order `s > dim E / 2` form an algebra.** The pointwise
product of two of them is again one. -/
theorem mul_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s) {f g : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) (hg : g ∈ realSobolevFunctions E s 2) :
    f * g ∈ realSobolevFunctions E s 2 := by
  obtain ⟨u, hu, hus⟩ := hf
  obtain ⟨v, hv, hvs⟩ := hg
  obtain ⟨w, hws, hw⟩ := exists_mem_realSobolevSubmodule_ae_eq_mul hs hus hvs
  refine ⟨w, ?_, hws⟩
  filter_upwards [hw, hu, hv] with z h h₁ h₂
  rw [h, h₁, h₂, Pi.mul_apply]

/-- **Decay of continuous Sobolev functions.** For `s > dim E / 2`, a continuous real function in
`H^s` tends to zero at infinity: by the Sobolev embedding it agrees almost everywhere with a
continuous function vanishing at infinity, hence everywhere. -/
theorem tendsto_cocompact_of_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {g : E → ℝ} (hg : g ∈ realSobolevFunctions E s 2) (hcont : Continuous g) :
    Tendsto g (cocompact E) (𝓝 0) := by
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hg
  obtain ⟨G, hG⟩ := MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq hs hS
  have hgc : Continuous fun z ↦ (g z : ℂ) := Complex.continuous_ofReal.comp hcont
  have hae : (fun z ↦ (g z : ℂ)) =ᵐ[volume] G := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu, hG] with z h₁ h₂ h₃
    rw [← h₃, h₁, h₂, Complex.ofRealCLM_apply]
  have heq := (hgc.ae_eq_iff_eq volume G.continuous).1 hae
  have hG0 : Tendsto (fun z ↦ (g z : ℂ)) (cocompact E) (𝓝 0) := heq ▸ G.zero_at_infty'
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp hG0

end TemperedDistribution
