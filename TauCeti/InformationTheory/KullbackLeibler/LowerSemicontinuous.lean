/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Lower semicontinuity of relative entropy along density convergence

For a finite reference measure `ρ`, relative entropy is lower semicontinuous along sequences of
measures whose Radon–Nikodym densities with respect to `ρ` converge `ρ`-almost everywhere: the
measure with the limit density has relative entropy at most the `liminf` of the entropies. The
proof is Fatou's lemma applied to the entropy integrand `InformationTheory.klFun` of the
densities.

## Main results

* `TauCeti.klDiv_withDensity_le_liminf`: if the densities of measures `p n ≪ ρ` converge
  `ρ`-almost everywhere to a measurable `g`, then `klDiv (ρ.withDensity g) ρ` is at most
  `liminf (klDiv (p n) ρ)`.
-/

public section

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace TauCeti

/-- **Lower semicontinuity of relative entropy along density convergence.** If the densities of
measures `p n` absolutely continuous with respect to `ρ` converge `ρ`-almost everywhere to a
measurable `g`, then the measure with density `g` has relative entropy at most the `liminf` of
the relative entropies `klDiv (p n) ρ`, by Fatou's lemma. -/
theorem klDiv_withDensity_le_liminf {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    {p : ℕ → Measure α} {g : α → ℝ}
    [IsFiniteMeasure ρ] [IsFiniteMeasure (ρ.withDensity fun z ↦ ENNReal.ofReal (g z))]
    [∀ n, IsFiniteMeasure (p n)]
    (hac : ∀ n, p n ≪ ρ) (hgm : Measurable g)
    (hlim : ∀ᵐ z ∂ρ, Tendsto (fun n ↦ ((p n).rnDeriv ρ z).toReal) atTop (𝓝 (g z))) :
    klDiv (ρ.withDensity fun z ↦ ENNReal.ofReal (g z)) ρ ≤
      liminf (fun n ↦ klDiv (p n) ρ) atTop := by
  set F : ℕ → α → ℝ := fun n z ↦ ((p n).rnDeriv ρ z).toReal
  have hg0 : 0 ≤ᵐ[ρ] g := hlim.mono fun z hz ↦ ge_of_tendsto' hz fun n ↦ ENNReal.toReal_nonneg
  calc klDiv (ρ.withDensity fun z ↦ ENNReal.ofReal (g z)) ρ
      = ∫⁻ z, ENNReal.ofReal (klFun (g z)) ∂ρ := by
        rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_withDensity ρ hgm.ennreal_ofReal, hg0]
          with z hz hz0
        rw [hz, ENNReal.toReal_ofReal hz0]
    _ = ∫⁻ z, liminf (fun n ↦ ENNReal.ofReal (klFun (F n z))) atTop ∂ρ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with z hz
        exact (((ENNReal.continuous_ofReal.comp continuous_klFun).tendsto _).comp
          hz).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ z, ENNReal.ofReal (klFun (F n z)) ∂ρ) atTop :=
        lintegral_liminf_le' fun n ↦ by fun_prop
    _ = liminf (fun n ↦ klDiv (p n) ρ) atTop := by
        simp_rw [F, ← klDiv_eq_lintegral_klFun_of_ac (hac _)]

end TauCeti
