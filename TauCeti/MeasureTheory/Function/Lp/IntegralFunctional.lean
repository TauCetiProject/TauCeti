/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of convex integral functionals on Lp

For a continuous real-valued integrand `Φ`, the extended integral of its positive part is
lower semicontinuous in the norm topology of `Lp`. If `Φ` is convex, it is also lower
semicontinuous in the weak topology. The integral may be taken against any measure absolutely
continuous with respect to the measure defining `Lp`; this includes weighted potentials.

Using an extended nonnegative integral is essential: a nonlinear potential need not be
integrable at every `Lp` function. The proofs use almost-everywhere subsequence convergence,
Fatou's lemma, and the equality of norm and weak closures for convex sets.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace TauCeti

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ ν : Measure α} {p : ℝ≥0∞} {Φ : F → ℝ}

/-- The positive part of a continuous integrand composed with an `Lp` representative is
almost everywhere measurable for any absolutely continuous measure. -/
theorem aemeasurable_ofReal_comp_Lp (hν : ν ≪ μ) (hΦ : Continuous Φ) (u : Lp F p μ) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (u x))) ν :=
  ((ENNReal.continuous_ofReal.comp hΦ).comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable u).mono_ac hν)).aemeasurable

/-- The extended integral of the positive part of a continuous integrand is norm lower
semicontinuous on `Lp`. Absolute continuity makes the integral independent of representatives. -/
theorem lowerSemicontinuous_lintegral_ofReal_comp_Lp [Fact (1 ≤ p)]
    (hν : ν ≪ μ) (hΦ : Continuous Φ) :
    LowerSemicontinuous (fun u : Lp F p μ ↦ ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv
  obtain ⟨s, -, hs⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  have hsν := hν.ae_le hs
  have hmeas (n : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (u (s n) x))) ν :=
    aemeasurable_ofReal_comp_Lp hν hΦ (u (s n))
  calc
    ∫⁻ x, ENNReal.ofReal (Φ (v x)) ∂ν =
        ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (Φ (u (s n) x))) atTop ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hsν] with x hx
      exact ((ENNReal.continuous_ofReal.comp hΦ).continuousAt.tendsto.comp hx).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (Φ (u (s n) x)) ∂ν) atTop :=
      lintegral_liminf_le' hmeas
    _ ≤ c := liminf_le_of_frequently_le (Frequently.of_forall fun n ↦ hu (s n))

variable [NormedSpace ℝ F]

/-- Sublevels of the extended integral of the positive part of a continuous convex integrand
are convex. No integrability assumption on the integrand is required. -/
theorem convex_setOf_lintegral_ofReal_comp_Lp_le
    (hν : ν ≪ μ) (hcont : Continuous Φ) (hΦ : ConvexOn ℝ univ Φ) (c : ℝ≥0∞) :
    Convex ℝ {u : Lp F p μ | ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν ≤ c} := by
  intro u hu v hv a b ha hb hab
  have hmeas (w : Lp F p μ) : AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (w x))) ν :=
    aemeasurable_ofReal_comp_Lp hν hcont w
  have hpoint : ∀ᵐ x ∂ν,
      ENNReal.ofReal (Φ ((a • u + b • v) x)) ≤
        ENNReal.ofReal a * ENNReal.ofReal (Φ (u x)) +
          ENNReal.ofReal b * ENNReal.ofReal (Φ (v x)) := by
    filter_upwards [hν.ae_le (Lp.coeFn_add (a • u) (b • v)),
      hν.ae_le (Lp.coeFn_smul a u), hν.ae_le (Lp.coeFn_smul b v)] with x hx hxu hxv
    simp only [Pi.add_apply, Pi.smul_apply] at hx hxu hxv
    rw [hx, hxu, hxv]
    calc
      ENNReal.ofReal (Φ (a • u x + b • v x)) ≤
          ENNReal.ofReal (a * Φ (u x) + b * Φ (v x)) :=
        ENNReal.ofReal_le_ofReal (hΦ.2 (mem_univ _) (mem_univ _) ha hb hab)
      _ ≤ ENNReal.ofReal (a * Φ (u x)) + ENNReal.ofReal (b * Φ (v x)) :=
        ENNReal.ofReal_add_le
      _ = _ := by rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  calc
    ∫⁻ x, ENNReal.ofReal (Φ ((a • u + b • v) x)) ∂ν ≤
        ∫⁻ x, ENNReal.ofReal a * ENNReal.ofReal (Φ (u x)) +
          ENNReal.ofReal b * ENNReal.ofReal (Φ (v x)) ∂ν := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal a * (∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν) +
        ENNReal.ofReal b * (∫⁻ x, ENNReal.ofReal (Φ (v x)) ∂ν) := by
      rw [lintegral_add_left' ((hmeas u).const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal a * c + ENNReal.ofReal b * c := by gcongr <;> assumption
    _ = c := by rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]; simp

/-- A continuous convex potential has weakly lower semicontinuous extended integral on `Lp`.
The value `∞` is allowed, so this applies before the effective domain of the potential has been
identified. The integrating measure can incorporate a nonnegative weight. -/
theorem lowerSemicontinuous_lintegral_ofReal_comp_toWeakSpace_symm [Fact (1 ≤ p)]
    (hν : ν ≪ μ) (hΦ : Continuous Φ) (hconv : ConvexOn ℝ univ Φ) :
    LowerSemicontinuous (fun u : WeakSpace ℝ (Lp F p μ) ↦
      ∫⁻ x, ENNReal.ofReal (Φ ((toWeakSpace ℝ (Lp F p μ)).symm u x)) ∂ν) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  have hc : IsClosed {u : Lp F p μ | ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν ≤ c} :=
    (lowerSemicontinuous_lintegral_ofReal_comp_Lp (p := p) hν hΦ).isClosed_preimage c
  have hcv := convex_setOf_lintegral_ofReal_comp_Lp_le (p := p) hν hΦ hconv c
  have heq := hcv.toWeakSpace_closure ℝ
  rw [hc.closure_eq] at heq
  have hclosed : IsClosed ((toWeakSpace ℝ (Lp F p μ)) ''
      {u : Lp F p μ | ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν ≤ c}) := by
    rw [heq]
    exact isClosed_closure
  rwa [(toWeakSpace ℝ (Lp F p μ)).image_eq_preimage_symm] at hclosed

end TauCeti
