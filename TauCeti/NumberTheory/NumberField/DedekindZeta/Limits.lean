/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Real-axis limits of the Dedekind zeta function at `1⁺`

For any number field `K`, Mathlib's class number formula
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` states that `(s - 1) ζ_K(s)` tends to the
positive residue `NumberField.dedekindZeta_residue K` as real `s → 1⁺`. Taking real parts gives the
real limit `(σ - 1) * (ζ_K σ).re → dedekindZeta_residue K` and hence the real-axis blowup
`(ζ_K σ).re → +∞` as real `σ → 1⁺`.

## Main results

* `TauCeti.tendsto_sub_one_mul_re_dedekindZeta_nhdsGT`: `(σ - 1) * (ζ_K σ).re → ρ` as `σ → 1⁺`.
* `TauCeti.tendsto_re_dedekindZeta_nhdsGT_one`: `(ζ_K σ).re → +∞` as `σ → 1⁺`.
-/

public section

namespace TauCeti

open Filter NumberField
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- **Real limit of `(σ - 1) * ζ_K(σ)` at `1⁺`.** As real `σ → 1⁺`,
`(σ - 1) * (ζ_K σ).re → dedekindZeta_residue K`. -/
theorem tendsto_sub_one_mul_re_dedekindZeta_nhdsGT :
    Tendsto (fun σ : ℝ ↦ (σ - 1) * (NumberField.dedekindZeta K σ).re) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  refine (Complex.ofReal_re (NumberField.dedekindZeta_residue K) ▸ h).congr fun σ ↦ ?_
  simp only [Function.comp_apply]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.re_ofReal_mul]

/-- **Real blowup of the Dedekind zeta function at `1⁺`.** As real `σ → 1⁺`, the real part of
`ζ_K(σ)` tends to `+∞`, since `(σ - 1) ζ_K(σ)` tends to the positive residue
`NumberField.dedekindZeta_residue K`. -/
theorem tendsto_re_dedekindZeta_nhdsGT_one :
    Tendsto (fun σ : ℝ ↦ (NumberField.dedekindZeta K σ).re) (𝓝[>] 1) atTop := by
  have hsub0 : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝 1) (𝓝 0) := by
    simpa using (continuous_sub_right (1 : ℝ)).tendsto 1
  have hsub : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝[>] 1) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsub0.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) ↦ sub_pos.mpr hσ)
  refine (Filter.Tendsto.atTop_mul_pos (NumberField.dedekindZeta_residue_pos K)
    (tendsto_inv_nhdsGT_zero.comp hsub) (tendsto_sub_one_mul_re_dedekindZeta_nhdsGT K)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  simp [inv_mul_cancel_left₀ (sub_ne_zero.mpr (ne_of_gt hσ))]

end TauCeti
