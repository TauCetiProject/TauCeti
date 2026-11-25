/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Slicing Lebesgue measure on `ι → ℝ` along the diagonal lines

On `ι → ℝ`, Lebesgue integrals split along the diagonal lines `u ↦ z - u·1`, weighted by the
indicator of the slab `{z | z i₀ ∈ [0, 1]}`, which cuts out a parameter interval of Lebesgue
measure one on each line. The proof transports the integral along the measure-preserving shear
`(u, z) ↦ (u, z - u·1)` of `ℝ × (ι → ℝ)`. This decomposition reduces a risk comparison between
location-equivariant estimators to a comparison on each line.

## Main results

* `TauCeti.lintegral_eq_lintegral_indicator_mul_lintegral_sub_const`: the decomposition for
  Lebesgue measure.
* `TauCeti.lintegral_withDensity_eq_lintegral_indicator_mul_lintegral_sub_const`: the
  decomposition for Lebesgue measure weighted by an a.e. measurable density.

The decomposition is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Inference/Families.lean` (`lintegral_eq_lintegral_indicator_mul_lintegral_sub_const`,
for `ι = Fin n` and measurable integrands).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Decomposition of Lebesgue measure on `ι → ℝ` along the diagonal lines.** The lower
integral of an a.e. measurable `H` over `ι → ℝ` is the integral, against the indicator of
`z i₀ ∈ [0, 1]`, of the integrals of `H` along the lines `u ↦ z - u·1`, each taken with respect to
Lebesgue measure in the parameter `u`. The condition `z i₀ - u ∈ [0, 1]` cuts out a parameter
interval of Lebesgue measure one on each line (not a Euclidean segment of length one).

The proof is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Inference/Families.lean` (`lintegral_eq_lintegral_indicator_mul_lintegral_sub_const`, for
`ι = Fin n` and measurable `H`). -/
theorem lintegral_eq_lintegral_indicator_mul_lintegral_sub_const (i₀ : ι)
    {H : (ι → ℝ) → ℝ≥0∞} (hH : AEMeasurable H) :
    ∫⁻ x, H x =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) * ∫⁻ u : ℝ, H fun i ↦ z i - u := by
  set k : ℝ → ℝ≥0∞ := (Icc (0 : ℝ) 1).indicator 1 with hkdef
  have hk : Measurable k := measurable_one.indicator measurableSet_Icc
  have hk1 (t : ℝ) : ∫⁻ u, k (t + u) = 1 := by
    rw [lintegral_add_left_eq_self k t, hkdef, lintegral_indicator_one measurableSet_Icc,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have hktop (t : ℝ) : k t ≠ ∞ := by
    simp only [hkdef, indicator_apply]
    split_ifs <;> simp
  -- The shear `(u, z) ↦ (u, z - u·1)` preserves Lebesgue measure on `ℝ × (ι → ℝ)`.
  have hΨ : MeasurePreserving (fun p : ℝ × (ι → ℝ) ↦ (p.1, fun i ↦ p.2 i - p.1))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).skew_product (g := fun u (z : ι → ℝ) i ↦ z i - u)
      (by fun_prop) (ae_of_all _ fun u ↦ (measurePreserving_sub_right volume fun _ ↦ u).map_eq)
  -- The integrand `(u, y) ↦ k (y i₀ + u) * H y`, which the shear turns into
  -- `(u, z) ↦ k (z i₀) * H (z - u·1)`.
  set F : ℝ × (ι → ℝ) → ℝ≥0∞ := fun p ↦ k (p.2 i₀ + p.1) * H p.2
  have hF : AEMeasurable F (volume.prod volume) :=
    (hk.comp (by fun_prop : Measurable fun p : ℝ × (ι → ℝ) ↦ p.2 i₀ + p.1)).aemeasurable.mul
      (hH.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  calc ∫⁻ x, H x = ∫⁻ y : ι → ℝ, ∫⁻ u : ℝ, F (u, y) := by
        refine lintegral_congr fun y ↦ ?_
        simp only [F]
        rw [lintegral_mul_const (f := fun u ↦ k (y i₀ + u)) _ (hk.comp (measurable_const_add _)),
          hk1, one_mul]
    _ = ∫⁻ p : ℝ × (ι → ℝ), F (p.1, fun i ↦ p.2 i - p.1) ∂(volume.prod volume) := by
        rw [hΨ.lintegral_comp' hF, lintegral_prod_symm _ hF]
    _ = ∫⁻ z : ι → ℝ, ∫⁻ u : ℝ, k (z i₀) * H fun i ↦ z i - u := by
        rw [lintegral_prod_symm (fun p : ℝ × (ι → ℝ) ↦ F (p.1, fun i ↦ p.2 i - p.1))
          (hF.comp_quasiMeasurePreserving hΨ.quasiMeasurePreserving)]
        simp only [F, sub_add_cancel]
    _ = ∫⁻ z : ι → ℝ, k (z i₀) * ∫⁻ u : ℝ, H fun i ↦ z i - u :=
        lintegral_congr fun z ↦ lintegral_const_mul' _ _ (hktop _)

/-- **Decomposition of a weighted Lebesgue measure on `ι → ℝ` along the diagonal lines.** For an
a.e. measurable density `d` and an integrand `G` that is a.e. measurable for
`volume.withDensity d`, the lower integral of `G` against `volume.withDensity d` is the integral,
against the indicator of `z i₀ ∈ [0, 1]`, of the integrals of `d * G` along the lines
`u ↦ z - u·1` in the parameter `u`. -/
theorem lintegral_withDensity_eq_lintegral_indicator_mul_lintegral_sub_const (i₀ : ι)
    {d : (ι → ℝ) → ℝ≥0∞} (hd : AEMeasurable d) {G : (ι → ℝ) → ℝ≥0∞}
    (hG : AEMeasurable G (volume.withDensity d)) :
    ∫⁻ x, G x ∂volume.withDensity d =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) *
        ∫⁻ u : ℝ, d (fun i ↦ z i - u) * G fun i ↦ z i - u := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hd hG]
  refine lintegral_eq_lintegral_indicator_mul_lintegral_sub_const i₀ ?_
  -- `d * G` agrees with `d` times a measurable representative of `G` off `{d = 0}`.
  refine (hd.mul hG.measurable_mk.aemeasurable).congr ?_
  filter_upwards [(ae_withDensity_iff' hd).1 hG.ae_eq_mk] with x hx
  by_cases h0 : d x = 0
  · simp [h0]
  · simp [hx h0]

end TauCeti
