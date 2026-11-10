/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ArctanCenter

/-!
# The distribution along a strip of a density, and its arctan center

For a density `f : ℝ × ℝ → ℝ≥0∞` on the strip `ℝ × [0, 1]`, the *strip measure*
`TauCeti.stripMeasure f` is the measure on `ℝ` giving each set `A` of `s`-values the integral of
`f` over `A × [0, 1]`: the pushforward to the `s`-axis of `f` times Lebesgue measure on the strip.
Its total mass is the integral of `f` over the strip, so it is finite and nonzero exactly when that
integral is.

Translating the density by `(c, 0)` translates the strip measure by `-c`
(`TauCeti.stripMeasure_comp_add_right`). Hence the arctan center of the strip measure
(`MeasureTheory.Measure.arctanCenter`) is translation equivariant
(`TauCeti.arctanCenter_stripMeasure_comp_add_right`), and exactly one translate of a density with
finite nonzero integral over the strip has center zero
(`TauCeti.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero`). Recentering is constant
on translation orbits (`TauCeti.arctanCenter_stripMeasure_comp_add_right_add`).

Applied to the energy density of a Floer cylinder, the strip measure is the distribution of its
energy along the strip, and its center is a global slice for the translation action on
nonstationary finite-energy Floer cylinders, in a symplectic vector space
(`TauCeti.Geometry.Symplectic.Floer.Translation.Slice`) or in a manifold
(`TauCeti.Geometry.Symplectic.Floer.Translation.Manifold`).

## Main definitions

* `TauCeti.stripMeasure f`: the distribution along the strip `ℝ × [0, 1]` of a density `f`.

## Main results

* `TauCeti.stripMeasure_apply`: the strip measure of `A` is the integral of `f` over `A × [0, 1]`.
* `TauCeti.stripMeasure_comp_add_right`: translating the density translates the strip measure.
* `TauCeti.arctanCenter_stripMeasure_comp_add_right`: the center is translation equivariant.
* `TauCeti.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero`: each translation orbit
  of a density with finite nonzero integral meets the slice of center zero exactly once.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable (f : ℝ × ℝ → ℝ≥0∞)

/-- The *strip measure* of a density `f` on the strip `ℝ × [0, 1]`: the measure on `ℝ` giving each
set `A` of `s`-values the integral of `f` over `A × [0, 1]` (`TauCeti.stripMeasure_apply`). It is
the pushforward to the `s`-axis of `f` times Lebesgue measure on the strip. -/
noncomputable def stripMeasure : Measure ℝ :=
  ((volume.restrict ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1)).withDensity f).map Prod.fst

/-- The strip measure of a measurable set `A` is the integral of the density over `A × [0, 1]`. -/
theorem stripMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) :
    stripMeasure f A = ∫⁻ z in A ×ˢ Icc 0 1, f z := by
  rw [stripMeasure, Measure.map_apply measurable_fst hA,
    withDensity_apply _ (measurable_fst hA), Measure.restrict_restrict (measurable_fst hA),
    ← prod_univ, prod_inter_prod, inter_univ, univ_inter]

/-- The total mass of the strip measure is the integral of the density over the strip. -/
theorem stripMeasure_univ : stripMeasure f univ = ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z :=
  stripMeasure_apply f MeasurableSet.univ

variable {f}

/-- The strip measure of a density of finite integral over the strip is finite. -/
theorem isFiniteMeasure_stripMeasure (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ ⊤) :
    IsFiniteMeasure (stripMeasure f) :=
  ⟨by rw [stripMeasure_univ]; exact hfin.lt_top⟩

/-- The strip measure vanishes exactly when the integral of the density over the strip does. -/
theorem stripMeasure_eq_zero_iff :
    stripMeasure f = 0 ↔ ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z = 0 := by
  rw [← Measure.measure_univ_eq_zero, stripMeasure_univ]

variable (f)

/-- **Translations translate the strip measure.** Translating the density by `(c, 0)` translates
its strip measure by `-c`. -/
theorem stripMeasure_comp_add_right (c : ℝ) :
    stripMeasure (fun z ↦ f (z + (c, 0))) = (stripMeasure f).map (· - c) := by
  ext A hA
  have hpre : A ×ˢ Icc (0 : ℝ) 1 = (· + (c, 0)) ⁻¹' (((· - c) ⁻¹' A) ×ˢ Icc 0 1) := by
    ext z
    simp
  have hv : MeasurePreserving (· + ((c, 0) : ℝ × ℝ)) volume volume :=
    (measurePreserving_add_right volume c).prod (measurePreserving_add_right volume 0)
  rw [Measure.map_apply (measurable_sub_const c) hA, stripMeasure_apply _ hA,
    stripMeasure_apply _ (measurable_sub_const c hA), hpre]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (c, 0)) f _

variable {f}

/-- **Translation equivariance of the center.** For a density of finite nonzero integral over the
strip, the arctan center of the strip measure of its translate by `(c, 0)` is that of the density
minus `c`. -/
theorem arctanCenter_stripMeasure_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ 0) (c : ℝ) :
    (stripMeasure fun z ↦ f (z + (c, 0))).arctanCenter = (stripMeasure f).arctanCenter - c := by
  have := isFiniteMeasure_stripMeasure hfin
  have : NeZero (stripMeasure f) := ⟨fun h ↦ hE (stripMeasure_eq_zero_iff.1 h)⟩
  simp_rw [stripMeasure_comp_add_right, sub_eq_add_neg, Measure.arctanCenter_map_add]

/-- **Each translation orbit meets the slice once.** For a density of finite nonzero integral over
the strip, there is exactly one translation by `(c, 0)` after which the arctan center of the strip
measure is `0`; it is translation by the center of the density. -/
theorem existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ 0) :
    ∃! c : ℝ, (stripMeasure fun z ↦ f (z + (c, 0))).arctanCenter = 0 := by
  simp_rw [arctanCenter_stripMeasure_comp_add_right hfin hE, sub_eq_zero]
  exact ⟨_, rfl, fun _ h ↦ h.symm⟩

/-- **Recentering is constant on translation orbits.** For a density of finite nonzero integral
over the strip, translating its translate by `(c, 0)` further by the center of that translate is
translating the density by its own center. So recentering is a section of the quotient by
translations, with values in the slice of center zero. -/
theorem arctanCenter_stripMeasure_comp_add_right_add
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z ≠ 0) (c : ℝ) :
    (((stripMeasure fun z ↦ f (z + (c, 0))).arctanCenter, 0) + (c, 0) : ℝ × ℝ) =
      ((stripMeasure f).arctanCenter, 0) := by
  rw [arctanCenter_stripMeasure_comp_add_right hfin hE]
  ext <;> simp

end TauCeti
