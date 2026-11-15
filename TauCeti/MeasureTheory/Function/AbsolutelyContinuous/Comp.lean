/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth maps composed with absolutely continuous curves

Locally Lipschitz maps preserve the absolute continuity of metric-valued curves under composition,
and isometries moreover reflect it.
In particular, a map that is continuously differentiable near every point of the compact trace of
an absolutely continuous curve preserves absolute continuity: this gives the principal logarithm
of a curve in the slit plane and the quotient of two curves with nonvanishing denominator.
-/

public section

open Set

/-- A locally Lipschitz map preserves the absolute continuity of a metric-valued curve whose
trace lies in its domain of local Lipschitz continuity. -/
theorem LocallyLipschitzOn.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {φ : X → Y} {γ : ℝ → X}
    {s : Set X} {a b : ℝ} (hφ : LocallyLipschitzOn s φ)
    (hmap : MapsTo γ (uIcc a b) s) (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  obtain ⟨K, hK⟩ := (hφ.mono hmap.image_subset).exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn')
  exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

/-- Post-composition with an isometry preserves and reflects the absolute continuity of a
metric-valued curve. -/
theorem Isometry.absolutelyContinuousOnInterval_comp_iff
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} (hf : Isometry f)
    {γ : ℝ → X} {a b : ℝ} :
    AbsolutelyContinuousOnInterval (f ∘ γ) a b ↔ AbsolutelyContinuousOnInterval γ a b := by
  simp only [absolutelyContinuousOnInterval_iff, Function.comp_apply, hf.dist_eq]

namespace AbsolutelyContinuousOnInterval

/-- Composing an absolutely continuous curve with a map that is `C¹` at every point of its trace
preserves absolute continuity. The smoothness assumption is local to the trace. -/
theorem comp_of_contDiffAt {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {γ : ℝ → F} {φ : F → G} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hφ : ∀ x ∈ γ '' uIcc a b, ContDiffAt ℝ 1 φ x) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  have hloc : LocallyLipschitzOn (γ '' uIcc a b) φ := by
    intro x hx
    obtain ⟨K, U, hU, hLip⟩ := (hφ x hx).exists_lipschitzOnWith
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  exact hloc.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

/-- The logarithm of an absolutely continuous real function that does not vanish on the interval
is absolutely continuous. -/
protected theorem log {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) :
    AbsolutelyContinuousOnInterval (fun t ↦ Real.log (f t)) a b :=
  hf.comp_of_contDiffAt fun _ ⟨t, ht, hft⟩ ↦ Real.contDiffAt_log.2 (hft ▸ h0 t ht)

/-- The principal logarithm of an absolutely continuous complex curve that stays in the slit plane
is absolutely continuous. -/
protected theorem clog {σ : ℝ → ℂ} {a b : ℝ} (hσ : AbsolutelyContinuousOnInterval σ a b)
    (h : ∀ t ∈ uIcc a b, σ t ∈ Complex.slitPlane) :
    AbsolutelyContinuousOnInterval (fun t ↦ Complex.log (σ t)) a b :=
  hσ.comp_of_contDiffAt fun _ ⟨t, ht, hσt⟩ ↦
    (Complex.contDiffAt_log (hσt ▸ h t ht)).restrict_scalars ℝ

/-- The inverse of an absolutely continuous curve valued in a normed field is absolutely
continuous when it does not vanish on the interval. -/
@[to_fun]
protected theorem inv {K : Type*} [NormedField K] [NormedAlgebra ℝ K] {g : ℝ → K} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (h0 : ∀ t ∈ uIcc a b, g t ≠ 0) :
    AbsolutelyContinuousOnInterval g⁻¹ a b :=
  hg.comp_of_contDiffAt (φ := fun x : K ↦ x⁻¹) fun _ ⟨t, ht, hgt⟩ ↦
    hgt ▸ contDiffAt_inv ℝ (h0 t ht)

/-- The quotient of two absolutely continuous curves valued in a normed field is absolutely
continuous when the denominator does not vanish on the interval. -/
@[to_fun]
protected theorem div {K : Type*} [NormedField K] [NormedAlgebra ℝ K] {f g : ℝ → K}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) (h0 : ∀ t ∈ uIcc a b, g t ≠ 0) :
    AbsolutelyContinuousOnInterval (f / g) a b := by
  simpa only [div_eq_mul_inv, smul_eq_mul] using hf.smul (hg.inv h0)

end AbsolutelyContinuousOnInterval
