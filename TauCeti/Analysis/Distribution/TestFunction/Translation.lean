/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Topology.Algebra.Support
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Translation of test functions

This file translates a test function on an open set `V` in the opposite direction to a vector
`h`, producing a test function on any open set `Ω` that contains `V + h`. The codomain may be
any real normed space. This is the common test-function operation used to prove translation
invariance of weak derivatives and distributional variation.

## Main declarations

* `TauCeti.translateTestFunction`: translate a test function while changing its domain.
* `TauCeti.translateTestFunction_apply`: evaluation of a translated test function.
* `TauCeti.fderiv_translateTestFunction`: Fréchet derivatives commute with translation.
* `TauCeti.lineDeriv_translateTestFunction`: directional derivatives commute with translation.
* `TauCeti.exists_testFunction_eq_intervalIntegral`: segment averages of a test function are test
  functions.
-/

public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Set TestFunction TopologicalSpace
open scoped ContDiff
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Omega V : Opens E} {h : E}

/-- Translate a test function in the opposite direction, regarding it as a test function on an
open set containing the translated support. -/
def translateTestFunction (hVO : MapsTo (· + h) V Omega) (phi : 𝓓(V, F)) :
    𝓓(Omega, F) :=
  ⟨fun y => phi (y - h),
    phi.contDiff.comp (contDiff_id.sub contDiff_const),
    by
      simpa [sub_eq_add_neg, Function.comp_def, Homeomorph.addRight] using
        phi.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-h)),
    by
      intro y hy
      rw [tsupport_comp_sub_right] at hy
      simpa using hVO (phi.tsupport_subset hy)⟩

/-- Translating a test function evaluates it at the oppositely translated point. -/
@[simp]
theorem translateTestFunction_apply (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, F)) (y : E) : translateTestFunction hVO phi y = phi (y - h) :=
  (rfl)

/-- The Fréchet derivative of a translated test function is the translated Fréchet
derivative. -/
@[simp]
theorem fderiv_translateTestFunction (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, F)) (y : E) :
    fderiv ℝ (translateTestFunction hVO phi : E → F) y = fderiv ℝ (phi : E → F) (y - h) :=
  fderiv_comp_sub (f := (phi : E → F)) h

/-- The directional derivative of a translated test function is the translated directional
derivative. -/
@[simp]
theorem lineDeriv_translateTestFunction (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, F)) (y w : E) :
    lineDeriv ℝ (translateTestFunction hVO phi : E → F) y w =
      lineDeriv ℝ (phi : E → F) (y - h) w := by
  simp only [lineDeriv, translateTestFunction_apply, sub_eq_add_neg]
  congr 1
  funext t
  congr 1
  abel

/-- For `g ∈ 𝓓(V, F)`, the function `Φ y = ∫₀¹ g (y - t h) dt` is a test function on
`Omega`, as soon as the segments `x + [0, 1] h` starting in `V` lie in `Omega`. -/
theorem exists_testFunction_eq_intervalIntegral
    (hVO : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Omega) (g : 𝓓(V, F)) :
    ∃ Φ : 𝓓(Omega, F), ∀ y, Φ y = ∫ t in (0 : ℝ)..1, g (y - t • h) := by
  set Φ : E → F := fun y => ∫ t in (0 : ℝ)..1, g (y - t • h) with hΦ_def
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [← contDiffOn_univ]
    refine (contDiffOn_integral_smul_of_contDiffOn (n := (⊤ : ℕ∞))
      (F := fun p : E × ℝ => g (p.1 - p.2 • h)) (μ := (volume : Measure unitInterval))
      (integrable_const (1 : ℝ)) continuous_subtype_val isOpen_univ
      (g.contDiff.comp (contDiff_fst.sub (contDiff_snd.smul contDiff_const))).contDiffOn
      isOpen_univ fun _ _ _ => mem_univ _).congr fun y _ => ?_
    simp [hΦ_def, intervalIntegral_eq_integral_unitInterval]
  -- `Φ` vanishes off the compact set `C ⊆ Omega` swept out by `tsupport g` along `[0, 1] h`.
  set C : Set E := (fun p : E × ℝ => p.1 + p.2 • h) '' (tsupport g ×ˢ Icc 0 1)
  have hCc : IsCompact C :=
    (g.hasCompactSupport.isCompact.prod isCompact_Icc).image (by fun_prop)
  have hCO : C ⊆ Omega := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hVO t ht (g.tsupport_subset hx)
  have hΦC (y : E) (hy : y ∉ C) : Φ y = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : F)) fun t ht => ?_).trans
      (by simp)
    rw [uIcc_of_le zero_le_one] at ht
    exact image_eq_zero_of_notMem_tsupport fun hmem =>
      hy ⟨(y - t • h, t), ⟨hmem, ht⟩, by simp⟩
  have hsupp : support Φ ⊆ C := fun y hy => by
    by_contra hyC
    exact hy (hΦC y hyC)
  exact ⟨⟨Φ, hΦs, HasCompactSupport.intro hCc hΦC,
    (closure_minimal hsupp hCc.isClosed).trans hCO⟩, fun _ => rfl⟩

end TauCeti
