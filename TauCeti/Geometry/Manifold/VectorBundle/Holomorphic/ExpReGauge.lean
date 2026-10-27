/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas

/-!
# A real-smooth gauge that is not holomorphic

The holomorphic trivializations of a holomorphic vector bundle are the members of the maximal
atlas of the groupoid `contMDiffFiberwiseLinear B F 𝓘(ℂ, EB) n`, and a change of frame must be
a holomorphic gauge (`Bundle.Trivialization.transFiberwiseLinear_mem_maximalAtlas_iff`). This
file shows that the restriction to that maximal atlas is necessary, already for the trivial
line bundle `Bundle.Trivial ℂ ℂ` over `ℂ`.

The gauge `TauCeti.expReGauge` multiplies the fibre by `exp (re z)`. It is complex linear on
every fibre and real smooth in `z`, but not holomorphic. The gauge transform
`TauCeti.expReTrivialization` of the standard trivialization is therefore not a holomorphic
trivialization. It sends the holomorphic constant section `1` to the coordinate function
`z ↦ exp (re z)`, which is nowhere complex differentiable, so the section criterion
`Bundle.Trivialization.contMDiffAt_section_iff_of_mem_maximalAtlas` fails for it.

## Main results

* `TauCeti.contDiff_expReGauge`: the gauge is real smooth.
* `TauCeti.expReTrivialization_notMem_maximalAtlas`: its gauge transform of the standard
  trivialization is not a holomorphic trivialization.
* `TauCeti.not_contMDiffAt_section_one_iff_expReTrivialization`: the constant section `1` is
  holomorphic, while its coordinate in that gauge transform is not.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

/-- Multiplication by `exp (re z)`, a complex linear automorphism of the fibre `ℂ` depending on
`z : ℂ`. -/
noncomputable def expReGauge (z : ℂ) : ℂ ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (Real.exp z.re) (Complex.ofReal_ne_zero.2 (Real.exp_pos z.re).ne'))

@[simp]
theorem expReGauge_apply (z v : ℂ) : expReGauge z v = v * Real.exp z.re := by
  simp [expReGauge]

@[simp]
theorem expReGauge_symm_apply (z v : ℂ) : (expReGauge z).symm v = v * Real.exp (-z.re) := by
  simp [expReGauge, Real.exp_neg]

/-- As a continuous linear map, the gauge is the scalar `exp (re z)`. -/
theorem coe_expReGauge (z : ℂ) :
    (expReGauge z : ℂ →L[ℂ] ℂ) = (Real.exp z.re : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
  ext
  simp [mul_comm]

/-- As a continuous linear map, the inverse gauge is the scalar `exp (- re z)`. -/
theorem coe_expReGauge_symm (z : ℂ) :
    ((expReGauge z).symm : ℂ →L[ℂ] ℂ) = (Real.exp (-z.re) : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
  ext
  simp [mul_comm]

/-- The gauge `exp (re z)` depends real smoothly on `z`. -/
theorem contDiff_expReGauge : ContDiff ℝ ∞ fun z ↦ (expReGauge z : ℂ →L[ℂ] ℂ) := by
  simp_rw [coe_expReGauge]
  exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)).smul
    contDiff_const

/-- The function `z ↦ exp (re z)` is nowhere complex differentiable: its derivative along the real
axis is `exp (re z)`, while it is constant along the imaginary axis. -/
theorem not_differentiableAt_ofReal_exp_re (z : ℂ) :
    ¬ DifferentiableAt ℂ (fun w : ℂ ↦ (Real.exp w.re : ℂ)) z := by
  intro h
  have hc := h.hasDerivAt
  have h₁ : HasDerivAt (fun t : ℝ ↦ z + t) (1 : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add z
  have hI : HasDerivAt (fun t : ℝ ↦ z + t * Complex.I) Complex.I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add z
  -- Along the real axis the function is `t ↦ exp (re z + t)`, with derivative `exp (re z)`.
  have hre : HasDerivAt (fun t : ℝ ↦ (Real.exp (z.re + t) : ℂ)) (Real.exp z.re : ℂ) 0 := by
    simpa using (((Real.hasDerivAt_exp (z.re + 0)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add z.re)).ofReal_comp)
  have hre' := (hc.comp_of_eq 0 h₁ (by simp)).unique (by simpa [Function.comp_def] using hre)
  -- Along the imaginary axis the function is constant.
  have him := (hc.comp_of_eq 0 hI (by simp)).unique
    (by simpa [Function.comp_def] using hasDerivAt_const (0 : ℝ) (Real.exp z.re : ℂ))
  rw [mul_one] at hre'
  rw [hre'] at him
  simp at him

/-- The gauge transform of the standard trivialization of the trivial line bundle over `ℂ` by
`expReGauge`. It sends `⟨z, v⟩` to `(z, v * exp (re z))`. -/
noncomputable def expReTrivialization : Trivialization ℂ (π ℂ (Bundle.Trivial ℂ ℂ)) :=
  (Bundle.Trivial.trivialization ℂ ℂ).transFiberwiseLinear expReGauge
    (contDiff_expReGauge.continuous.continuousOn)
    (by
      simp_rw [coe_expReGauge_symm]
      exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        Complex.continuous_re.neg)).smul continuous_const).continuousOn)

@[simp]
theorem expReTrivialization_apply (p : TotalSpace ℂ (Bundle.Trivial ℂ ℂ)) :
    expReTrivialization p = (p.proj, p.2 * Real.exp p.proj.re) := by
  simp [expReTrivialization]

@[simp]
theorem baseSet_expReTrivialization : expReTrivialization.baseSet = univ := by
  simp [expReTrivialization]

/-- The gauge transform of the standard trivialization by `exp (re z)` is not a holomorphic
trivialization of the trivial line bundle over `ℂ`, at any positive order of smoothness. -/
theorem expReTrivialization_notMem_maximalAtlas {n : ℕ∞ω} (hn : n ≠ 0) :
    expReTrivialization.toOpenPartialHomeomorph ∉
      (contMDiffFiberwiseLinear ℂ ℂ 𝓘(ℂ, ℂ) n).maximalAtlas
        (TotalSpace ℂ (Bundle.Trivial ℂ ℂ)) := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization ℂ ℂ) := ⟨mem_singleton _⟩
  intro h
  have hφ := ((Trivialization.transFiberwiseLinear_mem_maximalAtlas_iff
    (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ, ℂ) n _) _ _ _).1 h).1
  rw [Bundle.Trivial.trivialization_baseSet, contMDiffOn_univ, contMDiff_iff_contDiff] at hφ
  apply not_differentiableAt_ofReal_exp_re 0
  simpa using ((hφ.differentiable hn) 0).clm_apply (differentiableAt_const (1 : ℂ))

/-- The criterion `Bundle.Trivialization.contMDiffAt_section_iff_of_mem_maximalAtlas` fails for
`expReTrivialization`: the constant section `1` of the trivial line bundle over `ℂ` is
holomorphic, but its coordinate `z ↦ exp (re z)` in this trivialization is not. -/
theorem not_contMDiffAt_section_one_iff_expReTrivialization {n : ℕ∞ω} (hn : n ≠ 0) (z : ℂ) :
    ¬ (ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) n
          (fun w ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial ℂ ℂ) w 1) z ↔
        ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) n (fun w ↦ (expReTrivialization ⟨w, 1⟩).2) z) := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization ℂ ℂ) := ⟨mem_singleton _⟩
  rw [(Bundle.Trivial.trivialization ℂ ℂ).contMDiffAt_section_iff (mem_univ z)]
  simp only [Bundle.Trivial.trivialization_apply, expReTrivialization_apply, one_mul,
    contMDiffAt_iff_contDiffAt]
  exact fun h ↦ not_differentiableAt_ofReal_exp_re z ((h.1 contDiffAt_const).differentiableAt hn)

end TauCeti
