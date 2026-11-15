/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Local potentials of `ℂ`-linear covector fields

For a function `f : ℂ → F` taking values in a complex normed space `F`, multiplication `v ↦ v • f z`
defines the `ℂ`-linear covector `ContinuousLinearMap.toSpanSingleton ℂ (f z)`, whose restriction of
scalars `(ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ : ℂ →L[ℝ] F` is an
`ℝ`-linear covector field on `ℂ`.

When `F` is complete, Morera's theorem on discs (`Complex.IsConservativeOn.isExactOn_ball`,
`DifferentiableOn.isExactOn_ball`) together with analyticity of complex primitives
(`DifferentiableOn.contDiffOn`) shows that this covector field has local `C¹` potentials on an open
set `Ω ⊆ ℂ` whenever `f` is continuous and conservative on `Ω`, and that it has local potentials on
`Ω` if and only if `Ω` is open and `f` is holomorphic on `Ω`
(`TauCeti.hasLocalPotentials_toSpanSingleton_iff`). Non-`ℂ`-linear real covector fields such as
`dx = Complex.reCLM` have local potentials without arising from any `f : ℂ → F`.

## Main declarations

* `TauCeti.hasLocalPotentials_toSpanSingleton_of_isExactOn`: a complex primitive on an open set
  supplies local `C¹` potentials for the `ℂ`-linear covector field of `f`.
* `TauCeti.hasLocalPotentials_toSpanSingleton_of_isConservativeOn`: Morera's theorem on discs gives
  local `C¹` potentials from vanishing rectangle integrals.
* `TauCeti.hasLocalPotentials_toSpanSingleton_iff`: `(toSpanSingleton ℂ (f ·)).restrictScalars ℝ`
  has local potentials on `Ω` if and only if `Ω` is open and `f` is `ℂ`-differentiable on `Ω`.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §§1.3, 2.3, 4.2.
-/

public section

open Set Metric Complex ContinuousLinearMap
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- If `f : ℂ → F` has a complex primitive on an open set `Ω`, then the real-restricted covector
field `z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ` has local `C¹` potentials on `Ω`. -/
theorem hasLocalPotentials_toSpanSingleton_of_isExactOn {Ω : Set ℂ} {f : ℂ → F}
    (hΩ : IsOpen Ω) (hf : Complex.IsExactOn f Ω) :
    HasLocalPotentials Ω (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) := by
  obtain ⟨g, hg⟩ := hf
  have hg_diff : DifferentiableOn ℂ g Ω :=
    fun z hz ↦ (hg z hz).differentiableAt.differentiableWithinAt
  have hg_c1 : ContDiffOn ℝ 1 g Ω := (hg_diff.contDiffOn (n := 1) hΩ).restrict_scalars ℝ
  exact hasLocalPotentials_of_hasFDerivAt hΩ hg_c1 fun z hz ↦
    (hg z hz).hasFDerivAt.restrictScalars ℝ

/-- By Morera's theorem on discs, a continuous conservative function `f : ℂ → F` on an open set `Ω`
gives local `C¹` potentials for `z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ`. -/
theorem hasLocalPotentials_toSpanSingleton_of_isConservativeOn {Ω : Set ℂ} {f : ℂ → F}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω) (hcons : Complex.IsConservativeOn f Ω) :
    HasLocalPotentials Ω (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) := by
  rw [hasLocalPotentials_iff]
  intro z hz
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ z hz
  have hex : Complex.IsExactOn f (ball z r) :=
    (hcons.mono hrΩ).isExactOn_ball (hcont.mono hrΩ)
  obtain ⟨g, hg⟩ := hex
  have hg_diff : DifferentiableOn ℂ g (ball z r) :=
    fun w hw ↦ (hg w hw).differentiableAt.differentiableWithinAt
  exact ⟨r, hr, hrΩ, g, (hg_diff.contDiffOn (n := 1) isOpen_ball).restrict_scalars ℝ,
    fun w hw ↦ (hg w hw).hasFDerivAt.restrictScalars ℝ⟩

/-- For a complete complex normed space `F`, the `ℂ`-linear covector field
`z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ` has local `C¹` potentials on `Ω` if and only if
`Ω` is open and `f` is holomorphic (`DifferentiableOn ℂ f Ω`). -/
theorem hasLocalPotentials_toSpanSingleton_iff {Ω : Set ℂ} {f : ℂ → F} :
    HasLocalPotentials Ω (fun z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ) ↔
      IsOpen Ω ∧ DifferentiableOn ℂ f Ω := by
  refine ⟨fun hφ ↦ ⟨hφ.isOpen, fun z hz ↦ ?_⟩,
    fun ⟨hΩ, hf⟩ ↦ hasLocalPotentials_toSpanSingleton_of_isConservativeOn hΩ
      hf.continuousOn hf.isConservativeOn⟩
  obtain ⟨r, hr, -, g, -, hd⟩ := hasLocalPotentials_iff.mp hφ z hz
  have hex : Complex.IsExactOn f (ball z r) :=
    ⟨g, fun w hw ↦ by simpa using (hasFDerivAt_of_restrictScalars ℝ (hd w hw) rfl).hasDerivAt⟩
  have hdiff_ball : DifferentiableOn ℂ f (ball z r) := hex.differentiableOn isOpen_ball
  exact ((hdiff_ball z (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds z hr)).differentiableWithinAt

end TauCeti
