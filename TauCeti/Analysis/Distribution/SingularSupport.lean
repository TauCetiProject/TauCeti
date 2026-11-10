/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The singular support of a distribution

Let `Ω` be an open subset of a finite-dimensional real inner product space `E`. The **singular
support** `Distribution.singSupport T` of a complex distribution `T` on `Ω` is the set of points of
`Ω` having no open neighbourhood on which `T` is a smooth function (Hörmander I, Definition 2.2.3).
It is closed in `Ω`. Its relation to the wave front set, and further properties derived from it,
are in `TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport`.

## Main declarations

* `Distribution.singSupport T`: the singular support of a complex distribution.

## Main results

* `Distribution.notMem_singSupport_iff`: a point of `Ω` lies outside the singular support exactly
  when `T` is a smooth function near it.
* `Distribution.notMem_singSupport_of_apply_eq_integral`: a point of an open set on which `T` is a
  smooth function lies outside the singular support.
* `Distribution.isOpen_diff_singSupport`: the singular support is closed in `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Definition 2.2.3.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- The **singular support** of a complex distribution `T` on `Ω`: the points `x ∈ Ω` having no
open neighbourhood `U` on which `T` is a smooth function, in the sense that `T φ = ∫ φ • f` for
every real test function `φ` supported in `U`, with `f` smooth on `U`. -/
def singSupport (T : 𝓓'(Ω, ℂ)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

theorem mem_singSupport_iff {T : 𝓓'(Ω, ℂ)} {x : E} :
    x ∈ T.singSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- A point `x ∈ Ω` lies outside the singular support of `T` exactly when `T` is a smooth function
on some open neighbourhood of `x`. -/
theorem notMem_singSupport_iff {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.singSupport ↔ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ, ContDiffOn ℝ ∞ f U ∧
      ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  ⟨fun h ↦ not_not.1 fun h' ↦ h ⟨hx, h'⟩, fun h h' ↦ h'.2 h⟩

/-- The singular support lies in `Ω`. -/
theorem singSupport_subset (T : 𝓓'(Ω, ℂ)) : T.singSupport ⊆ Ω := fun _ hx ↦ hx.1

/-- A point of an open set on which `T` is a smooth function lies outside the singular support. -/
theorem notMem_singSupport_of_apply_eq_integral {T : 𝓓'(Ω, ℂ)} {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y) {x : E} (hx : x ∈ U) :
    x ∉ T.singSupport :=
  fun h ↦ h.2 ⟨U, hU, hx, f, hf, hT⟩

/-- The singular support is closed in `Ω`. -/
theorem isOpen_diff_singSupport (T : 𝓓'(Ω, ℂ)) : IsOpen ((Ω : Set E) \ T.singSupport) := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hxΩ, hx⟩ ↦ ?_
  obtain ⟨U, hU, hxU, f, hf, hT⟩ := (notMem_singSupport_iff hxΩ).1 hx
  filter_upwards [Ω.isOpen.mem_nhds hxΩ, hU.mem_nhds hxU] with y hyΩ hyU
  exact ⟨hyΩ, notMem_singSupport_of_apply_eq_integral hU hf hT hyU⟩

end Distribution
