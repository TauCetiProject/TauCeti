/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support

/-!
# The singular support of a distribution

A distribution `T` on an open set `Ω` is *smooth at* a point `x` (`Distribution.IsSmoothAt`) if
near `x` it is integration against a smooth function: there are an open neighbourhood `U` of `x`
and a function `f`, smooth on `U`, such that `T φ = ∫ φ • f` for every test function `φ`
supported in `U`. The **singular support** `Distribution.singularSupport T` is the set of points
of `Ω` at which `T` is not smooth. For complex distributions on a finite-dimensional real inner
product space it is the base projection of the wave front set
(`Distribution.fst_image_waveFrontSet`).

## Main declarations

* `Distribution.IsSmoothAt T x`: `T` agrees with a smooth function near `x`.
* `Distribution.singularSupport T`: the points of `Ω` at which `T` is not smooth.

## Main results

* `Distribution.isOpen_setOf_isSmoothAt`: the set of points at which `T` is smooth is open, so
  the singular support is relatively closed in `Ω`.
* `Distribution.singularSupport_subset_dsupport`: the singular support lies in the support.
* `Distribution.singularSupport_ofFun_eq_empty`: a function smooth on `Ω` has empty singular
  support.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Definition 2.2.3.
-/

public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- A distribution `T` on `Ω` is **smooth at** `x` if near `x` it is integration against a smooth
function: there are an open set `U` containing `x` and a function `f` smooth on `U` such that
`T φ = ∫ φ • f` for every test function `φ` supported in `U`. -/
def IsSmoothAt (T : 𝓓'^{n}(Ω, F)) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y

/-- Unfolds `IsSmoothAt` into its neighbourhood and smooth representative. -/
theorem isSmoothAt_iff {T : 𝓓'^{n}(Ω, F)} {x : E} :
    T.IsSmoothAt x ↔ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
      ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- The set of points at which a distribution is smooth is open. -/
theorem isOpen_setOf_isSmoothAt (T : 𝓓'^{n}(Ω, F)) : IsOpen {x | T.IsSmoothAt x} :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, hU, hxU, h⟩ ↦ ⟨U, fun _ hy ↦ ⟨U, hU, hy, h⟩, hU, hxU⟩

/-- A distribution vanishing near `x` is smooth at `x`. -/
theorem isSmoothAt_of_notMem_dsupport {T : 𝓓'^{n}(Ω, F)} {x : E} (hx : x ∉ dsupport T) :
    T.IsSmoothAt x := by
  obtain ⟨U, hT, hU, hxU⟩ := (notMem_dsupport_iff x).1 hx
  exact ⟨U, hU, hxU, 0, contDiffOn_const, fun φ hφ ↦ by simp [hT φ hφ]⟩

/-- The **singular support** of a distribution `T` on `Ω`: the points of `Ω` at which `T` is not
smooth. -/
def singularSupport (T : 𝓓'^{n}(Ω, F)) : Set E :=
  {x | x ∈ Ω ∧ ¬T.IsSmoothAt x}

@[simp]
theorem mem_singularSupport_iff {T : 𝓓'^{n}(Ω, F)} {x : E} :
    x ∈ T.singularSupport ↔ x ∈ Ω ∧ ¬T.IsSmoothAt x :=
  Iff.rfl

/-- The singular support lies in `Ω`. -/
theorem singularSupport_subset (T : 𝓓'^{n}(Ω, F)) : T.singularSupport ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- The singular support of a distribution lies in its support. -/
theorem singularSupport_subset_dsupport (T : 𝓓'^{n}(Ω, F)) : T.singularSupport ⊆ dsupport T :=
  fun _ hx ↦ by_contra fun h ↦ hx.2 (isSmoothAt_of_notMem_dsupport h)

/-- A locally integrable function on `Ω` is smooth, as a distribution, at every point near which
it is a smooth function. -/
theorem isSmoothAt_ofFun [OpensMeasurableSpace E] {f : E → F} (hf : LocallyIntegrableOn f Ω)
    {U : Set E} (hU : IsOpen U) (hfU : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) :
    (ofFun Ω f volume n).IsSmoothAt x :=
  ⟨U, hU, hx, f, hfU, fun _ _ ↦ ofFun_apply hf⟩

/-- A function smooth on `Ω` has empty singular support. -/
theorem singularSupport_ofFun_eq_empty [OpensMeasurableSpace E] [SecondCountableTopology E]
    [IsLocallyFiniteMeasure (volume : Measure E)] {f : E → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f volume n).singularSupport = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.2 <| isSmoothAt_ofFun
    (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) Ω.isOpen hf hx.1

end Distribution
