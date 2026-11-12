/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Support

/-!
# The singular support of a distribution

The *singular support* of a distribution `T` on an open set `Ω` consists of the points of `Ω`
near which `T` is not a smooth function: `x ∉ singularSupport T` when there are an open
neighbourhood `U` of `x` and a function `f` smooth on `U` with `T φ = ∫ φ • f` for every real test
function `φ` supported in `U`. It is a relatively closed subset of `Ω` contained in the support of
`T`.

## Main declarations

* `Distribution.singularSupport`: the singular support of a distribution.
* `Distribution.isOpen_diff_singularSupport`: the singular support is closed in `Ω`.
* `Distribution.singularSupport_subset_dsupport`: it lies in the support.
* `Distribution.singularSupport_ofFun_eq_empty`: a function smooth on `Ω` has empty singular
  support.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2.
-/

public section

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Distributions ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The **singular support** of a distribution `T` on `Ω`: the points `x ∈ Ω` having no open
neighbourhood `U` on which `T` is a smooth function, that is, no function `f` smooth on `U` with
`T φ = ∫ φ • f` for every real test function `φ` supported in `U`. -/
def singularSupport (T : 𝓓'(Ω, F)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

@[simp]
theorem mem_singularSupport_iff {T : 𝓓'(Ω, F)} {x : E} :
    x ∈ T.singularSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- A point of `Ω` lies outside the singular support of `T` exactly when `T` is a smooth function
on an open neighbourhood of it. -/
theorem notMem_singularSupport_iff {T : 𝓓'(Ω, F)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.singularSupport ↔ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
  simp [hx]

/-- The singular support lies in `Ω`. -/
theorem singularSupport_subset (T : 𝓓'(Ω, F)) : T.singularSupport ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- The singular support is closed in `Ω`: the points of `Ω` near which `T` is smooth form an
open set. -/
theorem isOpen_diff_singularSupport (T : 𝓓'(Ω, F)) :
    IsOpen ((Ω : Set E) \ T.singularSupport) := by
  refine isOpen_iff_forall_mem_open.2 fun x ⟨hxΩ, hx⟩ ↦ ?_
  obtain ⟨U, hU, hxU, hT⟩ := (notMem_singularSupport_iff hxΩ).1 hx
  exact ⟨U ∩ Ω, fun y ⟨hyU, hyΩ⟩ ↦ ⟨hyΩ, fun hy ↦ hy.2 ⟨U, hU, hyU, hT⟩⟩,
    hU.inter Ω.isOpen, hxU, hxΩ⟩

/-- The singular support lies in the support: `T` is the zero function on the open set where it
vanishes. -/
theorem singularSupport_subset_dsupport (T : 𝓓'(Ω, F)) : T.singularSupport ⊆ dsupport T := by
  intro x hx
  by_contra hxT
  obtain ⟨s, hT, hs, hxs⟩ := (notMem_dsupport_iff x).1 hxT
  exact hx.2 ⟨s, hs, hxs, 0, contDiffOn_const, fun φ hφ ↦ by simpa using hT φ hφ⟩

/-- The zero distribution has empty singular support. -/
@[simp]
theorem singularSupport_zero : (0 : 𝓓'(Ω, F)).singularSupport = ∅ := by
  refine subset_empty_iff.1 ((singularSupport_subset_dsupport 0).trans ?_)
  exact ((dsupport_eq_empty_iff _).2 rfl).subset

/-- A function smooth on `Ω` has empty singular support. -/
theorem singularSupport_ofFun_eq_empty {f : E → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f volume ⊤).singularSupport = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.2 ⟨Ω, Ω.isOpen, hx.1, f, hf, fun _ _ ↦
    ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)⟩

end Distribution
