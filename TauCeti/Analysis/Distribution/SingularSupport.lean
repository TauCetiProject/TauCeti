/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Distribution.Support
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The singular support of a distribution

Let `Ω` be an open subset of a finite-dimensional real inner product space `E`, and `T` an
`F`-valued distribution on `Ω`. The **singular support** `Distribution.singularSupport T` is the
set of points `x ∈ Ω` near which `T` is not a smooth function: `x` lies outside it when some open
neighbourhood `U` of `x` carries a function `f`, smooth on `U`, with `T φ = ∫ φ • f` (for Lebesgue
measure) for every test function `φ` supported in `U`. It measures where a distribution fails to
be smooth, just as the support `Distribution.dsupport T` measures where it fails to vanish, and
the wave front set refines it by recording the directions of the singularities.

## Main declarations

* `Distribution.singularSupport T`: the singular support.

## Main results

* `Distribution.isOpen_diff_singularSupport`: the singular support is closed in `Ω`.
* `Distribution.singularSupport_subset_dsupport`: it lies in the support.
* `Distribution.singularSupport_ofFun`: a function smooth on `Ω` has empty singular support.
* `Distribution.singularSupport_add_subset`, `Distribution.singularSupport_smul_subset`,
  `Distribution.singularSupport_neg`, `Distribution.singularSupport_sub_subset`: the singular
  support of a sum lies in the union of the singular supports, and scalar multiples do not enlarge
  it.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2 (the singular support).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}
  {n : ℕ∞}

/-- The **singular support** of a distribution `T` on `Ω`: the points `x ∈ Ω` near which `T` is
not a smooth function, that is, which have no open neighbourhood `U` carrying a function `f`
smooth on `U` with `T φ = ∫ φ • f` for every test function `φ` supported in `U`. -/
def singularSupport (T : 𝓓'^{n}(Ω, F)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

theorem mem_singularSupport_iff {T : 𝓓'^{n}(Ω, F)} {x : E} :
    x ∈ T.singularSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- A point of `Ω` lies outside the singular support of `T` exactly when `T` is a smooth function
on an open neighbourhood of it. -/
theorem notMem_singularSupport_iff {T : 𝓓'^{n}(Ω, F)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.singularSupport ↔ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
  simp [mem_singularSupport_iff, hx]

/-- The singular support lies in `Ω`. -/
theorem singularSupport_subset (T : 𝓓'^{n}(Ω, F)) : T.singularSupport ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- The singular support is closed in `Ω`: its complement in `Ω` is open. -/
theorem isOpen_diff_singularSupport (T : 𝓓'^{n}(Ω, F)) :
    IsOpen ((Ω : Set E) \ T.singularSupport) := by
  refine isOpen_iff_forall_mem_open.2 fun x ⟨hxΩ, hx⟩ ↦ ?_
  obtain ⟨U, hU, hxU, hT⟩ := (notMem_singularSupport_iff hxΩ).1 hx
  -- The neighbourhood `U` witnesses smoothness at each of its points.
  exact ⟨U ∩ Ω, fun y ⟨hyU, hyΩ⟩ ↦ ⟨hyΩ, (notMem_singularSupport_iff hyΩ).2 ⟨U, hU, hyU, hT⟩⟩,
    hU.inter Ω.isOpen, hxU, hxΩ⟩

/-- The singular support lies in the support. -/
theorem singularSupport_subset_dsupport (T : 𝓓'^{n}(Ω, F)) : T.singularSupport ⊆ dsupport T := by
  refine fun x hx ↦ by_contra fun hxT ↦ (notMem_singularSupport_iff hx.1).2.mt (not_not.2 hx) ?_
  -- Off the support, `T` is the zero function.
  exact ⟨(dsupport T)ᶜ, isClosed_dsupport.isOpen_compl, hxT, 0, contDiffOn_const,
    fun φ hφ ↦ by simpa using isVanishingOn_compl_dsupport T φ hφ⟩

/-- The zero distribution has empty singular support. -/
@[simp]
theorem singularSupport_zero : (0 : 𝓓'^{n}(Ω, F)).singularSupport = ∅ := by
  have h : dsupport ⇑(0 : 𝓓'^{n}(Ω, F)) = ∅ := (dsupport_eq_empty_iff _).2 rfl
  exact subset_empty_iff.1 (h ▸ singularSupport_subset_dsupport 0)

/-- A function smooth on `Ω` has empty singular support. -/
@[simp]
theorem singularSupport_ofFun {f : E → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f volume n).singularSupport = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.2 ⟨Ω, Ω.isOpen, hx.1, f, hf, fun _ _ ↦
    ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)⟩

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singularSupport_add_subset (S T : 𝓓'^{n}(Ω, F)) :
    (S + T).singularSupport ⊆ S.singularSupport ∪ T.singularSupport := by
  refine fun x hx ↦ by_contra fun h ↦ hx.2 ?_
  rw [mem_union, not_or] at h
  obtain ⟨U, hU, hxU, f, hf, hS⟩ := (notMem_singularSupport_iff hx.1).1 h.1
  obtain ⟨V, hV, hxV, g, hg, hT⟩ := (notMem_singularSupport_iff hx.1).1 h.2
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, f + g, (hf.mono inter_subset_left).add
    (hg.mono inter_subset_right), fun φ hφ ↦ ?_⟩
  have hφU := hφ.trans inter_subset_left
  have hφV := hφ.trans inter_subset_right
  have hfU := hf.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet
  have hgV := hg.continuousOn.locallyIntegrableOn (μ := volume) hV.measurableSet
  rw [add_apply, hS φ hφU, hT φ hφV, ← integral_add
    (hfU.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφU)
    (hgV.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφV)]
  simp [smul_add]

/-- A scalar multiple of a distribution has no larger singular support. -/
theorem singularSupport_smul_subset {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (T : 𝓓'^{n}(Ω, F)) :
    (c • T).singularSupport ⊆ T.singularSupport := by
  refine fun x hx ↦ ⟨hx.1, fun ⟨U, hU, hxU, f, hf, hT⟩ ↦ hx.2 ⟨U, hU, hxU, c • f,
    hf.const_smul c, fun φ hφ ↦ ?_⟩⟩
  rw [smul_apply, hT φ hφ, ← integral_smul]
  exact integral_congr_ae (.of_forall fun y ↦ (smul_comm (φ y) c (f y)).symm)

/-- Negation does not change the singular support. -/
@[simp]
theorem singularSupport_neg (T : 𝓓'^{n}(Ω, F)) : (-T).singularSupport = T.singularSupport := by
  refine (subset_antisymm ?_ ?_)
  · simpa using singularSupport_smul_subset (-1 : ℝ) T
  · simpa using singularSupport_smul_subset (-1 : ℝ) (-T)

/-- The singular support of a difference lies in the union of the singular supports. -/
theorem singularSupport_sub_subset (S T : 𝓓'^{n}(Ω, F)) :
    (S - T).singularSupport ⊆ S.singularSupport ∪ T.singularSupport := by
  simpa [sub_eq_add_neg] using singularSupport_add_subset S (-T)

end Distribution
