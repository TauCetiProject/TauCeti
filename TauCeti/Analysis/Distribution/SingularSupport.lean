/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Distribution.Support

/-!
# The singular support of a distribution

Let `Ω` be an open subset of a finite-dimensional real inner product space `E`, with its Lebesgue
measure. A distribution `T` on `Ω` is a smooth function near a point `x ∈ Ω` if there are an open
neighbourhood `U` of `x` and a function `f` smooth on `U` such that `T φ = ∫ φ • f` for every test
function `φ` supported in `U`. The **singular support** `Distribution.singularSupport T` is the set
of points of `Ω` near which `T` is not a smooth function. It is the part of `Ω` that regularity
theory has to control: elliptic regularity says that an elliptic operator does not enlarge it, and
the wave front set refines it by recording the singular directions over each of its points.

## Main declarations

* `Distribution.singularSupport T`: the singular support of `T`.

## Main results

* `Distribution.notMem_singularSupport_of_apply_eq_integral` and
  `Distribution.exists_apply_eq_integral_of_notMem_singularSupport`: a point of `Ω` lies outside
  the singular support exactly when `T` is a smooth function near it.
* `Distribution.isOpen_diff_singularSupport`: the singular support is closed in `Ω`.
* `Distribution.singularSupport_subset_dsupport`: it lies in the support of `T`.
* `Distribution.singularSupport_ofFun_eq_empty`: a function smooth on `Ω` has empty singular
  support.
* `Distribution.singularSupport_add_subset`, `Distribution.singularSupport_smul_subset`,
  `Distribution.singularSupport_smul`, `Distribution.singularSupport_neg`,
  `Distribution.singularSupport_sub_subset`: behaviour under the linear operations.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Definition 2.2.3.
-/

public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {n : ℕ∞}

/-- The **singular support** of a distribution `T` on `Ω`: the points `x ∈ Ω` near which `T` is
not a smooth function, that is, for which there are no open neighbourhood `U` of `x` and function
`f` smooth on `U` with `T φ = ∫ φ • f` for every test function `φ` supported in `U`. -/
def singularSupport (T : 𝓓'^{n}(Ω, F)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

theorem mem_singularSupport_iff {T : 𝓓'^{n}(Ω, F)} {x : E} :
    x ∈ T.singularSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- The singular support lies in `Ω`. -/
theorem singularSupport_subset (T : 𝓓'^{n}(Ω, F)) : T.singularSupport ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- If `T` is a function `f` smooth on an open set `U`, in the sense that `T φ = ∫ φ • f` for every
test function `φ` supported in `U`, then no point of `U` lies in the singular support of `T`. -/
theorem notMem_singularSupport_of_apply_eq_integral {T : 𝓓'^{n}(Ω, F)} {U : Set E}
    (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    (hT : ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y) {x : E} (hx : x ∈ U) :
    x ∉ T.singularSupport :=
  fun h ↦ h.2 ⟨U, hU, hx, f, hf, hT⟩

/-- Near a point of `Ω` outside its singular support, `T` is a smooth function: there are an open
neighbourhood `U ⊆ Ω` of the point and a function `f` smooth on `U` with `T φ = ∫ φ • f` for every
test function `φ` supported in `U`. -/
theorem exists_apply_eq_integral_of_notMem_singularSupport {T : 𝓓'^{n}(Ω, F)} {x : E}
    (hxΩ : x ∈ Ω) (hx : x ∉ T.singularSupport) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
      ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
  obtain ⟨U, hU, hxU, f, hf, hT⟩ := not_not.1 fun h ↦ hx ⟨hxΩ, h⟩
  exact ⟨U ∩ Ω, hU.inter Ω.isOpen, ⟨hxU, hxΩ⟩, inter_subset_right, f,
    hf.mono inter_subset_left, fun φ hφ ↦ hT φ (hφ.trans inter_subset_left)⟩

/-- The singular support is closed in `Ω`. -/
theorem isOpen_diff_singularSupport (T : 𝓓'^{n}(Ω, F)) :
    IsOpen ((Ω : Set E) \ T.singularSupport) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  obtain ⟨U, hU, hxU, hUΩ, f, hf, hT⟩ :=
    exists_apply_eq_integral_of_notMem_singularSupport hx.1 hx.2
  exact ⟨U, fun y hy ↦ ⟨hUΩ hy, notMem_singularSupport_of_apply_eq_integral hU hf hT hy⟩, hU,
    hxU⟩

/-- The singular support lies in the support: outside its support `T` is the zero function. -/
theorem singularSupport_subset_dsupport (T : 𝓓'^{n}(Ω, F)) :
    T.singularSupport ⊆ dsupport T := fun x hx ↦ by_contra fun hxT ↦
  notMem_singularSupport_of_apply_eq_integral (f := 0) isClosed_dsupport.isOpen_compl
    contDiffOn_const (fun φ hφ ↦ by
      simpa using map_eq_zero_of_disjoint_dsupport T (disjoint_compl_left.mono_left hφ)) hxT hx

/-- The zero distribution has empty singular support. -/
@[simp]
theorem singularSupport_zero : (0 : 𝓓'^{n}(Ω, F)).singularSupport = ∅ :=
  eq_empty_of_forall_notMem fun _ ↦
    notMem_singularSupport_of_apply_eq_integral (f := 0) isOpen_univ contDiffOn_const
      (fun _ _ ↦ by simp) (mem_univ _)

/-- A function smooth on `Ω` has empty singular support. -/
theorem singularSupport_ofFun_eq_empty {f : E → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f volume n).singularSupport = ∅ :=
  eq_empty_of_forall_notMem fun _ hx ↦
    notMem_singularSupport_of_apply_eq_integral Ω.isOpen hf
      (fun _ _ ↦ ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet))
      (singularSupport_subset _ hx) hx

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singularSupport_add_subset (S T : 𝓓'^{n}(Ω, F)) :
    (S + T).singularSupport ⊆ S.singularSupport ∪ T.singularSupport := by
  intro x hx
  by_contra h
  obtain ⟨hS, hT⟩ := not_or.1 h
  obtain ⟨U, hU, hxU, -, f, hf, hSf⟩ := exists_apply_eq_integral_of_notMem_singularSupport hx.1 hS
  obtain ⟨V, hV, hxV, -, g, hg, hTg⟩ := exists_apply_eq_integral_of_notMem_singularSupport hx.1 hT
  refine notMem_singularSupport_of_apply_eq_integral (hU.inter hV)
    ((hf.mono inter_subset_left).add (hg.mono inter_subset_right)) (fun φ hφ ↦ ?_) ⟨hxU, hxV⟩ hx
  -- A test function supported in an open set `W` is integrable against a function continuous on
  -- `W`, being a test function on `W`.
  have hint {W : Set E} (hW : IsOpen W) {h : E → F} (hh : ContinuousOn h W) (hφW : tsupport φ ⊆ W) :
      Integrable fun y ↦ φ y • h y :=
    TestFunction.integrable_smul (Ω := ⟨W, hW⟩) ⟨φ, φ.contDiff, φ.hasCompactSupport, hφW⟩
      (hh.locallyIntegrableOn hW.measurableSet)
  have hφU := hφ.trans inter_subset_left
  have hφV := hφ.trans inter_subset_right
  simp only [add_apply, smul_add, hSf φ hφU, hTg φ hφV]
  exact (integral_add (hint hU hf.continuousOn hφU) (hint hV hg.continuousOn hφV)).symm

section Smul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- A scalar multiple does not enlarge the singular support. -/
theorem singularSupport_smul_subset (c : 𝕜) (T : 𝓓'^{n}(Ω, F)) :
    (c • T).singularSupport ⊆ T.singularSupport := by
  intro x hx
  by_contra hT
  obtain ⟨U, hU, hxU, -, f, hf, hTf⟩ := exists_apply_eq_integral_of_notMem_singularSupport hx.1 hT
  refine notMem_singularSupport_of_apply_eq_integral hU (hf.const_smul c) (fun φ hφ ↦ ?_) hxU hx
  simp only [smul_apply, hTf φ hφ, ← integral_smul]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ (smul_comm (φ y) c (f y)).symm)

/-- A nonzero scalar multiple has the same singular support. -/
theorem singularSupport_smul {c : 𝕜} (hc : c ≠ 0) (T : 𝓓'^{n}(Ω, F)) :
    (c • T).singularSupport = T.singularSupport :=
  (singularSupport_smul_subset c T).antisymm <| by
    simpa [smul_smul, inv_mul_cancel₀ hc] using singularSupport_smul_subset c⁻¹ (c • T)

end Smul

/-- The negative of a distribution has the same singular support. -/
@[simp]
theorem singularSupport_neg (T : 𝓓'^{n}(Ω, F)) : (-T).singularSupport = T.singularSupport := by
  simpa using singularSupport_smul (𝕜 := ℝ) (neg_ne_zero.2 one_ne_zero) T

/-- The singular support of a difference lies in the union of the singular supports. -/
theorem singularSupport_sub_subset (S T : 𝓓'^{n}(Ω, F)) :
    (S - T).singularSupport ⊆ S.singularSupport ∪ T.singularSupport := by
  simpa [sub_eq_add_neg] using singularSupport_add_subset S (-T)

end Distribution
