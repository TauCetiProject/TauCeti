/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Bump functions realizing covectors

For `1 ≤ n` and a point `x` of a manifold `M`, the derivative at `x` of vector-valued `C^n` maps is
a continuous linear map `ContMDiffMap.mvfderivCLM : C^n(M, F) →L (T_x M →L F)` for the weak
Whitney topology. Over the reals this map is split surjective, and the splitting is realized by
compactly supported functions. For a smooth bump function `β` at `x`, the map
`ξ ↦ (y ↦ ξ (β y • φ y))`, where `φ` is the extended chart at `x`, is a continuous linear map
`(E →L F) →L C^n(M, F)` (`SmoothBumpFunction.bumpCovectorCLM`). Near `x` the bump function is `1`,
so this function is `ξ ∘ φ` there and its derivative at `x` is `ξ`
(`ContMDiffMap.mvfderivCLM_comp_bumpCovectorCLM`). Its support lies in that of `β`, which may be
chosen inside any neighbourhood of `x` (`SmoothBumpFunction.nhds_basis_tsupport`). So every
covector at `x` is the derivative at `x` of a function supported in a prescribed neighbourhood,
depending continuously and linearly on the covector.

This is the parameter part of the linearization of the universal section `(f, x) ↦ df_x` over
`C^n(M, ℝ) × M`, whose zeros are the critical points of all functions at once. Its surjectivity
and splitting are the linear ingredients of the transversality of that section; transversality
itself also needs the regularity of the section and the identification of its derivative with
this linearization, which are not proved here.

## Main declarations

* `SmoothBumpFunction.bumpCovector` and `SmoothBumpFunction.bumpCovectorCLM`: the compactly
  supported functions `y ↦ ξ (β y • φ y)` realizing a covector `ξ` at the centre of the bump
  function `β`.
* `SmoothBumpFunction.mvfderiv_bumpCovector` and `ContMDiffMap.mvfderivCLM_comp_bumpCovectorCLM`:
  their derivative at the centre is `ξ`, so they split the derivative at a point.
* `ContMDiffMap.surjective_mvfderivCLM`: every covector is the derivative at `x` of a `C^n` map.
* `SmoothBumpFunction.tsupport_bumpCovector_subset` and
  `SmoothBumpFunction.hasCompactSupport_bumpCovector`: the realizing functions are supported in
  the support of the bump function.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 2, §1 (the weak topology on
  spaces of `C^r` maps) and Chapter 6, §1 (local perturbations by bump functions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.3 (universal sections and their linearizations).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} {x : M}

namespace SmoothBumpFunction

/-- The `C^n` map `y ↦ ξ (β y • φ y)`, where `φ` is the extended chart at the centre `x` of the
smooth bump function `β`. Near `x` it is `ξ ∘ φ`, so its derivative at `x` is the covector `ξ`
(`SmoothBumpFunction.mvfderiv_bumpCovector`), and it is supported in the support of `β`. -/
noncomputable def bumpCovector (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) :
    C^n⟮I, M; 𝓘(ℝ, F), F⟯ :=
  ⟨fun y ↦ ξ (β y • extChartAt I x y),
    contMDiff_const.clm_apply
      ((β.contMDiff_smul contMDiffOn_extChartAt).of_le (WithTop.coe_le_coe.2 le_top))⟩

/-- The value of `bumpCovector β ξ` at `y` is `ξ (β y • φ y)`. -/
@[simp]
theorem bumpCovector_apply (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) (y : M) :
    bumpCovector (n := n) β ξ y = ξ (β y • extChartAt I x y) :=
  (rfl)

/-- Near the centre of the bump function, `bumpCovector β ξ` is the covector `ξ` read in the
extended chart. -/
theorem bumpCovector_eventuallyEq (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) :
    (bumpCovector (n := n) β ξ : M → F) =ᶠ[𝓝 x] ξ ∘ extChartAt I x := by
  filter_upwards [β.eventuallyEq_one] with y hy
  simp [hy]

/-- The functions `bumpCovector β ξ` are supported in the support of the bump function `β`. -/
theorem tsupport_bumpCovector_subset (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) :
    tsupport (bumpCovector (n := n) β ξ) ⊆ tsupport β := by
  refine closure_mono (Function.support_subset_iff'.2 fun y hy ↦ ?_)
  simp [Function.notMem_support.1 hy]

/-- The functions `bumpCovector β ξ` have compact support. -/
theorem hasCompactSupport_bumpCovector (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) :
    HasCompactSupport (bumpCovector (n := n) β ξ) :=
  β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_bumpCovector_subset β ξ)

/-- **Realizing a covector.** The derivative at the centre `x` of `bumpCovector β ξ` is `ξ`. -/
@[simp]
theorem mvfderiv_bumpCovector (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) :
    mvfderiv I (bumpCovector (n := n) β ξ) x = ξ := by
  ext v
  rw [(bumpCovector_eventuallyEq β ξ).mvfderiv_eq,
    ξ.mvfderiv_comp_apply (mdifferentiableAt_extChartAt (mem_chart_source H x)),
    TauCeti.mvfderiv_apply_of_eventuallyEq_extChartAt EventuallyEq.rfl]
  -- A tangent vector at `x` is a vector of the model space `E`.
  rfl

/-- The functions `bumpCovector β ξ`, as a continuous linear map of the covector `ξ` into the
`C^n` maps with the weak Whitney topology. -/
noncomputable def bumpCovectorCLM [IsManifold I n M] (β : SmoothBumpFunction I x) :
    (E →L[ℝ] F) →L[ℝ] C^n⟮I, M; 𝓘(ℝ, F), F⟯ where
  toFun := bumpCovector β
  map_add' ξ η := by ext y; simp
  map_smul' c ξ := by ext y; simpa using smul_comm (β y) c (ξ (extChartAt I x y))
  cont := ContMDiff.continuous_manifoldWeakWhitney <|
    contMDiff_fst.clm_apply (((β.contMDiff_smul contMDiffOn_extChartAt).of_le
      (WithTop.coe_le_coe.2 le_top)).comp contMDiff_snd)

/-- The continuous linear map `bumpCovectorCLM β` sends `ξ` to `bumpCovector β ξ`. -/
@[simp]
theorem bumpCovectorCLM_apply [IsManifold I n M] (β : SmoothBumpFunction I x) (ξ : E →L[ℝ] F) :
    bumpCovectorCLM (n := n) β ξ = bumpCovector β ξ :=
  (rfl)

end SmoothBumpFunction

namespace ContMDiffMap

/-- **The derivative at a point is split.** For `1 ≤ n`, the functions `bumpCovector β ξ` form a
continuous linear right inverse of the derivative at the centre of `β`. -/
@[simp]
theorem mvfderivCLM_comp_bumpCovectorCLM [IsManifold I n M] (hn : 1 ≤ (n : ℕ∞ω))
    (β : SmoothBumpFunction I x) :
    mvfderivCLM hn x ∘L β.bumpCovectorCLM = ContinuousLinearMap.id ℝ (E →L[ℝ] F) :=
  ContinuousLinearMap.ext fun ξ ↦ (mvfderivCLM_apply hn x _).trans (β.mvfderiv_bumpCovector ξ)

/-- For `1 ≤ n`, every covector at `x` is the derivative at `x` of a `C^n` map. -/
theorem surjective_mvfderivCLM [IsManifold I n M] (hn : 1 ≤ (n : ℕ∞ω)) (x : M) :
    Function.Surjective (mvfderivCLM (F := F) (I := I) (M := M) hn x) := fun ξ ↦
  ⟨_, (mvfderivCLM_apply hn x _).trans
    ((Classical.arbitrary (SmoothBumpFunction I x)).mvfderiv_bumpCovector ξ)⟩

end ContMDiffMap
