/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The differential at a point of `C^n` maps, and bump functions realizing covectors

For `1 ≤ n` and a point `x` of a manifold `M`, taking the derivative at `x` of vector-valued `C^n`
maps is a continuous linear map

`h ↦ dh_x : C^n(M, F) →L (T_x M →L F)`

for the weak Whitney topology (`ContMDiffMap.mvfderivCLM`). This holds on manifolds with boundary
or corners and in any regularity `n ≥ 1`, including the finite orders `C^k` on which the Banach
space structure of a compact manifold lives.

Over the reals this map is split surjective, and the splitting is realized by compactly supported
functions. For a smooth bump function `β` at `x`, the map
`ξ ↦ (y ↦ ξ (β y • φ y))`, where `φ` is the extended chart at `x`, is a continuous linear map
`(E →L F) →L C^n(M, F)` (`ContMDiffMap.bumpCovectorCLM`). Near `x` the bump function is `1`, so
this function is `ξ ∘ φ` there and its derivative at `x` is `ξ`
(`ContMDiffMap.mvfderivCLM_comp_bumpCovectorCLM`). Its support lies in that of `β`, which may be
chosen inside any neighbourhood of `x` (`SmoothBumpFunction.nhds_basis_tsupport`). So every
covector at `x` is the derivative at `x` of a function supported in a prescribed neighbourhood,
depending continuously and linearly on the covector.

This is the parameter part of the linearization of the universal section `(f, x) ↦ df_x` over
`C^n(M, ℝ) × M`, whose zeros are the critical points of all functions at once: its surjectivity
makes the universal zero set transverse, and its splitting is what a Banach-space implicit
function theorem consumes.

## Main declarations

* `ContMDiffMap.mvfderivCLM`: the derivative at a point as a continuous linear map on `C^n` maps.
* `ContMDiffMap.bumpCovector` and `ContMDiffMap.bumpCovectorCLM`: the compactly supported
  functions `y ↦ ξ (β y • φ y)` realizing a covector `ξ` at the centre of the bump function `β`.
* `ContMDiffMap.mvfderiv_bumpCovector` and `ContMDiffMap.mvfderivCLM_comp_bumpCovectorCLM`: their
  derivative at the centre is `ξ`, so they split the derivative at a point.
* `ContMDiffMap.surjective_mvfderivCLM`: every covector is the derivative at `x` of a `C^n` map.
* `ContMDiffMap.tsupport_bumpCovector_subset` and `ContMDiffMap.hasCompactSupport_bumpCovector`:
  the realizing functions are supported in the support of the bump function.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 2, §1 (the weak topology on
  spaces of `C^r` maps) and Chapter 6, §1 (local perturbations by bump functions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.3 (universal sections and their linearizations).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

section Differential

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} [IsManifold I n M]

omit [IsManifold I n M] in
/-- The derivative at `x` of a vector-valued map differentiable at `x` is the derivative within the
extended chart target of its coordinate expression. -/
private theorem mvfderiv_eq_fderivWithin_extChartAt_target {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    mvfderiv I f x = fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x).target
      (extChartAt I x x) := by
  rw [hf.mvfderiv, fderivWithin_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x)
    I.uniqueDiffWithinAt_image (hf.differentiableWithinAt_writtenInExtChartAt.mono
      (extChartAt_target_subset_range x)), writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp]

/-- The **derivative at `x`** of vector-valued `C^n` maps, `1 ≤ n`, as a continuous linear map for
the weak Whitney topology. -/
noncomputable def mvfderivCLM (hn : 1 ≤ n) (x : M) :
    C^n⟮I, M; 𝓘(𝕜, F), F⟯ →L[𝕜] TangentSpace I x →L[𝕜] F where
  toFun f := mvfderiv I f x
  map_add' f g := mvfderiv_add (f.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hn).ne')
    (g.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hn).ne')
  map_smul' c f := TauCeti.mvfderiv_const_smul_field f x c
  cont := by
    refine (continuous_congr fun f : C^n⟮I, M; 𝓘(𝕜, F), F⟯ ↦
      mvfderiv_eq_fderivWithin_extChartAt_target
        (f.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hn).ne')).2
      (continuous_iff_continuousAt.2 fun f₀ ↦ ?_)
    -- The coordinate differentials converge uniformly on the compact set `{φ x}`.
    have h := (TauCeti.tendstoUniformlyOn_fderivWithin_extChartAt (J := 𝓘(𝕜, F)) (y := f₀ x)
      (f₀ := f₀) hn isCompact_singleton (singleton_subset_iff.2 (mem_extChartAt_target x))
      (fun _ _ ↦ by simp)).tendsto_at (mem_singleton _)
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h
    -- `ContinuousAt` is this limit, with `TangentSpace I x` read as the model space `E`.
    exact h

/-- The derivative at `x` of a `C^n` map. -/
@[simp]
theorem mvfderivCLM_apply (hn : 1 ≤ n) (x : M) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    mvfderivCLM hn x f = mvfderiv I f x :=
  (rfl)

end Differential

section Bump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} {x : M}

/-- The `C^n` map `y ↦ ξ (β y • φ y)`, where `φ` is the extended chart at the centre `x` of the
smooth bump function `β`. Near `x` it is `ξ ∘ φ`, so its derivative at `x` is the covector `ξ`
(`ContMDiffMap.mvfderiv_bumpCovector`), and it is supported in the support of `β`. -/
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

/-- **The derivative at a point is split.** For `1 ≤ n`, the functions `bumpCovector β ξ` form a
continuous linear right inverse of the derivative at the centre of `β`. -/
@[simp]
theorem mvfderivCLM_comp_bumpCovectorCLM [IsManifold I n M] (hn : 1 ≤ (n : ℕ∞ω))
    (β : SmoothBumpFunction I x) :
    mvfderivCLM hn x ∘L bumpCovectorCLM β = ContinuousLinearMap.id ℝ (E →L[ℝ] F) :=
  ContinuousLinearMap.ext fun ξ ↦ mvfderiv_bumpCovector β ξ

/-- For `1 ≤ n`, every covector at `x` is the derivative at `x` of a `C^n` map. -/
theorem surjective_mvfderivCLM [IsManifold I n M] (hn : 1 ≤ (n : ℕ∞ω)) (x : M) :
    Function.Surjective (mvfderivCLM (F := F) (I := I) (M := M) hn x) := fun ξ ↦
  ⟨_, mvfderiv_bumpCovector (Classical.arbitrary (SmoothBumpFunction I x)) ξ⟩

end Bump

end ContMDiffMap
