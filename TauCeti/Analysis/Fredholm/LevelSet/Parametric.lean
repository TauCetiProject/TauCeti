/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Smooth
public import TauCeti.Analysis.Fredholm.LevelSet.Tangent
public import TauCeti.Analysis.Fredholm.UniversalLevelSet
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Fredholm.SardSmale

/-!
# Parameter maps on universal Fredholm level sets

Let `f : E × Λ → F` be a parametrized equation and suppose that its total linearization at a
solution `(x, l)` is `D₁.coprod D₂`. When this linearization is surjective with complemented
kernel, `TauCeti.levelSetChart` parametrizes the universal level set near `(x, l)` by
`ker (D₁.coprod D₂)`. Composing its inverse with the projection to `Λ` gives the local parameter
map `TauCeti.levelSetParameterMap`.

This file calculates that map's derivative at the chart origin. It is exactly
`TauCeti.parameterProj D₁ D₂`, the linear parameter projection developed in
`TauCeti.Analysis.Fredholm.Parametric`. Every statement about that linear map therefore transfers
to the derivative at the origin: it is surjective exactly when `D₁` is, by
`TauCeti.surjective_fderiv_levelSetParameterMap_iff`; it has the same index as `D₁`, by
`TauCeti.index_fderiv_levelSetParameterMap`; and over a complete `RCLike` field it is Fredholm as
soon as `D₁` is, by `TauCeti.isFredholm_fderiv_levelSetParameterMap`.

The same calculation is then carried out at the other points of the chart, where the level set has
turned and the derivative of the inverse chart is no longer an inclusion but the kernel section of
`TauCeti.Analysis.Fredholm.LevelSet.Tangent`. That upgrades the regularity criterion from the
chart origin to a whole neighbourhood of it, and the file closes with local Sard--Smale in the
resulting geometric form: the parameters near `l` which carry a nearby solution where the
fixed-parameter linearization fails to be surjective form a closed nowhere dense set of values.

These results are the local nonlinear calculation in the parametric transversality package of
McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3. Passing
from this one chart to a residual set of parameters for a whole universal moduli space requires
smooth compatibility and a countable cover, and is not asserted here.

## Main results

* `TauCeti.hasStrictFDerivAt_levelSetParameterMap`: the derivative at the chart origin is the
  linear parameter projection.
* `TauCeti.levelSetParameterMap_levelSetChart`: on the chart source, the local parameter map is
  the parameter projection of the universal level set.
* `TauCeti.exists_apply_levelSetParameterMap_eq`: every value of the local parameter map is a
  parameter at which the equation has a solution.
* `TauCeti.surjective_fderiv_levelSetParameterMap_iff`: the chart origin is a regular point of the
  local parameter map exactly when the fixed-parameter linearization is surjective.
* `TauCeti.index_fderiv_levelSetParameterMap`: that derivative has the index of the
  fixed-parameter linearization.
* `TauCeti.isFredholm_fderiv_levelSetParameterMap`: over a complete `RCLike` field, that
  derivative is Fredholm as soon as the fixed-parameter linearization is.
* `TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_levelSetParameterMap`:
  local Sard--Smale for the parameter map of a universal level set.
* `TauCeti.hasFDerivAt_levelSetParameterMap_of_mem`: the derivative of the local parameter map at
  a nearby chart point.
* `TauCeti.surjective_fderiv_levelSetParameterMap_iff_of_mem`: a nearby chart point is a regular
  point of the local parameter map exactly when the linearization of the equation at the solution
  it names is surjective.
* `TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_notSurjective_levelSetParameterMap`:
  local parametric transversality.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866.
-/

public section

open Function Module Set
open scoped ContDiff Topology

namespace TauCeti

variable {K E Λ F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup Λ] [NormedSpace K Λ] [CompleteSpace Λ]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E × Λ → F} {D₁ : E →L[K] F} {D₂ : Λ →L[K] F}
variable {x : E} {l : Λ} {c : F}

/-- The local projection from a universal level set to its parameter space, written in the
regular-level-set chart at `(x, l)`.

The function is meaningful on the target of the level-set chart, a neighbourhood of the origin.
As with `TauCeti.levelSetChart`, its value outside that target is an irrelevant total extension. -/
noncomputable def levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) : (D₁.coprod D₂).ker → Λ :=
  fun k ↦ (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
    ↥{z | f z = c}) : E × Λ).2

/-- The local parameter map reads the parameter component of the inverse level-set chart. -/
@[simp]
theorem levelSetParameterMap_apply
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) (k : (D₁.coprod D₂).ker) :
    levelSetParameterMap hf hD hker hxl k =
      (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
        ↥{z | f z = c}) : E × Λ).2 := by
  unfold levelSetParameterMap
  rfl

/-- At the chart origin, the local parameter map returns the base parameter. -/
theorem levelSetParameterMap_zero
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    levelSetParameterMap hf hD hker hxl 0 = l := by
  rw [levelSetParameterMap_apply, levelSetChart_symm_zero]

/-- On the source of the level-set chart, the local parameter map really is the parameter
projection of the universal level set: it sends the chart image of a solution `z` back to the
parameter component of `z`. -/
theorem levelSetParameterMap_levelSetChart
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) {z : ↥{z | f z = c}}
    (hz : z ∈ (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).source) :
    levelSetParameterMap hf hD hker hxl
        (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl z) = ((z : E × Λ)).2 := by
  rw [levelSetParameterMap_apply,
    (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).left_inv hz]

/-- Every value of the local parameter map is a parameter for which the equation has a solution:
the chart parametrizes the universal level set, so the point it produces solves the equation at
the parameter that the map returns. -/
theorem exists_apply_levelSetParameterMap_eq
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) (k : (D₁.coprod D₂).ker) :
    ∃ x' : E, f (x', levelSetParameterMap hf hD hker hxl k) = c := by
  refine ⟨(((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
    ↥{z | f z = c}) : E × Λ).1, ?_⟩
  rw [levelSetParameterMap_apply]
  exact ((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k).2

/-- The local parameter map is as smooth at the chart origin as the parametrized equation. -/
theorem contDiffAt_levelSetParameterMap {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hcont : ContDiffAt K n f (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    ContDiffAt K n (levelSetParameterMap hf hD hker hxl) 0 := by
  have hchart := contDiffAt_coe_levelSetChart_symm hf hcont
    (LinearMap.range_eq_top.mpr hD) hker hxl
  rw [funext fun k ↦ levelSetParameterMap_apply hf hD hker hxl k]
  exact hchart.snd

/-- The derivative at the chart origin of the local parameter map is the restriction of the
ambient parameter projection to the kernel of the total linearization. -/
theorem hasStrictFDerivAt_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    HasStrictFDerivAt (levelSetParameterMap hf hD hker hxl)
      (parameterProj D₁ D₂) 0 := by
  have hchart := hasStrictFDerivAt_coe_levelSetChart_symm hf
    (LinearMap.range_eq_top.mpr hD) hker hxl
  have hcomp := hchart.snd
  have hproj : parameterProj D₁ D₂ =
      (ContinuousLinearMap.snd K E Λ).comp (D₁.coprod D₂).ker.subtypeL := by
    ext v
    simp
  rw [hproj, funext fun k ↦ levelSetParameterMap_apply hf hD hker hxl k]
  exact hcomp

/-- The Fréchet derivative of the local parameter map at the chart origin is the linear
parameter projection. -/
@[simp]
theorem fderiv_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    fderiv K (levelSetParameterMap hf hD hker hxl) 0 = parameterProj D₁ D₂ :=
  (hasStrictFDerivAt_levelSetParameterMap hf hD hker hxl).hasFDerivAt.fderiv

/-- **Regularity at the chart origin.** The derivative of the local parameter map at the chart
origin is surjective exactly when the fixed-parameter linearization is. This is the
transversality criterion the parametric package is aimed at, transported to the nonlinear map by
`TauCeti.fderiv_levelSetParameterMap`. -/
theorem surjective_fderiv_levelSetParameterMap_iff
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    Surjective (fderiv K (levelSetParameterMap hf hD hker hxl) 0) ↔ Surjective D₁ := by
  rw [fderiv_levelSetParameterMap]
  exact parameterProj_surjective_iff D₁ D₂ hD

/-- The derivative of the local parameter map at the chart origin has the same index as the
fixed-parameter linearization. Neither map is assumed Fredholm: both indices are differences of
`Module.finrank`s, junk values included. -/
theorem index_fderiv_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    ContinuousLinearMap.index (fderiv K (levelSetParameterMap hf hD hker hxl) 0) =
      ContinuousLinearMap.index D₁ := by
  rw [fderiv_levelSetParameterMap]
  exact index_parameterProj D₁ D₂ hD

/-! ### The regularity criterion away from the chart origin -/

/-- The derivative of the local parameter map at a chart point of the coordinate neighbourhood:
the parameter component of the kernel section of the derivative of `f` there.

`TauCeti.hasStrictFDerivAt_levelSetParameterMap` is the case `k = 0`, where the kernel section is
the inclusion of `ker (D₁.coprod D₂)` and the composite is `TauCeti.parameterProj D₁ D₂`. -/
theorem hasFDerivAt_levelSetParameterMap_of_mem
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) {k : ↥(D₁.coprod D₂).ker}
    (hk : k ∈ (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).target)
    (hmem : (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
        ↥{z | f z = c}) : E × Λ) ∈
      hf.implicitCoordSource (LinearMap.range_eq_top.mpr hD) hker)
    {A : E × Λ →L[K] F}
    (hA : HasFDerivAt f A
      (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
        ↥{z | f z = c}) : E × Λ)) :
    HasFDerivAt (levelSetParameterMap hf hD hker hxl)
      ((ContinuousLinearMap.snd K E Λ).comp (A.kerSection (Classical.choose hker))) k := by
  have hchart := hasFDerivAt_coe_levelSetChart_symm_of_mem hf (LinearMap.range_eq_top.mpr hD)
    hker hxl hk hmem hA
  have hcomp := (ContinuousLinearMap.snd K E Λ).hasFDerivAt.comp k hchart
  refine hcomp.congr_of_eventuallyEq (.of_forall fun k' ↦ ?_)
  simp

/-- **Regularity away from the chart origin.** At a chart point of the coordinate neighbourhood,
the derivative of the local parameter map is surjective exactly when the fixed-parameter part of
the derivative of `f` there is.

This is `TauCeti.surjective_fderiv_levelSetParameterMap_iff` with the chart origin replaced by an
arbitrary nearby point: criticality of the local parameter map at `k` is failure of regularity of
the equation at the solution `k` names. No surjectivity hypothesis on the derivative at that
solution is needed, because `HasStrictFDerivAt.surjective_of_mem_implicitCoordSource` supplies it.
Every derivative is of the displayed coproduct shape, by
`ContinuousLinearMap.coprod_comp_inl_inr`. -/
theorem surjective_fderiv_levelSetParameterMap_iff_of_mem
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) {k : ↥(D₁.coprod D₂).ker}
    (hk : k ∈ (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).target)
    (hmem : (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
        ↥{z | f z = c}) : E × Λ) ∈
      hf.implicitCoordSource (LinearMap.range_eq_top.mpr hD) hker)
    {A₁ : E →L[K] F} {A₂ : Λ →L[K] F}
    (hA : HasFDerivAt f (A₁.coprod A₂)
      (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
        ↥{z | f z = c}) : E × Λ)) :
    Surjective (fderiv K (levelSetParameterMap hf hD hker hxl) k) ↔ Surjective A₁ := by
  have hinv := hf.isInvertible_prod_of_mem_implicitCoordSource
    (LinearMap.range_eq_top.mpr hD) hker hmem hA
  have hsurj : Surjective (A₁.coprod A₂) :=
    hf.surjective_of_mem_implicitCoordSource (LinearMap.range_eq_top.mpr hD) hker hmem hA
  rw [(hasFDerivAt_levelSetParameterMap_of_mem hf hD hker hxl hk hmem hA).fderiv]
  rw [← parameterProj_surjective_iff A₁ A₂ hsurj]
  have hfactor : ⇑((ContinuousLinearMap.snd K E Λ).comp
      ((A₁.coprod A₂).kerSection (Classical.choose hker))) =
      parameterProj A₁ A₂ ∘ (A₁.coprod A₂).kerEquivOfProd (Classical.choose hker) hinv :=
    funext fun v ↦ by simp
  rw [hfactor]
  exact ⟨fun h ↦ h.of_comp,
    fun h ↦ h.comp ((A₁.coprod A₂).kerEquivOfProd (Classical.choose hker) hinv).surjective⟩


section RCLike

variable [IsRCLikeNormedField K] [CompleteSpace K]

/-- If the fixed-parameter linearization is Fredholm, then so is the derivative at the origin of
the local parameter map. -/
theorem isFredholm_fderiv_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hxl : f (x, l) = c) (hD₁ : ContinuousLinearMap.IsFredholm D₁) :
    ContinuousLinearMap.IsFredholm
      (fderiv K (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) 0) := by
  rw [fderiv_levelSetParameterMap]
  exact isFredholm_parameterProj D₁ D₂ hD₁

end RCLike

section Real

variable {E Λ F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {f : E × Λ → F} {D₁ : E →L[ℝ] F} {D₂ : Λ →L[ℝ] F}
variable {x : E} {l : Λ} {c : F}

/-- **Local parametric Sard--Smale.** In a regular chart of a universal level set whose
fixed-parameter linearization is Fredholm, the critical values of the local parameter map coming
from a sufficiently small neighbourhood of the chart origin form a closed nowhere dense set.

The neighbourhood is contained in the target of the level-set chart, on which the local parameter
map really is the parameter projection of the universal level set rather than the irrelevant total
extension of `TauCeti.levelSetParameterMap`. It can also be confined to any prescribed
neighbourhood `U` of the chart origin, as
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints` allows; take `U = univ` for
the plain statement.

Here criticality is defined intrinsically for the local parameter map;
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_notSurjective_levelSetParameterMap`
rewrites it as failure of regularity of the original equation.

The differentiability threshold is the one currently supplied by
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints`, rewritten using the fact
that the kernel of `parameterProj D₁ D₂` has the same dimension as `ker D₁`. -/
theorem exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_levelSetParameterMap
    {n : ℕ∞ω} {U : Set (D₁.coprod D₂).ker}
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hcont : ContDiffAt ℝ n f (x, l))
    (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Surjective (D₁.coprod D₂))
    (hxl : f (x, l) = c)
    (hn : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hU : U ∈ 𝓝 (0 : (D₁.coprod D₂).ker)) :
    ∃ N ∈ 𝓝 (0 : (D₁.coprod D₂).ker),
      N ⊆ U ∩ (levelSetChart hf (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) hxl).target ∧
      IsClosed (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl ''
        (N ∩ {k | ¬ Surjective (fderiv ℝ
          (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) k)})) ∧
      IsNowhereDense (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl ''
        (N ∩ {k | ¬ Surjective (fderiv ℝ
          (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) k)})) := by
  let g := levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl
  have hg : ContDiffAt ℝ n g 0 :=
    contDiffAt_levelSetParameterMap hf hcont hD (hD₁.closedComplemented_ker_coprod hD) hxl
  have hg' : fderiv ℝ g 0 = parameterProj D₁ D₂ :=
    fderiv_levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl
  have hn' :
      ((finrank ℝ (parameterProj D₁ D₂).ker * finrank ℝ (parameterProj D₁ D₂).ker + 1 : ℕ) :
        ℕ∞ω) ≤ n := by
    simpa only [finrank_ker_parameterProj] using hn
  have hFred := isFredholm_fderiv_levelSetParameterMap hf hD hxl hD₁
  have hn'' :
      ((finrank ℝ (fderiv ℝ g 0).ker * finrank ℝ (fderiv ℝ g 0).ker + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rw [hg']
    exact hn'
  have htarget := (levelSetChart hf (LinearMap.range_eq_top.mpr hD)
    (hD₁.closedComplemented_ker_coprod hD) hxl).open_target.mem_nhds
      (mem_levelSetChart_target hf (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) hxl)
  exact exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints hg hFred hn''
    (Filter.inter_mem hU htarget)

/-- **Local parametric transversality.** Near a regular solution of a parametrized equation whose
fixed-parameter linearization is Fredholm, the parameters carrying a nearby solution at which the
fixed-parameter linearization fails to be surjective form a closed nowhere dense set of values.

This is
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_levelSetParameterMap` with
the intrinsic critical set of the local parameter map replaced by the geometric condition it
encodes: by `TauCeti.surjective_fderiv_levelSetParameterMap_iff_of_mem` the two agree at every
chart point close enough to the origin, so the statement is about non-regular parameters of the
original equation rather than about a chart. Every value of the parameter map really is a
parameter at which the equation has a solution, by
`TauCeti.exists_apply_levelSetParameterMap_eq`.

Only a neighbourhood of one solution is described: passing to a residual set of parameters for a
whole universal moduli space needs a countable cover, which is not asserted here. The
differentiability threshold is the one supplied by the local Sard--Smale theorem. -/
theorem exists_mem_nhds_isClosed_isNowhereDense_image_notSurjective_levelSetParameterMap
    {n : ℕ∞ω} {U : Set (D₁.coprod D₂).ker}
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hcont : ContDiffAt ℝ n f (x, l))
    (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Surjective (D₁.coprod D₂))
    (hxl : f (x, l) = c)
    (hn : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hU : U ∈ 𝓝 (0 : (D₁.coprod D₂).ker)) :
    ∃ N ∈ 𝓝 (0 : (D₁.coprod D₂).ker),
      N ⊆ U ∩ (levelSetChart hf (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) hxl).target ∧
      IsClosed (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl ''
        (N ∩ {k | ¬ Surjective ((fderiv ℝ f
          (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
              (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) :
            E × Λ)).comp (ContinuousLinearMap.inl ℝ E Λ))})) ∧
      IsNowhereDense (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl ''
        (N ∩ {k | ¬ Surjective ((fderiv ℝ f
          (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
              (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) :
            E × Λ)).comp (ContinuousLinearMap.inl ℝ E Λ))})) := by
  have hne : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≠ ∞ :=
    (fun m : ℕ ↦ (by simp : ((m : ℕ) : ℕ∞ω) ≠ ∞)) _
  have hne0 : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≠ 0 :=
    (fun m : ℕ ↦ (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≠ 0)) _
  have hdiff : ∀ᶠ w in 𝓝 ((x, l) : E × Λ), DifferentiableAt ℝ f w := by
    filter_upwards [(hcont.of_le hn).eventually hne] with w hw
    exact hw.differentiableAt hne0
  have hsource : hf.implicitCoordSource (LinearMap.range_eq_top.mpr hD)
      (hD₁.closedComplemented_ker_coprod hD) ∈ 𝓝 ((x, l) : E × Λ) :=
    (hf.isOpen_implicitCoordSource _ _).mem_nhds (hf.mem_implicitCoordSource _ _)
  have hval0 : (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
      (hD₁.closedComplemented_ker_coprod hD) hxl).symm 0 : ↥{z | f z = c}) : E × Λ) = (x, l) := by
    rw [levelSetChart_symm_zero]
  have hcontAt : ContinuousAt (fun k ↦ (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
      (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) : E × Λ)) 0 :=
    (hasStrictFDerivAt_coe_levelSetChart_symm hf (LinearMap.range_eq_top.mpr hD)
      (hD₁.closedComplemented_ker_coprod hD) hxl).continuousAt
  have hV : (fun k ↦ (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) : E × Λ)) ⁻¹'
      (hf.implicitCoordSource (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) ∩ {w | DifferentiableAt ℝ f w}) ∈
      𝓝 (0 : (D₁.coprod D₂).ker) := by
    refine hcontAt.preimage_mem_nhds ?_
    rw [hval0]
    exact Filter.inter_mem hsource hdiff
  obtain ⟨N, hN, hNsub, hNclosed, hNdense⟩ :=
    exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_levelSetParameterMap
      hf hcont hD₁ hD hxl hn (Filter.inter_mem hU hV)
  have hset : N ∩ {k | ¬ Surjective (fderiv ℝ
        (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) k)} =
      N ∩ {k | ¬ Surjective ((fderiv ℝ f
        (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
            (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) :
          E × Λ)).comp (ContinuousLinearMap.inl ℝ E Λ))} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hkN
    obtain ⟨⟨-, hksrc, hkdiff⟩, hktarget⟩ := hNsub hkN
    have hA : HasFDerivAt f
        (((fderiv ℝ f (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
                (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) :
              E × Λ)).comp (ContinuousLinearMap.inl ℝ E Λ)).coprod
          ((fderiv ℝ f (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
                (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) :
              E × Λ)).comp (ContinuousLinearMap.inr ℝ E Λ)))
        (((levelSetChart hf (LinearMap.range_eq_top.mpr hD)
            (hD₁.closedComplemented_ker_coprod hD) hxl).symm k : ↥{z | f z = c}) : E × Λ) := by
      rw [ContinuousLinearMap.coprod_comp_inl_inr]
      exact hkdiff.hasFDerivAt
    exact not_congr (surjective_fderiv_levelSetParameterMap_iff_of_mem hf hD
      (hD₁.closedComplemented_ker_coprod hD) hxl hktarget hksrc hA)
  refine ⟨N, hN, hNsub.trans (Set.inter_subset_inter_left _ Set.inter_subset_left), ?_, ?_⟩
  · rw [← hset]; exact hNclosed
  · rw [← hset]; exact hNdense

end Real

end TauCeti

end
