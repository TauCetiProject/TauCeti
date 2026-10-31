/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Derivatives on manifold chart domains

For a vector-valued smooth map on a manifold, differentiate its coordinate representative within
the target of each extended source chart. These derivatives are continuous on that target, even
when the manifold has boundary or corners: the model with corners supplies unique derivatives
within the chart target.

This construction allows a source covered by many charts, rather than requiring one global
chart. It supplies the vector-valued coordinate derivatives needed when treating maps between
manifolds locally in the target.

The construction follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, and extends
the global-chart construction in `ContMDiffMap.WeakWhitney` using Mathlib's extended charts and
iterated derivatives within sets. No boundaryless or compactness assumption is needed here.
-/

public section

open Set Filter Topology
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- The derivative of order `m` of a vector-valued map in the source chart at `x`, as a
continuous map on the extended chart target. Derivatives are taken within that target. -/
noncomputable def chartIteratedFDeriv
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M) (m : ℕ) (hm : m ≤ n) :
    C((extChartAt I x).target, E [×m]→L[𝕜] F) := by
  refine ⟨fun y ↦ iteratedFDerivWithin 𝕜 m
    (writtenInExtChartAt I (modelWithCornersSelf 𝕜 F) x f)
    (extChartAt I x).target y, ?_⟩
  have hf : ContDiffOn 𝕜 n (writtenInExtChartAt I (modelWithCornersSelf 𝕜 F) x f)
      (extChartAt I x).target :=
    (f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  exact (hf.continuousOn_iteratedFDerivWithin hm
    (uniqueDiffOn_extChartAt_target x)).domRestrict

-- Spell out the chart target in the coercion type so these simp lemmas are in normal form.
@[simp]
theorem chartIteratedFDeriv_apply
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M) (m : ℕ) (hm : m ≤ n)
    (y : (extChartAt I x).target) :
    DFunLike.coe (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×m]→L[𝕜] F))
      (chartIteratedFDeriv f x m hm) y = iteratedFDerivWithin 𝕜 m
      (writtenInExtChartAt I (modelWithCornersSelf 𝕜 F) x f) (extChartAt I x).target y := by
  rfl

/-- In a self-model target chart, the chart jet is the ordinary coordinate derivative. -/
theorem chartIteratedFDeriv_self_target_apply
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M) (m : ℕ) (hm : m ≤ n)
    (y : (extChartAt I x).target) :
    chartIteratedFDeriv f x m hm y =
      iteratedFDerivWithin 𝕜 m (f ∘ (extChartAt I x).symm)
        (extChartAt I x).target y := by
  change DFunLike.coe (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×m]→L[𝕜] F))
      (chartIteratedFDeriv f x m hm) y = _
  rw [chartIteratedFDeriv_apply]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp]

/-- Order zero of the chart jet recovers the map in source coordinates. -/
@[simp]
theorem chartIteratedFDeriv_zero_apply
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M)
    (y : (extChartAt I x).target) (v : Fin 0 → E) :
    DFunLike.coe (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×0]→L[𝕜] F))
      (chartIteratedFDeriv f x 0 (by simp)) y v =
        f ((extChartAt I x).symm y) := by
  simp only [chartIteratedFDeriv_apply, iteratedFDerivWithin_zero_apply]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe]
  rfl

omit [IsManifold I n M] in
/-- For the identity chart of a normed space, the chart derivative is the ordinary iterated
derivative, evaluated on the subtype representing the whole chart target.

The coercion type is spelled `Set.univ ∩ Set.univ`, the `simp`-normal form of the extended target
of the identity chart: the chart target rewrites to `Set.univ` by `chartAt_self_eq`, while the
intersection itself is not simplified inside a type. -/
@[simp]
theorem chartIteratedFDeriv_self_apply
    (f : C^n⟮modelWithCornersSelf 𝕜 E, E; modelWithCornersSelf 𝕜 F, F⟯)
    (x : E) (m : ℕ) (hm : m ≤ n)
    (y : (extChartAt (modelWithCornersSelf 𝕜 E) x).target) :
    DFunLike.coe (F := C(↥(Set.univ ∩ Set.univ : Set E), E [×m]→L[𝕜] F))
      (chartIteratedFDeriv f x m hm) y =
        f.iteratedFDerivContinuousMap m hm y := by
  refine (chartIteratedFDeriv_apply f x m hm y).trans ?_
  simp only [extChartAt_model_space_eq_id,
    PartialEquiv.refl_target, iteratedFDerivWithin_univ,
    ContMDiffMap.iteratedFDerivContinuousMap_apply]
  rw [writtenInExtChartAt_model_space]

/-- Coordinate differentiation of vector-valued maps, as a linear map into continuous maps
on the extended chart target. -/
noncomputable def chartIteratedFDerivLinearMap (x : M) (m : ℕ) (hm : m ≤ n) :
    C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜] C((extChartAt I x).target, E [×m]→L[𝕜] F) where
  toFun f := chartIteratedFDeriv f x m hm
  map_add' f g := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.add_apply, chartIteratedFDeriv_self_target_apply]
    simpa only [ContMDiffMap.coe_add, Function.comp_def, Pi.add_def] using
      iteratedFDerivWithin_add_apply
      (((f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn).of_le hm z z.2)
      (((g.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn).of_le hm z z.2)
      (uniqueDiffOn_extChartAt_target x) z.2
  map_smul' c f := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.smul_apply, chartIteratedFDeriv_self_target_apply]
    simpa only [ContMDiffMap.coe_smul, Function.comp_def, Pi.smul_def, RingHom.id_apply] using
      (iteratedFDerivWithin_const_smul_apply (a := c)
      (((f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn).of_le hm z z.2)
      (uniqueDiffOn_extChartAt_target x) z.2)

/-- The linear coordinate-derivative map agrees with the existing chart jet. -/
-- Spell out the chart target in the coercion type, as for `chartIteratedFDeriv_apply`.
@[simp]
theorem chartIteratedFDerivLinearMap_apply (x : M) (m : ℕ) (hm : m ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    DFunLike.coe (F := C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜]
      C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×m]→L[𝕜] F))
      (chartIteratedFDerivLinearMap x m hm) f = chartIteratedFDeriv f x m hm :=
  (rfl)

/-- Coordinate differentiation commutes with subtraction of vector-valued maps. -/
@[simp]
theorem chartIteratedFDeriv_sub
    (f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M) (m : ℕ) (hm : m ≤ n) :
    chartIteratedFDeriv (f - g) x m hm =
      chartIteratedFDeriv f x m hm - chartIteratedFDeriv g x m hm := by
  exact (chartIteratedFDerivLinearMap_apply x m hm (f - g)).symm.trans
    ((map_sub (chartIteratedFDerivLinearMap (F := F) x m hm) f g).trans
      (congrArg₂ (· - ·) (chartIteratedFDerivLinearMap_apply x m hm f)
        (chartIteratedFDerivLinearMap_apply x m hm g)))

end ContMDiffMap
