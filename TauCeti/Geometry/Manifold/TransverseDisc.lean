/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Discs transverse to a projection

Let `s` and `s'` be subsets of a finite-dimensional manifold `M` meeting transversally at a point
`y`, with `s` flattened onto a linear subspace by a chart of the maximal atlas. Let `e` be a chart
around `y` and `P : E →L[𝕜] G` a surjective linear map such that `P ∘ e` vanishes on `s'` near `y`,
so that, read in `e`, the set `s'` lies in the kernel of `P`. Let `g : M → 𝕜` be a `C^n` function
whose differential is nonzero on a tangent vector `v` of both `s` and `s'`.

Near `y` the level cut `s ∩ g⁻¹ {g y}` is a disc, of one dimension less than `s`, on which `P ∘ e`
has surjective derivative. This file constructs an explicit parametrization `ι` of the cut by a
linear subspace `F` of the model space: `ι 0 = y`, `ι` is injective near `0` and takes values in
the cut there, every point of the cut near `y` is `ι z` for some small `z`, and `e ∘ ι` is strictly
differentiable at `0` with a derivative `ι'` such that `P ∘ ι'` is surjective. If moreover the
tangent space of `s` at `y` has one dimension more than `G`, then `P ∘ ι'` is invertible: the cut
is a disc transverse to the kernel of `P ∘ e`.

The linear algebra is as follows. Transversality makes `P` (read through the derivative of the
transition to `e`) onto from the tangent space `T` of `s`. Its kernel contains `v`, and since
`dg v ≠ 0`, subtracting a multiple of `v` from a preimage in `T` gives one in `T ∩ ker dg`, the
tangent space of the cut, so `P` maps `T ∩ ker dg` onto `G`. When `T` has dimension `dim G + 1`, so
does `T ∩ ker dg` have the dimension of `G`. The cut itself is flattened onto `T ∩ ker dg` by
`TauCeti.exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top`.

In Morse homology this produces the discs that enter the gluing of broken trajectories: for an
adapted pseudo-gradient near a critical point, `s` is the unstable manifold of a critical point of
higher index, `s'` is the stable manifold, `P` is the projection onto the expanding coordinates of a
Morse chart, `g` is the Morse function and `v` is the pseudo-gradient. By rank–nullity the kernel
of `P ∘ ι'` then has dimension `dim s - 1 - dim G`, the difference of the two indices minus one, so
it is zero when the indices differ by one.

Without the level, when the tangent space of `s` at `y` has the dimension of `G`, the same
construction parametrizes `s` itself near `y` by the subspace onto which a chart flattens it. In
Morse homology this is a disc of a set transverse to an unstable manifold, through a point of
that manifold, as in the gluing of broken configurations of a Morse–Smale pair.

## Main results

* `TauCeti.exists_param_inter_preimage_surjective_of_span_mtangentConeAt_sup_eq_top`: an injective
  parametrization of the level cut of `s` near `y` whose derivative, read in `e` and followed by
  `P`, is surjective, and which reaches every point of the cut near `y`.
* `TauCeti.exists_param_inter_preimage_of_span_mtangentConeAt_sup_eq_top`: the same derivative is
  invertible when the tangent space of `s` has dimension `dim G + 1`.
* `TauCeti.exists_param_of_span_mtangentConeAt_sup_eq_top`: the same for `s` itself, when its
  tangent space has the dimension of `G`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (the transverse discs used to glue broken trajectories).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E G M : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω}
  [IsManifold 𝓘(𝕜, E) n M] {q e : OpenPartialHomeomorph M E} {L : Submodule 𝕜 E}
  {s s' U : Set M} {y : M} {g : M → 𝕜} {P : E →L[𝕜] G} {v : E}

omit [IsManifold 𝓘(𝕜, E) n M] in
/-- The parametrization `z ↦ q⁻¹ (q y + z)` of a set `S` flattened by a chart `q` of the maximal
atlas onto a subspace `F`, read in a chart `e` around `y`: it is continuous at `0` with value `y`,
takes values in `S` near `0` and reaches every point of `S` near `y` from small parameters, is
injective near `0`, and is strictly differentiable at `0` with derivative the derivative at `q y`
of the transition `e ∘ q⁻¹`, restricted to `F`. -/
private theorem exists_param_of_isSliceChart (hn : n ≠ 0) {F : Submodule 𝕜 E} {S : Set M}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hS : IsSliceChart q (F : Set E) S)
    (hy : y ∈ q.source) (hyS : y ∈ S)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hye : y ∈ e.source) :
    ∃ ι : F → M, ι 0 = y ∧ ContinuousAt ι 0 ∧ (∀ᶠ z in 𝓝 0, ι z ∈ S) ∧
      HasStrictFDerivAt (fun z ↦ e (ι z)) (fderiv 𝕜 (q.symm.trans e) (q y) ∘L F.subtypeL) 0 ∧
      (∃ V ∈ 𝓝 (0 : F), InjOn ι V) ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ S → ∃ z ∈ V, ι z = w := by
  have hι0 : q.symm (q y + ((0 : F) : E)) = y := by simp [q.left_inv hy]
  have hadd : Continuous fun z : F ↦ q y + (z : E) := continuous_const.add continuous_subtypeVal
  have hcont : ContinuousAt (fun z : F ↦ q.symm (q y + (z : E))) 0 :=
    (q.continuousAt_symm_add hy).comp_of_eq continuous_subtypeVal.continuousAt rfl
  -- The parametrization is injective where `q y + z` lies in the target of `q`.
  have hV : (fun z : F ↦ q y + (z : E)) ⁻¹' q.target ∈ 𝓝 (0 : F) :=
    hadd.continuousAt.preimage_mem_nhds (by simpa using q.open_target.mem_nhds (q.map_source hy))
  refine ⟨fun z ↦ q.symm (q y + z), hι0, hcont, hS.eventually_symm_add_mem hy hyS,
    hasStrictFDerivAt_comp_symm_add_subtypeL hn hq he hy hye F, ⟨_, hV, fun z hz z' hz' h ↦
      Subtype.ext (add_left_cancel (q.symm.injOn hz hz' h))⟩,
    hS.eventually_exists_symm_add_eq hy hyS⟩

/-- **A disc transverse to a projection.** Let a chart `q` of the maximal atlas flatten `s` onto a
subspace `L` near a point `y` of `s ∩ s'`, where the tangent spaces of `s` and `s'` span the model
space, and let `e` be a chart around `y` and `P : E →L[𝕜] G` a surjective linear map with
`P ∘ e = 0` on `s'` near `y`. Suppose that the tangent space of `s` at `y` has the dimension of
`G`.

Then the map `ι : L → M`, `ι z = q⁻¹ (q y + z)`, is continuous at `0` with `ι 0 = y`, takes values
in `s` near `0` and reaches every point of `s` near `y` from arbitrarily small parameters, and
`e ∘ ι` is strictly differentiable at `0` with derivative `ι'` such that `P ∘ ι'` is invertible.
So near `y`, read in `e`, the set `s` is a graph over `G`. -/
theorem exists_param_of_span_mtangentConeAt_sup_eq_top [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 G] (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hys' : y ∈ s')
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊔
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y) = ⊤)
    (hdim : Module.finrank 𝕜 (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)) =
      Module.finrank 𝕜 G)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hye : y ∈ e.source)
    (hP : Function.Surjective P) (hs'P : ∀ᶠ w in 𝓝 y, w ∈ s' → P (e w) = 0) :
    ∃ (ι : L → M) (ι' : L →L[𝕜] E), ι 0 = y ∧ ContinuousAt ι 0 ∧ (∀ᶠ z in 𝓝 0, ι z ∈ s) ∧
      HasStrictFDerivAt (fun z ↦ e (ι z)) ι' 0 ∧ (P ∘L ι').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : L), ∀ᶠ w in 𝓝 y, w ∈ s → ∃ z ∈ V, ι z = w := by
  set T := Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  -- Derivatives of the transitions from the preferred chart at `y` to `q` and to `e`.
  have hchart := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := n) y
  obtain ⟨A', hA'⟩ := exists_hasFDerivAt_symm_trans (z := chartAt E y y) hn hchart hq
    (by simp [hy, mem_chart_source])
  obtain ⟨Ae, hAe⟩ := exists_hasFDerivAt_symm_trans (z := chartAt E y y) hn hchart he
    (by simp [hye, mem_chart_source])
  -- `A'` carries the tangent space of `s` onto `L`.
  have hA'L : ∀ z ∈ L, A'.symm z ∈ T := by
    intro z hz
    rw [← SetLike.mem_coe, ← tangentConeAt_preimage_symm_eq hs hL hy hys,
      ← image_mtangentConeAt_eq_tangentConeAt hy hA'] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hu
  -- `π = P ∘ Ae` kills the tangent space of `s'` and is onto, so by transversality and the
  -- dimension count it is injective on `T`.
  set π : E →ₗ[𝕜] G := ((P ∘L (Ae : E →L[𝕜] E) : E →L[𝕜] G) : E →ₗ[𝕜] G) with hπdef
  have hT'π : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y) ≤ LinearMap.ker π :=
    Submodule.span_le.2 fun u hu ↦ map_mtangentConeAt_eq_zero hAe hye hys' hs'P hu
  have hsurj : Function.Surjective (π.domRestrict T) :=
    (LinearMap.surjective_domRestrict_iff (f := π) (hP.comp Ae.surjective)).2
      (codisjoint_iff.2 (top_unique (htr ▸ sup_le_sup_left hT'π T)))
  have hinjT : Function.Injective (π.domRestrict T) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  have hdimL : Module.finrank 𝕜 L = Module.finrank 𝕜 G := by
    rw [← hdim, IsSliceChart.finrank_span_mtangentConeAt hn hq hs hL hy hys]
  -- The derivative `D` of `e ∘ q⁻¹` at `q y` satisfies `D ∘ A' = Ae`.
  have hDA : fderiv 𝕜 (q.symm.trans e) (q y) ∘L (A' : E →L[𝕜] E) = Ae :=
    fderiv_symm_trans_comp_eq hy hA' hAe
  have hDF (z : E) : fderiv 𝕜 (q.symm.trans e) (q y) z = Ae (A'.symm z) := by
    simpa using congrArg (fun B : E →L[𝕜] E ↦ B (A'.symm z)) hDA
  obtain ⟨ι, hι0, hcont, hmem, hd, -, hreach⟩ :=
    exists_param_of_isSliceChart hn hq hs hy hys he hye
  refine ⟨ι, _, hι0, hcont, hmem, hd,
    (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdimL).2 fun z z' hzz' ↦ ?_,
    hreach⟩
  have h := @hinjT ⟨A'.symm z, hA'L z z.property⟩ ⟨A'.symm z', hA'L z' z'.property⟩ (by
    simp only [hπdef, LinearMap.domRestrict_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [← hDF, ← hDF]
    exact hzz')
  exact Subtype.ext (A'.symm.injective (congrArg Subtype.val h))

/-- The level cut `s ∩ g⁻¹ {g y}` of a set `s` flattened by a chart of the maximal atlas, when the
differential `dg` of `g` at `y` is nonzero on a tangent vector of `s`, is flattened near `y` by a
chart `q'` of the maximal atlas onto `T ⊓ ker dg`, where `T` is the tangent space of `s` at `y`, and
the inverse of the derivative at `y` of the transition from the preferred chart to `q'` maps
`T ⊓ ker dg` into itself. -/
private theorem exists_isSliceChart_inter_preimage_of_mvfderiv_ne_zero [FiniteDimensional 𝕜 E]
    (hn : n ≠ 0) (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) n g U)
    (hvs : v ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y))
    (hgv : mvfderiv 𝓘(𝕜, E) g y v ≠ 0) :
    ∃ (q' : OpenPartialHomeomorph M E) (A' : E ≃L[𝕜] E),
      q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M ∧ y ∈ q'.source ∧
      IsSliceChart q' ((Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓
        (mvfderiv 𝓘(𝕜, E) g y).ker : Submodule 𝕜 E) : Set E) (s ∩ g ⁻¹' {g y}) ∧
      HasFDerivAt ((chartAt E y).symm.trans q') (A' : E →L[𝕜] E) (chartAt E y y) ∧
      ∀ z ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓ (mvfderiv 𝓘(𝕜, E) g y).ker,
        A'.symm z ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓
          (mvfderiv 𝓘(𝕜, E) g y).ker := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  set T := Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)
  -- The differential of `g` at `y`, as a linear form on the model space.
  set dg : E →L[𝕜] 𝕜 := mvfderiv 𝓘(𝕜, E) g y
  replace hgv : dg v ≠ 0 := hgv
  -- In finite dimensions every subspace is complemented.
  have hcc (p : Submodule 𝕜 E) : p.ClosedComplemented :=
    .of_finiteDimensional_quotient (Submodule.isClosed_of_finiteDimensional _)
  have hrange : dg.range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (LinearMap.surjective_of_ne_zero fun h ↦
      hgv (by simpa using LinearMap.congr_fun h v))
  have htrK : T ⊔ dg.ker = ⊤ := top_unique <|
    (LinearMap.span_singleton_sup_ker_eq_top (dg : E →ₗ[𝕜] 𝕜) hgv).ge.trans
      (sup_le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).2 hvs) _)
  -- The level cut `s ∩ g⁻¹ {g y}` is flattened by a chart `q'` onto `F = T ⊓ ker dg`, which is
  -- also its tangent space.
  obtain ⟨q', hyq', hq', hs₀⟩ :=
    exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top hn hq hs hy hU
      hyU hg rfl hrange htrK (hcc _) (hcc _) (hcc _)
  have hmT := mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top hn hq hs hy hys
    hU hyU hg rfl hrange htrK (hcc _) (hcc _) (hcc _)
  set F : Submodule 𝕜 E := T ⊓ dg.ker
  -- Restate both facts with `F`, whose kernel is read on the model space rather than on the
  -- tangent space at `y`, which is the same type.
  replace hs₀ : IsSliceChart q' (F : Set E) (s ∩ g ⁻¹' {g y}) := hs₀
  replace hmT : mtangentConeAt 𝓘(𝕜, E) (s ∩ g ⁻¹' {g y}) y = F := hmT
  -- The derivative of the transition from the preferred chart at `y` to `q'`.
  have hchart := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := n) y
  obtain ⟨A', hA'⟩ := exists_hasFDerivAt_symm_trans (z := chartAt E y y) hn hchart hq'
    (by simp [hyq', mem_chart_source])
  -- `A'` carries the tangent space `F` of the cut onto its image `F` in `q'`.
  have hA'F : ∀ z ∈ F, A'.symm z ∈ F := by
    intro z hz
    rw [← SetLike.mem_coe, ← tangentConeAt_preimage_symm_eq hs₀
      (Submodule.isClosed_of_finiteDimensional _) hyq' ⟨hys, rfl⟩,
      ← image_mtangentConeAt_eq_tangentConeAt hyq' hA', hmT] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨q', A', hq', hyq', hs₀, hA', hA'F⟩

/-- **A level disc transverse to a projection, in any dimension.** Let a chart of the maximal atlas
flatten `s` near a point `y` of `s ∩ s'`, where the tangent spaces of `s` and `s'` span the model
space, and let `e` be a chart around `y` and `P : E →L[𝕜] G` a surjective linear map with
`P ∘ e = 0` on `s'` near `y`. Suppose that the differential of a `C^n` function `g` is nonzero on a
vector `v` tangent to both `s` and `s'`.

Then there are a linear subspace `F` of the model space, of one dimension less than the tangent
space of `s` at `y`, and a map `ι : F → M`, continuous at `0` with `ι 0 = y` and injective near
`0`, which near `0` takes values in the level cut `s ∩ g⁻¹ {g y}` and near `y` reaches every point
of it from arbitrarily small parameters, such that `e ∘ ι` is strictly differentiable at `0` with
derivative `ι'` and `P ∘ ι'` is surjective. -/
theorem exists_param_inter_preimage_surjective_of_span_mtangentConeAt_sup_eq_top
    [FiniteDimensional 𝕜 E] (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hys' : y ∈ s') (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) n g U)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊔
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y) = ⊤)
    (hvs : v ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y))
    (hvs' : v ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y))
    (hgv : mvfderiv 𝓘(𝕜, E) g y v ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hye : y ∈ e.source)
    (hP : Function.Surjective P) (hs'P : ∀ᶠ w in 𝓝 y, w ∈ s' → P (e w) = 0) :
    ∃ (F : Submodule 𝕜 E) (ι : F → M) (ι' : F →L[𝕜] E), ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ s ∧ g (ι z) = g y) ∧ HasStrictFDerivAt (fun z ↦ e (ι z)) ι' 0 ∧
      Function.Surjective (P ∘L ι') ∧
      Module.finrank 𝕜 F + 1 = Module.finrank 𝕜 (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)) ∧
      (∃ V ∈ 𝓝 (0 : F), InjOn ι V) ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ s → g w = g y → ∃ z ∈ V, ι z = w := by
  obtain ⟨q', A', hq', hyq', hs₀, hA', hA'F⟩ :=
    exists_isSliceChart_inter_preimage_of_mvfderiv_ne_zero hn hq hs hy hys hU hyU hg hvs hgv
  set T := Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)
  -- The differential of `g` at `y`, as a linear form on the model space.
  set dg : E →L[𝕜] 𝕜 := mvfderiv 𝓘(𝕜, E) g y
  replace hgv : dg v ≠ 0 := hgv
  set F : Submodule 𝕜 E := T ⊓ dg.ker
  -- The derivative of the transition from the preferred chart at `y` to `e`.
  obtain ⟨Ae, hAe⟩ := exists_hasFDerivAt_symm_trans (z := chartAt E y y) hn
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := n) y) he
    (by simp [hye, mem_chart_source])
  -- Linear algebra for `π = P ∘ Ae`: it kills the tangent space of `s'` and is onto, so by
  -- transversality it maps `T` onto `G`. Correcting a preimage in `T` by a multiple of `v`, which
  -- `π` kills, puts it in `ker dg`, so `π` maps `F` onto `G`.
  set π : E →ₗ[𝕜] G := ((P ∘L (Ae : E →L[𝕜] E) : E →L[𝕜] G) : E →ₗ[𝕜] G)
  have hT'π : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y) ≤ LinearMap.ker π :=
    Submodule.span_le.2 fun u hu ↦ map_mtangentConeAt_eq_zero hAe hye hys' hs'P hu
  have hsurjT : Function.Surjective (π.domRestrict T) :=
    (LinearMap.surjective_domRestrict_iff (f := π) (hP.comp Ae.surjective)).2
      (codisjoint_iff.2 (top_unique (htr ▸ sup_le_sup_left hT'π T)))
  have hvπ : π v = 0 := hT'π hvs'
  have hπF (w : G) : ∃ t ∈ F, π t = w := by
    obtain ⟨⟨t, ht⟩, htw⟩ := hsurjT w
    refine ⟨t - (dg t * (dg v)⁻¹) • v, ⟨T.sub_mem ht (T.smul_mem _ hvs), ?_⟩, ?_⟩
    · simp [inv_mul_cancel_right₀ hgv]
    · simpa [hvπ] using htw
  -- `A'⁻¹` maps `F` injectively into itself, hence onto itself.
  have hA'Fsurj : ∀ t ∈ F, ∃ z ∈ F, A'.symm z = t := by
    set B : F →ₗ[𝕜] F := (A'.symm : E →ₗ[𝕜] E).restrict hA'F
    have hB : Function.Surjective B := LinearMap.injective_iff_surjective.1 fun z z' h ↦
      Subtype.ext (A'.symm.injective (congrArg Subtype.val h))
    intro t ht
    obtain ⟨z, hz⟩ := hB ⟨t, ht⟩
    exact ⟨z, z.property, congrArg Subtype.val hz⟩
  have hdimF : Module.finrank 𝕜 F + 1 = Module.finrank 𝕜 T := by
    have h := Module.Dual.finrank_ker_inf_add_one (f := (dg : E →ₗ[𝕜] 𝕜)) (U := T)
      fun h ↦ hgv (h hvs)
    rwa [inf_comm] at h
  -- The parametrization `ι z = q'⁻¹ (q' y + z)` of the cut is read in `e` through the transition
  -- `e ∘ q'⁻¹`, whose derivative `D` at `q' y` satisfies `D ∘ A' = Ae`.
  have hDA : fderiv 𝕜 (q'.symm.trans e) (q' y) ∘L (A' : E →L[𝕜] E) = Ae :=
    fderiv_symm_trans_comp_eq hyq' hA' hAe
  have hDF (z : E) : fderiv 𝕜 (q'.symm.trans e) (q' y) z = Ae (A'.symm z) := by
    simpa using congrArg (fun B : E →L[𝕜] E ↦ B (A'.symm z)) hDA
  obtain ⟨ι, hι0, hcont, hmem, hd, hinj, hreach⟩ :=
    exists_param_of_isSliceChart hn hq' hs₀ hyq' ⟨hys, rfl⟩ he hye
  refine ⟨F, ι, _, hι0, hcont, hmem, hd, fun w ↦ ?_, hdimF, hinj,
    fun V hV ↦ (hreach V hV).mono fun w hw hws hwg ↦ hw ⟨hws, hwg⟩⟩
  obtain ⟨t, htF, htw⟩ := hπF w
  obtain ⟨z, hzF, hzt⟩ := hA'Fsurj t htF
  refine ⟨⟨z, hzF⟩, ?_⟩
  rw [← htw, ← hzt]
  exact congrArg P (hDF z)

/-- **A level disc transverse to a projection.** Let a chart of the maximal atlas flatten `s` near a
point `y` of `s ∩ s'`, where the tangent spaces of `s` and `s'` span the model space, and let `e`
be a chart around `y` and `P : E →L[𝕜] G` a surjective linear map with `P ∘ e = 0` on `s'` near
`y`. Suppose that the tangent space of `s` at `y` has dimension `dim G + 1`, and that the
differential of a `C^n` function `g` is nonzero on a vector `v` tangent to both `s` and `s'`.

Then there are a linear subspace `F` of the model space and a map `ι : F → M`, continuous at `0`
with `ι 0 = y`, which near `0` takes values in the level cut `s ∩ g⁻¹ {g y}` and near `y` reaches
every point of it from arbitrarily small parameters, such that `e ∘ ι` is strictly differentiable
at `0` with derivative `ι'` and `P ∘ ι'` is invertible. -/
theorem exists_param_inter_preimage_of_span_mtangentConeAt_sup_eq_top [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 G] (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hys' : y ∈ s') (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) n g U)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊔
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y) = ⊤)
    (hdim : Module.finrank 𝕜 (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)) =
      Module.finrank 𝕜 G + 1)
    (hvs : v ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y))
    (hvs' : v ∈ Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y))
    (hgv : mvfderiv 𝓘(𝕜, E) g y v ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hye : y ∈ e.source)
    (hP : Function.Surjective P) (hs'P : ∀ᶠ w in 𝓝 y, w ∈ s' → P (e w) = 0) :
    ∃ (F : Submodule 𝕜 E) (ι : F → M) (ι' : F →L[𝕜] E), ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ s ∧ g (ι z) = g y) ∧ HasStrictFDerivAt (fun z ↦ e (ι z)) ι' 0 ∧
      (P ∘L ι').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ s → g w = g y → ∃ z ∈ V, ι z = w := by
  obtain ⟨F, ι, ι', hι0, hcont, hmem, hd, hsurj, hdimF, -, hreach⟩ :=
    exists_param_inter_preimage_surjective_of_span_mtangentConeAt_sup_eq_top hn hq hs hy hys hys'
      hU hyU hg htr hvs hvs' hgv he hye hP hs'P
  -- A surjection between spaces of the same dimension is invertible.
  exact ⟨F, ι, ι', hι0, hcont, hmem, hd,
    (ContinuousLinearMap.isInvertible_iff_surjective_of_finrank_eq (by omega)).2 hsurj, hreach⟩

end TauCeti
