/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Level discs transverse to a projection

Let `s` and `s'` be subsets of a finite-dimensional manifold `M` meeting transversally at a point
`y`, with `s` flattened onto a linear subspace by a chart of the maximal atlas. Let `e` be a chart
around `y` and `P : E →L[𝕜] G` a surjective linear map such that `P ∘ e` vanishes on `s'` near `y`,
so that, read in `e`, the set `s'` lies in the kernel of `P`. Let `g : M → 𝕜` be a `C^n` function
whose differential is nonzero on a tangent vector `v` of both `s` and `s'`.

If the tangent space of `s` at `y` has one dimension more than `G`, then near `y` the level cut
`s ∩ g⁻¹ {g y}` is a disc transverse to the kernel of `P ∘ e`. This file constructs an explicit
parametrization `ι` of the cut by a linear subspace `F` of the model space:
`ι 0 = y`, `ι` takes values in the cut near `0`, every point of the cut near `y` is `ι z` for some
small `z`, and `e ∘ ι` is strictly differentiable at `0` with a derivative `ι'` such that
`P ∘ ι'` is invertible.

The linear algebra is as follows. Transversality makes `P` (read through the derivative of the
transition to `e`) onto from the tangent space `T` of `s`, so its kernel meets `T` in a line, which
is spanned by `v`. Since `dg v ≠ 0`, that line meets `ker dg` only in `0`, and `T ∩ ker dg`, the
tangent space of the cut, has the dimension of `G`. The cut itself is flattened onto `T ∩ ker dg` by
`TauCeti.exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top`.

In Morse homology this produces the discs that enter the gluing of broken trajectories: for an
adapted pseudo-gradient near a critical point, `s` is the unstable manifold of a critical point one
index higher, `s'` is the stable manifold, `P` is the projection onto the expanding coordinates of a
Morse chart, `g` is the Morse function and `v` is the pseudo-gradient.

## Main results

* `TauCeti.exists_param_inter_preimage_of_span_mtangentConeAt_sup_eq_top`: a parametrization of
  the level cut of `s` near `y` whose derivative, read in `e` and followed by `P`, is invertible,
  and which reaches every point of the cut near `y`.

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
  -- Derivatives of the transitions from the preferred chart at `y` to `q'` and to `e`.
  have hchart := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := n) y
  obtain ⟨A', hA'⟩ := exists_hasFDerivAt_symm_trans (z := chartAt E y y) hn hchart hq'
    (by simp [hyq', mem_chart_source])
  obtain ⟨Ae, hAe⟩ := exists_hasFDerivAt_symm_trans (z := chartAt E y y) hn hchart he
    (by simp [hye, mem_chart_source])
  -- `A'` carries the tangent space `F` of the cut onto its image `F` in `q'`.
  have hA'F : ∀ z ∈ F, A'.symm z ∈ F := by
    intro z hz
    rw [← SetLike.mem_coe, ← tangentConeAt_preimage_symm_eq hs₀
      (Submodule.isClosed_of_finiteDimensional _) hyq' ⟨hys, rfl⟩,
      ← image_mtangentConeAt_eq_tangentConeAt hyq' hA', hmT] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  -- Linear algebra for `π = P ∘ Ae`: it kills the tangent space of `s'` and is onto, so by
  -- transversality its kernel meets `T` in a line, spanned by `v`. That line meets `ker dg` only
  -- in `0`, so `π` is injective on `F`, and `F` has the dimension of `G`.
  set π : E →ₗ[𝕜] G := ((P ∘L (Ae : E →L[𝕜] E) : E →L[𝕜] G) : E →ₗ[𝕜] G)
  have hT'π : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s' y) ≤ LinearMap.ker π :=
    Submodule.span_le.2 fun u hu ↦ map_mtangentConeAt_eq_zero hAe hye hys' hs'P hu
  have hπdisj := Submodule.disjoint_inf_ker_ker_of_finrank_eq_succ (π := π) (dg := dg)
    (v := v) (hP.comp Ae.surjective) (top_unique (htr ▸ sup_le_sup_left hT'π T)) hdim hvs
    (hT'π hvs') hgv
  have hdimF : Module.finrank 𝕜 ↥(T ⊓ LinearMap.ker (dg : E →ₗ[𝕜] 𝕜)) = Module.finrank 𝕜 G := by
    have : FiniteDimensional 𝕜 T := Module.finite_of_finrank_eq_succ hdim
    have h := Module.Dual.finrank_ker_inf_add_one (f := (dg : E →ₗ[𝕜] 𝕜)) (U := T)
      fun h ↦ hgv (h hvs)
    rw [inf_comm] at h
    omega
  -- The parametrization `ι z = q'⁻¹ (q' y + z)` of the cut is read in `e` through the transition
  -- `e ∘ q'⁻¹`, whose derivative `D` at `q' y` satisfies `D ∘ A' = Ae`.
  set D := fderiv 𝕜 (q'.symm.trans e) (q' y)
  have hDA : D ∘L (A' : E →L[𝕜] E) = Ae := fderiv_symm_trans_comp_eq hn hq' he hyq' hye hA' hAe
  have hDF (z : E) : D z = Ae (A'.symm z) := by
    simpa using congrArg (fun B : E →L[𝕜] E ↦ B (A'.symm z)) hDA
  have hι0 : q'.symm (q' y + ((0 : F) : E)) = y := by simp [q'.left_inv hyq']
  have hcont : ContinuousAt (fun z : F ↦ q'.symm (q' y + (z : E))) 0 :=
    (q'.continuousAt_symm_add hyq').comp_of_eq continuous_subtype_val.continuousAt rfl
  have hmem := hs₀.eventually_symm_add_mem hyq' ⟨hys, rfl⟩
  have hreach := hs₀.eventually_exists_symm_add_eq hyq' ⟨hys, rfl⟩
  refine ⟨F, fun z ↦ q'.symm (q' y + z), D ∘L F.subtypeL, hι0, hcont, hmem,
    hasStrictFDerivAt_comp_symm_add_subtypeL hn hq' he hyq' hye F, ?_,
    fun V hV ↦ (hreach V hV).mono fun w hw hws hwg ↦ hw ⟨hws, hwg⟩⟩
  · refine ContinuousLinearMap.isInvertible_of_injective_of_finrank_eq
      (P ∘L D ∘L F.subtypeL) hdimF ?_
    refine (injective_iff_map_eq_zero (P ∘L D ∘L F.subtypeL)).2 fun z hz ↦ Subtype.ext ?_
    have h0 := Submodule.disjoint_def.1 hπdisj _ (hA'F z z.2)
      (LinearMap.mem_ker.2 (by simpa [π, hDF] using hz))
    simpa using h0

end TauCeti
