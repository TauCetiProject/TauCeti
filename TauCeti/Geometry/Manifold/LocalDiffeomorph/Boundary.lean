/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The inverse function theorem at boundary points

`TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq` is the inverse function theorem for manifolds at
interior points. At a boundary point of a manifold with boundary the chart representative of a map
is only defined on the range of the model, so invertibility of the differential alone cannot
produce a local inverse: the map must also send the model range onto the model range near the
point.

This file proves the inverse function theorem in that form. Let `f : M → N` be read near `x`, in
the extended charts at `x` and `f x`, as a map `g` of the model vector spaces which is `C^n` on an
open set `t`, `1 ≤ n`, with invertible derivative at the chart image of `x`. If on `t` the map `g`
sends exactly the points of the source model range into the target model range, then `f` is a
`C^n` local diffeomorphism at `x`
(`TauCeti.isLocalDiffeomorphAt_of_fderiv_eq_of_mem_range_iff`). In equal finite dimensions an
injective derivative suffices (`TauCeti.isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff`).

The point is that `g` is defined on a whole open set of the model vector space, also outside the
model range. The Banach-space inverse function theorem makes it a `C^n` partial homeomorphism near
the chart image of `x`, and the range condition lets it descend to a partial diffeomorphism
between the model spaces. For a map flowing the boundary of a manifold inward along a vector field,
the extension is the flow at negative times.

## Main results

* `TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff`: an open partial homeomorphism
  of the model vector spaces, `C^n` in both directions, which sends exactly the points of the
  source model range into the target model range, as a partial diffeomorphism of the model spaces.
* `TauCeti.isLocalDiffeomorphAt_of_fderiv_eq_of_mem_range_iff`: the inverse function theorem at
  any point, boundary points included, for a map with a range-preserving chart extension.
* `TauCeti.isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff`: in equal finite dimensions,
  an injective derivative suffices.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 4.5 (the inverse
  function theorem for manifolds).
-/

public section

open Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕂 E H} {J : ModelWithCorners 𝕂 F G} {n : WithTop ℕ∞}

/-- If an open partial homeomorphism `Θ` sends exactly the points of the range of `I` in its source
into the range of `J`, then its inverse sends the points of the range of `J` in its target into the
range of `I`. -/
private theorem range_of_mem_target (Θ : OpenPartialHomeomorph E F)
    (hrange : ∀ z ∈ Θ.source, Θ z ∈ range J ↔ z ∈ range I) {h : G} (hh : J h ∈ Θ.target) :
    Θ.symm (J h) ∈ range I :=
  (hrange _ (Θ.map_target hh)).1 (by rw [Θ.right_inv hh]; exact mem_range_self h)

/-- An open partial homeomorphism `Θ` of the model vector spaces, `C^n` in both directions, which
on its source sends exactly the points of the range of `I` into the range of `J`, as a partial
diffeomorphism `J.symm ∘ Θ ∘ I` between the model spaces `H` and `G`. For the trivial models this
is `TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph`. -/
noncomputable def PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff
    (Θ : OpenPartialHomeomorph E F) (hΘ : ContDiffOn 𝕂 n Θ Θ.source)
    (hΘsymm : ContDiffOn 𝕂 n Θ.symm Θ.target)
    (hrange : ∀ z ∈ Θ.source, Θ z ∈ range J ↔ z ∈ range I) : PartialDiffeomorph I J H G n where
  toFun := J.symm ∘ Θ ∘ I
  invFun := I.symm ∘ Θ.symm ∘ J
  source := I ⁻¹' Θ.source
  target := J ⁻¹' Θ.target
  map_source' h hh := by
    simp only [mem_preimage, Function.comp_apply]
    rw [J.right_inv ((hrange _ hh).2 (mem_range_self h))]
    exact Θ.map_source hh
  map_target' h hh := by
    simp only [mem_preimage, Function.comp_apply]
    rw [I.right_inv (range_of_mem_target Θ hrange hh)]
    exact Θ.map_target hh
  left_inv' h hh := by
    simp only [Function.comp_apply]
    rw [J.right_inv ((hrange _ hh).2 (mem_range_self h)), Θ.left_inv hh, I.left_inv]
  right_inv' h hh := by
    simp only [Function.comp_apply]
    rw [I.right_inv (range_of_mem_target Θ hrange hh), Θ.right_inv hh, J.left_inv]
  open_source := Θ.open_source.preimage I.continuous
  open_target := Θ.open_target.preimage J.continuous
  contMDiffOn_toFun :=
    (J.contMDiffOn_symm (n := n)).comp ((contMDiffOn_iff_contDiffOn.2 hΘ).comp
      (I.contMDiff (n := n)).contMDiffOn fun _ hh ↦ hh) fun h hh ↦
        (hrange _ hh).2 (mem_range_self h)
  contMDiffOn_invFun :=
    (I.contMDiffOn_symm (n := n)).comp ((contMDiffOn_iff_contDiffOn.2 hΘsymm).comp
      (J.contMDiff (n := n)).contMDiffOn fun _ hh ↦ hh) fun _ hh ↦ range_of_mem_target Θ hrange hh

section OfMemRangeIff

variable (Θ : OpenPartialHomeomorph E F) (hΘ : ContDiffOn 𝕂 n Θ Θ.source)
  (hΘsymm : ContDiffOn 𝕂 n Θ.symm Θ.target) (hrange : ∀ z ∈ Θ.source, Θ z ∈ range J ↔ z ∈ range I)

/-- `PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ` is `Θ` read in the model
spaces. -/
@[simp]
theorem PartialDiffeomorph.coe_ofOpenPartialHomeomorphOfMemRangeIff :
    ⇑(PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ hΘ hΘsymm hrange) =
      J.symm ∘ Θ ∘ I :=
  (rfl)

/-- The inverse of `PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ` is the inverse of
`Θ` read in the model spaces. -/
@[simp]
theorem PartialDiffeomorph.coe_ofOpenPartialHomeomorphOfMemRangeIff_toPartialEquiv_symm :
    ⇑(PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ hΘ hΘsymm
        hrange).toPartialEquiv.symm = I.symm ∘ Θ.symm ∘ J :=
  (rfl)

/-- The source of `PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ` is the preimage of
the source of `Θ` under the model. -/
@[simp]
theorem PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff_source :
    (PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ hΘ hΘsymm hrange).source =
      I ⁻¹' Θ.source :=
  (rfl)

/-- The target of `PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ` is the preimage of
the target of `Θ` under the model. -/
@[simp]
theorem PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff_target :
    (PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ hΘ hΘsymm hrange).target =
      J ⁻¹' Θ.target :=
  (rfl)

end OfMemRangeIff

variable [CompleteSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {x : M} {g : E → F} {t : Set E}

/-- **The inverse function theorem at boundary points.** Let `f : M → N` be read near `x`, in the
extended charts at `x` and `f x`, as a map `g` which is `C^n` on an open set `t` of the model
vector space, `1 ≤ n`, whose derivative at the chart image of `x` is a continuous linear
equivalence. If every point `z ∈ t` lies in the range of the model of `M` exactly when `g z` lies
in the range of the model of `N`, then `f` is a `C^n` local diffeomorphism at `x`.

No interior condition is imposed on `x`: at a boundary point, `g` extends the chart representative
of `f` beyond the model range, and the range condition says that `f` sends boundary to boundary and
interior to interior near `x`. -/
theorem isLocalDiffeomorphAt_of_fderiv_eq_of_mem_range_iff (hg : ContDiffOn 𝕂 n g t)
    (ht : IsOpen t) (hxt : extChartAt I x x ∈ t) (hn : 1 ≤ n) {e : E ≃L[𝕂] F}
    (he : (e : E →L[𝕂] F) = fderiv 𝕂 g (extChartAt I x x))
    (hrange : ∀ z ∈ t, g z ∈ range J ↔ z ∈ range I)
    (hgx : g (extChartAt I x x) = extChartAt J (f x) (f x))
    (hfg : ∀ᶠ y in 𝓝 x, f y = (extChartAt J (f x)).symm (g (extChartAt I x y))) :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨Θ, hΘg, hxΘ, hΘt, hΘsymm⟩ := ContDiffOn.exists_openPartialHomeomorph hg ht hxt hn he
  subst hΘg
  let Ξ : PartialDiffeomorph I J H G n :=
    PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff Θ (hg.mono hΘt) hΘsymm
      fun z hz ↦ hrange z (hΘt hz)
  -- The chart at `x`, the model partial diffeomorphism and the inverse chart at `f x`.
  have h₁ : IsLocalDiffeomorphAt I I n (chartAt H x) x :=
    (chartAt H x).isLocalDiffeomorphAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
      (mem_chart_source H x)
  have hΞx : chartAt H x x ∈ Ξ.source := by
    rw [PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff_source, mem_preimage,
      ← Function.comp_apply (f := I), ← extChartAt_coe]
    exact hxΘ
  have hΞcoe : ⇑Ξ = J.symm ∘ Θ ∘ I :=
    PartialDiffeomorph.coe_ofOpenPartialHomeomorphOfMemRangeIff ..
  have hΞ : Ξ (chartAt H x x) = chartAt G (f x) (f x) := by
    rw [hΞcoe, Function.comp_apply, Function.comp_apply, ← Function.comp_apply (f := I),
      ← extChartAt_coe, hgx, extChartAt_coe, Function.comp_apply, J.left_inv]
  have h₃ : IsLocalDiffeomorphAt J J n (chartAt G (f x)).symm (Ξ (chartAt H x x)) := by
    rw [hΞ]
    exact (chartAt G (f x)).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (f x)) ((chartAt G (f x)).map_source
        (mem_chart_source G (f x)))
  have h₂ : IsLocalDiffeomorphAt I J n Ξ (chartAt H x x) :=
    isLocalDiffeomorphAt_of_eqOn hΞx fun _ _ ↦ rfl
  have h₁₂ : IsLocalDiffeomorphAt I J n (Ξ ∘ chartAt H x) x :=
    IsLocalDiffeomorphAt.comp (hf := h₁) (hg := h₂)
  refine (IsLocalDiffeomorphAt.comp (hf := h₁₂) (hg := h₃)).congr_of_eventuallyEq ?_
  filter_upwards [hfg] with y hy
  simp only [hy, extChartAt_coe_symm, extChartAt_coe, hΞcoe, Function.comp_apply]

/-- **The inverse function theorem at boundary points**, injective form: between model vector
spaces of the same finite dimension, it suffices in
`TauCeti.isLocalDiffeomorphAt_of_fderiv_eq_of_mem_range_iff` that the derivative of the chart
extension `g` at the chart image of `x` is injective. -/
theorem isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff [FiniteDimensional 𝕂 E]
    [FiniteDimensional 𝕂 F] (hg : ContDiffOn 𝕂 n g t) (ht : IsOpen t) (hxt : extChartAt I x x ∈ t)
    (hn : 1 ≤ n) (hinj : Function.Injective (fderiv 𝕂 g (extChartAt I x x)))
    (hdim : Module.finrank 𝕂 E = Module.finrank 𝕂 F)
    (hrange : ∀ z ∈ t, g z ∈ range J ↔ z ∈ range I)
    (hgx : g (extChartAt I x x) = extChartAt J (f x) (f x))
    (hfg : ∀ᶠ y in 𝓝 x, f y = (extChartAt J (f x)).symm (g (extChartAt I x y))) :
    IsLocalDiffeomorphAt I J n f x :=
  isLocalDiffeomorphAt_of_fderiv_eq_of_mem_range_iff hg ht hxt hn
    (e := (LinearMap.linearEquivOfInjective (fderiv 𝕂 g (extChartAt I x x)).toLinearMap hinj
      hdim).toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun w ↦ LinearMap.linearEquivOfInjective_apply hinj hdim w)
    hrange hgx hfg

end TauCeti
