/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
import TauCeti.Geometry.Manifold.Immersion.Basic

/-!
# Maps between intrinsic normal spaces

A commuting square between two smooth embeddings of positive order induces a continuous linear
map between their normal spaces. The ambient differential carries tangent vectors to tangent
vectors, so it descends to the quotient. The induced map is an equivalence when the base
differential is surjective and the ambient differential is invertible. In particular, these
equivalences identify intrinsic normal fibres in different submanifold coordinates, without
choosing a metric or a complement.

`normalMap` and `normalBundleMap` assume differentiability of neither the base map nor the
ambient map. Where the ambient map is differentiable, so is the base map
(`TauCeti.SmoothEmbedding.mdifferentiableAt_of_eventuallyEq`), because the target embedding is an
immersion and differentiability lifts through it
(`IsDiffImmersionAt.mdifferentiableAt_iff_comp`). Where the ambient map is not differentiable, its
differential vanishes, so the induced normal map is zero. The composition results
(`normalMap_comp`, `normalBundleMap_comp`) and `map_tangentRange_mfderiv` assume the ambient maps
differentiable.

The square need only commute near the chosen base point. This local formulation allows the
construction to be applied to coordinate maps and to their restrictions.

A globally commuting square also induces a map of intrinsic normal total spaces, acting on each
fibre by the normal map; these maps respect identities, and respect composition of squares whose
ambient maps are differentiable.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §§5–6, for the
  normal-bundle and tubular-neighbourhood setting.
* Tau Ceti's `ContinuousLinearEquiv.quotientEquiv` topologically bundles Mathlib's
  `Submodule.Quotient.equiv`.
-/

public section

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H G H' G' : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace H'] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  {M N M' N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N']
  {n m : ℕ∞ω}
  (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' m M' N')
  {u : M → M'} {v : N → N'} {x : M} {K K' : Type*}

/-- In a square commuting near `x` between embeddings of positive order, the base map is
differentiable at `x` when the ambient map is differentiable at `f x`. -/
theorem mdifferentiableAt_of_eventuallyEq (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : MDifferentiableAt J J' v (f x)) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    MDifferentiableAt I I' u x := by
  have hgu := (hv.comp x (f.contMDiff.mdifferentiableAt hn)).congr_of_eventuallyEq h.symm
  exact (g.isImmersion.isDiffImmersionAt hm (u x)).mdifferentiableAt_iff_comp.2
    ⟨g.isEmbedding.isInducing.continuousAt_iff.2 hgu.continuousAt, hgu⟩

/-- The differentials in a square commuting near `x` commute at `x`. -/
private theorem mfderiv_comp_eq_of_eventuallyEq (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : MDifferentiableAt J J' v (f x)) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).comp (mfderiv I J f x) =
      (mfderiv I' J' g (u x)).comp (mfderiv I I' u x) := by
  -- The germ-congruence formula uses the identification in the opposite direction.
  -- Applying its inverse puts both differentials in the target tangent space.
  have hd := h.mfderiv_eq (I := I) (I' := J')
  rw [mfderiv_comp x hv (f.contMDiff.mdifferentiableAt hn),
    mfderiv_comp x (g.contMDiff.mdifferentiableAt hm)
      (f.mdifferentiableAt_of_eventuallyEq g hn hm hv h)] at hd
  ext w
  convert congrArg
    (fun L => (tangentSpaceCast J' (g (u x)) (v (f x))).symm (L w)) hd using 1
  · rfl
  · exact ((tangentSpaceCast J' (g (u x)) (v (f x))).symm_apply_apply _).symm

/-- The ambient differential in a locally commuting square carries tangent vectors to
tangent vectors. -/
theorem tangentRange_le_comap_mfderiv (hn : n ≠ 0) (hm : m ≠ 0)
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    f.tangentRange x hn ≤
      (g.tangentRange (u x) hm).comap
        ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).toLinearMap := by
  by_cases hv : MDifferentiableAt J J' v (f x)
  swap
  · intro w _
    simp [mfderiv_zero_of_not_mdifferentiableAt hv]
  intro w hw
  obtain ⟨w, rfl⟩ := (f.mem_tangentRange_iff x hn w).mp hw
  apply (g.mem_tangentRange_iff (u x) hm _).mpr
  refine ⟨mfderiv I I' u x w, ?_⟩
  exact (congrArg (fun L => L w) (f.mfderiv_comp_eq_of_eventuallyEq g hn hm hv h)).symm

/-- The normal map induced by a square commuting near `x`. On an ambient tangent class,
it is given by the differential of `v`. -/
def normalMap (hn : n ≠ 0) (hm : m ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    f.NormalSpace x hn →L[𝕜] g.NormalSpace (u x) hm :=
  f.normalLiftL x hn ((g.normalClassL (u x) hm).comp
      ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))))
    (fun w hw => by
      simp only [ContinuousLinearMap.comp_apply, normalClassL_apply,
        normalClass_eq_zero_iff]
      exact f.tangentRange_le_comap_mfderiv g hn hm h hw)

/-- The induced normal map commutes with the continuous quotient maps. -/
@[simp]
theorem normalMap_comp_normalClassL (hn : n ≠ 0) (hm : m ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    (f.normalMap g hn hm h).comp (f.normalClassL x hn) =
      (g.normalClassL (u x) hm).comp
        ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))) := by
  exact f.normalLiftL_comp_normalClassL x hn _ _

/-- The induced normal map sends the class of `w` to the class of `dv(w)`. -/
@[simp]
theorem normalMap_normalClass (hn : n ≠ 0) (hm : m ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u)
    (w : TangentSpace J (f x)) :
    f.normalMap g hn hm h (f.normalClass x hn w) =
      g.normalClass (u x) hm
        (tangentSpaceCast J' (v (f x)) (g (u x)) (mfderiv J J' v (f x) w)) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    normalClassL_apply] using
    congrArg (fun L => L w) (f.normalMap_comp_normalClassL g hn hm h)

/-- The identity square induces the identity on the normal space. -/
@[simp]
theorem normalMap_id (hn : n ≠ 0) (x : M) :
    f.normalMap f hn hn (u := _root_.id) (v := _root_.id) (x := x)
      (Filter.EventuallyEq.refl _ _) =
      ContinuousLinearMap.id 𝕜 (f.NormalSpace x hn) := by
  ext z
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn z
  simp [tangentSpaceCast]

/-- A commuting square induces a map of intrinsic normal total spaces.
On each fibre it is the normal map induced by the ambient differential. -/
def normalBundleMap (hn : n ≠ 0) (hm : m ≠ 0) (h : v ∘ f = g ∘ u)
    (p : Bundle.TotalSpace K (fun x => f.NormalSpace x hn)) :
    Bundle.TotalSpace K' (fun x => g.NormalSpace x hm) :=
  ⟨u p.proj, f.normalMap g hn hm (EventuallyEq.of_eq h) p.snd⟩

/-- The induced total map applies the normal map in each fibre. -/
@[simp] theorem normalBundleMap_apply (hn : n ≠ 0) (hm : m ≠ 0) (h : v ∘ f = g ∘ u)
    (p : Bundle.TotalSpace K (fun x => f.NormalSpace x hn)) :
    f.normalBundleMap (K' := K') g hn hm h p =
      ⟨u p.proj, f.normalMap g hn hm (EventuallyEq.of_eq h) p.snd⟩ :=
  (rfl)

/-- The identity square induces the identity of the normal bundle. -/
@[simp] theorem normalBundleMap_id (hn : n ≠ 0) :
    f.normalBundleMap (K := K) (K' := K) f hn hn (u := _root_.id) (v := _root_.id) rfl =
      _root_.id := by
  funext p
  simp only [normalBundleMap_apply, normalMap_id, ContinuousLinearMap.id_apply]
  rfl

section Composition

variable {E'' F'' H'' G'' M'' N'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  [TopologicalSpace H''] [TopologicalSpace G'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {J'' : ModelWithCorners 𝕜 F'' G''}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  [TopologicalSpace N''] [ChartedSpace G'' N'']
  {r : ℕ∞ω} (q : SmoothEmbedding I'' J'' r M'' N'')
  {u' : M' → M''} {v' : N' → N''} {K'' : Type*}

/-- Composing locally commuting squares whose ambient maps are differentiable at the base points
composes their induced normal maps. The composite square is obtained from the two given germs. -/
theorem normalMap_comp (hn : n ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0)
    (hv : MDifferentiableAt J J' v (f x)) (hv' : MDifferentiableAt J' J'' v' (g (u x)))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (h' : v' ∘ g =ᶠ[𝓝 (u x)] q ∘ u') :
    f.normalMap q hn hr (u := u' ∘ u) (v := v' ∘ v) (by
        filter_upwards [h, h'.comp_tendsto
          (f.mdifferentiableAt_of_eventuallyEq g hn hm hv h).continuousAt] with y hy hy'
        exact (congrArg v' hy).trans hy') =
      (g.normalMap q hm hr h').comp (f.normalMap g hn hm h) := by
  ext z
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn z
  simp only [ContinuousLinearMap.comp_apply, normalMap_normalClass]
  -- The first square identifies `v (f x)` with `g (u x)`, so the middle
  -- tangent-space identification cancels in the chain rule for `v' ∘ v`.
  rw [mfderiv_comp_of_eq hv' hv h.eq_of_nhds]
  congr 1
  have hd := mfderiv_congr_point (I := J') (I' := J'') (f := v') h.eq_of_nhds
  convert congrArg
    (fun L => tangentSpaceCast J'' (v' (g (u x))) (q (u' (u x)))
      (L (tangentSpaceCast J' (v (f x)) (g (u x)) (mfderiv J J' v (f x) w)))) hd using 1 <;>
    rfl

/-- Composing commuting squares whose ambient maps are differentiable composes their induced maps
on normal total spaces. -/
theorem normalBundleMap_comp (hn : n ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0)
    (hv : MDifferentiable J J' v) (hv' : MDifferentiable J' J'' v')
    (h : v ∘ f = g ∘ u) (h' : v' ∘ g = q ∘ u') :
    f.normalBundleMap (K := K) (K' := K'') q hn hr (u := u' ∘ u) (v := v' ∘ v)
        (by
          funext x
          exact (congrArg v' (congrFun h x)).trans (congrFun h' (u x))) =
      g.normalBundleMap (K := K') (K' := K'') q hm hr h' ∘
        f.normalBundleMap g hn hm h := by
  funext p
  simp only [Function.comp_apply, normalBundleMap_apply]
  have hc := f.normalMap_comp g q hn hm hr (hv (f p.proj)) (hv' (g (u p.proj)))
    (EventuallyEq.of_eq h) (EventuallyEq.of_eq h')
  exact congrArg (Bundle.TotalSpace.mk (u' (u p.proj))) (congrArg (fun L => L p.snd) hc)

end Composition

/-- If the ambient map is differentiable at `f x` and the base differential is surjective, the
ambient differential carries the tangent range onto the target tangent range. -/
theorem map_tangentRange_mfderiv (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (hsurj : Surjective (mfderiv I I' u x)) :
    (f.tangentRange x hn).map ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).toLinearMap =
      g.tangentRange (u x) hm := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr
      (f.tangentRange_le_comap_mfderiv g hn hm h)
  · intro w hw
    obtain ⟨w, rfl⟩ := (g.mem_tangentRange_iff (u x) hm w).mp hw
    obtain ⟨z, rfl⟩ := hsurj w
    refine ⟨mfderiv I J f x z, (f.mem_tangentRange_iff x hn _).mpr ⟨z, rfl⟩, ?_⟩
    exact congrArg (fun L => L z) (f.mfderiv_comp_eq_of_eventuallyEq g hn hm hv h)

/-- A commuting square identifies the intrinsic normal fibres when the base differential is
surjective and the ambient differential is invertible at the chosen point. -/
def normalSpaceEquiv (hn : n ≠ 0) (hm : m ≠ 0) (hv : (mfderiv J J' v (f x)).IsInvertible)
    (hsurj : Surjective (mfderiv I I' u x)) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    f.NormalSpace x hn ≃L[𝕜] g.NormalSpace (u x) hm :=
  -- The range hypothesis `map_tangentRange_mfderiv` is stated for the linear map underlying
  -- `tangentSpaceCast ∘L mfderiv`. It is the one underlying the equivalence below by definition,
  -- since `ContinuousLinearEquiv.ofContinuousLinearMap` applies `mfderiv` (see
  -- `ContinuousLinearEquiv.coe_ofContinuousLinearMap`) and the cast then follows it.
  f.normalSpaceEquivOfMapTangentRange g x (u x) hn hm
    ((ContinuousLinearEquiv.ofContinuousLinearMap _ _ hv.self_comp_inverse
      hv.inverse_comp_self).trans
      (tangentSpaceCast J' (v (f x)) (g (u x))))
    (f.map_tangentRange_mfderiv g hn hm (mdifferentiableAt_of_isInvertible_mfderiv hv) h hsurj)

/-- The normal-fibre equivalence has the normal map as its underlying continuous linear map. -/
@[simp]
theorem normalSpaceEquiv_toContinuousLinearMap (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : (mfderiv J J' v (f x)).IsInvertible) (hsurj : Surjective (mfderiv I I' u x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    (f.normalSpaceEquiv g hn hm hv hsurj h).toContinuousLinearMap = f.normalMap g hn hm h := by
  ext z
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn z
  rw [ContinuousLinearEquiv.coe_apply, normalMap_normalClass]
  refine (f.normalSpaceEquivOfMapTangentRange_normalClass g x (u x) hn hm _ _ w).trans ?_
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_ofContinuousLinearMap]

/-- On representatives, the normal-fibre equivalence applies the ambient differential. -/
@[simp]
theorem normalSpaceEquiv_normalClass (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : (mfderiv J J' v (f x)).IsInvertible) (hsurj : Surjective (mfderiv I I' u x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (w : TangentSpace J (f x)) :
    f.normalSpaceEquiv g hn hm hv hsurj h (f.normalClass x hn w) =
      g.normalClass (u x) hm
        (tangentSpaceCast J' (v (f x)) (g (u x)) (mfderiv J J' v (f x) w)) := by
  simpa only [ContinuousLinearEquiv.coe_apply, normalMap_normalClass] using
    congrArg (fun L => L (f.normalClass x hn w))
      (f.normalSpaceEquiv_toContinuousLinearMap g hn hm hv hsurj h)

/-- On representatives, the inverse normal-fibre equivalence applies the inverse ambient
differential, after identifying the equal ambient base points. -/
@[simp]
theorem normalSpaceEquiv_symm_normalClass (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : (mfderiv J J' v (f x)).IsInvertible) (hsurj : Surjective (mfderiv I I' u x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (w : TangentSpace J' (g (u x))) :
    (f.normalSpaceEquiv g hn hm hv hsurj h).symm (g.normalClass (u x) hm w) =
      f.normalClass x hn
        ((mfderiv J J' v (f x)).inverse ((tangentSpaceCast J' (v (f x)) (g (u x))).symm w)) := by
  apply (f.normalSpaceEquiv g hn hm hv hsurj h).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, normalSpaceEquiv_normalClass,
    hv.self_apply_inverse, ContinuousLinearEquiv.apply_symm_apply]

end TauCeti.SmoothEmbedding
