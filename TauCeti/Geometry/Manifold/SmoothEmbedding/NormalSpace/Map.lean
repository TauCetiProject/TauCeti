/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Maps between intrinsic normal spaces

A commuting square of differentiable maps between two smooth embeddings induces a continuous
linear map between their normal spaces. The ambient differential carries tangent vectors to
tangent vectors, so it descends to the quotient. The induced map is an equivalence when the base
differential is surjective and the ambient map is a local diffeomorphism. In particular, these
equivalences identify intrinsic normal fibres in different submanifold coordinates, without
choosing a metric or a complement.

The square need only commute near the chosen base point. This local formulation allows the
construction to be applied to coordinate maps and to their restrictions.

A globally commuting square of differentiable maps also induces a map of intrinsic normal total
spaces, acting on each fibre by the normal map; these maps respect identities and composition.

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

/-- The differentials in a square commuting near `x` commute at `x`. -/
private theorem mfderiv_comp_eq_of_eventuallyEq (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).comp (mfderiv I J f x) =
      (mfderiv I' J' g (u x)).comp (mfderiv I I' u x) := by
  -- The germ-congruence formula uses the identification in the opposite direction.
  -- Applying its inverse puts both differentials in the target tangent space.
  have hd := h.mfderiv_eq (I := I) (I' := J')
  rw [mfderiv_comp x hv (f.contMDiff.mdifferentiableAt hn),
    mfderiv_comp x (g.contMDiff.mdifferentiableAt hm) hu] at hd
  ext w
  convert congrArg
    (fun L => (tangentSpaceCast J' (g (u x)) (v (f x))).symm (L w)) hd using 1
  · rfl
  · exact ((tangentSpaceCast J' (g (u x)) (v (f x))).symm_apply_apply _).symm

/-- The ambient differential in a locally commuting square carries tangent vectors to
tangent vectors. -/
theorem tangentRange_le_comap_mfderiv (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    f.tangentRange x hn ≤
      (g.tangentRange (u x) hm).comap
        ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).toLinearMap := by
  intro w hw
  obtain ⟨w, rfl⟩ := (f.mem_tangentRange_iff x hn w).mp hw
  apply (g.mem_tangentRange_iff (u x) hm _).mpr
  refine ⟨mfderiv I I' u x w, ?_⟩
  exact (congrArg (fun L => L w) (f.mfderiv_comp_eq_of_eventuallyEq g hn hm hu hv h)).symm

/-- The normal map induced by a square commuting near `x`. On an ambient tangent class,
it is given by the differential of `v`. -/
def normalMap (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    f.NormalSpace x hn →L[𝕜] g.NormalSpace (u x) hm :=
  f.normalLiftL x hn ((g.normalClassL (u x) hm).comp
      ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))))
    (fun w hw => by
      simp only [ContinuousLinearMap.comp_apply, normalClassL_apply,
        normalClass_eq_zero_iff]
      exact f.tangentRange_le_comap_mfderiv g hn hm hu hv h hw)

/-- The induced normal map commutes with the continuous quotient maps. -/
@[simp]
theorem normalMap_comp_normalClassL (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    (f.normalMap g hn hm hu hv h).comp (f.normalClassL x hn) =
      (g.normalClassL (u x) hm).comp
        ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))) := by
  exact f.normalLiftL_comp_normalClassL x hn _ _

/-- The induced normal map sends the class of `w` to the class of `dv(w)`. -/
@[simp]
theorem normalMap_normalClass (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (w : TangentSpace J (f x)) :
    f.normalMap g hn hm hu hv h (f.normalClass x hn w) =
      g.normalClass (u x) hm
        (tangentSpaceCast J' (v (f x)) (g (u x)) (mfderiv J J' v (f x) w)) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    normalClassL_apply] using
    congrArg (fun L => L w) (f.normalMap_comp_normalClassL g hn hm hu hv h)

/-- The identity square induces the identity on the normal space. -/
@[simp]
theorem normalMap_id (hn : n ≠ 0) (x : M) :
    f.normalMap f hn hn (mdifferentiableAt_id (x := x))
      mdifferentiableAt_id (Filter.EventuallyEq.refl _ _) =
      ContinuousLinearMap.id 𝕜 (f.NormalSpace x hn) := by
  ext z
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn z
  simp [tangentSpaceCast]

/-- A differentiable commuting square induces a map of intrinsic normal total spaces.
On each fibre it is the normal map induced by the ambient differential. -/
def normalBundleMap (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiable I I' u) (hv : MDifferentiable J J' v)
    (h : v ∘ f = g ∘ u) (p : Bundle.TotalSpace K (fun x => f.NormalSpace x hn)) :
    Bundle.TotalSpace K' (fun x => g.NormalSpace x hm) :=
  ⟨u p.proj, f.normalMap g hn hm (hu p.proj) (hv (f p.proj)) (EventuallyEq.of_eq h) p.2⟩

/-- The induced total map applies the normal map in each fibre. -/
@[simp] theorem normalBundleMap_apply (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiable I I' u) (hv : MDifferentiable J J' v)
    (h : v ∘ f = g ∘ u) (p : Bundle.TotalSpace K (fun x => f.NormalSpace x hn)) :
    f.normalBundleMap (K' := K') g hn hm hu hv h p =
      ⟨u p.proj, f.normalMap g hn hm (hu p.proj) (hv (f p.proj)) (EventuallyEq.of_eq h) p.2⟩ :=
  (rfl)

/-- The identity square induces the identity of the normal bundle. -/
@[simp] theorem normalBundleMap_id (hn : n ≠ 0) :
    f.normalBundleMap (K := K) (K' := K) f hn hn (u := _root_.id) (v := _root_.id)
      mdifferentiable_id mdifferentiable_id rfl =
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

/-- Composing locally commuting squares composes their induced normal maps.
The composite square is obtained from the two given germs. -/
theorem normalMap_comp (hn : n ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (hu' : MDifferentiableAt I' I'' u' (u x))
    (hv' : MDifferentiableAt J' J'' v' (g (u x)))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (h' : v' ∘ g =ᶠ[𝓝 (u x)] q ∘ u') :
    f.normalMap q hn hr (hu'.comp x hu)
      (hv'.comp_of_eq (f x) hv h.eq_of_nhds) (by
        filter_upwards [h, h'.comp_tendsto hu.continuousAt] with y hy hy'
        exact (congrArg v' hy).trans hy') =
      (g.normalMap q hm hr hu' hv' h').comp (f.normalMap g hn hm hu hv h) := by
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

/-- Composing commuting squares composes their induced maps on normal total spaces. -/
theorem normalBundleMap_comp (hn : n ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0)
    (hu : MDifferentiable I I' u) (hv : MDifferentiable J J' v)
    (hu' : MDifferentiable I' I'' u') (hv' : MDifferentiable J' J'' v')
    (h : v ∘ f = g ∘ u) (h' : v' ∘ g = q ∘ u') :
    f.normalBundleMap (K := K) (K' := K'') q hn hr (hu'.comp hu) (hv'.comp hv)
        (by
          funext x
          exact (congrArg v' (congrFun h x)).trans (congrFun h' (u x))) =
      g.normalBundleMap (K := K') (K' := K'') q hm hr hu' hv' h' ∘
        f.normalBundleMap g hn hm hu hv h := by
  funext p
  simp only [Function.comp_apply, normalBundleMap_apply]
  have hc := f.normalMap_comp g q hn hm hr (hu p.proj) (hv (f p.proj))
    (hu' (u p.proj)) (hv' (g (u p.proj)))
    (EventuallyEq.of_eq h) (EventuallyEq.of_eq h')
  exact congrArg (Bundle.TotalSpace.mk (u' (u p.proj))) (congrArg (fun L => L p.2) hc)

end Composition

/-- If the base differential is surjective, the ambient differential carries the tangent
range onto the target tangent range. -/
theorem map_tangentRange_mfderiv (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : MDifferentiableAt J J' v (f x))
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (hsurj : Surjective (mfderiv I I' u x)) :
    (f.tangentRange x hn).map ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).toLinearMap =
      g.tangentRange (u x) hm := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr
      (f.tangentRange_le_comap_mfderiv g hn hm hu hv h)
  · intro w hw
    obtain ⟨w, rfl⟩ := (g.mem_tangentRange_iff (u x) hm w).mp hw
    obtain ⟨z, rfl⟩ := hsurj w
    refine ⟨mfderiv I J f x z, (f.mem_tangentRange_iff x hn _).mpr ⟨z, rfl⟩, ?_⟩
    exact congrArg (fun L => L z) (f.mfderiv_comp_eq_of_eventuallyEq g hn hm hu hv h)

/-- The ambient tangent equivalence has the cast-composed differential as its linear map. -/
private theorem mfderivEquiv_trans_tangentSpaceCast_toLinearMap {l : ℕ∞ω}
    (hv : IsLocalDiffeomorphAt J J' l v (f x)) (hl : l ≠ 0) :
    ((hv.mfderivToContinuousLinearEquiv hl).trans
      (tangentSpaceCast J' (v (f x)) (g (u x)))).toLinearMap =
      ((tangentSpaceCast J' (v (f x)) (g (u x))).toContinuousLinearMap.comp
        (mfderiv J J' v (f x))).toLinearMap := by
  ext w
  simpa only [LinearEquiv.coe_toLinearMap, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.comp_apply] using
    congrArg (fun L : TangentSpace J (f x) →L[𝕜] TangentSpace J' (v (f x)) =>
      tangentSpaceCast J' (v (f x)) (g (u x)) (L w))
      (hv.mfderivToContinuousLinearEquiv_coe hl)

/-- A commuting square identifies the intrinsic normal fibres when the base differential is
surjective and the ambient map is a local diffeomorphism at the chosen point. -/
def normalSpaceEquiv {l : ℕ∞ω} (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : IsLocalDiffeomorphAt J J' l v (f x))
    (hsurj : Surjective (mfderiv I I' u x)) (hl : l ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    f.NormalSpace x hn ≃L[𝕜] g.NormalSpace (u x) hm :=
  f.normalSpaceEquivOfMapTangentRange g x (u x) hn hm
    ((hv.mfderivToContinuousLinearEquiv hl).trans
      (tangentSpaceCast J' (v (f x)) (g (u x))))
    (by
      rw [f.mfderivEquiv_trans_tangentSpaceCast_toLinearMap g (u := u) hv hl]
      exact f.map_tangentRange_mfderiv g hn hm hu (hv.mdifferentiableAt hl) h hsurj)

/-- The normal-fibre equivalence has the normal map as its underlying continuous linear map. -/
@[simp]
theorem normalSpaceEquiv_toContinuousLinearMap {l : ℕ∞ω} (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : IsLocalDiffeomorphAt J J' l v (f x))
    (hsurj : Surjective (mfderiv I I' u x)) (hl : l ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) :
    (f.normalSpaceEquiv g hn hm hu hv hsurj hl h).toContinuousLinearMap =
      f.normalMap g hn hm hu (hv.mdifferentiableAt hl) h := by
  ext z
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn z
  simp only [ContinuousLinearEquiv.coe_apply, normalSpaceEquiv,
    normalSpaceEquivOfMapTangentRange_normalClass, normalMap_normalClass]
  exact congrArg (g.normalClass (u x) hm)
    (congrArg (fun L => L w) (f.mfderivEquiv_trans_tangentSpaceCast_toLinearMap g (u := u) hv hl))

/-- On representatives, the normal-fibre equivalence applies the ambient differential. -/
@[simp]
theorem normalSpaceEquiv_normalClass {l : ℕ∞ω} (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : IsLocalDiffeomorphAt J J' l v (f x))
    (hsurj : Surjective (mfderiv I I' u x)) (hl : l ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u)
    (w : TangentSpace J (f x)) :
    f.normalSpaceEquiv g hn hm hu hv hsurj hl h (f.normalClass x hn w) =
      g.normalClass (u x) hm
        (tangentSpaceCast J' (v (f x)) (g (u x)) (mfderiv J J' v (f x) w)) := by
  simpa only [ContinuousLinearEquiv.coe_apply, normalMap_normalClass] using
    congrArg (fun L => L (f.normalClass x hn w))
      (f.normalSpaceEquiv_toContinuousLinearMap g hn hm hu hv hsurj hl h)

/-- On representatives, the inverse normal-fibre equivalence applies the inverse ambient
differential, after identifying the equal ambient base points. -/
@[simp]
theorem normalSpaceEquiv_symm_normalClass {l : ℕ∞ω} (hn : n ≠ 0) (hm : m ≠ 0)
    (hu : MDifferentiableAt I I' u x) (hv : IsLocalDiffeomorphAt J J' l v (f x))
    (hsurj : Surjective (mfderiv I I' u x)) (hl : l ≠ 0) (h : v ∘ f =ᶠ[𝓝 x] g ∘ u)
    (w : TangentSpace J' (g (u x))) :
    (f.normalSpaceEquiv g hn hm hu hv hsurj hl h).symm (g.normalClass (u x) hm w) =
      f.normalClass x hn
        (((hv.mfderivToContinuousLinearEquiv hl).trans
          (tangentSpaceCast J' (v (f x)) (g (u x)))).symm w) := by
  apply (f.normalSpaceEquiv g hn hm hu hv hsurj hl h).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, normalSpaceEquiv_normalClass]
  congr 1
  let e := (hv.mfderivToContinuousLinearEquiv hl).trans
    (tangentSpaceCast J' (v (f x)) (g (u x)))
  exact ((congrArg (fun L => L (e.symm w))
    (f.mfderivEquiv_trans_tangentSpaceCast_toLinearMap g (u := u) hv hl)).symm.trans
      (e.apply_symm_apply w)).symm

end TauCeti.SmoothEmbedding
