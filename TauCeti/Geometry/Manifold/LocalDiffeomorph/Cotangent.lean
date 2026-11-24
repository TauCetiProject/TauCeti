/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Relation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Cotangent maps of local diffeomorphisms

A smooth map `f : M → N` relates covectors of `M` and `N` by pulling them back along its
differential (`TauCeti.CotangentBundle.cotangentRel`), and in general this relation is not the
graph of a map. When `f` is a local diffeomorphism, every differential `df_x` is invertible, and
the relation is the graph of the **cotangent map**

`T*M → T*N, (x, p) ↦ (f x, p ∘ (df_x)⁻¹)`

(`IsLocalDiffeomorph.cotangent`, `TauCeti.CotangentBundle.cotangentRel_iff_of_isLocalDiffeomorph`).
For a diffeomorphism it is the cotangent lift `Diffeomorph.cotangent` (`Diffeomorph.coe_cotangent`).

The cotangent map is smooth (`IsLocalDiffeomorph.contMDiff_cotangent`) and is itself a local
diffeomorphism (`IsLocalDiffeomorph.isLocalDiffeomorph_cotangent`): near the covectors over a
point, it is inverted by pulling covectors back along `df` at the points of a local inverse of
`f`. It is
injective, or surjective, exactly when `f` is (`IsLocalDiffeomorph.cotangent_injective_iff`,
`IsLocalDiffeomorph.cotangent_surjective_iff`), and it is functorial
(`IsLocalDiffeomorph.cotangent_id`, `IsLocalDiffeomorph.cotangent_comp`).

So a covering map such as `ℝ → ℝ / 2πℤ` has a cotangent map which is a surjective local
diffeomorphism without a global inverse: the cotangent relation is locally, but not globally,
invertible. This example is worked out in
`TauCeti.Geometry.Manifold.Instances.AddCircle.Cotangent`. The cotangent map preserves the
Liouville and canonical symplectic forms; see `TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2 (cotangent lifts).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 4 and 11 (local diffeomorphisms and pullbacks of covectors).
-/

public section

noncomputable section

open Bundle Function Set
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {f : M → N}

namespace IsLocalDiffeomorph

open TauCeti TauCeti.CotangentBundle

/-- The **cotangent map** of a smooth local diffeomorphism `f : M → N`: the map `T*M → T*N`
sending a covector `p` at `x` to the covector `p ∘ (df_x)⁻¹` at `f x`. -/
def cotangent (hf : IsLocalDiffeomorph I J ∞ f) (z : CotangentBundle I M) :
    CotangentBundle J N :=
  TotalSpace.mk' (F →L[𝕜] 𝕜) (f z.proj)
    (z.snd ∘L (((hf z.proj).mfderivToContinuousLinearEquiv (by simp)).symm :
      TangentSpace J (f z.proj) →L[𝕜] TangentSpace I z.proj))

variable (hf : IsLocalDiffeomorph I J ∞ f)

/-- The cotangent map sends a covector `p` at `x` to `p ∘ (df_x)⁻¹` at `f x`. -/
theorem cotangent_apply (z : CotangentBundle I M) :
    hf.cotangent z = TotalSpace.mk' (F →L[𝕜] 𝕜) (f z.proj)
      (z.snd ∘L (((hf z.proj).mfderivToContinuousLinearEquiv (by simp)).symm :
        TangentSpace J (f z.proj) →L[𝕜] TangentSpace I z.proj)) :=
  (rfl)

/-- The cotangent map of `f` covers `f`. -/
@[simp]
theorem proj_cotangent (z : CotangentBundle I M) : (hf.cotangent z).proj = f z.proj :=
  (rfl)

/-- The image covector evaluates a tangent vector `w` at `f x` as the original covector evaluates
`(df_x)⁻¹ w`. -/
theorem cotangent_snd_apply (z : CotangentBundle I M) (w : TangentSpace J (f z.proj)) :
    (hf.cotangent z).snd w = z.snd (((hf z.proj).mfderivToContinuousLinearEquiv
        (by simp)).symm w) :=
  (rfl)

/-- **The cotangent map preserves the pairing of covectors with tangent vectors:** the image
covector evaluated on `df_x v` is the original covector evaluated on `v`. -/
@[simp]
theorem cotangent_snd_apply_mfderiv (z : CotangentBundle I M) (v : TangentSpace I z.proj) :
    (hf.cotangent z).snd (mfderiv I J f z.proj v) = z.snd v :=
  congrArg z.snd ((hf z.proj).mfderivToContinuousLinearEquiv_symm_mfderiv_apply (by simp) v)

/-- The cotangent map sends the zero covector at `x` to the zero covector at `f x`. -/
@[simp]
theorem cotangent_zeroSection (x : M) :
    hf.cotangent (zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x) =
      zeroSection (F →L[𝕜] 𝕜) (fun y : N ↦ TangentSpace J y →L[𝕜] 𝕜) (f x) :=
  CotangentBundle.ext rfl fun _ ↦ rfl

end IsLocalDiffeomorph

namespace TauCeti.CotangentBundle

/-- **For a local diffeomorphism, the cotangent relation is the graph of the cotangent map.** -/
theorem cotangentRel_iff_of_isLocalDiffeomorph (hf : IsLocalDiffeomorph I J ∞ f)
    (z : CotangentBundle I M) (w : CotangentBundle J N) :
    cotangentRel I J f z w ↔ hf.cotangent z = w := by
  constructor
  · intro hz
    refine CotangentBundle.ext (cotangentRel_proj hz) fun v ↦ ?_
    -- Evaluate both covectors on `v = df_x ((df_x)⁻¹ v)`.
    exact (hf.cotangent_snd_apply z v).trans ((cotangentRel_snd_apply hz _).trans
      (congrArg w.snd ((hf z.proj).mfderiv_mfderivToContinuousLinearEquiv_symm_apply (by simp) v)))
  · rintro rfl
    exact (cotangentRel_iff I J f z _).2
      ⟨rfl, ContinuousLinearMap.ext fun v ↦ (hf.cotangent_snd_apply_mfderiv z v).symm⟩

end TauCeti.CotangentBundle

open TauCeti TauCeti.CotangentBundle

/-- The cotangent lift of a diffeomorphism is the cotangent map of the underlying local
diffeomorphism. -/
theorem Diffeomorph.coe_cotangent [IsManifold I 2 M] [IsManifold J 2 N] (h : M ≃ₘ⟮I, J⟯ N) :
    ⇑h.cotangent = h.isLocalDiffeomorph.cotangent :=
  funext fun z ↦ ((cotangentRel_iff_of_isLocalDiffeomorph _ z _).1
    ((cotangentRel_diffeomorph_iff I J h z _).2 rfl)).symm

namespace IsLocalDiffeomorph

/-- The cotangent map of the identity is the identity. -/
@[simp]
theorem cotangent_id (h : IsLocalDiffeomorph I I ∞ (id : M → M)) : h.cotangent = id :=
  funext fun z ↦ ((cotangentRel_iff_of_isLocalDiffeomorph h z z).1
    ((cotangentRel_id_iff I z z).2 rfl))

/-- **Functoriality:** the cotangent map of a composite of local diffeomorphisms is the composite
of their cotangent maps. -/
theorem cotangent_comp {g : N → P} (hg : IsLocalDiffeomorph J K ∞ g)
    (hf : IsLocalDiffeomorph I J ∞ f) (hgf : IsLocalDiffeomorph I K ∞ (g ∘ f)) :
    hgf.cotangent = hg.cotangent ∘ hf.cotangent := by
  funext z
  refine (cotangentRel_iff_of_isLocalDiffeomorph hgf z _).1 ?_
  refine (cotangentRel_comp_iff I J K z _ (hf.mdifferentiable (by simp) z.proj)
    (hg.mdifferentiable (by simp) (f z.proj))).2 ⟨hf.cotangent z, ?_, ?_⟩
  · exact (cotangentRel_iff_of_isLocalDiffeomorph hf z _).2 rfl
  · exact (cotangentRel_iff_of_isLocalDiffeomorph hg _ _).2 rfl

variable (hf : IsLocalDiffeomorph I J ∞ f)

/-- The cotangent map of a local diffeomorphism is injective exactly when the map is. -/
theorem cotangent_injective_iff : Injective hf.cotangent ↔ Injective f := by
  constructor
  · intro h x y hxy
    have h0 := h ((hf.cotangent_zeroSection x).trans
      ((congrArg (zeroSection (F →L[𝕜] 𝕜) _) hxy).trans (hf.cotangent_zeroSection y).symm))
    simpa only [zeroSection_proj] using congrArg TotalSpace.proj h0
  · intro h z z' hzz'
    -- Both covectors are related to the same covector, over the same base point.
    refine eq_of_cotangentRel_of_proj_eq ((cotangentRel_iff_of_isLocalDiffeomorph hf z _).2 rfl)
      ((cotangentRel_iff_of_isLocalDiffeomorph hf z' _).2 hzz'.symm) (h ?_)
    simpa only [proj_cotangent] using congrArg TotalSpace.proj hzz'

/-- The cotangent map of a local diffeomorphism is surjective exactly when the map is. -/
theorem cotangent_surjective_iff : Surjective hf.cotangent ↔ Surjective f := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (zeroSection (F →L[𝕜] 𝕜) (fun y : N ↦ TangentSpace J y →L[𝕜] 𝕜) y)
    exact ⟨z.proj, by
      simpa only [proj_cotangent, zeroSection_proj] using congrArg TotalSpace.proj hz⟩
  · intro h w
    obtain ⟨x, hx⟩ := h w.proj
    -- The covector over `x` related to `w` is the pullback of `w` along `df_x`.
    exact ⟨TotalSpace.mk' (E →L[𝕜] 𝕜) x (w.snd ∘L mfderiv I J f x),
      (cotangentRel_iff_of_isLocalDiffeomorph hf _ w).1
        ((cotangentRel_iff I J f _ w).2 ⟨hx, rfl⟩)⟩

section Smooth

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **The cotangent map of a local diffeomorphism is smooth.** -/
theorem contMDiff_cotangent :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) ∞ hf.cotangent := by
  intro z₀
  obtain ⟨Φ, hx₀, hfΦ⟩ := hf z₀.proj
  have hU : ∀ᶠ z in 𝓝 z₀, z.proj ∈ Φ.source :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hx₀)
  -- Every fibre of `T*M` is `E →L[𝕜] 𝕜`, so `z.2` may be placed over `Φ⁻¹ (f z.proj)`; near `z₀`
  -- this point is `z.proj`, and the cotangent map pulls `z.2` back along `dΦ⁻¹`.
  have hΨ : (fun z : CotangentBundle I M ↦
      TotalSpace.mk' (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)
        (Φ.symm (f z.proj)) z.snd) =ᶠ[𝓝 z₀] id := by
    filter_upwards [hU] with z hz
    exact CotangentBundle.ext (by simp [hfΦ hz, Φ.left_inv hz]) fun _ ↦ rfl
  refine (contMDiffAt_mk_comp_mfderiv (g := fun z : CotangentBundle I M ↦ f z.proj)
    (f := Φ.symm) (fun _ ↦ rfl) (contMDiffAt_id.congr_of_eventuallyEq hΨ)
    (hf.contMDiff.comp (contMDiff_proj _) z₀)
    (Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds ((hfΦ hx₀).symm ▸ Φ.map_source hx₀)))
    (by simp)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with z hz
  exact CotangentBundle.ext rfl fun w ↦
    congrArg z.snd ((hf z.proj).mfderivToContinuousLinearEquiv_symm_apply (by simp) hfΦ hz w)

/-- Near the covectors over the source of a partial diffeomorphism `Φ` agreeing with `f`, the
cotangent map of `f` is a partial diffeomorphism. Its inverse pulls a covector at `y` back along
`df` at `Φ⁻¹ y`. -/
private def cotangentPartialDiffeomorph {Φ : PartialDiffeomorph I J M N ∞}
    (hfΦ : EqOn f Φ Φ.source) :
    PartialDiffeomorph (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      (CotangentBundle I M) (CotangentBundle J N) ∞ where
  toFun := hf.cotangent
  invFun w := TotalSpace.mk' (E →L[𝕜] 𝕜) (Φ.symm w.proj) (w.snd ∘L mfderiv I J f (Φ.symm w.proj))
  source := TotalSpace.proj ⁻¹' Φ.source
  target := TotalSpace.proj ⁻¹' Φ.target
  map_source' z hz := by
    rw [mem_preimage, proj_cotangent, hfΦ hz]
    exact Φ.map_source hz
  map_target' _ hw := Φ.map_target hw
  left_inv' z hz := by
    have hx : Φ.symm (f z.proj) = z.proj := (hfΦ hz).symm ▸ Φ.left_inv hz
    refine CotangentBundle.ext hx fun v ↦ ?_
    -- Transport the differential of `f` from `Φ⁻¹ (f x)` to `x`, then cancel it.
    exact (hf.cotangent_snd_apply z _).trans (congrArg z.snd
      ((congrArg (fun y : M ↦
        (((hf z.proj).mfderivToContinuousLinearEquiv (by simp)).symm (mfderiv I J f y v) : E))
        hx).trans ((hf z.proj).mfderivToContinuousLinearEquiv_symm_mfderiv_apply (by simp) v)))
  right_inv' w hw := by
    have hy : f (Φ.symm w.proj) = w.proj := (hfΦ (Φ.map_target hw)).trans (Φ.right_inv hw)
    refine CotangentBundle.ext hy fun v ↦ ?_
    exact (hf.cotangent_snd_apply _ v).trans (congrArg w.snd
      ((hf (Φ.symm w.proj)).mfderiv_mfderivToContinuousLinearEquiv_symm_apply (by simp) v))
  open_source := Φ.open_source.preimage (FiberBundle.continuous_proj _ _)
  open_target := Φ.open_target.preimage (FiberBundle.continuous_proj _ _)
  contMDiffOn_toFun := hf.contMDiff_cotangent.contMDiffOn
  contMDiffOn_invFun w₀ hw₀ := by
    have hV : ∀ᶠ w in 𝓝 w₀, w.proj ∈ Φ.target :=
      (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hw₀)
    -- Place `w.2` over `f (Φ⁻¹ w.proj)`, which is `w.proj` near `w₀`, and pull it back along `df`.
    have hΨ : (fun w : CotangentBundle J N ↦
        TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun y : N ↦ TangentSpace J y →L[𝕜] 𝕜)
          (f (Φ.symm w.proj)) w.snd) =ᶠ[𝓝 w₀] id := by
      filter_upwards [hV] with w hw
      exact CotangentBundle.ext ((hfΦ (Φ.map_target hw)).trans (Φ.right_inv hw)) fun _ ↦ rfl
    exact (contMDiffAt_mk_comp_mfderiv (g := fun w : CotangentBundle J N ↦ Φ.symm w.proj)
      (f := f) (fun _ ↦ rfl) (contMDiffAt_id.congr_of_eventuallyEq hΨ)
      ((Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hw₀)).comp w₀
        (contMDiff_proj _ w₀)) (hf.contMDiff _) (by simp)).contMDiffWithinAt

/-- **The cotangent map of a local diffeomorphism is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_cotangent :
    IsLocalDiffeomorph (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) ∞ hf.cotangent := by
  intro z
  obtain ⟨Φ, hx, hfΦ⟩ := hf z.proj
  exact ⟨cotangentPartialDiffeomorph hf hfΦ, hx, fun _ _ ↦ rfl⟩

end Smooth

end IsLocalDiffeomorph
