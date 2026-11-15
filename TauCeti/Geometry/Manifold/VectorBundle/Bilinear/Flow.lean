/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.LieDeriv
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Flow.Eulerian
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Pullback variation of covariant two-tensors along isotopies and flows

Let `b_t` be a time-dependent family of covariant two-tensors on a boundaryless `C²` manifold `M`,
taking values in a normed space `G`, with parameter derivative `b'` at time `t`. Along a smooth
family of maps or diffeomorphisms `φ_t`, the pullbacks `φ_t^* b_t` at a point `x` form a curve in
the space of continuous bilinear maps on `T_x M`, and its time derivative splits into the pullback
of `b'` and the pullback of the Lie derivative along the instantaneous velocity field:

`d/du|_{u = t} (φ_u^* b_u)_x = (φ_t^* (b' + L_{X_t} b_t))_x`.

Specializing to a stationary tensor `b_u = b` (`b' = 0`) identifies the chart-defined Lie derivative
`TauCeti.mlieDerivBilin` with the flow derivative `d/dt|₀ (φ_t^* b)` along maximal, time-dependent,
and isotopy flows; specializing to `b'_t + L_{X_t} b_t = 0` shows that `φ_t^* b_t` is independent of
time (the Lie-transported / diffeomorphism-gauge case).

## Main results

* `TauCeti.hasDerivAt_mpullbackBilin_family_of_eq_id`, `TauCeti.hasDerivAt_mpullbackBilin_of_eq_id`:
  velocity of pulled-back covariant two-tensors along a family equal to the identity at time `t`.
* `TauCeti.hasDerivAt_mpullbackBilin_of_eq_comp`: base-point transport along `ψ_u = χ_u ∘ g`.
* `TauCeti.hasDerivAt_mpullbackBilin_family_eulerianField`,
  `TauCeti.hasDerivAt_mpullbackBilin_eulerianField`,
  `TauCeti.mpullbackBilin_family_eulerianField_eq_of_add_mlieDerivBilin_eq_zero`,
  `TauCeti.forall_mpullbackBilin_eq_iff_forall_mlieDerivBilin_eulerianField_eq_zero`: pullback
  variation, constancy, and invariance along smooth isotopies (`TauCeti.eulerianField`).
* `TauCeti.hasDerivAt_mpullbackBilin_flowOf_zero`, `TauCeti.hasDerivAt_mpullbackBilin_flowOf`,
  `TauCeti.hasDerivAt_mpullbackBilin_family_flowOf`,
  `TauCeti.mpullbackBilin_flowOf_apply_eq_of_mlieDerivBilin_eq_zero`: pullback variation and
  invariance along autonomous maximal flows (`TauCeti.flowOf`).
* `TauCeti.hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self`,
  `TauCeti.hasDerivAt_mpullbackBilin_family_timeDependentFlowOf`,
  `TauCeti.hasDerivAt_mpullbackBilin_timeDependentFlowOf`,
  `TauCeti.mpullbackBilin_timeDependentFlowOf_eq_self_iff`: pullback variation and invariance along
  time-dependent flows (`TauCeti.timeDependentFlowOf`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition 12.36
  and Chapter 22.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapters 1 and 3.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006),
  Proposition 1.2.2 and Appendix A.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

-- Resolve normed-space vs seminormed-space diamonds on nested continuous linear map spaces.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

/-! ### Pullbacks along a general family of maps -/

section Family

variable {E H M E' H' M' G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Near time `t`, the pullback of a time-dependent covariant two-tensor `b_u` at `y` along a
jointly `C¹` family `ψ_u` sending `(t, y)` into `(extChartAt I' c).source` equals the flat pullback
of `inChartAtBilin I' c (b u)` along the coordinate expression of `ψ_u`. -/
theorem eventuallyEq_mpullbackBilin_pullbackBilinL [IsManifold I 1 M] [I.Boundaryless]
    [IsManifold I' 1 M']
    (b : ℝ → (y : M') → TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] G)
    {ψ : ℝ → M → M'} {t : ℝ} {y : M} (c : M')
    (hψt : ψ t y ∈ (extChartAt I' c).source)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I' 1 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y)) :
    (fun u ↦ (mpullbackBilin I I' (ψ u) (b u) y : E →L[ℝ] E →L[ℝ] G)) =ᶠ[𝓝 t] fun u ↦
      ContinuousLinearMap.pullbackBilinL
        (fderiv ℝ (fun z ↦ extChartAt I' c (ψ u ((extChartAt I y).symm z))) (extChartAt I y y))
        (inChartAtBilin I' c (b u)
          (extChartAt I' c (ψ u ((extChartAt I y).symm (extChartAt I y y))))) := by
  have hψ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I' (ψ u) y := by
    have h := ((continuous_id.prodMk continuous_const).tendsto t).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hsmooth)
    filter_upwards [h] with u hu
    exact (hu.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_id) rfl).mdifferentiableAt
      (by norm_num)
  have hcont : ContinuousAt (fun u ↦ ψ u y) t :=
    hsmooth.continuousAt.comp (f := fun u : ℝ ↦ (u, y))
      (continuous_id.prodMk continuous_const).continuousAt
  have hsrc : ∀ᶠ u in 𝓝 t, ψ u y ∈ (extChartAt I' c).source :=
    hcont.preimage_mem_nhds ((isOpen_extChartAt_source c).mem_nhds hψt)
  filter_upwards [hsrc, hψ] with u hu hψu
  rw [extChartAt_to_inv, mpullbackBilin_eq_pullbackBilinL (b u) c hψu hu,
    I.range_eq_univ, fderivWithin_univ]
  rfl

/-- If a time-dependent covariant two-tensor `b` is jointly differentiable as a bundle map at
`(t, y)` on a boundaryless manifold, then `(u, z) ↦ inChartAtBilin I y (b u) z` is jointly Fréchet
differentiable at `(t, extChartAt I y y)`. -/
theorem differentiableAt_uncurry_inChartAtBilin [IsManifold I 1 M] [I.Boundaryless]
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} {t : ℝ} {y : M}
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y)) :
    DifferentiableAt ℝ (fun p : ℝ × E ↦ inChartAtBilin I y (b p.1) p.2)
      (t, extChartAt I y y) := by
  let _ : ∀ q : M, IsNormableSpace ℝ (TangentSpace I q) := fun q ↦
    (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I : M → Type _) q).isNormableSpace
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I y).symm (extChartAt I y y) := by
    have h := mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target (I := I) y)
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hpair : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I)
      (fun p : ℝ × E ↦ (p.1, (extChartAt I y).symm p.2)) (t, extChartAt I y y) :=
    mdifferentiableAt_fst.prodMk (hsymm.comp (t, extChartAt I y y) mdifferentiableAt_snd)
  rw [mdifferentiableAt_totalSpace] at hb
  have hcomp := hb.2.comp_of_eq (t, extChartAt I y y) hpair (Prod.ext rfl (extChartAt_to_inv y))
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
    mdifferentiableAt_iff_differentiableAt] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.eventually (extChartAt_target_mem_nhds y)] with p hp
  exact inChartAtBilin_eq_trivializationAt y (b p.1) hp

/-- If a time-dependent covariant two-tensor `b` is jointly differentiable at `(t, y)` on a
boundaryless manifold, then its parameter curve `u ↦ b u y` is differentiable at `t`. -/
theorem differentiableAt_atPoint_of_mdifferentiableAt [IsManifold I 1 M] [I.Boundaryless]
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} {t : ℝ} {y : M}
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y)) :
    DifferentiableAt ℝ (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) t := by
  have hpair : DifferentiableAt ℝ (fun u : ℝ ↦ (u, extChartAt I y y)) t :=
    differentiableAt_id.prodMk (differentiableAt_const (extChartAt I y y))
  have h := (differentiableAt_uncurry_inChartAtBilin hb).comp t hpair
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun u ↦ (inChartAtBilin_extChartAt_self y (b u)).symm)

/-- **Pullback variation at the identity.** Let `ψ_u` be a family of maps of `M` that is the
identity near `y` at time `t`, is jointly `C²` at `(t, y)`, and moves points near `y` at time `t`
with velocity `V`. For a family `b_u` jointly differentiable at `(t, y)` with parameter derivative
`b' y` at `y`, `d/du|_{u = t} (ψ_u^* b_u)_y = (b' + L_V b_t)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_of_eq_id [IsManifold I 2 M] [I.Boundaryless]
    {ψ : ℝ → M → M} {V : (x : M) → TangentSpace I x}
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} {t : ℝ} (y : M)
    (hid : ∀ᶠ x in 𝓝 y, ψ t x = x)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y))
    (hvel : ∀ᶠ x in 𝓝 y,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ t x))))
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) y)
      ((b' + mlieDerivBilin I V (b t)) y) t := by
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  set Φ : ℝ × E → E := fun p ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))
  set W := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I) with hW
  have hΦsmooth : ContDiffAt ℝ 2 Φ (t, extChartAt I y y) :=
    Manifold.contDiffAt_extChartAt_family hid.self_of_nhds hsmooth
  have hΦt_nhds : (fun z ↦ Φ (t, z)) =ᶠ[𝓝 (extChartAt I y y)] id :=
    Manifold.eventuallyEq_extChartAt_family_of_eq_id hid
  have hΦt : Φ (t, extChartAt I y y) = extChartAt I y y := hΦt_nhds.self_of_nhds
  have hvel' : ∀ᶠ z in 𝓝 (extChartAt I y y), HasDerivAt (fun u ↦ Φ (u, z)) (W z) t :=
    eventually_hasDerivAt_extChartAt_family hid hvel
  have hspatial : HasDerivAt (fun u ↦ fderiv ℝ (fun z ↦ Φ (u, z)) (extChartAt I y y))
      (fderiv ℝ W (Φ (t, extChartAt I y y)) ∘L
        fderiv ℝ (fun z ↦ Φ (t, z)) (extChartAt I y y)) t := by
    rw [hΦt, hΦt_nhds.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id]
    exact ContDiffAt.hasDerivAt_fderiv_slice_of_eventually_hasDerivAt
      (by simpa only [minSmoothness_of_isRCLikeNormedField] using hΦsmooth) hvel'
  have hflat := hasDerivAt_pullbackBilinL_fderiv (b := fun u ↦ inChartAtBilin I y (b u))
    (b' := b' y) (ψ := fun u z ↦ Φ (u, z)) (V := W) (x := extChartAt I y y) (t := t)
    (by rw [hΦt]; exact differentiableAt_uncurry_inChartAtBilin hb)
    (by
      rw [hΦt]
      exact hb'.congr_of_eventuallyEq
        (Eventually.of_forall fun u ↦ inChartAtBilin_extChartAt_self y (b u)))
    (by rw [hΦt]; exact hvel'.self_of_nhds) hspatial
  refine (hflat.congr_of_eventuallyEq
    (eventuallyEq_mpullbackBilin_pullbackBilinL b y
      (by rw [hid.self_of_nhds]; exact mem_extChartAt_source y)
      (hsmooth.of_le one_le_two))).congr_deriv ?_
  rw [hΦt, hΦt_nhds.fderiv_eq, fderiv_id]
  have hlie : (mlieDerivBilin I V (b t) y : E →L[ℝ] E →L[ℝ] G) =
      lieDerivBilin (E := E) W (inChartAtBilin I y (b t)) (extChartAt I y y) := by
    rw [mlieDerivBilin_def, ← hW, I.range_eq_univ]
    erw [lieDerivBilinWithin_univ]
  ext v w
  simp only [ContinuousLinearMap.pullbackBilinL_apply, ContinuousLinearMap.id_apply, Pi.add_apply]
  exact congrArg (b' y v w + ·) (DFunLike.congr_fun (DFunLike.congr_fun hlie.symm v) w)

/-- Stationary specialization of `hasDerivAt_mpullbackBilin_family_of_eq_id`: for a fixed
differentiable covariant two-tensor `b`, `d/du|_{u = t} (ψ_u^* b)_y = (L_V b)_y`. -/
theorem hasDerivAt_mpullbackBilin_of_eq_id [IsManifold I 2 M] [I.Boundaryless]
    {ψ : ℝ → M → M} {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} {t : ℝ} (y : M)
    (hid : ∀ᶠ x in 𝓝 y, ψ t x = x)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y))
    (hvel : ∀ᶠ x in 𝓝 y,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ t x))))
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) y) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) b y)
      (mlieDerivBilin I V b y) t := by
  have h := hasDerivAt_mpullbackBilin_family_of_eq_id (b := fun _ ↦ b) (b' := 0) y hid hsmooth
    hvel (hb.comp (t, y) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))
  simpa only [zero_add] using h

/-- **Moving the base point of pulled-back covariant two-tensors.** If `ψ_u` factors near `(t, x)`
as `χ_u ∘ g` with `g` differentiable at `x` and `χ_u` differentiable at `g x`, and
`(χ_u^* b_u)_{g x}` has time derivative `β (g x)` at `t`, then `(ψ_u^* b_u)_x` has time derivative
`(g^* β)_x` at `t`. -/
theorem hasDerivAt_mpullbackBilin_of_eq_comp
    {ψ χ : ℝ → M → M} {g : M → M}
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {β : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {x : M} {t : ℝ} (hψ : ∀ᶠ u in 𝓝 t, ψ u =ᶠ[𝓝 x] χ u ∘ g) (hg : MDifferentiableAt I I g x)
    (hχ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (χ u) (g x))
    (h : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (χ u) (b u) (g x))
      (β (g x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) x)
      (mpullbackBilin I I g β x) t := by
  set L : E →L[ℝ] E := mfderiv I I g x
  have hL := (ContinuousLinearMap.pullbackBilinL (V := E) (W := E) (G := G) L).hasFDerivAt
    |>.comp_hasDerivAt t h
  refine (hL.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hψ, hχ] with u hu hχu
    rw [hu.mpullbackBilin_eq (b u), mpullbackBilin_comp_at hg hχu (b u)]
    exact mpullbackBilin_apply_eq_pullbackBilinL g _ x
  · exact (mpullbackBilin_apply_eq_pullbackBilinL g β x).symm

/-- If at every time `u` and point `x` the curve `u ↦ (ψ_u^* b_u)_x` has derivative
`(ψ_u^* (β u))_x` with `β u = 0`, then `ψ_s^* b_s = ψ_t^* b_t` for all times `s` and `t`. -/
theorem mpullbackBilin_family_eq_of_forall_eq_zero {ψ : ℝ → M → M}
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {β : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hd : ∀ u x, HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) x)
      (mpullbackBilin I I (ψ u) (β u) x) u)
    (hβ : ∀ u, β u = 0) (s t : ℝ) :
    mpullbackBilin I I (ψ s) (b s) = mpullbackBilin I I (ψ t) (b t) := by
  funext x
  have hderiv (u : ℝ) :
      HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) x) 0 u := by
    have h := hd u x
    rwa [hβ u, mpullbackBilin_zero] at h
  exact is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) s t

end Family

/-! ### Smooth isotopies and Eulerian velocity fields -/

section Isotopy

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : ℝ → M ≃ M}

variable (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ φ p.1 p.2))
  (hφ' : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ (φ p.1).symm p.2))
include hφ hφ'

/-- At the base time `t`, the pullbacks `(φ_u ∘ φ_t⁻¹)^* b_u` at `y` have time derivative
`(b' + L_{X_t} b_t)_y`, where `X_t = eulerianField I φ t`. -/
theorem hasDerivAt_mpullbackBilin_family_eulerianField_self
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (t : ℝ) (y : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (fun x ↦ φ u ((φ t).symm x)) (b u) y)
      ((b' + mlieDerivBilin I (eulerianField I φ t) (b t)) y) t := by
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ φ p.1 ((φ t).symm p.2)) :=
    hφ.comp (contMDiff_fst.prodMk
      ((hφ'.curry_right (f := fun u y ↦ (φ u).symm y) (x := t)).comp contMDiff_snd))
  refine hasDerivAt_mpullbackBilin_family_of_eq_id (ψ := fun u x ↦ φ u ((φ t).symm x))
    (V := eulerianField I φ t) y (Eventually.of_forall fun x ↦ (φ t).apply_symm_apply x)
    hsmooth.contMDiffAt (Eventually.of_forall fun x ↦ ?_) hb hb'
  exact hasMFDerivAt_eulerianField
    ((hφ.curry_left (f := fun u x ↦ φ u x)).mdifferentiable two_ne_zero t)

/-- **Time-dependent pullback variation along a smooth isotopy.** Let `φ_t` be a smooth isotopy of
`M` with Eulerian velocity field `X_t = eulerianField I φ t`. For a family `b_u` jointly
differentiable at `(t, φ_t x)` with parameter derivative `b' (φ_t x)` there,
`d/du|_{u = t} (φ_u^* b_u)_x = (φ_t^* (b' + L_{X_t} b_t))_x`. -/
theorem hasDerivAt_mpullbackBilin_family_eulerianField
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (t : ℝ) (x : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, φ t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (φ t x)) (b' (φ t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (φ u) (b u) x)
      (mpullbackBilin I I (φ t) (b' + mlieDerivBilin I (eulerianField I φ t) (b t)) x) t := by
  have hφu (u : ℝ) : MDifferentiable I I (φ u) :=
    (hφ.curry_right (f := fun u x ↦ φ u x) (x := u)).mdifferentiable two_ne_zero
  have hφt : MDifferentiable I I (φ t).symm :=
    (hφ'.curry_right (f := fun u y ↦ (φ u).symm y) (x := t)).mdifferentiable two_ne_zero
  exact hasDerivAt_mpullbackBilin_of_eq_comp (χ := fun u z ↦ φ u ((φ t).symm z))
    (Eventually.of_forall fun u ↦ Eventually.of_forall fun z ↦ by simp) (hφu t x)
    (Eventually.of_forall fun u ↦ ((hφu u).comp hφt) _)
    (hasDerivAt_mpullbackBilin_family_eulerianField_self hφ hφ' t (φ t x) hb hb')

/-- Stationary pullback variation along a smooth isotopy: for a fixed covariant two-tensor `b`
differentiable at `φ_t x`, `d/du|_{u = t} (φ_u^* b)_x = (φ_t^* (L_{X_t} b))_x`. -/
theorem hasDerivAt_mpullbackBilin_eulerianField
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (t : ℝ) (x : M)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (φ t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (φ u) b x)
      (mpullbackBilin I I (φ t) (mlieDerivBilin I (eulerianField I φ t) b) x) t := by
  have h := hasDerivAt_mpullbackBilin_family_eulerianField hφ hφ' (b := fun _ ↦ b) (b' := 0) t x
    (hb.comp (t, φ t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (φ t x)))
  simpa only [zero_add] using h

/-- **Constancy of Lie-transported covariant two-tensor families.** If a jointly differentiable
family `b_t` has parameter derivative `b'_t` satisfying `b'_t + L_{X_t} b_t = 0` at every time `t`,
where `X_t` is the Eulerian velocity field of `φ`, then `φ_s^* b_s = φ_t^* b_t` for all `s, t`. -/
theorem mpullbackBilin_family_eulerianField_eq_of_add_mlieDerivBilin_eq_zero
    {b b' : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2)))
    (hb' : ∀ t y, HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' t y) t)
    (hL : ∀ t, b' t + mlieDerivBilin I (eulerianField I φ t) (b t) = 0)
    (s t : ℝ) :
    mpullbackBilin I I (φ s) (b s) = mpullbackBilin I I (φ t) (b t) :=
  mpullbackBilin_family_eq_of_forall_eq_zero
    (fun u x ↦ hasDerivAt_mpullbackBilin_family_eulerianField hφ hφ' u x (hb (u, φ u x))
      (hb' u (φ u x))) hL s t

/-- **Invariance of covariant two-tensors under isotopies.** For a differentiable covariant
two-tensor `b`, the pullback `φ_t^* b` is independent of `t` if and only if
`mlieDerivBilin I (eulerianField I φ t) b = 0` for every `t`. -/
theorem forall_mpullbackBilin_eq_iff_forall_mlieDerivBilin_eulerianField_eq_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z))) :
    (∀ s t, mpullbackBilin I I (φ s) b = mpullbackBilin I I (φ t) b) ↔
      ∀ t, mlieDerivBilin I (eulerianField I φ t) b = 0 := by
  constructor
  · intro h t
    funext y
    have hd := hasDerivAt_mpullbackBilin_family_eulerianField_self hφ hφ' (b := fun _ ↦ b)
      (b' := 0) t y ((hb y).comp (t, y) mdifferentiableAt_snd)
      (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))
    rw [zero_add] at hd
    have hconst : (fun u ↦ mpullbackBilin I I (fun x ↦ φ u ((φ t).symm x)) b y) =
        fun _ ↦ mpullbackBilin I I (fun x ↦ φ t ((φ t).symm x)) b y := by
      funext u
      have hcomp (s : ℝ) : (fun x ↦ φ s ((φ t).symm x)) = φ s ∘ (φ t).symm := rfl
      have hφt : MDifferentiableAt I I (φ t).symm y :=
        (hφ'.curry_right (f := fun u y ↦ (φ u).symm y) (x := t)).mdifferentiableAt two_ne_zero
      have hφu (s : ℝ) : MDifferentiable I I (φ s) :=
        (hφ.curry_right (f := fun u x ↦ φ u x) (x := s)).mdifferentiable two_ne_zero
      rw [hcomp, hcomp, mpullbackBilin_comp_at hφt (hφu u _) b,
        mpullbackBilin_comp_at hφt (hφu t _) b, h u t]
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t _)
  · intro h s t
    exact mpullbackBilin_family_eq_of_forall_eq_zero (b := fun _ ↦ b)
      (fun u x ↦ hasDerivAt_mpullbackBilin_eulerianField hφ hφ' u x (hb _)) h s t

end Isotopy

/-! ### Autonomous maximal flows -/

section MaximalFlow

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Z : (x : M) → TangentSpace I x}

variable (hZ : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hZ

/-- **Pullback variation at time zero along the maximal flow.** For a `C²` vector field `Z` with
maximal flow `flowOf Z` and a family `b_s` jointly differentiable at `(0, y)` with parameter
derivative `b' y` there, `d/ds|_{s = 0} ((flowOf Z s)^* b_s)_y = (b' + L_Z b_0)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_flowOf_zero
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (y : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (0, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ b s y) (b' y) 0) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) (b s) y)
      ((b' + mlieDerivBilin I Z (b 0)) y) 0 := by
  have hZ1 := hZ.of_le one_le_two
  refine hasDerivAt_mpullbackBilin_family_of_eq_id (ψ := flowOf Z) (V := Z) y
    (Eventually.of_forall (flowOf_zero Z))
    ((contMDiffOn_flowOf (n := 2) one_le_two hZ).contMDiffAt
      ((isOpen_flowDomain hZ1).mem_nhds (mem_flowDomain_zero hZ1 y)))
    (Eventually.of_forall fun x ↦ ?_) hb hb'
  have hopen : {s | (s, x) ∈ flowDomain Z} ∈ 𝓝 (0 : ℝ) :=
    ((isOpen_flowDomain hZ1).preimage (continuous_id.prodMk continuous_const)).mem_nhds
      (mem_flowDomain_zero hZ1 x)
  exact ((isMIntegralCurveOn_flowOf hZ1 x).isMIntegralCurveAt hopen).hasMFDerivAt

/-- **Flow characterization of the Lie derivative at time zero.** For a `C²` vector field `Z` and a
covariant two-tensor `b` differentiable at `y`, `d/ds|_{s = 0} ((flowOf Z s)^* b)_y = (L_Z b)_y`. -/
theorem hasDerivAt_mpullbackBilin_flowOf_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (y : M)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) y) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) b y)
      (mlieDerivBilin I Z b y) 0 := by
  have h := hasDerivAt_mpullbackBilin_family_flowOf_zero hZ (b := fun _ ↦ b) (b' := 0) y
    (hb.comp (0, y) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) 0 (b y))
  simpa only [zero_add] using h

/-- **Time-dependent pullback variation along a maximal flow.** Wherever `(t, x) ∈ flowDomain Z`
and `b` is jointly differentiable at `(t, flowOf Z t x)` with parameter derivative
`b' (flowOf Z t x)` there,
`d/ds|_{s = t} ((flowOf Z s)^* b_s)_x = ((flowOf Z t)^* (b' + L_Z b_t))_x`. -/
theorem hasDerivAt_mpullbackBilin_family_flowOf
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, flowOf Z t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (flowOf Z t x))
      (b' (flowOf Z t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) (b s) x)
      (mpullbackBilin I I (flowOf Z t) (b' + mlieDerivBilin I Z (b t)) x) t := by
  have hZ1 := hZ.of_le one_le_two
  have hD := isOpen_flowDomain hZ1
  set y := flowOf Z t x
  have hφ : ContMDiffAt I I 2 (flowOf Z t) x :=
    contMDiffAt_flowOf_comp (n := 2) one_le_two hZ contMDiffAt_const contMDiffAt_id hx
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), x),
      (t, p.2) ∈ flowDomain Z ∧ (p.1, flowOf Z t p.2) ∈ flowDomain Z :=
    ((continuous_const.prodMk continuous_snd).continuousAt.eventually_mem (hD.mem_nhds hx)).and
      ((continuousAt_fst.prodMk (hφ.continuousAt.comp continuousAt_snd)).eventually_mem
        (hD.mem_nhds (mem_flowDomain_zero hZ1 _)))
  rw [nhds_prod_eq] at hev
  have hsub : Tendsto (fun s ↦ s - t) (𝓝 t) (𝓝 0) := by
    simpa using (continuous_sub_right t).tendsto t
  have hadd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ r + t) 0 :=
    mdifferentiableAt_iff_differentiableAt.2 (differentiableAt_id.add_const t)
  have hshift : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (fun p : ℝ × M ↦ (p.1 + t, p.2)) (0, y) :=
    (hadd.comp (0, y) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd
  have hb0 : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      ((fun p : ℝ × M ↦ (p.1 + t, p.2)) (0, y)) := by
    simpa only [zero_add] using hb
  have h0 := hasDerivAt_mpullbackBilin_family_flowOf_zero hZ (b := fun r ↦ b (r + t)) (b' := b') y
    (hb0.comp (0, y) hshift) ((zero_add t ▸ hb').comp_add_const 0 t)
  rw [zero_add] at h0
  have h0_sub : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun s ↦ mpullbackBilin I I (flowOf Z (s - t)) (b s) y)
      ((b' + mlieDerivBilin I Z (b t)) y) t :=
    (HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])).congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ congrArg
        (fun r ↦ (mpullbackBilin I I (flowOf Z (s - t)) (b r) y : E →L[ℝ] E →L[ℝ] G))
        (sub_add_cancel s t).symm)
  refine hasDerivAt_mpullbackBilin_of_eq_comp (ψ := flowOf Z) (χ := fun s ↦ flowOf Z (s - t))
    ?_ (hφ.mdifferentiableAt two_ne_zero) ?_ h0_sub
  · filter_upwards [hsub.eventually hev.curry] with s hs
    refine hs.mono fun z hz ↦ ?_
    have h := (flowOf_add hZ1 hz.1 hz.2).2
    rw [add_sub_cancel] at h
    exact h.symm
  · filter_upwards [hsub.eventually hev.curry] with s hs
    exact (contMDiffAt_flowOf_comp (n := 2) one_le_two hZ contMDiffAt_const contMDiffAt_id
      hs.self_of_nhds.2).mdifferentiableAt two_ne_zero

/-- **Lie derivatives of covariant two-tensors along maximal flows.** Wherever
`(t, x) ∈ flowDomain Z` and `b` is differentiable at `flowOf Z t x`,
`d/ds|_{s = t} ((flowOf Z s)^* b)_x = ((flowOf Z t)^* (L_Z b))_x`. -/
theorem hasDerivAt_mpullbackBilin_flowOf
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (flowOf Z t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) b x)
      (mpullbackBilin I I (flowOf Z t) (mlieDerivBilin I Z b) x) t := by
  have h := hasDerivAt_mpullbackBilin_family_flowOf hZ (b := fun _ ↦ b) (b' := 0) hx
    (hb.comp (t, flowOf Z t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (flowOf Z t x)))
  simpa only [zero_add] using h

/-- **Maximal flows preserve covariant two-tensors with vanishing Lie derivative.** If `b` is
differentiable and `mlieDerivBilin I Z b = 0`, then `mpullbackBilin I I (flowOf Z t) b x = b x`
wherever `(t, x) ∈ flowDomain Z`. No completeness of `Z` is required. -/
theorem mpullbackBilin_flowOf_apply_eq_of_mlieDerivBilin_eq_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)))
    (hL : mlieDerivBilin I Z b = 0) {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z) :
    mpullbackBilin I I (flowOf Z t) b x = b x := by
  have hZ1 := hZ.of_le one_le_two
  set J : Set ℝ := {s | (s, x) ∈ flowDomain Z}
  have hJopen : IsOpen J :=
    (isOpen_flowDomain hZ1).preimage (continuous_id.prodMk continuous_const)
  have hJc : J.OrdConnected := by
    rw [show J = maximalIntegralCurveInterval Z x from Set.ext fun _ ↦ mem_flowDomain]
    exact ordConnected_maximalIntegralCurveInterval
  have hJ0 : (0 : ℝ) ∈ J := mem_flowDomain_zero hZ1 x
  set P : ℝ → (E →L[ℝ] E →L[ℝ] G) := fun s ↦ mpullbackBilin I I (flowOf Z s) b x
  have hP (s : ℝ) (hs : s ∈ J) : HasDerivAt P 0 s := by
    have h := hasDerivAt_mpullbackBilin_flowOf hZ hs (hb _)
    rwa [hL, mpullbackBilin_zero] at h
  have hP0 : P 0 = b x := by
    change mpullbackBilin I I (flowOf Z 0) b x = b x
    rw [show flowOf Z 0 = id from funext (flowOf_zero Z), mpullbackBilin_id]
  refine (hJc.convex.is_const_of_fderivWithin_eq_zero
    (fun s hs ↦ (hP s hs).differentiableAt.differentiableWithinAt) (fun s hs ↦ ?_) hx hJ0).trans hP0
  have h0 : ContinuousLinearMap.toSpanSingleton ℝ (0 : E →L[ℝ] E →L[ℝ] G) = 0 := by ext; simp
  have hf := (hP s hs).hasFDerivAt.hasFDerivWithinAt (s := J)
  rw [h0] at hf
  exact hf.fderivWithin (hJopen.uniqueDiffWithinAt hs)

end MaximalFlow

/-! ### Time-dependent flows -/

section TimeDependentFlow

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {X : ℝ → (x : M) → TangentSpace I x}

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hc hX

omit hc in
/-- **Pullback variation at the base time along a time-dependent flow.** For a jointly `C²`
time-dependent vector field `X` and a family `b_u` jointly differentiable at `(t, y)` with
parameter derivative `b' y` there,
`d/du|_{u = t} ((timeDependentFlowOf X t u)^* b_u)_y = (b' + L_{X_t} b_t)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (t : ℝ) (y : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X t u) (b u) y)
      ((b' + mlieDerivBilin I (X t) (b t)) y) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hflow : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I 2
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ((t, t), y) :=
    (contMDiffOn_timeDependentFlowOf (n := 2) one_le_two hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain hX₁).mem_nhds (mem_timeDependentFlowDomain_self hX₁ t y))
  exact hasDerivAt_mpullbackBilin_family_of_eq_id (ψ := timeDependentFlowOf X t) (V := X t) y
    (Eventually.of_forall (timeDependentFlowOf_self X t))
    (hflow.comp (t, y) (((contMDiff_const (c := t)).prodMk contMDiff_fst).prodMk
      contMDiff_snd).contMDiffAt)
    (Eventually.of_forall fun x ↦
      hasMFDerivAt_timeDependentFlowOf hX₁ (mem_timeDependentFlowDomain_self hX₁ t x)) hb hb'

/-- **Time-dependent pullback variation along a complete time-dependent flow.** For a jointly `C²`
time-dependent vector field `X` with complete suspension and a family `b_u` jointly differentiable
at `(t, timeDependentFlowOf X s t x)` with parameter derivative `b' (timeDependentFlowOf X s t x)`,
`d/du|_{u = t} ((timeDependentFlowOf X s u)^* b_u)_x` equals
`((timeDependentFlowOf X s t)^* (b' + L_{X_t} b_t))_x`. -/
theorem hasDerivAt_mpullbackBilin_family_timeDependentFlowOf
    {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (s t : ℝ) (x : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, timeDependentFlowOf X s t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (timeDependentFlowOf X s t x))
      (b' (timeDependentFlowOf X s t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X s u) (b u) x)
      (mpullbackBilin I I (timeDependentFlowOf X s t) (b' + mlieDerivBilin I (X t) (b t)) x) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hsmooth (a c : ℝ) : MDifferentiable I I (timeDependentFlowOf X a c) :=
    ((contMDiff_timeDependentFlowOf hc (n := 2) one_le_two hX).comp
      ((contMDiff_const (c := (a, c))).prodMk contMDiff_id)).mdifferentiable two_ne_zero
  exact hasDerivAt_mpullbackBilin_of_eq_comp (χ := timeDependentFlowOf X t)
    (Eventually.of_forall fun u ↦ Eventually.of_forall fun z ↦
      (timeDependentFlowOf_trans hc hX₁ s t u z).symm)
    (hsmooth s t x) (Eventually.of_forall fun u ↦ hsmooth t u _)
    (hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self hX t _ hb hb')

/-- Stationary pullback variation along a complete time-dependent flow:
`d/du|_{u = t} ((timeDependentFlowOf X s u)^* b)_x = ((timeDependentFlowOf X s t)^* (L_{X_t} b))_x`.
-/
theorem hasDerivAt_mpullbackBilin_timeDependentFlowOf
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (s t : ℝ) (x : M)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X s u) b x)
      (mpullbackBilin I I (timeDependentFlowOf X s t) (mlieDerivBilin I (X t) b) x) t := by
  have h := hasDerivAt_mpullbackBilin_family_timeDependentFlowOf hc hX (b := fun _ ↦ b) (b' := 0)
    s t x (hb.comp (t, timeDependentFlowOf X s t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (timeDependentFlowOf X s t x)))
  simpa only [zero_add] using h

/-- **Invariance of covariant two-tensors under time-dependent flows.** For a jointly `C²`
time-dependent vector field `X` with complete suspension, its flow preserves a differentiable
covariant two-tensor `b` (`(timeDependentFlowOf X s t)^* b = b` for all `s, t`) if and only if
`mlieDerivBilin I (X t) b = 0` for every time `t`. -/
theorem mpullbackBilin_timeDependentFlowOf_eq_self_iff
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z))) :
    (∀ s t, mpullbackBilin I I (timeDependentFlowOf X s t) b = b) ↔
      ∀ t, mlieDerivBilin I (X t) b = 0 := by
  have hid (s : ℝ) : mpullbackBilin I I (timeDependentFlowOf X s s) b = b := by
    have h : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
    rw [h, mpullbackBilin_id]
  constructor
  · intro h t
    funext y
    have hd := hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self hX (b := fun _ ↦ b)
      (b' := 0) t y ((hb y).comp (t, y) mdifferentiableAt_snd)
      (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))
    rw [zero_add] at hd
    have hconst : (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X t u) b y) = fun _ ↦ b y :=
      funext fun u ↦ congrFun (h t u) y
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))
  · intro h s t
    rw [mpullbackBilin_family_eq_of_forall_eq_zero (b := fun _ ↦ b)
      (fun u x ↦ hasDerivAt_mpullbackBilin_timeDependentFlowOf hc hX s u x (hb _)) h t s, hid s]

end TimeDependentFlow

end TauCeti
