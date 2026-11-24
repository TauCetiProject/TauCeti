/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.LieDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Pullback variation of covariant two-tensors along isotopies and flows

For a time-dependent covariant two-tensor `b_t` on a boundaryless `C²` manifold `M` with parameter
derivative `b'` at time `t`, pulling back along a smooth family `φ_t` satisfies

`d/du|_{u = t} (φ_u^* b_u)_x = (φ_t^* (b' + L_{X_t} b_t))_x`,

identifying `TauCeti.mlieDerivBilin` with `d/dt|₀ (φ_t^* b)` for stationary `b`.

The tensor-independent flow reductions are obtained by instantiating `TauCeti.PullbackAction`
(`TauCeti.PullbackAction.bilinear`). For general families of maps,
`TauCeti.mpullbackBilin_family_eq_of_forall_eq_zero` deduces time constancy from a supplied
zero-derivative hypothesis. Along smooth isotopies (`TauCeti.eulerianField`), time constancy of
`φ_t^* b_t` holds whenever `b'_t + L_{X_t} b_t = 0`
(`TauCeti.mpullbackBilin_family_eulerianField_eq_of_add_mlieDerivBilin_eq_zero`). Along autonomous
maximal flows (`TauCeti.flowOf`) and complete time-dependent flows
(`TauCeti.timeDependentFlowOf`), we prove the time-dependent variation formulas together with
invariance of a stationary `b` whose Lie derivative vanishes.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed. (2013), Proposition 12.36 and Chapter 22.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapters 1 and 3.
* P. Topping, *Lectures on the Ricci Flow*, CUP (2006), Proposition 1.2.2 and Appendix A.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

/-- The `PullbackAction` instance for covariant two-tensors, acting by `TauCeti.mpullbackBilin`
with fibre operator `ContinuousLinearMap.pullbackBilinL`. -/
@[expose] def PullbackAction.bilinear {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M G : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup G] [NormedSpace ℝ G] :
    PullbackAction I M (E →L[ℝ] E →L[ℝ] G)
      ((x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G) where
  pull := mpullbackBilin I I
  eval b x := b x
  fibrePull := ContinuousLinearMap.pullbackBilinL (V := E) (W := E) (G := G)
  eval_pull := mpullbackBilin_apply_eq_pullbackBilinL
  fibrePull_id := by ext b v w; simp [ContinuousLinearMap.pullbackBilinL_apply]
  fibrePull_comp A B := by ext b v w; simp [ContinuousLinearMap.pullbackBilinL_apply]
  eval_zero _ := rfl
  ext := funext

section Family

variable {E H M E' H' M' G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Near `t`, the pullback `(ψ_u^* b_u)_y` agrees with the flat `pullbackBilinL` of the chart
representation of `b_u` along the spatial Fréchet derivative of `ψ_u` in charts. -/
theorem eventuallyEq_mpullbackBilin_pullbackBilinL [IsManifold I 1 M] [I.Boundaryless]
    [IsManifold I' 1 M']
    (b : ℝ → (y : M') → TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] G)
    {ψ : ℝ → M → M'} {t : ℝ} {y : M} (c : M') (hψt : ψ t y ∈ (extChartAt I' c).source)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I' 1 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y)) :
    (fun u ↦ (mpullbackBilin I I' (ψ u) (b u) y : E →L[ℝ] E →L[ℝ] G)) =ᶠ[𝓝 t] fun u ↦
      ContinuousLinearMap.pullbackBilinL
        (fderiv ℝ (fun z ↦ extChartAt I' c (ψ u ((extChartAt I y).symm z))) (extChartAt I y y))
        (inChartAtBilin I' c (b u)
          (extChartAt I' c (ψ u ((extChartAt I y).symm (extChartAt I y y))))) := by
  have hψ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I' (ψ u) y := by
    filter_upwards [((continuous_id.prodMk continuous_const).tendsto t).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hsmooth)] with u hu
    exact (hu.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_id) rfl).mdifferentiableAt
      (by norm_num)
  have hsrc : ∀ᶠ u in 𝓝 t, ψ u y ∈ (extChartAt I' c).source :=
    (hsmooth.continuousAt.comp (f := fun u : ℝ ↦ (u, y))
      (continuous_id.prodMk continuous_const).continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_source c).mem_nhds hψt)
  filter_upwards [hsrc, hψ] with u hu hψu
  rw [extChartAt_to_inv, mpullbackBilin_eq_pullbackBilinL (b u) c hψu hu,
    I.range_eq_univ, fderivWithin_univ]
  -- `extChartAt I' c ∘ ψ u ∘ (extChartAt I y).symm` agrees definitionally with the lambda.
  rfl

variable {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
  {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
  {ψ χ : ℝ → M → M} {V : (x : M) → TangentSpace I x} {t : ℝ} {x y : M}

/-- Joint differentiability of a time-dependent covariant two-tensor `b` at `(t, y)` implies joint
Fréchet differentiability of its chart representation `(u, z) ↦ inChartAtBilin I y (b u) z` at
`(t, extChartAt I y y)`. -/
theorem differentiableAt_uncurry_inChartAtBilin [IsManifold I 1 M] [I.Boundaryless]
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
  rw [mdifferentiableAt_totalSpace] at hb
  have hcomp := hb.2.comp_of_eq (t, extChartAt I y y)
    (mdifferentiableAt_fst.prodMk (hsymm.comp (t, extChartAt I y y) mdifferentiableAt_snd))
    (Prod.ext rfl (extChartAt_to_inv y))
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
    mdifferentiableAt_iff_differentiableAt] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.eventually (extChartAt_target_mem_nhds y)] with p hp
  exact inChartAtBilin_eq_trivializationAt y (b p.1) hp

/-- Common chart step for `hasDerivAt_mpullbackBilin_family_of_eq_id` and its `C¹` counterpart. -/
private theorem hasDerivAt_mpullbackBilin_family_of_eq_id_of_hasDerivAt_fderiv
    [IsManifold I 1 M] [I.Boundaryless] (y : M) (hid : ∀ᶠ x in 𝓝 y, ψ t x = x)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y))
    (hvel : HasDerivAt
      (fun u ↦ extChartAt I y (ψ u ((extChartAt I y).symm (extChartAt I y y))))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I)
        (extChartAt I y y)) t)
    (hspatial : HasDerivAt
      (fun u ↦ fderiv ℝ (fun z ↦ extChartAt I y (ψ u ((extChartAt I y).symm z)))
        (extChartAt I y y))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I))
        (extChartAt I y y)) t)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) y)
      ((b' + mlieDerivBilin I V (b t)) y) t := by
  set Φ : ℝ × E → E := fun p ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))
  set W : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I)
  have hΦt_nhds : (fun z ↦ Φ (t, z)) =ᶠ[𝓝 (extChartAt I y y)] id :=
    Manifold.eventuallyEq_extChartAt_family_of_eq_id hid
  have hΦt : Φ (t, extChartAt I y y) = extChartAt I y y := hΦt_nhds.self_of_nhds
  have hflat := hasDerivAt_pullbackBilinL_fderiv (b := fun u ↦ inChartAtBilin I y (b u))
    (b' := b' y) (ψ := fun u z ↦ Φ (u, z)) (V := W) (x := extChartAt I y y) (t := t)
    (by rw [hΦt]; exact differentiableAt_uncurry_inChartAtBilin hb)
    (by rw [hΦt]; exact hb'.congr_of_eventuallyEq
          (Eventually.of_forall fun u ↦ inChartAtBilin_extChartAt_self y (b u)))
    (by rw [hΦt]; exact hvel)
    (by rw [hΦt, hΦt_nhds.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id]; exact hspatial)
  refine (hflat.congr_of_eventuallyEq
    (eventuallyEq_mpullbackBilin_pullbackBilinL b y
      (by rw [hid.self_of_nhds]; exact mem_extChartAt_source y) hsmooth)).congr_deriv ?_
  rw [hΦt, hΦt_nhds.fderiv_eq, fderiv_id]
  have hlie : (mlieDerivBilin I V (b t) y : E →L[ℝ] E →L[ℝ] G) =
      lieDerivBilin (E := E) W (inChartAtBilin I y (b t)) (extChartAt I y y) := by
    rw [mlieDerivBilin_def, ← lieDerivBilinWithin_univ, I.range_eq_univ]
    exact congrArg (fun s ↦ lieDerivBilinWithin (E := E)
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V s)
      (inChartAtBilin I y (b t)) univ (extChartAt I y y)) I.range_eq_univ.symm
  ext v w
  simp only [ContinuousLinearMap.pullbackBilinL_apply, ContinuousLinearMap.id_apply, Pi.add_apply]
  exact congrArg (b' y v w + ·) (DFunLike.congr_fun (DFunLike.congr_fun hlie.symm v) w)

/-- **Pullback variation at the identity:** along a jointly `C²` family `ψ` with `ψ t = id` near
`y` and velocity `V`, `d/du|_{u = t} (ψ_u^* b_u)_y = (b' + L_V b_t)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_of_eq_id [IsManifold I 2 M] [I.Boundaryless] (y : M)
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
  exact hasDerivAt_mpullbackBilin_family_of_eq_id_of_hasDerivAt_fderiv y hid
    (hsmooth.of_le one_le_two) (eventually_hasDerivAt_extChartAt_family hid hvel).self_of_nhds
    (hasDerivAt_fderiv_extChartAt_family_of_eq_id y hid
      (by simpa only [minSmoothness_of_isRCLikeNormedField] using hsmooth) hvel) hb hb'

/-- **Pullback variation at the identity for a `C¹` family:** along a jointly `C¹` family `ψ` with
`ψ t = id` near `y` moving near `(t, y)` with the velocity of a `C¹` field `V`,
`d/du|_{u = t} (ψ_u^* b_u)_y = (b' + L_V b_t)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_of_eq_id_of_eventually_nhds_prod
    [CompleteSpace E] [IsManifold I 2 M] [I.Boundaryless] (y : M) (hid : ∀ᶠ x in 𝓝 y, ψ t x = x)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y))
    (hV : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)) y)
    (hvel : ∀ᶠ p in 𝓝 (t, y),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u p.2) p.1 ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ p.1 p.2))))
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) y)
      ((b' + mlieDerivBilin I V (b t)) y) t := by
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  set G : ℝ × E → E := fun p ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))
  have hGt : G (t, extChartAt I y y) = extChartAt I y y :=
    (Manifold.eventuallyEq_extChartAt_family_of_eq_id hid).self_of_nhds
  have h : HasDerivAt (fun u ↦ G (u, extChartAt I y y))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I)
        (G (t, extChartAt I y y))) t :=
    (eventually_hasDerivAt_extChartAt_family_of_eventually_nhds_prod hid.self_of_nhds
      hsmooth.continuousAt hvel).self_of_nhds
  rw [hGt] at h
  exact hasDerivAt_mpullbackBilin_family_of_eq_id_of_hasDerivAt_fderiv y hid hsmooth h
    (hasDerivAt_fderiv_extChartAt_family_of_eq_id_of_eventually_nhds_prod y hid hsmooth hV hvel)
    hb hb'

/-- **Stationary pullback variation at the identity:** along a jointly `C²` family `ψ` with
`ψ t = id` near `y` and velocity `V`, `d/du|_{u = t} (ψ_u^* b)_y = (L_V b)_y`. -/
theorem hasDerivAt_mpullbackBilin_of_eq_id [IsManifold I 2 M] [I.Boundaryless]
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (y : M)
    (hid : ∀ᶠ x in 𝓝 y, ψ t x = x)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y))
    (hvel : ∀ᶠ x in 𝓝 y,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ t x))))
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) y) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) b y)
      (mlieDerivBilin I V b y) t := by
  simpa only [zero_add] using hasDerivAt_mpullbackBilin_family_of_eq_id (b := fun _ ↦ b) (b' := 0)
    y hid hsmooth hvel (hb.comp (t, y) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))

/-- **Moving the base point of pulled-back covariant two-tensors** along `ψ_u =ᶠ χ_u ∘ g`. -/
theorem hasDerivAt_mpullbackBilin_of_eq_comp {g : M → M}
    {β : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hψ : ∀ᶠ u in 𝓝 t, ψ u =ᶠ[𝓝 x] χ u ∘ g) (hg : MDifferentiableAt I I g x)
    (hχ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (χ u) (g x))
    (h : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (χ u) (b u) (g x))
      (β (g x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) x)
      (mpullbackBilin I I g β x) t :=
  (PullbackAction.bilinear I M G).hasDerivAt_of_eq_comp hψ hg hχ h

/-- **Constancy from vanishing pullback velocity:** if `(ψ_u^* b_u)_x` has derivative
`(ψ_u^* β_u)_x` everywhere and `β_u = 0` for all `u`, then `ψ_s^* b_s = ψ_t^* b_t`. -/
theorem mpullbackBilin_family_eq_of_forall_eq_zero
    {β : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hd : ∀ u x, HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (ψ u) (b u) x)
      (mpullbackBilin I I (ψ u) (β u) x) u)
    (hβ : ∀ u, β u = 0) (s t : ℝ) :
    mpullbackBilin I I (ψ s) (b s) = mpullbackBilin I I (ψ t) (b t) :=
  (PullbackAction.bilinear I M G).pull_eq_of_forall_eq_zero hd hβ s t

end Family

section Flows

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

section Isotopy

variable {φ : ℝ → M ≃ M}
  (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ φ p.1 p.2))
  (hφ' : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ (φ p.1).symm p.2))
include hφ hφ'

variable {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
  {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}

/-- **Time-dependent pullback variation at the base time of a smooth isotopy:**
`d/du|_{u = t} ((φ_u ∘ φ_t⁻¹)^* b_u)_y = (b' + L_{X_t} b_t)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_eulerianField_self (t : ℝ) (y : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (fun x ↦ φ u ((φ t).symm x)) (b u) y)
      ((b' + mlieDerivBilin I (eulerianField I φ t) (b t)) y) t :=
  (PullbackAction.bilinear I M G).hasDerivAt_eulerianField_self hφ hφ' t y
    (fun hid hsmooth hvel ↦ hasDerivAt_mpullbackBilin_family_of_eq_id y hid hsmooth hvel hb hb')

/-- **Time-dependent pullback variation along a smooth isotopy:**
`d/du|_{u = t} (φ_u^* b_u)_x = (φ_t^* (b' + L_{X_t} b_t))_x`. -/
theorem hasDerivAt_mpullbackBilin_family_eulerianField (t : ℝ) (x : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, φ t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (φ t x)) (b' (φ t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (φ u) (b u) x)
      (mpullbackBilin I I (φ t) (b' + mlieDerivBilin I (eulerianField I φ t) (b t)) x) t :=
  (PullbackAction.bilinear I M G).hasDerivAt_eulerianField hφ hφ' t x
    (hasDerivAt_mpullbackBilin_family_eulerianField_self hφ hφ' t (φ t x) hb hb')

/-- **Stationary pullback variation along a smooth isotopy:**
`d/du|_{u = t} (φ_u^* b)_x = (φ_t^* L_{X_t} b)_x` for a smooth isotopy `φ`. -/
theorem hasDerivAt_mpullbackBilin_eulerianField
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (t : ℝ) (x : M)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (φ t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ mpullbackBilin I I (φ u) b x)
      (mpullbackBilin I I (φ t) (mlieDerivBilin I (eulerianField I φ t) b) x) t := by
  simpa only [zero_add] using hasDerivAt_mpullbackBilin_family_eulerianField hφ hφ' (b := fun _ ↦ b)
    (b' := 0) t x (hb.comp (t, φ t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (φ t x)))

/-- **Time constancy along a smooth isotopy:** if a jointly differentiable family `b_t` has time
derivative `b'_t` satisfying `b'_t + L_{X_t} b_t = 0` for the Eulerian field `X_t` of `φ`, then
`φ_s^* b_s = φ_t^* b_t` for all `s, t : ℝ`. -/
theorem mpullbackBilin_family_eulerianField_eq_of_add_mlieDerivBilin_eq_zero
    {b b' : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2)))
    (hb' : ∀ t y, HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' t y) t)
    (hL : ∀ t, b' t + mlieDerivBilin I (eulerianField I φ t) (b t) = 0) (s t : ℝ) :
    mpullbackBilin I I (φ s) (b s) = mpullbackBilin I I (φ t) (b t) :=
  mpullbackBilin_family_eq_of_forall_eq_zero
    (fun u x ↦ hasDerivAt_mpullbackBilin_family_eulerianField hφ hφ' u x (hb (u, φ u x))
      (hb' u (φ u x))) hL s t

/-- **Invariance of covariant two-tensors under isotopies:** `φ_t^* b` is independent of `t` if and
only if `L_{X_t} b = 0` for all `t`. -/
theorem forall_mpullbackBilin_eq_iff_forall_mlieDerivBilin_eulerianField_eq_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z))) :
    (∀ s t, mpullbackBilin I I (φ s) b = mpullbackBilin I I (φ t) b) ↔
      ∀ t, mlieDerivBilin I (eulerianField I φ t) b = 0 :=
  (PullbackAction.bilinear I M G).forall_pull_eulerianField_eq_iff hφ hφ'
    (L := fun V ↦ mlieDerivBilin I V b) fun t y ↦ by
      have hd := hasDerivAt_mpullbackBilin_family_eulerianField_self hφ hφ'
        (b := fun _ ↦ b) (b' := 0) t y ((hb y).comp (t, y) mdifferentiableAt_snd)
        (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))
      rw [zero_add] at hd
      exact hd

end Isotopy

variable [FiniteDimensional ℝ E] [T2Space M]

section MaximalFlow

/-- The flow lemmas are applied at smoothness `1`, read in `ℕ∞`. -/
local instance : IsManifold I ((1 : ℕ∞) : WithTop ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)

variable {Z : (x : M) → TangentSpace I x}
  (hZ : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hZ

variable {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
  {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}

/-- **Time-dependent pullback variation at time zero along a maximal flow:**
`d/ds|_{s = 0} ((flowOf Z s)^* b_s)_y = (b' + L_Z b_0)_y`. -/
theorem hasDerivAt_mpullbackBilin_family_flowOf_zero (y : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (0, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ b s y) (b' y) 0) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) (b s) y)
      ((b' + mlieDerivBilin I Z (b 0)) y) 0 :=
  (PullbackAction.bilinear I M G).hasDerivAt_flowOf_zero hZ y
    (fun hid hsmooth hZy hvel ↦
      hasDerivAt_mpullbackBilin_family_of_eq_id_of_eventually_nhds_prod y hid hsmooth hZy hvel hb
        hb')

/-- **Flow characterization of the Lie derivative at time zero:**
`d/ds|_{s = 0} ((flowOf Z s)^* b)_y = (L_Z b)_y`. -/
theorem hasDerivAt_mpullbackBilin_flowOf_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (y : M)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) y) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) b y)
      (mlieDerivBilin I Z b y) 0 := by
  simpa only [zero_add] using hasDerivAt_mpullbackBilin_family_flowOf_zero hZ (b := fun _ ↦ b)
    (b' := 0) y (hb.comp (0, y) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) 0 (b y))

/-- **Time-dependent pullback variation along a maximal flow:** wherever `(t, x) ∈ flowDomain Z`,
`d/ds|_{s = t} ((flowOf Z s)^* b_s)_x = ((flowOf Z t)^* (b' + L_Z b_t))_x`. -/
theorem hasDerivAt_mpullbackBilin_family_flowOf {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, flowOf Z t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (flowOf Z t x))
      (b' (flowOf Z t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) (b s) x)
      (mpullbackBilin I I (flowOf Z t) (b' + mlieDerivBilin I Z (b t)) x) t := by
  set y := flowOf Z t x
  have hshift : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (fun p : ℝ × M ↦ (p.1 + t, p.2)) (0, y) :=
    ((mdifferentiableAt_iff_differentiableAt.2 (differentiableAt_id.add_const t)).comp
      (0, y) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd
  have h0 := hasDerivAt_mpullbackBilin_family_flowOf_zero hZ (b := fun r ↦ b (r + t)) (b' := b')
    y (hb.comp_of_eq (0, y) hshift (Prod.ext (zero_add t) rfl))
    ((zero_add t ▸ hb').comp_add_const 0 t)
  rw [zero_add] at h0
  exact (PullbackAction.bilinear I M G).hasDerivAt_flowOf hZ hx h0

/-- **Stationary pullback variation along a maximal flow:** wherever `(t, x) ∈ flowDomain Z`,
`d/ds|_{s = t} ((flowOf Z s)^* b)_x = ((flowOf Z t)^* L_Z b)_x`. -/
theorem hasDerivAt_mpullbackBilin_flowOf
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (flowOf Z t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun s ↦ mpullbackBilin I I (flowOf Z s) b x)
      (mpullbackBilin I I (flowOf Z t) (mlieDerivBilin I Z b) x) t := by
  simpa only [zero_add] using hasDerivAt_mpullbackBilin_family_flowOf hZ (b := fun _ ↦ b) (b' := 0)
    hx (hb.comp (t, flowOf Z t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (flowOf Z t x)))

/-- **Maximal flows preserve stationary covariant two-tensors with vanishing Lie derivative:** if
`L_Z b = 0`, then `((flowOf Z t)^* b)_x = b_x` wherever `(t, x) ∈ flowDomain Z`. -/
theorem mpullbackBilin_flowOf_apply_eq_of_mlieDerivBilin_eq_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)))
    (hL : mlieDerivBilin I Z b = 0) {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z) :
    mpullbackBilin I I (flowOf Z t) b x = b x :=
  (PullbackAction.bilinear I M G).eval_pull_flowOf_eq_of_eq_zero hZ
    (fun _ hr ↦ hasDerivAt_mpullbackBilin_flowOf hZ hr (hb _)) hL hx

end MaximalFlow

section TimeDependentFlow

variable {X : ℝ → (x : M) → TangentSpace I x}
  (hc : IsCompleteVectorField (timeDependentSuspensionField X))
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

variable {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
  {b' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}

/-- **Time-dependent pullback variation at the base time of a time-dependent flow:**
`d/du|_{u = t} ((timeDependentFlowOf X t u)^* b_u)_y = (b' + L_{X_t} b_t)_y`. Completeness is not
required. -/
theorem hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self (t : ℝ) (y : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, y))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u y) (b' y) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X t u) (b u) y)
      ((b' + mlieDerivBilin I (X t) (b t)) y) t :=
  (PullbackAction.bilinear I M G).hasDerivAt_timeDependentFlowOf_self hX t y
    (fun hid hsmooth hvel ↦ hasDerivAt_mpullbackBilin_family_of_eq_id y hid hsmooth hvel hb hb')

/-- **Time-dependent pullback variation along a maximal time-dependent flow:** wherever
`((s, t), x) ∈ timeDependentFlowDomain X`,
`d/du|_{u = t} (φ_{s,u}^* b_u)_x = (φ_{s,t}^* (b' + L_{X_t} b_t))_x`. -/
theorem hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_of_mem {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, timeDependentFlowOf X s t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (timeDependentFlowOf X s t x))
      (b' (timeDependentFlowOf X s t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X s u) (b u) x)
      (mpullbackBilin I I (timeDependentFlowOf X s t) (b' + mlieDerivBilin I (X t) (b t)) x) t :=
  (PullbackAction.bilinear I M G).hasDerivAt_timeDependentFlowOf_of_mem hX h
    (hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self hX t _ hb hb')

/-- **Stationary pullback variation along a maximal time-dependent flow:** wherever
`((s, t), x) ∈ timeDependentFlowDomain X`,
`d/du|_{u = t} (φ_{s,u}^* b)_x = (φ_{s,t}^* L_{X_t} b)_x`. -/
theorem hasDerivAt_mpullbackBilin_timeDependentFlowOf_of_mem
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X s u) b x)
      (mpullbackBilin I I (timeDependentFlowOf X s t) (mlieDerivBilin I (X t) b) x) t := by
  simpa only [zero_add] using hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_of_mem hX
    (b := fun _ ↦ b) (b' := 0) h
    (hb.comp (t, timeDependentFlowOf X s t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (timeDependentFlowOf X s t x)))

include hc

/-- **Time-dependent pullback variation along a complete time-dependent flow:**
`d/du|_{u = t} (φ_{s,u}^* b_u)_x = (φ_{s,t}^* (b' + L_{X_t} b_t))_x`, where
`φ = timeDependentFlowOf X`. -/
theorem hasDerivAt_mpullbackBilin_family_timeDependentFlowOf (s t : ℝ) (x : M)
    (hb : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] G) q.2 (b q.1 q.2))
      (t, timeDependentFlowOf X s t x))
    (hb' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] G) (fun u ↦ b u (timeDependentFlowOf X s t x))
      (b' (timeDependentFlowOf X s t x)) t) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X s u) (b u) x)
      (mpullbackBilin I I (timeDependentFlowOf X s t) (b' + mlieDerivBilin I (X t) (b t)) x) t :=
  (PullbackAction.bilinear I M G).hasDerivAt_timeDependentFlowOf hc hX s t x
    (hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self hX t _ hb hb')

/-- **Stationary pullback variation along a complete time-dependent flow:**
`d/du|_{u = t} (φ_{s,u}^* b)_x = (φ_{s,t}^* L_{X_t} b)_x`, where `φ = timeDependentFlowOf X`. -/
theorem hasDerivAt_mpullbackBilin_timeDependentFlowOf
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G} (s t : ℝ) (x : M)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z)) (timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E →L[ℝ] E →L[ℝ] G)
      (fun u ↦ mpullbackBilin I I (timeDependentFlowOf X s u) b x)
      (mpullbackBilin I I (timeDependentFlowOf X s t) (mlieDerivBilin I (X t) b) x) t := by
  simpa only [zero_add] using hasDerivAt_mpullbackBilin_family_timeDependentFlowOf hc hX
    (b := fun _ ↦ b) (b' := 0) s t x
    (hb.comp (t, timeDependentFlowOf X s t x) mdifferentiableAt_snd)
    (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b (timeDependentFlowOf X s t x)))

/-- **Invariance of stationary covariant two-tensors under complete time-dependent flows:**
`(timeDependentFlowOf X s t)^* b = b` for all `s, t` if and only if `L_{X_t} b = 0` for all `t`. -/
theorem forall_mpullbackBilin_timeDependentFlowOf_eq_self_iff_forall_mlieDerivBilin_eq_zero
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] G}
    (hb : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] G))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] G) z (b z))) :
    (∀ s t, mpullbackBilin I I (timeDependentFlowOf X s t) b = b) ↔
      ∀ t, mlieDerivBilin I (X t) b = 0 :=
  (PullbackAction.bilinear I M G).forall_pull_timeDependentFlowOf_eq_self_iff hc hX
    (L := fun V ↦ mlieDerivBilin I V b) fun t y ↦ by
      have hd := hasDerivAt_mpullbackBilin_family_timeDependentFlowOf_self hX
        (b := fun _ ↦ b) (b' := 0) t y ((hb y).comp (t, y) mdifferentiableAt_snd)
        (hasDerivAt_const (F := E →L[ℝ] E →L[ℝ] G) t (b y))
      rw [zero_add] at hd
      exact hd

end TimeDependentFlow

end Flows

end TauCeti
