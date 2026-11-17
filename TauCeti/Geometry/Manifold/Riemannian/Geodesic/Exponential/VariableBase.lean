/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Topology.IsLocalHomeomorph
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# The exponential map with a variable base point

Consider the exponential map with a variable base point, `(x, v) ↦ (x, exp_x v)`, from the
tangent bundle `TM` to `M × M`. It is smooth on the open set of tangent vectors in the natural
domain of the exponential map. At the zero vector `0_p` of `T_p M`, the tangent space of `TM`
splits as `T_p M × T_p M` (the horizontal and vertical summands of
`TauCeti.Bundle.zeroSectionTangentEquiv`), and in this splitting the differential of the map is
`(u, v) ↦ (u, u + v)`: the zero section goes to the diagonal, and the fibre over `p` is sent
through `exp_p`, whose differential at the origin is the identity. This differential is
invertible, so by the inverse function theorem the map is a local diffeomorphism at `0_p`.
At a vector `v` in the domain of `exp_q`, the map is a local diffeomorphism at `⟨q, v⟩` exactly
when its restriction `exp_q` to the fibre over `q` is one at `v`. Hence on a tube of tangent balls
of radius `r` over a set `W` of points `q` at which `exp_q` is an injective local diffeomorphism on
the ball, the map is an injective local diffeomorphism, and for open `W` its image is open.

## Main results

* `TauCeti.Manifold.contMDiffAt_riemannianExp_tangentBundle` and
  `TauCeti.Manifold.contMDiffOn_prodMk_proj_riemannianExp`: `(x, v) ↦ exp_x v` and
  `(x, v) ↦ (x, exp_x v)` are smooth where the exponential map is defined.
* `TauCeti.Manifold.mfderiv_prodMk_proj_riemannianExp_zeroSection_apply`,
  `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_zeroSection_apply`: the differentials of
  `(x, v) ↦ (x, exp_x v)` and `(x, v) ↦ exp_x v` at a zero vector are `(u, v) ↦ (u, u + v)` and
  `(u, v) ↦ u + v`.
* `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_zeroSection_curveVelocity`,
  `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_curveVelocity_zero`, and
  `TauCeti.Manifold.variationField_riemannianExp_smul`: evaluating the differential of
  `(x, v) ↦ exp_x v` along ray-rescaled tangent-bundle curves `q ↦ ⟨(σ q).proj, t • (σ q).2⟩`
  (including at `t = 0` and along curves through a zero vector).
* `TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection`: the
  variable-base inverse function theorem, `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism at
  every zero vector.
* `TauCeti.Manifold.isLocalDiffeomorphAt_riemannianExp_of_prodMk`: where `(x, v) ↦ (x, exp_x v)`
  is a local diffeomorphism, so is `exp_q` on the fibre.
* `TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp`,
  `TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp_iff`: conversely, where `exp_q`
  is a local diffeomorphism, so is `(x, v) ↦ (x, exp_x v)`.
* `TauCeti.Manifold.isLocalDiffeomorphOn_prodMk_proj_riemannianExp`,
  `TauCeti.Manifold.injOn_prodMk_proj_riemannianExp`: on the tube of tangent vectors of norm less
  than `r` over a set `W` of points `q` at which `exp_q` is an injective local diffeomorphism on the
  tangent ball of radius `r`, so is `(x, v) ↦ (x, exp_x v)`.
* `TauCeti.Manifold.isOpen_setOf_mem_riemannianExp_image_ball`: for such an open `W`, the pairs
  `(x, y)` with `x ∈ W` and `y ∈ exp_x '' B(0, r)` form an open subset of `M × M`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Theorem 3.7 (totally normal
  neighbourhoods), whose proof applies the inverse function theorem to the same map.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6
  (uniformly normal neighbourhoods).
-/

public section

noncomputable section

open Bundle Manifold Set Function
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The bundle exponential map `(x, v) ↦ exp_x v` is smooth at every tangent vector in its natural
domain. -/
theorem contMDiffAt_riemannianExp_tangentBundle {z : TangentBundle I M}
    (hz : z.2 ∈ expDomain I M z.proj) :
    ContMDiffAt I.tangent I ∞
      (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2) z :=
  (contMDiffOn_riemannianExp_tangentBundle z hz).contMDiffAt
    (isOpen_setOfPred_mem_expDomain.mem_nhds hz)

/-- The map `(x, v) ↦ (x, exp_x v)` is smooth on the open subset of the tangent bundle where the
exponential map is naturally defined. -/
theorem contMDiffOn_prodMk_proj_riemannianExp :
    ContMDiffOn I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2))
      {z | z.2 ∈ expDomain I M z.proj} :=
  (Bundle.contMDiff_proj (TangentSpace I)).contMDiffOn.prodMk
    contMDiffOn_riemannianExp_tangentBundle

/-- **The differential of `(x, v) ↦ (x, exp_x v)` at a zero vector.** In the splitting of the
tangent space of `TM` at `0_p` into horizontal and vertical parts, it sends `(u, v)` to
`(u, u + v)`. -/
theorem mfderiv_prodMk_proj_riemannianExp_zeroSection_apply (p : M) (u v : TangentSpace I p) :
    mfderiv I.tangent (I.prod I)
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2))
      (zeroSection E (TangentSpace I) p)
      ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) p).symm (u, v)) = (u, u + v) := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  have hFd : MDifferentiableAt I.tangent (I.prod I) F (zeroSection E (TangentSpace I) p) :=
    ((contMDiffOn_prodMk_proj_riemannianExp _ (zero_mem_expDomain p)).contMDiffAt
      (isOpen_setOfPred_mem_expDomain.mem_nhds (zero_mem_expDomain p))).mdifferentiableAt
      (by simp)
  -- Split `(u, v)` into the differential of the zero section at `u` and the velocity of the
  -- fibre line `t ↦ t • v`, and compute the differential of `F` on each summand.
  rw [TauCeti.Bundle.zeroSectionTangentEquiv_symm_eq, map_add]
  have h1 : mfderiv I.tangent (I.prod I) F (zeroSection E (TangentSpace I) p)
      (mfderiv I I.tangent (zeroSection E (TangentSpace I)) p u) = (u, u) := by
    have h := mfderiv_comp_apply p hFd (mdifferentiableAt_zeroSection ℝ _) u
    have hfun : F ∘ zeroSection E (TangentSpace I) = fun x : M ↦ (id x, id x) := by
      funext x
      simp [F, zeroSection]
    rw [hfun, mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_id, mfderiv_id] at h
    exact h.symm.trans (ContinuousLinearMap.prod_apply _ _ u)
  have h2 : mfderiv I.tangent (I.prod I) F (zeroSection E (TangentSpace I) p)
      ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) p).symm (0, v)) = (0, v) := by
    rw [TauCeti.Bundle.zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → TangentBundle I M := fun t ↦ ⟨p, t • v⟩
    have hl : ContMDiff 𝓘(ℝ) I.tangent 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨p, v⟩ : TangentBundle I M)))
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) hFd (hl.mdifferentiableAt one_ne_zero)
      (by simp [line, zeroSection]) (1 : ℝ)
    have hexp := (contMDiffAt_riemannianExp_smul_zero p v).mdifferentiableAt (by simp)
    have hfun : F ∘ line = fun t ↦ (p, riemannianExp I M p (t • v)) := rfl
    rw [hfun, mfderiv_prodMk mdifferentiableAt_const hexp, mfderiv_const] at h
    have hv := curveVelocity_riemannianExp_smul_zero p v
    rw [← curveVelocityWithin_univ, curveVelocityWithin_apply, mfderivWithin_univ] at hv
    exact h.symm.trans ((ContinuousLinearMap.prod_apply _ _ 1).trans
      (Prod.ext (zero_apply 1) hv))
  rw [h1, h2]
  exact (Prod.mk_add_mk u 0 u v).trans (congrArg (·, u + v) (add_zero u))

/-- **The differential of `(x, v) ↦ exp_x v` at a zero vector.** In the horizontal and vertical
splitting `TauCeti.Bundle.zeroSectionTangentEquiv` of `T_{0_p}(TM)`, the differential sends `(u, w)`
to `u + w`. -/
theorem mfderiv_riemannianExp_tangentBundle_zeroSection_apply
    (p : M) (u w : TangentSpace I p) :
    mfderiv I.tangent I (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2)
      (zeroSection E (TangentSpace I) p)
      ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) p).symm (u, w)) = u + w := by
  let F : TangentBundle I M → M × M := fun z ↦ (z.proj, riemannianExp I M z.proj z.2)
  have hFd : MDifferentiableAt I.tangent (I.prod I) F (zeroSection E (TangentSpace I) p) :=
    ((contMDiffOn_prodMk_proj_riemannianExp _ (zero_mem_expDomain p)).contMDiffAt
      (isOpen_setOfPred_mem_expDomain.mem_nhds (zero_mem_expDomain p))).mdifferentiableAt
      (by simp)
  have hcomp := mfderiv_comp_apply (zeroSection E (TangentSpace I) p)
    mdifferentiableAt_snd hFd ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) p).symm (u, w))
  -- `TangentSpace I (riemannianExp I M p 0)` and `TangentSpace I p` both reduce to `E`.
  rw [mfderiv_prodMk_proj_riemannianExp_zeroSection_apply, mfderiv_snd] at hcomp
  exact hcomp

/-- **Variable-base exponential formula along a curve through a zero vector.** For any curve
`σ : ℝ → TM` differentiable at `0` through `0_p`, differentiating `(x, v) ↦ exp_x v` along the
ray-rescaled path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩` gives the affine combination
`∂_q (σ q).proj (0) + t • D_q (σ q).2 (0)` for all `t : ℝ`. -/
theorem mfderiv_riemannianExp_tangentBundle_zeroSection_curveVelocity
    {p : M} {σ : ℝ → TangentBundle I M}
    (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    (hσ0 : σ 0 = TotalSpace.mk' E p 0) (t : ℝ) :
    mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (zeroSection E (TangentSpace I) p)
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) =
      curveVelocity I (fun q ↦ (σ q).proj) 0 +
         t • CovariantDerivative.alongCurve (CovariantDerivative.leviCivitaConnection I M)
           (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 := by
  obtain ⟨hp, hv⟩ := TotalSpace.ext_iff.mp hσ0.symm
  subst hp
  let σ_t : ℝ → TangentBundle I M := fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)
  have hσ_t : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ_t 0 :=
    (((contMDiffAt_const (c := t)).smul_totalSpace contMDiffAt_id).mdifferentiableAt
      (n := 1) one_ne_zero).comp 0 hσ
  -- Both `TangentSpace I.tangent (σ_t 0)` and `TangentSpace I.tangent (zeroSection E _ _)` reduce
  -- to `E × E`; split the velocity through `zeroSectionTangentEquiv` to apply the zero-section
  -- differential formula.
  let e := TauCeti.Bundle.zeroSectionTangentEquiv (I := I) (F := E) (V := TangentSpace I) (σ 0).proj
  let ξ : TangentSpace I.tangent (zeroSection E (TangentSpace I) (σ 0).proj) :=
    curveVelocity I.tangent σ_t 0
  have hdiff : mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
      (zeroSection E (TangentSpace I) (σ 0).proj) ξ = (e ξ).1 + (e ξ).2 := by
    simpa only [e, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using
      mfderiv_riemannianExp_tangentBundle_zeroSection_apply (σ 0).proj (e ξ).1 (e ξ).2
  have hfst : (e ξ).1 = curveVelocity I (fun q ↦ (σ q).proj) 0 := by
    have hcomp := mfderiv_comp_apply 0
      ((Bundle.contMDiff_proj (TangentSpace I) (σ_t 0)).mdifferentiableAt one_ne_zero) hσ_t (1 : ℝ)
    rw [Bundle.mfderiv_proj] at hcomp
    dsimp only [e]
    rw [TauCeti.Bundle.zeroSectionTangentEquiv_apply, curveVelocity_apply]
    dsimp only [ξ]
    rw [curveVelocity_apply]
    exact hcomp.symm
  have hsnd : (e ξ).2 =
      t • CovariantDerivative.alongCurve (CovariantDerivative.leviCivitaConnection I M)
        (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 := by
    have hD := CovariantDerivative.alongCurve_eq_symmL_curveVelocity
      (CovariantDerivative.leviCivitaConnection I M) hσ_t
    have hD' : CovariantDerivative.alongCurve (CovariantDerivative.leviCivitaConnection I M)
        (fun q ↦ (σ_t q).proj) (fun q ↦ (σ_t q).2) 0 =
        (trivializationAt E (TangentSpace I) (σ 0).proj).symmL ℝ (σ 0).proj ξ.2 := by
      refine hD.trans (congrArg
        ((trivializationAt E (TangentSpace I) (σ 0).proj).symmL ℝ (σ 0).proj) ?_)
      have hfib0 : ((σ_t 0).2 : E) = (0 : E) :=
        (congrArg (t • ·) (eq_of_heq hv).symm).trans (smul_zero t)
      have hzero : christoffelMap (Module.finBasis ℝ E)
          ((CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (σ_t 0).proj).baseSet))
          (σ_t 0).proj (σ_t 0).2 = 0 :=
        (congrArg _ hfib0).trans (map_zero _)
      exact (congrArg (ξ.2 + ·)
        ((DFunLike.congr_fun hzero _).trans (zero_apply _))).trans (add_zero _)
    rw [← CovariantDerivative.alongCurve_const_smul, hD']
    exact congrArg Prod.snd (TauCeti.Bundle.zeroSectionTangentEquiv_apply (σ 0).proj ξ)
  exact hdiff.trans (congrArg₂ (· + ·) hfst hsnd)

/-- At `t = 0`, the variable-base differential of `exp` along a ray-rescaled curve evaluates to the
base-point velocity of `σ`, without any differentiability assumption on `σ`. -/
theorem mfderiv_riemannianExp_tangentBundle_curveVelocity_zero
    (σ : ℝ → TangentBundle I M) :
    mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E (σ 0).proj ((0 : ℝ) • (σ 0).2))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj ((0 : ℝ) • (σ q).2)) 0) =
      curveVelocity I (fun q ↦ (σ q).proj) 0 := by
  set c : ℝ → M := fun q ↦ (σ q).proj
  set σ₀ : ℝ → TangentBundle I M := fun q ↦ TotalSpace.mk' E (σ q).proj ((0 : ℝ) • (σ q).2)
  set expTM : TangentBundle I M → M := fun w ↦ riemannianExp I M w.proj w.2
  have hζ : σ₀ = zeroSection E (TangentSpace I) ∘ c := by
    funext q
    simp [σ₀, c, zeroSection]
  by_cases hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0
  · have hσ₀ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ₀ 0 :=
      hζ ▸ (((contMDiff_zeroSection ℝ (TangentSpace I) :
        ContMDiff I I.tangent ∞ _).contMDiffAt).mdifferentiableAt (by simp)).comp 0 hc
    have hexp : MDifferentiableAt I.tangent I expTM (σ₀ 0) :=
      (contMDiffAt_riemannianExp_tangentBundle
        (by simpa only [σ₀, zero_smul] using zero_mem_expDomain (σ 0).proj)).mdifferentiableAt
        (by simp)
    have h1 : mfderiv I.tangent I expTM (σ₀ 0) (curveVelocity I.tangent σ₀ 0) =
        curveVelocity I (expTM ∘ σ₀) 0 := by
      rw [curveVelocity_apply, curveVelocity_apply]
      exact (mfderiv_comp_apply 0 hexp hσ₀ (1 : ℝ)).symm
    have h0 : expTM ∘ σ₀ = c := by
      funext q
      simp [expTM, σ₀, c, zero_smul]
    -- `TangentSpace I (expTM (σ₀ 0))` and `TangentSpace I (c 0)` both reduce to `E`.
    exact h1.trans (Filter.EventuallyEq.of_eq h0).curveVelocity_eq
  · have hσ₀ : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ₀ 0 := fun h ↦ by
      have hc_eq : c = TotalSpace.proj ∘ σ₀ := rfl
      exact hc (hc_eq ▸ (((Bundle.contMDiff_proj (TangentSpace I) :
        ContMDiff I.tangent I ∞ _).contMDiffAt).mdifferentiableAt (by simp)).comp 0 h)
    have hv₀ : curveVelocity I.tangent σ₀ 0 = 0 := by
      rw [curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hσ₀]
      exact zero_apply _
    have hvc : curveVelocity I c 0 = 0 := by
      rw [curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hc]
      exact zero_apply _
    -- Both velocities vanish; `TangentSpace I (expTM (σ₀ 0))` and `TangentSpace I (c 0)` both
    -- reduce to the model space `E` with the same `Zero` instance.
    rw [hv₀]
    exact (map_zero _).trans hvc.symm

/-- **Variation field of a variable-base exponential family.** Along a curve `σ : ℝ → TM`
differentiable at `0`, the variation field of `(q, t) ↦ exp_{(σ q).proj} (t • (σ q).2)` at a time
`t` in the maximal geodesic interval equals the differential of `(x, v) ↦ exp_x v` applied to the
velocity of the ray-rescaled path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩`. -/
theorem variationField_riemannianExp_smul
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    {t : ℝ} (ht : t ∈ geodesicInterval I M (σ 0).proj (σ 0).2) :
    variationField I (fun q r ↦ riemannianExp I M (σ q).proj (r • (σ q).2)) t =
      mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) := by
  let σ_t : ℝ → TangentBundle I M := fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)
  have hσ_t : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ_t 0 :=
    (((contMDiffAt_const (c := t)).smul_totalSpace contMDiffAt_id).mdifferentiableAt
      (n := 1) one_ne_zero).comp 0 hσ
  have hexp : MDifferentiableAt I.tangent I
      (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2) (σ_t 0) :=
    (contMDiffAt_riemannianExp_tangentBundle
      (mem_geodesicInterval_iff_smul_mem_expDomain.mp ht)).mdifferentiableAt (by simp)
  rw [variationField_apply, curveVelocity_apply, curveVelocity_apply]
  exact mfderiv_comp_apply 0 hexp hσ_t (1 : ℝ)

/-- **The variable-base inverse function theorem.** The map `(x, v) ↦ (x, exp_x v)` from the
tangent bundle to `M × M` is a local diffeomorphism at every zero vector. -/
theorem isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection (p : M) :
    IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2))
      (zeroSection E (TangentSpace I) p) := by
  let e := TauCeti.Bundle.zeroSectionTangentEquiv (I := I) (F := E) (V := TangentSpace I) p
  let A : (TangentSpace I p × TangentSpace I p) ≃L[ℝ] (TangentSpace I p × TangentSpace I p) :=
    (ContinuousLinearEquiv.refl ℝ _).skewProd (ContinuousLinearEquiv.refl ℝ _)
      (ContinuousLinearMap.id ℝ _)
  refine isLocalDiffeomorphAt_of_mfderiv_eq contMDiffOn_prodMk_proj_riemannianExp
    isOpen_setOfPred_mem_expDomain
    (zero_mem_expDomain p) BoundarylessManifold.isInteriorPoint (by simp) (e := e.trans A) ?_
  ext w
  obtain ⟨⟨u, v⟩, rfl⟩ := e.symm.surjective w
  rw [mfderiv_prodMk_proj_riemannianExp_zeroSection_apply]
  -- `e.trans A` applied to `e.symm (u, v)` is `A (u, v) = (u, v + u)`.
  exact (congrArg A (e.apply_symm_apply (u, v))).trans
    ((ContinuousLinearEquiv.skewProd_apply _ _ _ (u, v)).trans (congrArg (u, ·) (add_comm v u)))

/-- Where `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism, so is its restriction `exp_q` to the
fibre over `q`: the differential of `exp_q` is the vertical part of an invertible differential. -/
theorem isLocalDiffeomorphAt_riemannianExp_of_prodMk {q : M} {v : TangentSpace I q}
    (hv : v ∈ expDomain I M q)
    (h : IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) ⟨q, v⟩) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q) v := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  let ι : TangentSpace I q → TangentBundle I M := TotalSpace.mk q
  have hFinv := h.isInvertible_mfderiv (by simp)
  have hFd := h.mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v :=
    (contMDiffAt_riemannianExp hv).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt 𝓘(ℝ, TangentSpace I q) I.tangent ι v :=
    ((contMDiff_totalSpaceMk (n := 1) q).mdifferentiable one_ne_zero) v
  -- The derivative of `exp_q` at `v` is injective, since `F ∘ ι = (q, exp_q)`.
  have hinj : Injective (mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v) := by
    refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
    have hcomp := mfderiv_comp_apply v hFd hι w
    have hfun : F ∘ ι = fun w ↦ (q, riemannianExp I M q w) := rfl
    rw [hfun, mfderiv_prodMk mdifferentiableAt_const hexp, mfderiv_const] at hcomp
    have h0 : mfderiv I.tangent (I.prod I) F (ι v)
        (mfderiv 𝓘(ℝ, TangentSpace I q) I.tangent ι v w) = 0 :=
      hcomp.symm.trans ((ContinuousLinearMap.prod_apply _ _ w).trans
        ((Prod.ext (zero_apply w) hw).trans Prod.mk_zero_zero))
    obtain ⟨A, hA⟩ := hFinv
    rw [← hA] at h0
    have h1 := A.injective (h0.trans (map_zero A).symm)
    exact injective_mfderiv_totalSpaceMk q v (h1.trans (map_zero _).symm)
  -- Both tangent spaces are definitionally the model space `E`, so their dimensions agree.
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, TangentSpace I q) v) =
      Module.finrank ℝ (TangentSpace I (riemannianExp I M q v)) := rfl
  have hbij : Bijective (mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_riemannianExp q) (isOpen_expDomain q) hv
    BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv) rfl

/-- Where `exp_q` is a local diffeomorphism at `v ∈ expDomain I M q`, so is
`(x, v) ↦ (x, exp_x v)` at `⟨q, v⟩`. This is the converse of
`isLocalDiffeomorphAt_riemannianExp_of_prodMk`. -/
theorem isLocalDiffeomorphAt_prodMk_proj_riemannianExp {q : M} {v : TangentSpace I q}
    (hv : v ∈ expDomain I M q)
    (h : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q) v) :
    IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) ⟨q, v⟩ := by
  set z : TangentBundle I M := ⟨q, v⟩
  let ι : TangentSpace I q → TangentBundle I M := TotalSpace.mk q
  have hzO : z ∈ {z : TangentBundle I M | z.2 ∈ expDomain I M z.proj} := hv
  have hOopen := isOpen_setOfPred_mem_expDomain (I := I) (M := M)
  have hπd : MDifferentiableAt I.tangent I (π E (TangentSpace I)) z :=
    (Bundle.contMDiff_proj (TangentSpace I) z).mdifferentiableAt one_ne_zero
  have hexpd : MDifferentiableAt I.tangent I (fun z : TangentBundle I M ↦
      riemannianExp I M z.proj z.2) z :=
    ((contMDiffOn_riemannianExp_tangentBundle z hzO).contMDiffAt
      (hOopen.mem_nhds hzO)).mdifferentiableAt (by simp)
  have hιd : MDifferentiableAt 𝓘(ℝ, TangentSpace I q) I.tangent ι v :=
    ((contMDiff_totalSpaceMk (n := 1) q).mdifferentiable one_ne_zero) v
  -- A vector killed by the differential is killed by that of the projection, so it is vertical,
  -- and on vertical vectors the differential is that of `exp_q`, which is injective.
  refine isLocalDiffeomorphAt_of_injective_mfderiv contMDiffOn_prodMk_proj_riemannianExp hOopen
    hzO BoundarylessManifold.isInteriorPoint (by simp) ?_ rfl
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_
  rw [mfderiv_prodMk hπd hexpd] at hξ
  replace hξ := Prod.mk_eq_zero.1 ((ContinuousLinearMap.prod_apply _ _ ξ).symm.trans hξ)
  obtain ⟨w, rfl⟩ : ξ ∈ (mfderiv 𝓘(ℝ, TangentSpace I q) I.tangent ι v).range := by
    rw [← ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk]
    exact hξ.1
  have hfun : ((fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2) ∘ ι) =
      riemannianExp I M q := rfl
  rw [ContinuousLinearMap.coe_coe, ← mfderiv_comp_apply v hexpd hιd, hfun] at hξ
  rw [(h.isInvertible_mfderiv (by simp)).injective.eq_iff' (map_zero _) |>.1 hξ.2, map_zero]

/-- At `v ∈ expDomain I M q`, the map `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism at
`⟨q, v⟩` exactly when `exp_q` is one at `v`. -/
theorem isLocalDiffeomorphAt_prodMk_proj_riemannianExp_iff {q : M} {v : TangentSpace I q}
    (hv : v ∈ expDomain I M q) :
    IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
        (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) ⟨q, v⟩ ↔
      IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q) v :=
  ⟨isLocalDiffeomorphAt_riemannianExp_of_prodMk hv,
    isLocalDiffeomorphAt_prodMk_proj_riemannianExp hv⟩

variable {W : Set M} {r : ℝ}

/-- On the tube of tangent vectors of norm less than `r` over a set `W` of points `q` at which the
tangent ball of radius `r` lies in the domain of `exp_q` and `exp_q` is a local diffeomorphism on
it, the map `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism. -/
theorem isLocalDiffeomorphOn_prodMk_proj_riemannianExp
    (hsub : ∀ q ∈ W, Metric.ball 0 r ⊆ expDomain I M q)
    (hloc : ∀ q ∈ W,
      IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q) (Metric.ball 0 r)) :
    IsLocalDiffeomorphOn I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2))
      {z | z.proj ∈ W ∧ ‖z.2‖ < r} := by
  rintro ⟨⟨q, v⟩, hq, hv⟩
  have hvr : v ∈ Metric.ball 0 r := mem_ball_zero_iff.2 hv
  exact isLocalDiffeomorphAt_prodMk_proj_riemannianExp (hsub q hq hvr) (hloc q hq ⟨v, hvr⟩)

omit [I.Boundaryless] [T2Space M] in
/-- On the tube of tangent vectors of norm less than `r` over a set `W` of points `q` at which
`exp_q` is injective on the tangent ball of radius `r`, the map `(x, v) ↦ (x, exp_x v)` is
injective. -/
theorem injOn_prodMk_proj_riemannianExp
    (hW : ∀ q ∈ W, InjOn (riemannianExp I M q) (Metric.ball 0 r)) :
    InjOn (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2))
      {z | z.proj ∈ W ∧ ‖z.2‖ < r} := by
  rintro ⟨q, v⟩ ⟨hq, hv⟩ ⟨q', v'⟩ ⟨-, hv'⟩ h
  obtain ⟨rfl, h⟩ := Prod.mk.inj h
  exact congrArg (TotalSpace.mk q) (hW q hq (mem_ball_zero_iff.2 hv) (mem_ball_zero_iff.2 hv') h)

omit [I.Boundaryless] [T2Space M] in
/-- The image of the tube of tangent vectors of norm less than `r` over `W` under
`(x, v) ↦ (x, exp_x v)` consists of the pairs `(x, y)` with `x ∈ W` and `y ∈ exp_x '' B(0, r)`. -/
theorem image_prodMk_proj_riemannianExp_setOf_norm_lt :
    (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) ''
        {z | z.proj ∈ W ∧ ‖z.2‖ < r} =
      {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨q, v⟩, ⟨hq, hv⟩, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hq, v, mem_ball_zero_iff.2 hv, rfl⟩
  · rintro ⟨hx, v, hv, hy⟩
    exact ⟨⟨x, v⟩, ⟨hx, mem_ball_zero_iff.1 hv⟩, Prod.ext rfl hy⟩

/-- For an open set `W` of points `q` at which the tangent ball of radius `r` lies in the domain of
`exp_q` and `exp_q` is a local diffeomorphism on it, the pairs `(x, y)` with `x ∈ W` and
`y ∈ exp_x '' B(0, r)` form an open subset of `M × M`. -/
theorem isOpen_setOf_mem_riemannianExp_image_ball (hWo : IsOpen W)
    (hsub : ∀ q ∈ W, Metric.ball 0 r ⊆ expDomain I M q)
    (hloc : ∀ q ∈ W,
      IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q) (Metric.ball 0 r)) :
    IsOpen {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  rw [← image_prodMk_proj_riemannianExp_setOf_norm_lt]
  exact (isLocalDiffeomorphOn_prodMk_proj_riemannianExp hsub hloc).isLocalHomeomorphOn.isOpen_image
    (hWo.norm_lt_bundle r)

end TauCeti.Manifold
