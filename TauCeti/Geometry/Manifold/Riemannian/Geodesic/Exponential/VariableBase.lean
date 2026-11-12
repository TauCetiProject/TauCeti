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
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

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
Wherever the map is a local diffeomorphism, so is its restriction `exp_q` to a fibre.

## Main results

* `TauCeti.Manifold.contMDiffOn_prodMk_proj_riemannianExp`: the map `(x, v) ↦ (x, exp_x v)` is
  smooth where the exponential map is defined.
* `TauCeti.Manifold.mfderiv_prodMk_proj_riemannianExp_zeroSection_apply`: the differential of
  `(x, v) ↦ (x, exp_x v)` at a zero vector is `(u, v) ↦ (u, u + v)`.
* `TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection`: the
  variable-base inverse function theorem, `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism at
  every zero vector.
* `TauCeti.Manifold.isLocalDiffeomorphAt_riemannianExp_of_prodMk`: where `(x, v) ↦ (x, exp_x v)`
  is a local diffeomorphism, so is `exp_q` on the fibre.

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

/-- Where `exp_q` is a local diffeomorphism, so is `(x, v) ↦ (x, exp_x v)`: a tangent vector of
`TM` killed by the differential of this map projects to zero, so it is vertical, and on vertical
vectors the differential is that of `exp_q`. This is the converse of
`isLocalDiffeomorphAt_riemannianExp_of_prodMk`. -/
theorem isLocalDiffeomorphAt_prodMk_proj_riemannianExp {q : M} {v : TangentSpace I q}
    (hv : v ∈ expDomain I M q)
    (h : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q) v) :
    IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) ⟨q, v⟩ := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  set z : TangentBundle I M := ⟨q, v⟩
  let ι : TangentSpace I q → TangentBundle I M := TotalSpace.mk q
  have hzO : z ∈ {z : TangentBundle I M | z.2 ∈ expDomain I M z.proj} := hv
  have hOopen := isOpen_setOfPred_mem_expDomain (I := I) (M := M)
  have hexpd : MDifferentiableAt I.tangent I (fun z : TangentBundle I M ↦
      riemannianExp I M z.proj z.2) z :=
    ((contMDiffOn_riemannianExp_tangentBundle z hzO).contMDiffAt
      (hOopen.mem_nhds hzO)).mdifferentiableAt (by simp)
  have hιd : MDifferentiableAt 𝓘(ℝ, TangentSpace I q) I.tangent ι v :=
    ((contMDiff_totalSpaceMk (n := 1) q).mdifferentiable one_ne_zero) v
  set dι := mfderiv 𝓘(ℝ, TangentSpace I q) I.tangent ι v
  -- The differential of `F` is the differential of the projection, which reads the first
  -- coordinate of the model `E × E`, paired with that of `(x, v) ↦ exp_x v`.
  have hdF (ξ : TangentSpace I.tangent z) : mfderiv I.tangent (I.prod I) F z ξ =
      (ξ.1, mfderiv I.tangent I (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2) z
        ξ) := by
    rw [mfderiv_prodMk ((Bundle.contMDiff_proj (TangentSpace I) z).mdifferentiableAt one_ne_zero)
      hexpd, Bundle.mfderiv_proj]
    exact ContinuousLinearMap.prod_apply _ _ ξ
  -- Vertical vectors, those of vanishing first coordinate, are the image of the differential of
  -- the fibre inclusion `ι`: it is injective and lands in them, and both have the dimension of `E`.
  have hι1 (w : TangentSpace I q) : (dι w).1 = 0 := by
    have h := mfderiv_comp_apply v
      ((Bundle.contMDiff_proj (TangentSpace I) (ι v)).mdifferentiableAt one_ne_zero) hιd w
    have hfun : (TotalSpace.proj ∘ ι : TangentSpace I q → M) = fun _ ↦ q := rfl
    rw [hfun, mfderiv_const, Bundle.mfderiv_proj] at h
    exact h.symm
  let dι₂ : TangentSpace I q →ₗ[ℝ] E :=
    (LinearMap.snd ℝ E E).comp (dι : TangentSpace I q →L[ℝ] E × E).toLinearMap
  have hdι₂ : Injective dι₂ := fun w w' hww' ↦
    injective_mfderiv_totalSpaceMk q v (Prod.ext ((hι1 w).trans (hι1 w').symm) hww')
  have hvert (ξ : TangentSpace I.tangent z) (hξ : ξ.1 = 0) : ∃ w, dι w = ξ := by
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hdι₂ ξ.2
    exact ⟨w, Prod.ext ((hι1 w).trans hξ.symm) hw⟩
  -- On vertical vectors the differential of `F` is that of `exp_q`, which is injective.
  have hinj : Injective (mfderiv I.tangent (I.prod I) F z) := by
    refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_
    rw [hdF] at hξ
    obtain ⟨w, rfl⟩ := hvert ξ (congrArg Prod.fst hξ)
    have hcomp := mfderiv_comp_apply v hexpd hιd w
    have hfun : ((fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2) ∘ ι) =
        riemannianExp I M q := rfl
    rw [hfun] at hcomp
    obtain ⟨A, hA⟩ := h.isInvertible_mfderiv (by simp)
    have h0 : A w = 0 := by
      rw [← ContinuousLinearEquiv.coe_coe, hA, hcomp]
      exact congrArg Prod.snd hξ
    rw [A.map_eq_zero_iff.1 h0, map_zero]
  -- Both tangent spaces are definitionally the model space `E × E`, so their dimensions agree.
  have hdim : Module.finrank ℝ (TangentSpace I.tangent z) =
      Module.finrank ℝ (TangentSpace (I.prod I) (F z)) := rfl
  have hbij : Bijective (mfderiv I.tangent (I.prod I) F z) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  exact isLocalDiffeomorphAt_of_mfderiv_eq contMDiffOn_prodMk_proj_riemannianExp hOopen hzO
    BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv) rfl

end TauCeti.Manifold
