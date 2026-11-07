/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Topology.VectorBundle.Radius
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# Uniformly normal neighbourhoods

Consider the exponential map with a variable base point, `(x, v) ↦ (x, exp_x v)`, from the
tangent bundle `TM` to `M × M`. It is smooth on the open set of tangent vectors in the natural
domain of the exponential map. At the zero vector `0_p` of `T_p M`, the tangent space of `TM`
splits as `T_p M × T_p M` (the horizontal and vertical summands of
`TauCeti.Bundle.zeroSectionTangentEquiv`), and in this splitting the differential of the map is
`(u, v) ↦ (u, u + v)`: the zero section goes to the diagonal, and the fibre over `p` is sent
through `exp_p`, whose differential at the origin is the identity. This differential is
invertible, so by the inverse function theorem the map is a local diffeomorphism at `0_p`.

Consequently every point `p` has a *uniformly normal* neighbourhood: there are a neighbourhood
`W` of `p` and a radius `r > 0` such that, for every `q ∈ W`, the ball of radius `r` in `T_q M`
is a normal domain at `q` and its exponential image contains all of `W`. The radius is uniform
in the base point, unlike the radius of `TauCeti.Manifold.exists_isNormalDomain_ball`, which
depends on the point. On a compact set of base points a single positive radius gives normal
domains at all of them.

These neighbourhoods are the starting point for geodesically convex neighbourhoods and for
coordinates built from the Riemannian distance to finitely many nearby centres.

## Main results

* `TauCeti.Manifold.mfderiv_prodMk_proj_riemannianExp_zeroSection_apply`: the differential of
  `(x, v) ↦ (x, exp_x v)` at a zero vector is `(u, v) ↦ (u, u + v)`.
* `TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection`: the
  variable-base inverse function theorem, `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism at
  every zero vector.
* `TauCeti.Manifold.exists_mem_nhds_forall_isNormalDomain_ball`: every point has a uniformly
  normal neighbourhood.
* `IsCompact.exists_pos_forall_isNormalDomain_ball`: on a compact set, one positive radius gives
  normal domains at every point.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Theorem 3.7 (totally normal
  neighbourhoods), whose proof applies the inverse function theorem to the same map.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6
  (uniformly normal neighbourhoods).
-/

public section

noncomputable section

open Bundle Manifold Set Filter Function
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
    exact h.symm.trans rfl
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
    exact h.symm.trans (Prod.ext rfl hv)
  rw [h1, h2]
  exact Prod.ext (add_zero u) rfl

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
  exact (congrArg A (e.apply_symm_apply (u, v))).trans (Prod.ext rfl (add_comm v u))

/-- Where `(x, v) ↦ (x, exp_x v)` is a local diffeomorphism, so is its restriction `exp_q` to the
fibre over `q`: the differential of `exp_q` is the vertical part of an invertible differential. -/
private theorem isLocalDiffeomorphAt_riemannianExp_of_prodMk {q : M} {v : TangentSpace I q}
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
      hcomp.symm.trans (Prod.ext rfl hw)
    obtain ⟨A, hA⟩ := hFinv
    rw [← hA] at h0
    have h1 := A.injective (h0.trans (map_zero A).symm)
    exact injective_mfderiv_totalSpaceMk q v (h1.trans (map_zero _).symm)
  have hbij : Bijective (mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hinj⟩
  exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_riemannianExp q) (isOpen_expDomain q) hv
    BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv) rfl

/-- A tangent ball at `q` is a normal domain as soon as all its vectors lie in a set of tangent
vectors on which `(x, v) ↦ (x, exp_x v)` is injective, a local diffeomorphism and defined. -/
private theorem isNormalDomain_ball_of_injOn {O : Set (TangentBundle I M)}
    (hinj : InjOn (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) O)
    (hO : ∀ z ∈ O, IsLocalDiffeomorphAt I.tangent (I.prod I) ∞
      (fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)) z ∧
        z.2 ∈ expDomain I M z.proj)
    {q : M} {r : ℝ} (hr : 0 < r)
    (hball : ∀ v : TangentSpace I q, ‖v‖ < r → TotalSpace.mk' E q v ∈ O) :
    IsNormalDomain I M q (Metric.ball 0 r) := by
  have hmem (v : TangentSpace I q) (hv : v ∈ Metric.ball 0 r) := hO _ (hball v
    (mem_ball_zero_iff.1 hv))
  refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball 0 r).starConvex (Metric.mem_ball_self hr), fun v hv ↦ (hmem v hv).2,
    fun v hv w hw hvw ↦ TotalSpace.mk_inj.1 (hinj (hball v (mem_ball_zero_iff.1 hv))
      (hball w (mem_ball_zero_iff.1 hw)) (by simp only [hvw])),
    fun v ↦ isLocalDiffeomorphAt_riemannianExp_of_prodMk (hmem v v.2).2 (hmem v v.2).1⟩

/-- **Uniformly normal neighbourhoods.** Every point `p` has a neighbourhood `W` with a radius
`r > 0` such that, for every `q ∈ W`, the tangent ball of radius `r` at `q` is a normal domain whose
exponential image contains `W`. In particular `W` lies in a normal neighbourhood of each of its
points. -/
theorem exists_mem_nhds_forall_isNormalDomain_ball (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∃ W ∈ 𝓝 p, ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r) ∧
      W ⊆ riemannianExp I M q '' Metric.ball 0 r := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  have hloc := isLocalDiffeomorphAt_prodMk_proj_riemannianExp_zeroSection (I := I) (M := M) p
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  -- On `O`, the map `F` is a local diffeomorphism, injective (it has the left inverse
  -- `hloc.localInverse`), and the exponential map is defined.
  set O : Set (TangentBundle I M) := hloc.localInverse.target ∩
    ({z | IsLocalDiffeomorphAt I.tangent (I.prod I) ∞ F z} ∩
      {z | z.2 ∈ expDomain I M z.proj})
  have hOopen : IsOpen O := hloc.localInverse.open_target.inter
    ((isOpen_iff_mem_nhds.2 fun _ (hz : IsLocalDiffeomorphAt I.tangent (I.prod I) ∞ F _) ↦
      hz.eventually).inter isOpen_setOfPred_mem_expDomain)
  have hpO : zeroSection E (TangentSpace I) p ∈ O :=
    ⟨hloc.localInverse_mem_target, hloc, zero_mem_expDomain p⟩
  obtain ⟨r, hr, hball⟩ := hOopen.exists_pos_forall_norm_le_subset_bundle hpO
  obtain ⟨A, hAball, hAopen, hpA⟩ := eventually_nhds_iff.1 hball
  have hnorm : Continuous fun z : TangentBundle I M ↦ ‖z.2‖ :=
    TauCeti.continuous_norm_bundle E (TangentSpace I)
  set S : Set (TangentBundle I M) :=
    O ∩ (TotalSpace.proj ⁻¹' A ∩ {z | ‖z.2‖ < r})
  have hSopen : IsOpen S := hOopen.inter
    ((hAopen.preimage (FiberBundle.continuous_proj E _)).inter
      (isOpen_lt hnorm continuous_const))
  -- The zero of the fibre and that of its Riemannian normed group agree only up to instances,
  -- so `norm_zero` is applied after `convert` rather than by `simp`.
  have hpS : zeroSection E (TangentSpace I) p ∈ S :=
    ⟨hpO, hpA, by rw [mem_ofPred_eq]; convert hr using 1; exact norm_zero (E := TangentSpace I p)⟩
  -- The image of `S` is a neighbourhood of `F (0_p) = (p, p)`.
  have hFS : F '' S ∈ 𝓝 (p, p) := by
    have hFp : F (zeroSection E (TangentSpace I) p) = (p, p) := by simp [F, zeroSection]
    rw [← hFp]
    refine mem_of_superset (inter_mem (hloc.continuousAt_localInverse.preimage_mem_nhds
      (hSopen.mem_nhds ?_)) (hloc.localInverse.open_source.mem_nhds
        hloc.localInverse_mem_source)) fun y hy ↦ ⟨_, hy.1, hloc.localInverse_right_inv hy.2⟩
    rwa [hloc.localInverse_left_inv hloc.localInverse_mem_target]
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 hFS
  refine ⟨r, hr, W₁ ∩ W₂ ∩ A, inter_mem (inter_mem hW₁ hW₂) (hAopen.mem_nhds hpA),
    fun q hq ↦ ⟨?_, ?_⟩⟩
  · -- `F` is injective on `O`, where it has the left inverse `hloc.localInverse`.
    exact isNormalDomain_ball_of_injOn
      (fun z (hz : z ∈ O) z' (hz' : z' ∈ O) h ↦ (hloc.localInverse_left_inv hz.1).symm.trans
        ((congrArg hloc.localInverse h).trans (hloc.localInverse_left_inv hz'.1)))
      (fun z (hz : z ∈ O) ↦ hz.2) hr fun v hv ↦ hAball q hq.2 v hv.le
  · intro q' hq'
    obtain ⟨⟨b, w⟩, ⟨-, -, hzr⟩, hz⟩ := hW (mk_mem_prod hq.1.1 hq'.1.2)
    simp only [F, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨w, mem_ball_zero_iff.2 hzr, rfl⟩

/-- **A uniform normal radius on a compact set.** For a compact set `K` of points there is one
radius `r > 0` such that the tangent ball of radius `r` at every point of `K` is a normal domain. -/
theorem _root_.IsCompact.exists_pos_forall_isNormalDomain_ball {K : Set M} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, IsNormalDomain I M q (Metric.ball 0 r) := by
  choose! R hR W hW hRW using exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M)
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover W fun p _ ↦ hW p
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, fun q hq ↦ by simpa using hKt hq⟩
  refine ⟨t.inf' ht R, (Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p, fun q hq ↦ ?_⟩
  obtain ⟨p, hpt, hqp⟩ := mem_iUnion₂.1 (hKt hq)
  exact (hRW p q hqp).1.ball (Metric.ball_subset_ball (Finset.inf'_le R hpt))
    ((Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p)

end TauCeti.Manifold
