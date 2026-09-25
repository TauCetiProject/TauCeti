/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential

/-!
# Normal domains and the Riemannian logarithm

A *normal domain* at a point `p` of a Riemannian manifold is an open star-shaped neighbourhood
`U` of the origin of `T_p M`, inside the natural domain of the exponential map, on which `exp_p`
restricts to a diffeomorphism onto its image.  The image `exp_p '' U` is the associated *normal
neighbourhood* of `p`.

Since the differential of `exp_p` at the origin is the identity, the inverse function theorem
produces a ball of some positive radius that is a normal domain at every point.  On a normal
neighbourhood the restricted exponential map has an inverse, the Riemannian logarithm `log_p`,
which is again smooth; it is the chart underlying normal coordinates, and it turns a point of the
normal neighbourhood into the initial velocity of the radial geodesic reaching it.

The logarithm is defined as a total function taking a junk value outside the normal
neighbourhood, so each theorem about its value carries the corresponding membership hypothesis.
There is deliberately no single global logarithm: beyond a normal neighbourhood the exponential
map may lose injectivity or local invertibility, so no canonical smooth global inverse is provided.

## Main definitions and results

* `TauCeti.Manifold.IsNormalDomain`: the predicate defining normal domains.
* `TauCeti.Manifold.riemannianLog`: the Riemannian logarithm relative to a normal domain.
* `TauCeti.Manifold.IsNormalDomain.toPartialDiffeomorph`: the exponential map and logarithm as a
  partial diffeomorphism between a normal domain and its normal neighbourhood.
* `TauCeti.Manifold.exists_isNormalDomain_ball`: balls of small enough radius are normal domains.
* `TauCeti.Manifold.isCompact_riemannianExp_image_closedBall`: a closed tangent ball in the
  exponential domain has compact exponential image.
* `TauCeti.Manifold.exists_isNormalDomain_ball_with_isCompact_riemannianExp_image_closedBall`:
  a smaller closed tangent ball inside a larger normal ball has compact exponential image.
* `TauCeti.Manifold.IsNormalDomain.isOpen_image`: a normal neighbourhood is open.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_riemannianExp` and
  `TauCeti.Manifold.IsNormalDomain.riemannianExp_riemannianLog`: the two inverse identities.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_self`: the logarithm vanishes at the base point.
* `TauCeti.Manifold.IsNormalDomain.contMDiffOn_riemannianLog`: the logarithm is smooth on the
  normal neighbourhood.
* `TauCeti.Manifold.IsNormalDomain.mem_geodesicInterval`: the geodesic towards a vector of a
  normal domain is defined at least up to time one.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5 and 6.
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Normal domains -/

variable (I M) in
/-- A **normal domain** at `p` is an open star-shaped neighbourhood `U` of the origin of `T_p M`,
contained in the natural domain of the exponential map, on which `exp_p` restricts to a
diffeomorphism onto its image.  The image `exp_p '' U` is the associated *normal neighbourhood*
of `p`. -/
structure IsNormalDomain (p : M) (U : Set (TangentSpace I p)) : Prop where
  /-- A normal domain is open. -/
  isOpen : IsOpen U
  /-- A normal domain contains the origin. -/
  zero_mem : (0 : TangentSpace I p) ∈ U
  /-- A normal domain is star-shaped at the origin. -/
  starConvex : StarConvex ℝ (0 : TangentSpace I p) U
  /-- A normal domain lies in the natural domain of the exponential map. -/
  subset_expDomain : U ⊆ expDomain I M p
  /-- The exponential map is injective on a normal domain. -/
  injOn : InjOn (riemannianExp I M p) U
  /-- The exponential map is a local diffeomorphism at each vector of a normal domain. -/
  isLocalDiffeomorphOn :
    IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) U

namespace IsNormalDomain

variable {p : M} {U V : Set (TangentSpace I p)} {v : TangentSpace I p} {t : ℝ}

omit [I.Boundaryless] in
/-- An open star-shaped neighbourhood of the origin inside a normal domain is a normal domain. -/
theorem mono (h : IsNormalDomain I M p U) (hVU : V ⊆ U) (hV : IsOpen V)
    (hzero : (0 : TangentSpace I p) ∈ V) (hstar : StarConvex ℝ (0 : TangentSpace I p) V) :
    IsNormalDomain I M p V where
  isOpen := hV
  zero_mem := hzero
  starConvex := hstar
  subset_expDomain := hVU.trans h.subset_expDomain
  injOn := h.injOn.mono hVU
  isLocalDiffeomorphOn w := h.isLocalDiffeomorphOn ⟨w, hVU w.2⟩

omit [I.Boundaryless] in
/-- A normal neighbourhood is open. -/
theorem isOpen_image (h : IsNormalDomain I M p U) :
    IsOpen (riemannianExp I M p '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨w, hw, rfl⟩
  rw [← h.isLocalDiffeomorphOn.isLocalHomeomorphOn.map_nhds_eq hw]
  exact Filter.image_mem_map (h.isOpen.mem_nhds hw)

omit [I.Boundaryless] in
/-- A vector of a normal domain can be shrunk towards the origin inside the normal domain. -/
theorem smul_mem (h : IsNormalDomain I M p U) (hv : v ∈ U) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    t • v ∈ U :=
  starConvex_zero_iff.1 h.starConvex hv ht₀ ht₁

/-- **The radial geodesic of a normal domain is defined up to time one.**  The maximal geodesic
from `p` with initial velocity a vector `v` of a normal domain exists on `[0, 1]`; by
`riemannianExp_smul` its value at `t` is the exponential of `t • v`. -/
theorem mem_geodesicInterval (h : IsNormalDomain I M p U) (hv : v ∈ U) (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : t ∈ geodesicInterval I M p v :=
  mem_geodesicInterval_iff_smul_mem_expDomain.2 (h.subset_expDomain (h.smul_mem hv ht₀ ht₁))

variable [T2Space (TangentBundle I M)]

/-- The base point belongs to every normal neighbourhood. -/
theorem self_mem_image (h : IsNormalDomain I M p U) : p ∈ riemannianExp I M p '' U :=
  ⟨0, h.zero_mem, riemannianExp_zero p⟩

/-- A normal neighbourhood is a neighbourhood of the base point. -/
theorem image_mem_nhds (h : IsNormalDomain I M p U) :
    riemannianExp I M p '' U ∈ 𝓝 p :=
  h.isOpen_image.mem_nhds h.self_mem_image

end IsNormalDomain

/-! ### Existence of normal balls -/

/-- **Normal balls exist.**  There is a positive radius such that the ball of that radius around
the origin of `T_p M` is a normal domain at `p`; its image is a normal neighbourhood of `p`. -/
theorem exists_isNormalDomain_ball [T2Space (TangentBundle I M)] (p : M) :
    ∃ r : ℝ, 0 < r ∧ IsNormalDomain I M p (Metric.ball 0 r) := by
  have hd := isLocalDiffeomorphAt_riemannianExp_zero (I := I) p
  -- On the target of the local inverse at the origin, the exponential map is injective.
  have hinj : InjOn (riemannianExp I M p) hd.localInverse.target := fun v hv w hw hvw => by
    rw [← hd.localInverse_left_inv hv, ← hd.localInverse_left_inv hw, hvw]
  have hnhds : {v : TangentSpace I p |
        IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v} ∩
      (hd.localInverse.target ∩ expDomain I M p) ∈ 𝓝 (0 : TangentSpace I p) :=
    Filter.inter_mem hd.eventually
      (Filter.inter_mem (hd.localInverse.open_target.mem_nhds hd.localInverse_mem_target)
        ((isOpen_expDomain (I := I) p).mem_nhds (zero_mem_expDomain p)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  exact ⟨r, hr, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball (0 : TangentSpace I p) r).starConvex (Metric.mem_ball_self hr),
    fun v hv => (hball hv).2.2, hinj.mono fun v hv => (hball hv).2.1,
    fun v => (hball v.2).1⟩

/-! ### Compactly contained normal balls -/

/-- The exponential image of a closed tangent ball contained in the exponential domain is
compact. -/
theorem isCompact_riemannianExp_image_closedBall [T2Space (TangentBundle I M)]
    (p : M) {r : ℝ} (hr : Metric.closedBall 0 r ⊆ expDomain I M p) :
    IsCompact (riemannianExp I M p '' Metric.closedBall 0 r) := by
  apply (isCompact_closedBall (0 : TangentSpace I p) r).image_of_continuousOn
  exact (continuousOn_riemannianExp (I := I) (M := M) p).mono hr

/-- **Normal balls can be chosen compactly contained in a larger normal ball.** More precisely,
there are positive radii `r < R` such that the ball of radius `R` is a normal domain and the
closed ball of radius `r` is contained in it.  The exponential image of that closed ball is
compact.

The nested tangent balls and compact exponential image are inputs to the escape estimate for
curves leaving a normal neighbourhood. -/
theorem exists_isNormalDomain_ball_with_isCompact_riemannianExp_image_closedBall
    [T2Space (TangentBundle I M)] (p : M) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ IsNormalDomain I M p (Metric.ball 0 R) ∧
      Metric.closedBall 0 r ⊆ Metric.ball 0 R ∧
      IsCompact (riemannianExp I M p '' Metric.closedBall 0 r) := by
  obtain ⟨R, hR, hRnormal⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  refine ⟨R / 2, R, half_pos hR, half_lt_self hR, hRnormal,
    Metric.closedBall_subset_ball (half_lt_self hR), ?_⟩
  exact isCompact_riemannianExp_image_closedBall (I := I) (M := M) p
    ((Metric.closedBall_subset_ball (half_lt_self hR)).trans hRnormal.subset_expDomain)

/-! ### The Riemannian logarithm -/

variable (I M) in
/-- The **Riemannian logarithm** at `p` relative to a set `U` of tangent vectors, defined as the
chosen preimage function `invFunOn` for the restriction of `exp_p` to `U`.  When `U` is a normal
domain, it inverts `exp_p` on the normal neighbourhood `exp_p '' U`; outside that neighbourhood
it takes a junk value, so every theorem about its value carries a membership hypothesis. -/
def riemannianLog (p : M) (U : Set (TangentSpace I p)) : M → TangentSpace I p :=
  invFunOn (riemannianExp I M p) U

omit [I.Boundaryless] in
/-- The Riemannian logarithm relative to `U` is `invFunOn` for `exp_p` restricted to `U`. -/
theorem riemannianLog_def (p : M) (U : Set (TangentSpace I p)) :
    riemannianLog I M p U = invFunOn (riemannianExp I M p) U := by
  rfl

namespace IsNormalDomain

variable {p : M} {U : Set (TangentSpace I p)} {v : TangentSpace I p} {q : M}

omit [I.Boundaryless] in
/-- **The logarithm inverts the exponential map** on a normal domain. -/
@[simp] theorem riemannianLog_riemannianExp (h : IsNormalDomain I M p U) (hv : v ∈ U) :
    riemannianLog I M p U (riemannianExp I M p v) = v := by
  rw [riemannianLog_def]
  exact h.injOn.leftInvOn_invFunOn hv

omit [I.Boundaryless] in
/-- The logarithm of a point of a normal neighbourhood lies in the normal domain. -/
theorem riemannianLog_mem (h : IsNormalDomain I M p U) (hq : q ∈ riemannianExp I M p '' U) :
    riemannianLog I M p U q ∈ U := by
  obtain ⟨w, hw, rfl⟩ := hq
  rw [h.riemannianLog_riemannianExp hw]
  exact hw

omit [I.Boundaryless] in
/-- **The exponential map inverts the logarithm** on a normal neighbourhood. -/
@[simp] theorem riemannianExp_riemannianLog (h : IsNormalDomain I M p U)
    (hq : q ∈ riemannianExp I M p '' U) :
    riemannianExp I M p (riemannianLog I M p U q) = q := by
  obtain ⟨w, hw, rfl⟩ := hq
  rw [h.riemannianLog_riemannianExp hw]

variable [T2Space (TangentBundle I M)]

/-- The logarithm vanishes at the base point. -/
@[simp] theorem riemannianLog_self (h : IsNormalDomain I M p U) :
    riemannianLog I M p U p = 0 := by
  have h0 := h.riemannianLog_riemannianExp h.zero_mem
  rwa [riemannianExp_zero] at h0

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- **The Riemannian logarithm is smooth** on the normal neighbourhood it inverts. -/
theorem contMDiffOn_riemannianLog (h : IsNormalDomain I M p U) :
    ContMDiffOn I 𝓘(ℝ, TangentSpace I p) ∞ (riemannianLog I M p U)
      (riemannianExp I M p '' U) := by
  rintro _ ⟨w, hw, rfl⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hloc := h.isLocalDiffeomorphOn ⟨w, hw⟩
  have hinv : hloc.localInverse (riemannianExp I M p w) = w :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hsource : hloc.localInverse.source ∈ 𝓝 (riemannianExp I M p w) :=
    hloc.localInverse.open_source.mem_nhds hloc.localInverse_mem_source
  have hpre : hloc.localInverse ⁻¹' U ∈ 𝓝 (riemannianExp I M p w) :=
    hloc.continuousAt_localInverse.preimage_mem_nhds (by rw [hinv]; exact h.isOpen.mem_nhds hw)
  refine hloc.contMDiffAt_localInverse.congr_of_eventuallyEq ?_
  filter_upwards [hsource, hpre] with z hz hzU
  have hzexp : riemannianExp I M p (hloc.localInverse z) = z := hloc.localInverse_right_inv hz
  have hlog := h.riemannianLog_riemannianExp hzU
  rwa [hzexp] at hlog

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The Riemannian logarithm is continuous on the normal neighbourhood it inverts. -/
theorem continuousOn_riemannianLog (h : IsNormalDomain I M p U) :
    ContinuousOn (riemannianLog I M p U) (riemannianExp I M p '' U) :=
  h.contMDiffOn_riemannianLog.continuousOn

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The exponential map and Riemannian logarithm as a partial diffeomorphism from a normal domain
to its normal neighbourhood. -/
def toPartialDiffeomorph (h : IsNormalDomain I M p U) :
    PartialDiffeomorph (modelWithCornersSelf ℝ (TangentSpace I p)) I
      (TangentSpace I p) M ∞ where
  toPartialEquiv :=
    { toFun := riemannianExp I M p
      invFun := riemannianLog I M p U
      source := U
      target := riemannianExp I M p '' U
      map_source' := fun _ hv => ⟨_, hv, rfl⟩
      map_target' := fun _ hq => h.riemannianLog_mem hq
      left_inv' := fun _ hv => h.riemannianLog_riemannianExp hv
      right_inv' := fun _ hq => h.riemannianExp_riemannianLog hq }
  open_source := h.isOpen
  open_target := h.isOpen_image
  contMDiffOn_toFun := h.isLocalDiffeomorphOn.contMDiffOn
  contMDiffOn_invFun := h.contMDiffOn_riemannianLog

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The source of the normal-domain partial diffeomorphism is the normal domain. -/
@[simp] theorem toPartialDiffeomorph_source (h : IsNormalDomain I M p U) :
    h.toPartialDiffeomorph.source = U := (rfl)

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The target of the normal-domain partial diffeomorphism is the normal neighbourhood. -/
@[simp] theorem toPartialDiffeomorph_target (h : IsNormalDomain I M p U) :
    h.toPartialDiffeomorph.target = riemannianExp I M p '' U := (rfl)

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The forward map of the normal-domain partial diffeomorphism is the exponential map. -/
@[simp] theorem coe_toPartialDiffeomorph (h : IsNormalDomain I M p U) :
    ⇑h.toPartialDiffeomorph = riemannianExp I M p := (rfl)

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The inverse map of the normal-domain partial diffeomorphism is the Riemannian logarithm. -/
@[simp] theorem toPartialDiffeomorph_symm_apply (h : IsNormalDomain I M p U) (q : M) :
    h.toPartialDiffeomorph.toPartialEquiv.symm q = riemannianLog I M p U q := (rfl)

end IsNormalDomain

end TauCeti.Manifold

end
