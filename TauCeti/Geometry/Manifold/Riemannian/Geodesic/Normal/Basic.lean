/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

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
* `TauCeti.Manifold.IsNormalDomain.exists_partialDiffeomorph_riemannianExp_comp`: the
  exponential map precomposed with a linear isomorphism carrying an open set into a normal domain
  is a partial diffeomorphism with that open set as source.
* `TauCeti.Manifold.exists_isNormalDomain_ball`: balls of small enough radius are normal domains.
* `TauCeti.Manifold.exists_pos_maximalGeodesic_eq_iff_of_not_sameRay`: radial geodesics in
  directions on no common ray meet for small nonnegative parameters only at zero parameters.
* `TauCeti.Manifold.IsNormalDomain.ball`: a tangent ball contained in a normal domain is
  itself a normal domain.
* `TauCeti.Manifold.isCompact_riemannianExp_image_closedBall`: a closed tangent ball in the
  exponential domain has compact exponential image.
* `TauCeti.Manifold.isCompact_riemannianExp_image_sphere`: a tangent sphere in the exponential
  domain has compact exponential image.
* `TauCeti.Manifold.exists_isNormalDomain_ball_with_isCompact_riemannianExp_image_closedBall`:
  a smaller closed tangent ball inside a larger normal ball has compact exponential image.
* `TauCeti.Manifold.IsNormalDomain.isOpen_image`: a normal neighbourhood is open.
* `TauCeti.Manifold.IsNormalDomain.injective_mfderiv_riemannianExp`: the differential of the
  exponential map is injective on a normal domain.
* `TauCeti.Manifold.IsNormalDomain.contDiffOn_norm_angular_riemannianExp`: the length of the
  differential of the exponential map along a fixed vector is smooth on a normal domain.
* `TauCeti.Manifold.IsNormalDomain.opens`: a normal domain as an open subset of `T_p M`, on which
  the exponential map is smooth with invertible differential
  (`TauCeti.Manifold.IsNormalDomain.isInvertible_mfderiv_riemannianExp_comp_val`).
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_riemannianExp` and
  `TauCeti.Manifold.riemannianExp_riemannianLog`: the two inverse identities.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_eq_of_subset`: the logarithm does not depend on
  the normal domain.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_self`: the logarithm vanishes at the base point.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_eq_neg_mfderiv_riemannianExp_radial`: the
  logarithm of `p` at `exp_p v` is the negated arrival velocity `-d(exp_p)_v v`.
* `TauCeti.Manifold.IsNormalDomain.contMDiffOn_riemannianLog`: the logarithm is smooth on the
  normal neighbourhood.
* `TauCeti.Manifold.IsNormalDomain.mfderiv_riemannianLog_comp_mfderiv_riemannianExp` and
  `TauCeti.Manifold.IsNormalDomain.mfderiv_riemannianExp_comp_mfderiv_riemannianLog`: the
  differentials of the logarithm and the exponential map are mutually inverse.
* `TauCeti.Manifold.IsNormalDomain.mfderiv_riemannianLog_self_apply` and
  `TauCeti.Manifold.IsNormalDomain.mvfderiv_riemannianLog_self`: the differential of the logarithm
  at the base point is the identity.
* `MDifferentiableAt.hasFDerivAt_riemannianLog_comp_riemannianExp_zero`: the Fréchet derivative at
  `0` of `u ↦ log_{f p} (f (exp_p u))` is `mfderiv I J f p`.
* `TauCeti.Manifold.IsNormalDomain.mvfderiv_comp_riemannianLog_self`: composition with the
  logarithm preserves the scalar differential at the base point, without a regularity hypothesis.
* `TauCeti.Manifold.IsNormalDomain.mem_geodesicInterval` and
  `TauCeti.Manifold.IsNormalDomain.isGeodesicCurveOn_riemannianExp_smul_Icc`: the radial geodesic
  towards a vector of a normal domain is defined and a geodesic on `[0, 1]`.
* `TauCeti.Manifold.radialGeodesicHomotopyDomain` and `TauCeti.Manifold.radialGeodesicHomotopy`:
  the raw radial geodesic contraction `H(s, x) = exp_q (s • log_q x)` on a normal domain, its open
  natural domain, and its smoothness (`IsNormalDomain.contMDiffOn_radialGeodesicHomotopy`).

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5 and 6.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Bundle Function Manifold Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
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

variable {p : M} {U V : Set (TangentSpace I p)} {r : ℝ} {v : TangentSpace I p} {t : ℝ}

/-- An open star-shaped neighbourhood of the origin inside a normal domain is a normal domain. -/
theorem mono (h : IsNormalDomain I M p U) (hVU : V ⊆ U) (hV : IsOpen V)
    (hzero : (0 : TangentSpace I p) ∈ V) (hstar : StarConvex ℝ (0 : TangentSpace I p) V) :
    IsNormalDomain I M p V where
  isOpen := hV
  zero_mem := hzero
  starConvex := hstar
  subset_expDomain := hVU.trans h.subset_expDomain
  injOn := h.injOn.mono hVU
  isLocalDiffeomorphOn w := h.isLocalDiffeomorphOn ⟨w, hVU w.property⟩

/-- A tangent ball contained in a normal domain is itself a normal domain. -/
theorem ball (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U) (hr : 0 < r) :
    IsNormalDomain I M p (Metric.ball 0 r) :=
  h.mono hU Metric.isOpen_ball (Metric.mem_ball_self hr)
    ((convex_ball (0 : TangentSpace I p) r).starConvex (Metric.mem_ball_self hr))

/-- A normal neighbourhood is open. -/
theorem isOpen_image (h : IsNormalDomain I M p U) :
    IsOpen (riemannianExp I M p '' U) :=
  h.isLocalDiffeomorphOn.isLocalHomeomorphOn.isOpen_image h.isOpen

/-- The differential of the exponential map is injective at every vector of a normal domain. -/
theorem injective_mfderiv_riemannianExp (h : IsNormalDomain I M p U) (hv : v ∈ U) :
    Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v) :=
  ((h.isLocalDiffeomorphOn ⟨v, hv⟩).isInvertible_mfderiv (by simp)).injective

/-- A vector of a normal domain can be shrunk towards the origin inside the normal domain. -/
theorem smul_mem (h : IsNormalDomain I M p U) (hv : v ∈ U) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    t • v ∈ U :=
  starConvex_zero_iff.1 h.starConvex hv ht₀ ht₁

/-- **The radial geodesic of a normal domain is defined up to time one.**  The maximal geodesic
from `p` with initial velocity a vector `v` of a normal domain exists on `[0, 1]`; by
`riemannianExp_smul` its value at `t` is the exponential of `t • v`. -/
theorem mem_geodesicInterval (h : IsNormalDomain I M p U) (hv : v ∈ U)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : t ∈ geodesicInterval I M p v :=
  ordConnected_geodesicInterval.out
    (zero_mem_geodesicInterval_of_mem (mem_expDomain_iff.1 (h.subset_expDomain hv)))
    (mem_expDomain_iff.1 (h.subset_expDomain hv)) ⟨ht₀, ht₁⟩

/-- A normal domain, as an open subset of the tangent space. -/
def opens (h : IsNormalDomain I M p U) : TopologicalSpace.Opens (TangentSpace I p) :=
  ⟨U, h.isOpen⟩

@[simp]
theorem coe_opens (h : IsNormalDomain I M p U) : (h.opens : Set (TangentSpace I p)) = U :=
  (rfl)

@[simp]
theorem mem_opens (h : IsNormalDomain I M p U) : v ∈ h.opens ↔ v ∈ U :=
  Iff.rfl

/-- The origin belongs to a normal domain, seen as an open subset of the tangent space. -/
theorem zero_mem_opens (h : IsNormalDomain I M p U) : (0 : TangentSpace I p) ∈ h.opens :=
  h.mem_opens.2 h.zero_mem

/-- A normal domain, seen as an open subset of the tangent space, is star-shaped about the
origin. -/
theorem starConvex_opens (h : IsNormalDomain I M p U) :
    StarConvex ℝ (0 : TangentSpace I p) (h.opens : Set (TangentSpace I p)) := by
  rw [coe_opens]
  exact h.starConvex

/-- The exponential map is smooth on a normal domain. -/
theorem contMDiff_riemannianExp_comp_val (h : IsNormalDomain I M p U) {n : ℕ∞ω}
    (hn : n ≤ ∞ + 1) :
    ContMDiff 𝓘(ℝ, TangentSpace I p) I n
      (riemannianExp I M p ∘ (Subtype.val : h.opens → TangentSpace I p)) := by
  intro v
  have h' : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      (v : TangentSpace I p) :=
    h.isLocalDiffeomorphOn ⟨v, h.mem_opens.1 v.property⟩
  exact (h'.contMDiffAt.of_le (by simpa using hn)).comp v contMDiff_subtypeVal.contMDiffAt

/-- On a normal domain, the differential of the exponential map read on the open subset is the
differential of the exponential map, after identifying the tangent spaces of the open subset and
of `T_p M`. -/
theorem mfderiv_riemannianExp_comp_val (h : IsNormalDomain I M p U) (v : h.opens) :
    mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p ∘ (Subtype.val : h.opens → TangentSpace I p)) v =
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).comp
        (tangentSpaceOpenEquiv (I := 𝓘(ℝ, TangentSpace I p)) v).toContinuousLinearMap := by
  have h' : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      (v : TangentSpace I p) :=
    h.isLocalDiffeomorphOn ⟨v, h.mem_opens.1 v.property⟩
  rw [mfderiv_comp v (h'.contMDiffAt.mdifferentiableAt (by simp))
    (contMDiff_subtypeVal.contMDiffAt.mdifferentiableAt one_ne_zero),
    mfderiv_subtype_val (I := 𝓘(ℝ, TangentSpace I p)) v]

/-- The exponential map has invertible differential on a normal domain. -/
theorem isInvertible_mfderiv_riemannianExp_comp_val (h : IsNormalDomain I M p U)
    (v : h.opens) :
    (mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p ∘ (Subtype.val : h.opens → TangentSpace I p)) v).IsInvertible := by
  rw [h.mfderiv_riemannianExp_comp_val v]
  exact ((h.isLocalDiffeomorphOn ⟨v, h.mem_opens.1 v.property⟩).isInvertible_mfderiv (by simp)).comp
    ContinuousLinearMap.isInvertible_equiv

variable [I.Boundaryless] [T2Space M]

/-- **The radial segment of a normal domain is a geodesic on `[0, 1]`.** -/
theorem isGeodesicCurveOn_riemannianExp_smul_Icc (h : IsNormalDomain I M p U) (hv : v ∈ U) :
    IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) :=
  ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono
    (uniqueDiffOn_Icc zero_lt_one) fun _ ht ↦ h.mem_geodesicInterval hv ht.1 ht.2).congr
      fun t _ ↦ riemannianExp_smul p v t

/-- The base point belongs to every normal neighbourhood. -/
theorem self_mem_image (h : IsNormalDomain I M p U) : p ∈ riemannianExp I M p '' U :=
  ⟨0, h.zero_mem, riemannianExp_zero p⟩

/-- A normal neighbourhood is a neighbourhood of the base point. -/
theorem image_mem_nhds (h : IsNormalDomain I M p U) :
    riemannianExp I M p '' U ∈ 𝓝 p :=
  h.isOpen_image.mem_nhds h.self_mem_image

/-- The Riemannian length of the differential of the exponential map, applied to a fixed tangent
vector `w`, is smooth on any normal domain, where that differential is injective. -/
theorem contDiffOn_norm_angular_riemannianExp {w : TangentSpace I p}
    (h : IsNormalDomain I M p U) :
    ContDiffOn ℝ ∞ (fun z : TangentSpace I p ↦
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z w‖) U := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact (contDiffOn_const (c := (0 : ℝ))).congr fun z _ ↦
      (congrArg norm (map_zero _)).trans norm_zero
  have hinner := (contDiffOn_inner_angular_riemannianExp (I := I) p w).mono
    h.subset_expDomain
  have hsqrt := hinner.sqrt fun z hz ↦ by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (fun hzero ↦ hw
      (h.injective_mfderiv_riemannianExp hz (hzero.trans (map_zero _).symm))))
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using hsqrt

end IsNormalDomain

section

variable [I.Boundaryless] [T2Space M]

/-! ### Existence of normal balls -/

/-- **Normal balls exist.**  There is a positive radius such that the ball of that radius around
the origin of `T_p M` is a normal domain at `p`; its image is a normal neighbourhood of `p`. -/
theorem exists_isNormalDomain_ball (p : M) :
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
    fun v => (hball v.property).1⟩

/-- **Radial geodesics in different directions separate.** If the tangent vectors `v` and
`w` at `p` do not lie on a common ray, the radial geodesics from `p` with these initial
velocities meet for small nonnegative parameters exactly when both parameters vanish. -/
theorem exists_pos_maximalGeodesic_eq_iff_of_not_sameRay {p : M} {v w : TangentSpace I p}
    (hvw : ¬ SameRay ℝ v w) :
    ∃ ε > 0, ∀ a ∈ Ico 0 ε, ∀ b ∈ Ico 0 ε,
      maximalGeodesic I M p v a = maximalGeodesic I M p w b ↔ a = 0 ∧ b = 0 := by
  obtain ⟨r, hr, hN⟩ := exists_isNormalDomain_ball (I := I) p
  have hmem {x : TangentSpace I p} {a : ℝ} (ha : a ∈ Ico 0 (r / (‖x‖ + 1))) :
      a • x ∈ ball (0 : TangentSpace I p) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
    have h := ha.2
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [norm_nonneg x, ha.1]
  refine ⟨min (r / (‖v‖ + 1)) (r / (‖w‖ + 1)), by positivity, fun a ha b hb ↦ ?_⟩
  refine ⟨fun hab ↦ ?_, ?_⟩
  · have hav := hmem (x := v) ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
    have hbw := hmem (x := w) ⟨hb.1, hb.2.trans_le (min_le_right _ _)⟩
    rw [← riemannianExp_smul, ← riemannianExp_smul] at hab
    have heq := hN.injOn hav hbw hab
    by_cases ha0 : a = 0
    · refine ⟨ha0, ?_⟩
      have hw : w ≠ 0 := fun hw ↦ hvw (by simp [hw])
      simpa [ha0, hw] using heq.symm
    · by_cases hb0 : b = 0
      · have hv : v ≠ 0 := fun hv ↦ hvw (by simp [hv])
        have : a = 0 := by simpa [hb0, hv] using heq
        exact (ha0 this).elim
      · exact (hvw (Or.inr (Or.inr ⟨a, b, lt_of_le_of_ne ha.1 (Ne.symm ha0),
          lt_of_le_of_ne hb.1 (Ne.symm hb0), heq⟩))).elim
  · rintro ⟨rfl, rfl⟩
    simp

/-! ### Compactly contained normal balls -/

/-- The exponential image of a closed tangent ball contained in the exponential domain is
compact. -/
theorem isCompact_riemannianExp_image_closedBall
    (p : M) {r : ℝ} (hr : Metric.closedBall 0 r ⊆ expDomain I M p) :
    IsCompact (riemannianExp I M p '' Metric.closedBall 0 r) := by
  apply (isCompact_closedBall (0 : TangentSpace I p) r).image_of_continuousOn
  exact (continuousOn_riemannianExp (I := I) (M := M) p).mono hr

/-- The exponential image of a tangent sphere contained in the exponential domain is compact. -/
theorem isCompact_riemannianExp_image_sphere
    (p : M) {r : ℝ} (hr : Metric.sphere 0 r ⊆ expDomain I M p) :
    IsCompact (riemannianExp I M p '' Metric.sphere 0 r) := by
  apply (isCompact_sphere (0 : TangentSpace I p) r).image_of_continuousOn
  exact (continuousOn_riemannianExp (I := I) (M := M) p).mono hr

/-- **Normal balls can be chosen compactly contained in a larger normal ball.** More precisely,
there are positive radii `r < R` such that the ball of radius `R` is a normal domain and the
closed ball of radius `r` is contained in it.  The exponential image of that closed ball is
compact.

The nested tangent balls and compact exponential image are inputs to the escape estimate for
curves leaving a normal neighbourhood. -/
theorem exists_isNormalDomain_ball_with_isCompact_riemannianExp_image_closedBall
    (p : M) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ IsNormalDomain I M p (Metric.ball 0 R) ∧
      Metric.closedBall 0 r ⊆ Metric.ball 0 R ∧
      IsCompact (riemannianExp I M p '' Metric.closedBall 0 r) := by
  obtain ⟨R, hR, hRnormal⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  refine ⟨R / 2, R, half_pos hR, half_lt_self hR, hRnormal,
    Metric.closedBall_subset_ball (half_lt_self hR), ?_⟩
  exact isCompact_riemannianExp_image_closedBall (I := I) (M := M) p
    ((Metric.closedBall_subset_ball (half_lt_self hR)).trans hRnormal.subset_expDomain)

end

/-! ### The Riemannian logarithm -/

variable (I M) in
/-- The **Riemannian logarithm** at `p` relative to a set `U` of tangent vectors, defined as the
chosen preimage function `invFunOn` for the restriction of `exp_p` to `U`.  When `U` is a normal
domain, it inverts `exp_p` on the normal neighbourhood `exp_p '' U`; outside that neighbourhood
it takes a junk value, so every theorem about its value carries a membership hypothesis. -/
def riemannianLog (p : M) (U : Set (TangentSpace I p)) : M → TangentSpace I p :=
  invFunOn (riemannianExp I M p) U

/-- The Riemannian logarithm relative to `U` is `invFunOn` for `exp_p` restricted to `U`. -/
theorem riemannianLog_def (p : M) (U : Set (TangentSpace I p)) :
    riemannianLog I M p U = invFunOn (riemannianExp I M p) U := by
  rfl

section

variable {p : M} {U : Set (TangentSpace I p)} {q : M}

/-- The logarithm of a point of `exp_p '' U` lies in `U`. -/
theorem riemannianLog_mem (hq : q ∈ riemannianExp I M p '' U) :
    riemannianLog I M p U q ∈ U := by
  rw [riemannianLog_def]
  exact invFunOn_mem hq

/-- **The exponential map inverts the logarithm** on `exp_p '' U`. -/
@[simp] theorem riemannianExp_riemannianLog (hq : q ∈ riemannianExp I M p '' U) :
    riemannianExp I M p (riemannianLog I M p U q) = q := by
  rw [riemannianLog_def]
  exact invFunOn_eq hq

end

namespace IsNormalDomain

variable {p : M} {U : Set (TangentSpace I p)} {v : TangentSpace I p} {q : M}

/-- **The logarithm inverts the exponential map** on a normal domain. -/
@[simp] theorem riemannianLog_riemannianExp (h : IsNormalDomain I M p U) (hv : v ∈ U) :
    riemannianLog I M p U (riemannianExp I M p v) = v := by
  rw [riemannianLog_def]
  exact h.injOn.leftInvOn_invFunOn hv

/-- The logarithm does not depend on the normal domain: on the normal neighbourhood of a smaller
set `U ⊆ V`, the logarithms relative to `U` and to the normal domain `V` agree. -/
theorem riemannianLog_eq_of_subset {V : Set (TangentSpace I p)} (h : IsNormalDomain I M p V)
    (hUV : U ⊆ V) (hq : q ∈ riemannianExp I M p '' U) :
    riemannianLog I M p U q = riemannianLog I M p V q := by
  conv_rhs => rw [← riemannianExp_riemannianLog hq]
  exact (h.riemannianLog_riemannianExp (hUV (riemannianLog_mem hq))).symm

/-- **The Riemannian logarithm is smooth** on the normal neighbourhood it inverts. -/
theorem contMDiffOn_riemannianLog (h : IsNormalDomain I M p U) :
    ContMDiffOn I 𝓘(ℝ, TangentSpace I p) ∞ (riemannianLog I M p U)
      (riemannianExp I M p '' U) := by
  rw [riemannianLog_def]
  exact h.isLocalDiffeomorphOn.contMDiffOn_invFunOn h.isOpen h.injOn

/-- The Riemannian logarithm is differentiable at every point of the normal neighbourhood. -/
theorem mdifferentiableAt_riemannianLog (h : IsNormalDomain I M p U)
    (hq : q ∈ riemannianExp I M p '' U) :
    MDifferentiableAt I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) q :=
  (h.contMDiffOn_riemannianLog.contMDiffAt (h.isOpen_image.mem_nhds hq)).mdifferentiableAt
    (by simp)

/-- The Riemannian logarithm is continuous on the normal neighbourhood it inverts. -/
theorem continuousOn_riemannianLog (h : IsNormalDomain I M p U) :
    ContinuousOn (riemannianLog I M p U) (riemannianExp I M p '' U) :=
  h.contMDiffOn_riemannianLog.continuousOn

/-- The exponential map and Riemannian logarithm as a partial diffeomorphism from a normal domain
to its normal neighbourhood. -/
def toPartialDiffeomorph (h : IsNormalDomain I M p U) :
    PartialDiffeomorph (modelWithCornersSelf ℝ (TangentSpace I p)) I
      (TangentSpace I p) M ∞ :=
  h.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn h.isOpen h.injOn

/-- The source of the normal-domain partial diffeomorphism is the normal domain. -/
@[simp] theorem toPartialDiffeomorph_source (h : IsNormalDomain I M p U) :
    h.toPartialDiffeomorph.source = U := by
  simp [toPartialDiffeomorph]

/-- The target of the normal-domain partial diffeomorphism is the normal neighbourhood. -/
@[simp] theorem toPartialDiffeomorph_target (h : IsNormalDomain I M p U) :
    h.toPartialDiffeomorph.target = riemannianExp I M p '' U := by
  simp [toPartialDiffeomorph]

/-- The forward map of the normal-domain partial diffeomorphism is the exponential map. -/
@[simp] theorem coe_toPartialDiffeomorph (h : IsNormalDomain I M p U) :
    ⇑h.toPartialDiffeomorph = riemannianExp I M p := by
  simp [toPartialDiffeomorph]

/-- The inverse map of the normal-domain partial diffeomorphism is the Riemannian logarithm. -/
@[simp] theorem toPartialDiffeomorph_symm_apply (h : IsNormalDomain I M p U) (q : M) :
    h.toPartialDiffeomorph.toPartialEquiv.symm q = riemannianLog I M p U q := by
  simp [toPartialDiffeomorph, riemannianLog_def]

/-- The exponential map precomposed with a linear isomorphism that maps an open set into a normal
domain is a partial diffeomorphism with that open set as source. -/
theorem exists_partialDiffeomorph_riemannianExp_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : IsNormalDomain I M p U) (A : F ≃L[ℝ] TangentSpace I p)
    {s : Set F} (hs : IsOpen s) (hmap : MapsTo A s U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞,
      Φ.source = s ∧ ⇑Φ = riemannianExp I M p ∘ A := by
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, F) I ∞ (riemannianExp I M p ∘ A) s := by
    intro x
    have hA := A.toDiffeomorph.isLocalDiffeomorph x.val
    rw [ContinuousLinearEquiv.coe_toDiffeomorph] at hA
    exact IsLocalDiffeomorphAt.comp I M hA (h.isLocalDiffeomorphOn ⟨A x, hmap x.property⟩)
  have hinj : InjOn (riemannianExp I M p ∘ A) s := fun x hx y hy hxy ↦
    A.injective (h.injOn (hmap hx) (hmap hy) hxy)
  exact ⟨hlocal.partialDiffeomorphOfInjOn hs hinj,
    hlocal.partialDiffeomorphOfInjOn_source hs hinj,
    hlocal.coe_partialDiffeomorphOfInjOn hs hinj⟩

variable [I.Boundaryless] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
/-- The differential of the logarithm at `exp_p v` is a left inverse of the differential of the
exponential map at a vector `v` of the normal domain. -/
theorem mfderiv_riemannianLog_comp_mfderiv_riemannianExp (h : IsNormalDomain I M p U)
    (hv : v ∈ U) :
    mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) (riemannianExp I M p v) ∘L
        mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v =
      ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  have hq : riemannianExp I M p v ∈ riemannianExp I M p '' U := mem_image_of_mem _ hv
  have heq : riemannianLog I M p U ∘ riemannianExp I M p =ᶠ[𝓝 v] id :=
    Filter.eventually_of_mem (h.isOpen.mem_nhds hv) fun u hu ↦ h.riemannianLog_riemannianExp hu
  exact hasMFDerivAt_unique
    ((h.mdifferentiableAt_riemannianLog hq).hasMFDerivAt.comp v
      ((h.isLocalDiffeomorphOn ⟨v, hv⟩).contMDiffAt.mdifferentiableAt
        (by simp)).hasMFDerivAt)
    ((hasMFDerivAt_id v).congr_of_eventuallyEq_abuse heq)

omit [I.Boundaryless] [T2Space M] in
/-- The differential of the logarithm at `exp_p v` is a right inverse of the differential of the
exponential map at a vector `v` of the normal domain. -/
theorem mfderiv_riemannianExp_comp_mfderiv_riemannianLog (h : IsNormalDomain I M p U)
    (hv : v ∈ U) :
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ∘L
        mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) (riemannianExp I M p v) =
      ContinuousLinearMap.id ℝ (TangentSpace I (riemannianExp I M p v)) := by
  have hq : riemannianExp I M p v ∈ riemannianExp I M p '' U := mem_image_of_mem _ hv
  have heq : riemannianExp I M p ∘ riemannianLog I M p U =ᶠ[𝓝 (riemannianExp I M p v)] id :=
    Filter.eventually_of_mem (h.isOpen_image.mem_nhds hq) fun q hq ↦
      riemannianExp_riemannianLog hq
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
      (riemannianLog I M p U (riemannianExp I M p v)) := by
    rw [h.riemannianLog_riemannianExp hv]
    exact (h.isLocalDiffeomorphOn ⟨v, hv⟩).contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := hasMFDerivAt_unique
    (hexp.hasMFDerivAt.comp (riemannianExp I M p v)
      (h.mdifferentiableAt_riemannianLog hq).hasMFDerivAt)
    ((hasMFDerivAt_id (riemannianExp I M p v)).congr_of_eventuallyEq_abuse heq)
  rwa [h.riemannianLog_riemannianExp hv] at hcomp

omit [I.Boundaryless] [T2Space M] in
/-- The differential of the logarithm is invertible at every point of the normal
neighbourhood. -/
theorem isInvertible_mfderiv_riemannianLog (h : IsNormalDomain I M p U)
    (hq : q ∈ riemannianExp I M p '' U) :
    (mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) q).IsInvertible := by
  obtain ⟨v, hv, rfl⟩ := hq
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (h.mfderiv_riemannianLog_comp_mfderiv_riemannianExp hv)
    (h.mfderiv_riemannianExp_comp_mfderiv_riemannianLog hv)

/-- The logarithm vanishes at the base point. -/
@[simp] theorem riemannianLog_self (h : IsNormalDomain I M p U) :
    riemannianLog I M p U p = 0 := by
  have h0 := h.riemannianLog_riemannianExp h.zero_mem
  rwa [riemannianExp_zero] at h0

/-- **The logarithm of the base point along a radial geodesic.** If `v` lies in the domain of
`exp_p` and `-d(exp_p)_v v` lies in a normal domain `V` at `exp_p v`, then `log_{exp_p v} p` is
the negated arrival velocity `-d(exp_p)_v v`. -/
theorem riemannianLog_eq_neg_mfderiv_riemannianExp_radial
    {V : Set (TangentSpace I (riemannianExp I M p v))}
    (hq : IsNormalDomain I M (riemannianExp I M p v) V) (hv : v ∈ expDomain I M p)
    (hw : -mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v ∈ V) :
    riemannianLog I M (riemannianExp I M p v) V p =
      -mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v := by
  have hrev := riemannianExp_neg_mfderiv_riemannianExp_radial hv
  simpa only [hrev] using hq.riemannianLog_riemannianExp hw

/-- The differential of the logarithm at the base point is the identity. -/
@[simp] theorem mfderiv_riemannianLog_self_apply (h : IsNormalDomain I M p U)
    (v : TangentSpace I p) :
    mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) p v = v := by
  have hcomp := DFunLike.congr_fun
    (h.mfderiv_riemannianLog_comp_mfderiv_riemannianExp h.zero_mem) v
  -- The composite runs through `TangentSpace I (riemannianExp I M p 0)`, which is only
  -- definitionally `TangentSpace I p`, so `ContinuousLinearMap.comp_apply` and `id_apply` do not
  -- match syntactically under `rw` or `simp`; unfold the application by defeq instead.
  change mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) (riemannianExp I M p 0)
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v) = v at hcomp
  rwa [mfderiv_riemannianExp_apply_zero, riemannianExp_zero] at hcomp

/-- The vector-valued differential of the logarithm at the base point is the identity. -/
@[simp] theorem mvfderiv_riemannianLog_self (h : IsNormalDomain I M p U) :
    mvfderiv I (riemannianLog I M p U) p = ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  ext v
  simp only [mvfderiv_apply_eq_mfderiv_apply, h.mfderiv_riemannianLog_self_apply,
    ContinuousLinearMap.id_apply]

/-- At the center, composition with the logarithm preserves the scalar differential. -/
theorem mvfderiv_comp_riemannianLog_self (h : IsNormalDomain I M p U)
    (P : TangentSpace I p → ℝ) :
    mvfderiv I (P ∘ riemannianLog I M p U) p = fderiv ℝ P 0 := by
  by_cases hP : DifferentiableAt ℝ P 0
  · have hdP : DifferentiableAt ℝ P (riemannianLog I M p U p) := by
      simpa only [h.riemannianLog_self] using hP
    ext v
    rw [mvfderiv_comp_apply_of_differentiableAt hdP
      (h.mdifferentiableAt_riemannianLog h.self_mem_image), h.mvfderiv_riemannianLog_self,
      ContinuousLinearMap.id_apply, h.riemannianLog_self]
  · have heq : (P ∘ riemannianLog I M p U) ∘ riemannianExp I M p =ᶠ[𝓝 0] P := by
      filter_upwards [h.isOpen.mem_nhds h.zero_mem] with v hv
      simp only [Function.comp_apply, h.riemannianLog_riemannianExp hv]
    have hnot : ¬MDifferentiableAt I 𝓘(ℝ) (P ∘ riemannianLog I M p U) p := by
      intro hcomp
      have hcomp' : MDifferentiableAt I 𝓘(ℝ) (P ∘ riemannianLog I M p U)
          (riemannianExp I M p 0) := by simpa only [riemannianExp_zero] using hcomp
      have hd := hcomp'.comp 0
        ((contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt (by simp))
      exact hP (heq.mdifferentiableAt_iff.mp hd).differentiableAt
    rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnot,
      fderiv_zero_of_not_differentiableAt hP, ContinuousLinearMap.comp_zero]

end IsNormalDomain

/-! ### Radial geodesic homotopy on a normal domain -/

section RadialHomotopy

variable (I M) in
/-- The natural domain of the raw radial geodesic homotopy centered at `q` on a tangent set `U`:
pairs `(s, x) ∈ ℝ × M` with `x ∈ exp_q '' U` and `s • log_q x ∈ expDomain`. -/
def radialGeodesicHomotopyDomain (q : M) (U : Set (TangentSpace I q)) : Set (ℝ × M) :=
  {p : ℝ × M | p.2 ∈ riemannianExp I M q '' U ∧
    p.1 • riemannianLog I M q U p.2 ∈ expDomain I M q}

@[simp]
theorem mem_radialGeodesicHomotopyDomain_iff {q : M} {U : Set (TangentSpace I q)} {p : ℝ × M} :
    p ∈ radialGeodesicHomotopyDomain I M q U ↔
      p.2 ∈ riemannianExp I M q '' U ∧ p.1 • riemannianLog I M q U p.2 ∈ expDomain I M q := by
  rw [radialGeodesicHomotopyDomain]
  rfl

variable (I M) in
/-- The raw radial geodesic contraction `H(s, x) = exp_q (s • log_q x)` centered at `q` using a
tangent set `U`. -/
def radialGeodesicHomotopy (q : M) (U : Set (TangentSpace I q)) (p : ℝ × M) : M :=
  riemannianExp I M q (p.1 • riemannianLog I M q U p.2)

theorem radialGeodesicHomotopy_def (q : M) (U : Set (TangentSpace I q)) (p : ℝ × M) :
    radialGeodesicHomotopy I M q U p =
      riemannianExp I M q (p.1 • riemannianLog I M q U p.2) := by
  rw [radialGeodesicHomotopy]

theorem radialGeodesicHomotopy_one_left {q : M} {U : Set (TangentSpace I q)} {x : M}
    (hx : x ∈ riemannianExp I M q '' U) :
    radialGeodesicHomotopy I M q U (1, x) = x := by
  simp [radialGeodesicHomotopy, riemannianExp_riemannianLog hx]

/-- The raw radial geodesic homotopy does not depend on the normal domain: on the normal
neighbourhood of a smaller set `V ⊆ U`, the homotopies relative to `V` and `U` agree. -/
theorem IsNormalDomain.radialGeodesicHomotopy_eq_of_subset {q x : M}
    {U V : Set (TangentSpace I q)} (hq : IsNormalDomain I M q U) (hVU : V ⊆ U)
    (hx : x ∈ riemannianExp I M q '' V) (s : ℝ) :
    radialGeodesicHomotopy I M q V (s, x) = radialGeodesicHomotopy I M q U (s, x) := by
  rw [radialGeodesicHomotopy_def, radialGeodesicHomotopy_def, hq.riemannianLog_eq_of_subset hVU hx]

/-- The raw radial geodesic homotopy at `(s, x)` does not depend on the normal ball radius once `x`
lies in both normal balls. -/
theorem radialGeodesicHomotopy_ball_eq_of_isNormalDomain {q x : M} {r₁ r₂ : ℝ} (s : ℝ)
    (hq₁ : IsNormalDomain I M q (Metric.ball 0 r₁))
    (hq₂ : IsNormalDomain I M q (Metric.ball 0 r₂))
    (hx₁ : x ∈ riemannianExp I M q '' Metric.ball 0 r₁)
    (hx₂ : x ∈ riemannianExp I M q '' Metric.ball 0 r₂) :
    radialGeodesicHomotopy I M q (Metric.ball 0 r₁) (s, x) =
      radialGeodesicHomotopy I M q (Metric.ball 0 r₂) (s, x) := by
  rcases le_total r₁ r₂ with hle | hle
  · exact hq₂.radialGeodesicHomotopy_eq_of_subset (Metric.ball_subset_ball hle) hx₁ s
  · exact (hq₁.radialGeodesicHomotopy_eq_of_subset (Metric.ball_subset_ball hle) hx₂ s).symm

/-- For any subset `W ⊆ exp_q '' U` of a normal neighbourhood, the cylinder `[0, 1] ×ˢ W` lies in
`radialGeodesicHomotopyDomain I M q U`. -/
theorem IsNormalDomain.Icc_prod_subset_radialGeodesicHomotopyDomain {q : M}
    {U : Set (TangentSpace I q)} (hq : IsNormalDomain I M q U) {W : Set M}
    (hW : W ⊆ riemannianExp I M q '' U) :
    Icc (0 : ℝ) 1 ×ˢ W ⊆ radialGeodesicHomotopyDomain I M q U := by
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  rw [mem_radialGeodesicHomotopyDomain_iff]
  exact ⟨hW hx, hq.subset_expDomain (hq.smul_mem (riemannianLog_mem (hW hx)) hs.1 hs.2)⟩

/-- On a normal domain `U` at `q`, the raw radial geodesic homotopy maps `[0, 1] ×ˢ (exp_q '' U)`
into `exp_q '' U`. -/
theorem IsNormalDomain.mapsTo_radialGeodesicHomotopy {q : M} {U : Set (TangentSpace I q)}
    (hq : IsNormalDomain I M q U) :
    MapsTo (radialGeodesicHomotopy I M q U) (Icc (0 : ℝ) 1 ×ˢ (riemannianExp I M q '' U))
      (riemannianExp I M q '' U) := by
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  exact ⟨s • riemannianLog I M q U x, hq.smul_mem (riemannianLog_mem hx) hs.1 hs.2, rfl⟩

variable [I.Boundaryless] [T2Space M]

@[simp]
theorem radialGeodesicHomotopy_zero_left (q : M) (U : Set (TangentSpace I q)) (x : M) :
    radialGeodesicHomotopy I M q U (0, x) = q := by
  simp [radialGeodesicHomotopy]

@[simp]
theorem IsNormalDomain.radialGeodesicHomotopy_self_right {q : M} {U : Set (TangentSpace I q)}
    (hq : IsNormalDomain I M q U) (s : ℝ) :
    radialGeodesicHomotopy I M q U (s, q) = q := by
  simp [radialGeodesicHomotopy, hq.riemannianLog_self]

/-- When `U` is a normal domain at `q`, the natural domain of `radialGeodesicHomotopy` is open in
`ℝ × M`. -/
theorem IsNormalDomain.isOpen_radialGeodesicHomotopyDomain {q : M} {U : Set (TangentSpace I q)}
    (hq : IsNormalDomain I M q U) :
    IsOpen (radialGeodesicHomotopyDomain I M q U) := by
  let V := riemannianExp I M q '' U
  have hcont : ContinuousOn (fun p : ℝ × M ↦ p.1 • riemannianLog I M q U p.2) (univ ×ˢ V) :=
    continuousOn_fst.smul (hq.continuousOn_riemannianLog.comp continuousOn_snd fun _ hp ↦ hp.2)
  have hopen := hcont.isOpen_inter_preimage (isOpen_univ.prod hq.isOpen_image) (isOpen_expDomain q)
  have heq : (univ ×ˢ V) ∩
      (fun p : ℝ × M ↦ p.1 • riemannianLog I M q U p.2) ⁻¹' expDomain I M q =
      radialGeodesicHomotopyDomain I M q U := by
    ext ⟨s, x⟩
    simp [radialGeodesicHomotopyDomain, V]
  rwa [← heq]

/-- On a normal domain `U` at `q`, the raw radial geodesic homotopy is smooth on its open domain
`radialGeodesicHomotopyDomain I M q U`. -/
theorem IsNormalDomain.contMDiffOn_radialGeodesicHomotopy {q : M} {U : Set (TangentSpace I q)}
    (hq : IsNormalDomain I M q U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I ∞ (radialGeodesicHomotopy I M q U)
      (radialGeodesicHomotopyDomain I M q U) := by
  intro p hp
  rw [mem_radialGeodesicHomotopyDomain_iff] at hp
  have hlog : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, TangentSpace I q) ∞
      (fun u : ℝ × M ↦ riemannianLog I M q U u.2) p :=
    (hq.contMDiffOn_riemannianLog.contMDiffAt
      (hq.isOpen_image.mem_nhds hp.1)).comp p contMDiffAt_snd
  have hsmul : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, TangentSpace I q) ∞
      (fun u : ℝ × M ↦ u.1 • riemannianLog I M q U u.2) p :=
    contMDiffAt_fst.smul hlog
  exact ((contMDiffAt_riemannianExp hp.2).comp p hsmul).contMDiffWithinAt

end RadialHomotopy

end TauCeti.Manifold

namespace MDifferentiableAt

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- The Fréchet derivative at `0` of the normal-coordinate representative
`u ↦ log_{f p} (f (exp_p u))` of a map `f : M → N` differentiable at `p` is `df_p`. -/
theorem hasFDerivAt_riemannianLog_comp_riemannianExp_zero {f : M → N} {p : M}
    (hf : MDifferentiableAt I J f p) {V : Set (TangentSpace J (f p))}
    (hN : IsNormalDomain J N (f p) V) :
    HasFDerivAt (fun u ↦ riemannianLog J N (f p) V (f (riemannianExp I M p u)))
      (mfderiv I J f p) 0 := by
  set L : N → TangentSpace J (f p) := riemannianLog J N (f p) V
  set Ψ : TangentSpace I p → TangentSpace J (f p) := (L ∘ f) ∘ riemannianExp I M p
  have hL : MDifferentiableAt J 𝓘(ℝ, TangentSpace J (f p)) L (f p) :=
    hN.mdifferentiableAt_riemannianLog hN.self_mem_image
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 :=
    (contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt (by simp)
  have hLf : MDifferentiableAt I 𝓘(ℝ, TangentSpace J (f p)) (L ∘ f) p := hL.comp p hf
  have hΨ_diff : DifferentiableAt ℝ Ψ 0 :=
    mdifferentiableAt_iff_differentiableAt.1 (hLf.comp_of_eq 0 hexp (riemannianExp_zero p))
  have hfderiv : fderiv ℝ Ψ 0 = mfderiv I J f p := by
    ext v
    let v₀ : TangentSpace 𝓘(ℝ, TangentSpace I p) (0 : TangentSpace I p) :=
      (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).symm v
    calc fderiv ℝ Ψ 0 v
        = mvfderiv 𝓘(ℝ, TangentSpace I p) Ψ 0 v₀ := by
            rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
              ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      _ = mvfderiv I (L ∘ f) p (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v₀) :=
            mvfderiv_comp_apply_of_eq 0 hLf hexp (riemannianExp_zero p) v₀
      _ = mvfderiv I (L ∘ f) p v :=
            congrArg (mvfderiv I (L ∘ f) p) <|
              (congrArg (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0)
                (NormedSpace.fromTangentSpace_symm_apply (𝕜 := ℝ) (0 : TangentSpace I p) v)).trans
                (mfderiv_riemannianExp_apply_zero (I := I) p v)
      _ = mfderiv I J f p v := by
            rw [mvfderiv_comp_apply p hL hf v, hN.mvfderiv_riemannianLog_self,
              ContinuousLinearMap.id_apply]
  exact hfderiv ▸ hΨ_diff.hasFDerivAt

end MDifferentiableAt

end
