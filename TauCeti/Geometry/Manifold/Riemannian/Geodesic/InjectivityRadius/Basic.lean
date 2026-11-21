/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ExpKernel

/-!
# The injectivity radius of a Riemannian manifold

The *injectivity radius* `inj(p)` at a point `p` of a smooth Riemannian manifold `M` is the
supremum in `[0, ∞]` of the radii `r` for which the open tangent ball `B(0, r) ⊆ T_p M` is a normal
domain (`TauCeti.Manifold.IsNormalDomain`). Defining it via normal domains makes `inj(p)` and the
global injectivity radius `inj(M) = ⨅ p, inj(p)` apply before an intrinsic metric instance is
installed (e.g. on embedded spheres); the metric-ball characterization is proved in
`TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Distance`.

## Main definitions

* `TauCeti.Manifold.injectivityRadiusAt`: the pointwise injectivity radius `inj(p) : ℝ≥0∞`.
* `TauCeti.Manifold.injectivityRadius`: the global injectivity radius `inj(M) = ⨅ p, inj(p) : ℝ≥0∞`.

## Main results

* `TauCeti.Manifold.isNormalDomain_ball_iff_ofReal_le_injectivityRadiusAt`,
  `TauCeti.Manifold.isNormalDomain_eball_iff_le_injectivityRadiusAt`,
  `TauCeti.Manifold.isNormalDomain_eball_injectivityRadiusAt`,
  `TauCeti.Manifold.injectivityRadiusAt_eq_top_iff_isNormalDomain_univ`: exact attainment of the
  supremum on open balls (real or extended, including `⊤`).
* `TauCeti.Manifold.injectivityRadiusAt_le_of_notMem_expDomain`,
  `TauCeti.Manifold.injectivityRadiusAt_le_of_not_injective_mfderiv_riemannianExp`,
  `TauCeti.Manifold.injectivityRadiusAt_le_of_isConjugateOn`,
  `TauCeti.Manifold.injectivityRadiusAt_le_max_of_riemannianExp_eq`: upper bounds from
  incompleteness, critical/conjugate vectors, and colliding geodesics.
* `TauCeti.Manifold.injectivityRadiusAt_pos`, `IsCompact.exists_pos_forall_le_injectivityRadiusAt`,
  `TauCeti.Manifold.injectivityRadius_pos`: strict positivity on boundaryless Hausdorff manifolds
  and uniform positive lower bounds on compact sets and compact manifolds.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Definition 4.1.23, p. 151.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 6
  and 10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 3, §3 and Chapter 13, §2.
-/

public section

open Bundle Filter Function Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Definitions and basic order properties -/

variable (I M) in
/-- The **injectivity radius** `inj(p)` of a Riemannian manifold `M` at a point `p`, valued in
`ℝ≥0∞`: the supremum of the radii `r` for which the open tangent ball `B(0, r) ⊆ T_p M` is a normal
domain (`IsNormalDomain`). -/
def injectivityRadiusAt (p : M) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : IsNormalDomain I M p (Metric.ball 0 r)), ENNReal.ofReal r

variable (I M) in
/-- The global **injectivity radius** `inj(M) = ⨅ p, inj(p)` of a Riemannian manifold `M`, valued
in `ℝ≥0∞`. -/
def injectivityRadius : ℝ≥0∞ :=
  ⨅ p : M, injectivityRadiusAt I M p

/-- Unfolding lemma for `injectivityRadiusAt`. -/
theorem injectivityRadiusAt_def (p : M) :
    injectivityRadiusAt I M p =
      ⨆ (r : ℝ) (_ : IsNormalDomain I M p (Metric.ball 0 r)), ENNReal.ofReal r := (rfl)

/-- Unfolding lemma for `injectivityRadius`. -/
theorem injectivityRadius_def : injectivityRadius I M = ⨅ p : M, injectivityRadiusAt I M p := (rfl)

/-- The global injectivity radius is bounded above by the injectivity radius at each point. -/
theorem injectivityRadius_le (p : M) : injectivityRadius I M ≤ injectivityRadiusAt I M p :=
  iInf_le _ p

/-- A lower bound holds for `injectivityRadius I M` if and only if it holds at every point. -/
theorem le_injectivityRadius_iff {c : ℝ≥0∞} :
    c ≤ injectivityRadius I M ↔ ∀ p : M, c ≤ injectivityRadiusAt I M p := le_iInf_iff

/-- An empty manifold has infinite global injectivity radius. -/
@[simp] theorem injectivityRadius_of_isEmpty [IsEmpty M] : injectivityRadius I M = ⊤ :=
  iInf_of_empty _

/-! ### Exact characterization of normal tangent balls -/

/-- Every normal tangent ball of radius `r` bounds the injectivity radius from below by `r`. -/
theorem IsNormalDomain.ofReal_le_injectivityRadiusAt {p : M} {r : ℝ}
    (h : IsNormalDomain I M p (Metric.ball 0 r)) : ENNReal.ofReal r ≤ injectivityRadiusAt I M p :=
  le_iSup₂ (f := fun (r : ℝ) (_ : IsNormalDomain I M p (Metric.ball 0 r)) ↦ ENNReal.ofReal r) r h

/-- Any positive radius strictly below `injectivityRadiusAt I M p` gives a normal tangent ball. -/
theorem isNormalDomain_ball_of_lt_injectivityRadiusAt {p : M} {r : ℝ} (hr₀ : 0 < r)
    (hr : ENNReal.ofReal r < injectivityRadiusAt I M p) :
    IsNormalDomain I M p (Metric.ball 0 r) := by
  simp only [injectivityRadiusAt_def, lt_iSup_iff] at hr; obtain ⟨R, hRnorm, hrR⟩ := hr
  exact hRnorm.ball (Metric.ball_subset_ball ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr₀.le).1
    hrR).le) hr₀

/-- **Attainment of the supremum.** Every positive radius `r` with
`ENNReal.ofReal r ≤ injectivityRadiusAt I M p` gives a normal tangent ball `B(0, r)`, because
`B(0, r)` is the union of the strictly smaller balls `B(0, s)` (`0 < s < r`). -/
theorem isNormalDomain_ball_of_le_injectivityRadiusAt {p : M} {r : ℝ} (hr₀ : 0 < r)
    (hr : ENNReal.ofReal r ≤ injectivityRadiusAt I M p) :
    IsNormalDomain I M p (Metric.ball 0 r) := by
  have hmid {x : ℝ} (hx0 : 0 ≤ x) (hxr : x < r) :
      IsNormalDomain I M p (Metric.ball 0 ((x + r) / 2)) :=
    isNormalDomain_ball_of_lt_injectivityRadiusAt (by linarith)
      (((ENNReal.ofReal_lt_ofReal_iff hr₀).2 (by linarith)).trans_le hr)
  refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hr₀,
    (convex_ball (0 : TangentSpace I p) r).starConvex (Metric.mem_ball_self hr₀),
    fun v hv ↦ (hmid (norm_nonneg v) (mem_ball_zero_iff.1 hv)).subset_expDomain
      (mem_ball_zero_iff.2 (by linarith [mem_ball_zero_iff.1 hv])), fun v hv w hw hvw ↦ ?_,
    fun ⟨v, hv⟩ ↦ (hmid (norm_nonneg v) (mem_ball_zero_iff.1 hv)).isLocalDiffeomorphOn
      ⟨v, mem_ball_zero_iff.2 (by linarith [mem_ball_zero_iff.1 hv])⟩⟩
  exact (hmid ((norm_nonneg v).trans (le_max_left _ _))
      (max_lt (mem_ball_zero_iff.1 hv) (mem_ball_zero_iff.1 hw))).injOn
    (mem_ball_zero_iff.2 (by linarith [le_max_left ‖v‖ ‖w‖, mem_ball_zero_iff.1 hv]))
    (mem_ball_zero_iff.2 (by linarith [le_max_right ‖v‖ ‖w‖, mem_ball_zero_iff.1 hw])) hvw

/-- **Exact characterization of normal tangent balls.** For `r > 0`, the open ball `B(0, r)` in
`T_p M` is a normal domain if and only if `ENNReal.ofReal r ≤ injectivityRadiusAt I M p`. -/
theorem isNormalDomain_ball_iff_ofReal_le_injectivityRadiusAt {p : M} {r : ℝ} (hr : 0 < r) :
    IsNormalDomain I M p (Metric.ball 0 r) ↔ ENNReal.ofReal r ≤ injectivityRadiusAt I M p :=
  ⟨IsNormalDomain.ofReal_le_injectivityRadiusAt, isNormalDomain_ball_of_le_injectivityRadiusAt hr⟩

/-- For `r > 0` with `ENNReal.ofReal r ≤ injectivityRadius I M`, the open ball `B(0, r)` is a
normal domain at every point of `M`. -/
theorem isNormalDomain_ball_of_le_injectivityRadius {r : ℝ} (hr₀ : 0 < r)
    (hr : ENNReal.ofReal r ≤ injectivityRadius I M) (p : M) :
    IsNormalDomain I M p (Metric.ball 0 r) :=
  isNormalDomain_ball_of_le_injectivityRadiusAt hr₀ (hr.trans (injectivityRadius_le p))

/-- Every tangent vector of extended norm strictly less than `inj(p)` lies in a normal tangent ball
at `p` whose radius is still strictly below `inj(p)`. -/
theorem exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt {p : M} {v : TangentSpace I p}
    (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    ∃ r : ℝ, 0 < r ∧ v ∈ Metric.ball 0 r ∧ ENNReal.ofReal r < injectivityRadiusAt I M p ∧
      IsNormalDomain I M p (Metric.ball 0 r) := by
  obtain ⟨r, -, hvr, hr⟩ := ENNReal.lt_iff_exists_real_btwn.1 hv
  have hr₀ : 0 < r := ENNReal.ofReal_pos.1 (zero_le.trans_lt hvr)
  exact ⟨r, hr₀, mem_ball_zero_iff.2 ((ENNReal.ofReal_lt_ofReal_iff hr₀).1 (by rwa [ofReal_norm])),
    hr, isNormalDomain_ball_of_lt_injectivityRadiusAt hr₀ hr⟩

/-- Every tangent vector with `‖v‖ₑ < inj(p)` belongs to `expDomain I M p`. -/
theorem mem_expDomain_of_enorm_lt_injectivityRadiusAt {p : M} {v : TangentSpace I p}
    (hv : ‖v‖ₑ < injectivityRadiusAt I M p) : v ∈ expDomain I M p :=
  let ⟨_, _, hvr, _, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  hball.subset_expDomain hvr

/-- At every tangent vector with `‖v‖ₑ < inj(p)`, the exponential map is a smooth local
diffeomorphism. -/
theorem isLocalDiffeomorphAt_riemannianExp_of_enorm_lt_injectivityRadiusAt
    {p : M} {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v :=
  let ⟨_, _, hvr, _, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  hball.isLocalDiffeomorphOn ⟨v, hvr⟩

/-- At every tangent vector with `‖v‖ₑ < inj(p)`, the differential of `exp_p` is injective. -/
theorem injective_mfderiv_riemannianExp_of_enorm_lt_injectivityRadiusAt
    {p : M} {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v) :=
  let ⟨_, _, hvr, _, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  hball.injective_mfderiv_riemannianExp hvr

/-- The exponential map is injective on `Metric.eball (0 : TangentSpace I p) (inj(p))`. -/
theorem injOn_riemannianExp_eball_injectivityRadiusAt (p : M) :
    InjOn (riemannianExp I M p) (Metric.eball 0 (injectivityRadiusAt I M p)) := by
  intro v hv w hw hvw; simp only [Metric.mem_eball, edist_zero_right] at hv hw
  obtain ⟨r, -, hmr, hr⟩ := ENNReal.lt_iff_exists_real_btwn.1 (max_lt hv hw)
  have hr₀ : 0 < r := ENNReal.ofReal_pos.1 (zero_le.trans_lt hmr)
  have hmem {u : TangentSpace I p} (hu : ‖u‖ₑ < ENNReal.ofReal r) : u ∈ Metric.ball 0 r :=
    mem_ball_zero_iff.2 ((ENNReal.ofReal_lt_ofReal_iff hr₀).1 (by rwa [ofReal_norm]))
  exact (isNormalDomain_ball_of_lt_injectivityRadiusAt hr₀ hr).injOn
    (hmem ((le_max_left _ _).trans_lt hmr)) (hmem ((le_max_right _ _).trans_lt hmr)) hvw

/-- When `0 < inj(p)`, the extended metric ball `Metric.eball 0 (inj(p))`—which is a tangent ball
when `inj(p) < ⊤` and `Set.univ` when `inj(p) = ⊤`—is the maximal open-ball normal domain at `p`. -/
theorem isNormalDomain_eball_injectivityRadiusAt {p : M} (hpos : 0 < injectivityRadiusAt I M p) :
    IsNormalDomain I M p (Metric.eball 0 (injectivityRadiusAt I M p)) where
  isOpen := Metric.isOpen_eball
  zero_mem := Metric.mem_eball_self hpos
  starConvex := (convex_eball (0 : TangentSpace I p) _).starConvex (Metric.mem_eball_self hpos)
  subset_expDomain _ hv := mem_expDomain_of_enorm_lt_injectivityRadiusAt
    (by simpa only [Metric.mem_eball, edist_zero_right] using hv)
  injOn := injOn_riemannianExp_eball_injectivityRadiusAt p
  isLocalDiffeomorphOn v := isLocalDiffeomorphAt_riemannianExp_of_enorm_lt_injectivityRadiusAt
    (by simpa only [Metric.mem_eball, edist_zero_right] using v.2)

/-- For any extended radius `0 < r ≤ ∞`, `Metric.eball (0 : TangentSpace I p) r` is a normal domain
if and only if `r ≤ injectivityRadiusAt I M p`. -/
theorem isNormalDomain_eball_iff_le_injectivityRadiusAt {p : M} {r : ℝ≥0∞} (hr : 0 < r) :
    IsNormalDomain I M p (Metric.eball 0 r) ↔ r ≤ injectivityRadiusAt I M p := by
  refine ⟨fun h ↦ ENNReal.le_of_forall_pos_nnreal_lt fun s hs hsr ↦ ?_, fun hle ↦
    (isNormalDomain_eball_injectivityRadiusAt (hr.trans_le hle)).mono
      (Metric.eball_subset_eball hle) Metric.isOpen_eball (Metric.mem_eball_self hr)
      ((convex_eball (0 : TangentSpace I p) r).starConvex (Metric.mem_eball_self hr))⟩
  have hs' : 0 < (s : ℝ) := NNReal.coe_pos.2 hs
  have hsub : Metric.ball (0 : TangentSpace I p) (s : ℝ) ⊆ Metric.eball 0 r := fun v hv ↦ by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ((ENNReal.ofReal_lt_ofReal_iff hs').2 (mem_ball_zero_iff.1 hv)).trans
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hsr)
  simpa only [ENNReal.ofReal_coe_nnreal] using (h.ball hsub hs').ofReal_le_injectivityRadiusAt

/-- The injectivity radius at `p` is infinite if and only if every open tangent ball around `0` is
a normal domain. -/
theorem injectivityRadiusAt_eq_top_iff {p : M} :
    injectivityRadiusAt I M p = ⊤ ↔ ∀ r : ℝ, 0 < r → IsNormalDomain I M p (Metric.ball 0 r) := by
  refine ⟨fun h r hr ↦ isNormalDomain_ball_of_le_injectivityRadiusAt hr (h ▸ le_top), fun h ↦
    eq_top_iff.2 <| ENNReal.le_of_forall_pos_nnreal_lt fun r _ _ ↦ ?_⟩
  simpa only [ENNReal.ofReal_coe_nnreal] using (ENNReal.ofReal_le_ofReal
    (le_add_of_nonneg_right zero_le_one)).trans
    (h ((r : ℝ) + 1) (by positivity)).ofReal_le_injectivityRadiusAt

/-- The injectivity radius at `p` is infinite if and only if the whole tangent space `T_p M` is a
normal domain. -/
theorem injectivityRadiusAt_eq_top_iff_isNormalDomain_univ {p : M} :
    injectivityRadiusAt I M p = ⊤ ↔ IsNormalDomain I M p univ := by
  simpa only [Metric.eball_top] using
    top_le_iff.symm.trans (isNormalDomain_eball_iff_le_injectivityRadiusAt
      (I := I) (M := M) (p := p) (r := ⊤) ENNReal.zero_lt_top).symm

/-! ### Upper bounds on the injectivity radius -/

/-- A tangent vector outside `expDomain I M p` bounds `injectivityRadiusAt I M p` above by its
extended norm. -/
theorem injectivityRadiusAt_le_of_notMem_expDomain {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain I M p) : injectivityRadiusAt I M p ≤ ‖v‖ₑ := by
  by_contra! hlt; exact hv (mem_expDomain_of_enorm_lt_injectivityRadiusAt hlt)

/-- A tangent vector where `exp_p` fails to be a local diffeomorphism bounds
`injectivityRadiusAt I M p` above by its extended norm. -/
theorem injectivityRadiusAt_le_of_not_isLocalDiffeomorphAt_riemannianExp
    {p : M} {v : TangentSpace I p}
    (hv : ¬ IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v) :
    injectivityRadiusAt I M p ≤ ‖v‖ₑ := by
  by_contra! hlt; exact hv (isLocalDiffeomorphAt_riemannianExp_of_enorm_lt_injectivityRadiusAt hlt)

/-- A critical point of `exp_p` (where `mfderiv` is not injective) bounds
`injectivityRadiusAt I M p` above by its extended norm. -/
theorem injectivityRadiusAt_le_of_not_injective_mfderiv_riemannianExp
    {p : M} {v : TangentSpace I p}
    (hv : ¬ Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v)) :
    injectivityRadiusAt I M p ≤ ‖v‖ₑ := by
  by_contra! hlt; exact hv (injective_mfderiv_riemannianExp_of_enorm_lt_injectivityRadiusAt hlt)

/-- Two distinct tangent vectors having the same exponential image bound
`injectivityRadiusAt I M p` above by the maximum of their extended norms. -/
theorem injectivityRadiusAt_le_max_of_riemannianExp_eq {p : M} {v w : TangentSpace I p}
    (hvw : v ≠ w) (hexp : riemannianExp I M p v = riemannianExp I M p w) :
    injectivityRadiusAt I M p ≤ max ‖v‖ₑ ‖w‖ₑ := by
  by_contra! hlt; exact hvw (injOn_riemannianExp_eball_injectivityRadiusAt p
    (by simpa [Metric.mem_eball] using (le_max_left _ _).trans_lt hlt)
    (by simpa [Metric.mem_eball] using (le_max_right _ _).trans_lt hlt) hexp)

/-- Two distinct tangent vectors with `‖w‖ₑ ≤ ‖v‖ₑ` and `exp_p v = exp_p w` bound
`injectivityRadiusAt I M p` above by `‖v‖ₑ`. -/
theorem injectivityRadiusAt_le_of_riemannianExp_eq_of_enorm_le {p : M} {v w : TangentSpace I p}
    (hvw : v ≠ w) (hn : ‖w‖ₑ ≤ ‖v‖ₑ) (hexp : riemannianExp I M p v = riemannianExp I M p w) :
    injectivityRadiusAt I M p ≤ ‖v‖ₑ :=
  (injectivityRadiusAt_le_max_of_riemannianExp_eq hvw hexp).trans (max_eq_left hn).le

/-! ### Positivity, conjugate-point bound, and compact manifolds -/

section Boundaryless

variable [I.Boundaryless] [T2Space M]

/-- **Conjugate-point upper bound.** If `b ≠ 0` is conjugate to `0` along the radial geodesic
`t ↦ exp_p (t • v)`, then `injectivityRadiusAt I M p ≤ ‖b • v‖ₑ`. -/
theorem injectivityRadiusAt_le_of_isConjugateOn {p : M} {v : TangentSpace I p} {s : Set ℝ} {b : ℝ}
    (hγ : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s)
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
    (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)
    (hconj : IsConjugateOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0 b) :
    injectivityRadiusAt I M p ≤ ‖b • v‖ₑ :=
  injectivityRadiusAt_le_of_not_injective_mfderiv_riemannianExp
    ((isConjugateOn_iff_not_injective_mfderiv_riemannianExp hγ hs hsub h0 hb hb0).1 hconj)

/-- **Positivity of the pointwise injectivity radius.** At every point of a boundaryless Hausdorff
Riemannian manifold, `0 < injectivityRadiusAt I M p`. -/
theorem injectivityRadiusAt_pos (p : M) : 0 < injectivityRadiusAt I M p :=
  let ⟨_, hr, hnorm⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  (ENNReal.ofReal_pos.2 hr).trans_le hnorm.ofReal_le_injectivityRadiusAt

/-- The pointwise injectivity radius on a boundaryless Hausdorff Riemannian manifold is nonzero. -/
theorem injectivityRadiusAt_ne_zero (p : M) : injectivityRadiusAt I M p ≠ 0 :=
  (injectivityRadiusAt_pos p).ne'

/-- On a zero-dimensional boundaryless Hausdorff manifold, every point has infinite injectivity
radius. -/
@[simp] theorem injectivityRadiusAt_eq_top_of_subsingleton [Subsingleton E] (p : M) :
    injectivityRadiusAt I M p = ⊤ :=
  let _ : Subsingleton (TangentSpace I p) := ‹Subsingleton E›
  injectivityRadiusAt_eq_top_iff_isNormalDomain_univ.2 ⟨isOpen_univ, mem_univ _, starConvex_univ _,
    fun v _ ↦ Subsingleton.elim v 0 ▸ zero_mem_expDomain p, fun v _ w _ _ ↦ Subsingleton.elim v w,
    fun ⟨v, _⟩ ↦ Subsingleton.elim v 0 ▸ isLocalDiffeomorphAt_riemannianExp_zero p⟩

/-- A zero-dimensional boundaryless Hausdorff manifold has infinite global injectivity radius. -/
@[simp] theorem injectivityRadius_eq_top_of_subsingleton [Subsingleton E] :
    injectivityRadius I M = ⊤ := by simp [injectivityRadius_def]

/-- **Local uniform lower bound.** Every point `p` has a neighbourhood on which `inj(q)` is bounded
below by a single positive real constant. -/
theorem exists_pos_eventually_le_injectivityRadiusAt (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ q in 𝓝 p, ENNReal.ofReal r ≤ injectivityRadiusAt I M q :=
  let ⟨r, hr, _, hW, hnorm⟩ := exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  ⟨r, hr, Filter.eventually_of_mem hW fun q hq ↦ (hnorm q hq).1.ofReal_le_injectivityRadiusAt⟩

/-- **Uniform lower bound on a compact set.** For any compact subset `K ⊆ M`, there exists `r > 0`
such that `ENNReal.ofReal r ≤ injectivityRadiusAt I M q` for all `q ∈ K`. -/
theorem _root_.IsCompact.exists_pos_forall_le_injectivityRadiusAt {K : Set M} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ENNReal.ofReal r ≤ injectivityRadiusAt I M q :=
  let ⟨r, hr, _, _, hKU, hnorm⟩ :=
    hK.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball (I := I)
  ⟨r, hr, fun q hq ↦ (hnorm q (hKU hq)).ofReal_le_injectivityRadiusAt⟩

/-- **Positivity of the global injectivity radius of a compact Riemannian manifold.** No
connectedness or nonemptiness hypothesis is required (when `M` is empty, `inj(M) = ⊤`). -/
theorem injectivityRadius_pos [CompactSpace M] : 0 < injectivityRadius I M :=
  let ⟨_, hr, hle⟩ := (isCompact_univ (X := M)).exists_pos_forall_le_injectivityRadiusAt (I := I)
  (ENNReal.ofReal_pos.2 hr).trans_le (le_injectivityRadius_iff.2 fun q ↦ hle q (mem_univ q))

/-- On a compact boundaryless Hausdorff Riemannian manifold, `injectivityRadius I M ≠ 0`. -/
theorem injectivityRadius_ne_zero [CompactSpace M] : injectivityRadius I M ≠ 0 :=
  (injectivityRadius_pos (I := I) (M := M)).ne'

end Boundaryless

end TauCeti.Manifold

end
