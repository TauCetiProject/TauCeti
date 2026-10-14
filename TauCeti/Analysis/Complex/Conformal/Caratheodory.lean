/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Inside
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence
public import TauCeti.Topology.ClusterSet
public import TauCeti.Topology.JordanCurve.Basic
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
import TauCeti.Analysis.Complex.Conformal.Crosscut.SmallEnclosure
import TauCeti.Analysis.Complex.Conformal.Jordan.Domain
import TauCeti.Analysis.Complex.Conformal.LocallyConnectedBoundary
import TauCeti.Analysis.Normed.Module.Ball.Cut
import TauCeti.Topology.MetricSpace.Cut
import TauCeti.Topology.UniformlyLocallyConnected

/-!
# Carathéodory's continuity theorem

A conformal map of a disc onto a bounded region extends continuously to the closed disc if and only
if the boundary of the region is locally connected. In particular it does so when that boundary is
a Jordan curve.

## The argument

Fix a point `ζ` of the bounding circle and a tolerance `ε`. The **crosscut neighbourhoods**
`ball c r ∩ ball ζ ρ` shrink to `ζ`, so by the Cauchy criterion
`TauCeti.subsingleton_clusterSetOn_of_forall_exists` it is enough to make the image of one of them
have diameter at most `ε`. Four inputs combine to do that, at a radius `ρ` chosen by the
length–area method:

* **a small set along the crosscut.** The boundary is compact, so local connectedness is uniform
  (`IsCompact.isUniformlyLocallyConnected`), and
  `TauCeti.exists_isCompact_superset_image_ball_inter_sphere_diam_le` produces, at some radius `ρ`
  below any prescribed bound, a compact set `K` of diameter at most `ε` consisting of the closed
  image crosscut and a small connected piece of the image boundary joining its two ends;
* **the far side stays wide.** `TauCeti.exists_pos_forall_le_diam_image_sdiff_closedBall`, applied
  at the point `ζ` off the disc, gives a `d > 0` below which the image of the far side
  `ball c r \ closedBall ζ ρ` never shrinks, for every small `ρ`; taking `K` narrower than `d` makes
  it narrower than the far side;
* **both sides of the cut are connected.** The near side `ball c r ∩ ball ζ ρ` is an intersection of
  two discs, hence convex (`TauCeti.isConnected_ball_inter_ball`); the far side
  `ball c r \ closedBall ζ ρ` is connected by the Möbius reduction
  `TauCeti.isConnected_ball_diff_closedBall`;
* **`K` minus a crosscut point is preconnected**, as the construction of `K` guarantees, so the
  winding-number two-sidedness theorem applies directly. No plane-separation hypothesis is needed.

`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton`
then puts the *near* side inside `filledHull K` — the far side cannot be the enclosed one, being
wider than `K` — and `TauCeti.diam_le_diam_of_subset_filledHull` reads that enclosure as the width
bound `diam (f '' (ball c r ∩ ball ζ ρ)) ≤ diam K ≤ ε`. Since this holds at every boundary point,
the extension theorem `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` assembles the
continuous extension on `closedBall c r`.

Conversely, a continuous extension carries the locally connected circle onto the boundary of the
image (`TauCeti.IsJordanDomain.locallyConnectedSpace_frontier_image`), so local connectedness of
the boundary is also necessary.

## What is not claimed

**Injectivity of the extension is not established**, and no statement below asserts it: it fails
in general, for instance for a slit disc, whose boundary is locally connected. For a Jordan domain
the boundary correspondence is a homeomorphism of the closures; given injectivity on the bounding
circle, `TauCeti.closureHomeomorph` of `Conformal/BoundaryCorrespondence.lean` upgrades the
extension to that homeomorphism, and `TauCeti.injOn_closure_of_injOn_frontier` of
`Conformal/ClusterSet.lean` reduces injectivity on the closed disc to injectivity on the circle;
producing the latter is a separate Jordan-curve argument whose analytic half is
`TauCeti.not_eqOn_const_inter_sphere_of_injOn` of `Conformal/ArcConstancy.lean`.

Nor is the *converse* route through `Conformal/Crosscut/BoundarySplit.lean` taken: the enclosure
route used here asks only that the near side fall inside a small set, whereas that route asks
which arc of the image boundary the near side clings to.

Mathlib has no boundary correspondence for conformal maps; the in-progress human-curated Riemann
mapping theorem effort [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505)
does not treat boundary behaviour either.

## Main results

* `TauCeti.exists_diam_image_ball_inter_ball_le_of_locallyConnectedSpace_frontier` — the crosscut
  neighbourhoods at a boundary point have images of arbitrarily small diameter.
* `TauCeti.subsingleton_clusterSetOn_of_locallyConnectedSpace_frontier` and
  `TauCeti.exists_tendsto_nhdsWithin_of_locallyConnectedSpace_frontier` — such a map has at most
  one boundary cluster value at each point of the bounding circle, hence a boundary limit there.
* `TauCeti.exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier` —
  **Carathéodory's continuity theorem**: it extends continuously to the closed disc.
* `TauCeti.exists_continuousOn_closedBall_eqOn_iff_locallyConnectedSpace_frontier` — the
  continuity theorem as a characterization of local connectedness of the boundary.
* `TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier` — a
  bounded simply connected domain with locally connected boundary is the image of the disc under a
  holomorphic bijection continuous up to the closed disc.
* `TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier` — the same for a
  bounded domain with Jordan-curve boundary, the form the Jordan-domain correspondence starts from.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913), 305–320.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Theorem 2.1 and §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Theorem 3.1.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {c ζ : ℂ} {r : ℝ}

/-! ## The crosscut neighbourhoods have small images -/

/-- **The image of a crosscut neighbourhood can be made arbitrarily small.** Let `f` be holomorphic
and injective on `ball c r`, with bounded image whose boundary is locally connected, and let `ζ`
lie on the bounding circle. For every `ε > 0` there is a crosscut radius `ρ > 0` with

> `Metric.diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε`.

The preconnectedness hypothesis on the enclosing set minus a point, needed by the enclosure theorem
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton`, is
supplied by `TauCeti.exists_isCompact_superset_image_ball_inter_sphere_diam_le`. Connectedness of
both cut sides and a far side wider than the enclosing set are discharged here. -/
theorem exists_diam_image_ball_inter_ball_le_of_locallyConnectedSpace_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) [LocallyConnectedSpace (frontier (f '' ball c r))]
    (hζ : dist ζ c = r) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε := by
  -- the image of the disc has two distinct points, so the far side does not degenerate
  have hhalf : (0 : ℝ) < r / 2 := by linarith
  have hc : c ∈ ball c r := mem_ball_self hr
  have hc' : c + ((r / 2 : ℝ) : ℂ) ∈ ball c r := by
    simp only [mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hhalf]
    linarith
  have hne : c ≠ c + ((r / 2 : ℝ) : ℂ) := by simp [hr.ne']
  have hnotsub : ¬ (f '' ball c r).Subsingleton := fun h =>
    hne (hinj hc hc' (h (mem_image_of_mem f hc) (mem_image_of_mem f hc')))
  have hζball : ζ ∉ ball c r := by simp [mem_ball, hζ]
  obtain ⟨d, hd, ρ₀, hρ₀, hfar⟩ :=
    exists_pos_forall_le_diam_image_sdiff_closedBall hnotsub hζball hb
  -- a small enclosing set along the image crosscut, narrower than half the far-side width
  have hulc : IsUniformlyLocallyConnected (frontier (f '' ball c r)) :=
    (isCompact_of_isClosed_isBounded isClosed_frontier
      (hb.closure.subset frontier_subset_closure)).isUniformlyLocallyConnected
  obtain ⟨ρ, hρmem, hρr, K, hK, hγK, hKsub, hKp, hdiamK⟩ :=
    exists_isCompact_superset_image_ball_inter_sphere_diam_le hζ hr hf hinj
      (lintegral_enorm_deriv_sq_ne_top_of_isBounded isOpen_ball hf
        measurableSet_ball.nullMeasurableSet subset_rfl hinj hb)
      hulc (lt_min hε (half_pos hd)) hρ₀
  refine ⟨ρ, hρmem.1, ?_⟩
  have hKb : IsBounded K := hK.isBounded
  have hlt : diam K < diam (f '' (ball c r \ closedBall ζ ρ)) := by
    have h₁ : diam K ≤ d / 2 := hdiamK.trans (min_le_right _ _)
    have h₂ := hfar ρ hρmem.2.le
    linarith
  obtain ⟨z, hz⟩ := nonempty_ball_inter_sphere hζ hρmem.1 hρr
  have hAc : IsPreconnected (ball c r ∩ ball ζ ρ) :=
    (isConnected_ball_inter_ball hr hρmem.1
      (by rw [dist_comm, hζ]; linarith [hρmem.1])).isPreconnected
  have hBc : IsPreconnected (ball c r \ closedBall ζ ρ) :=
    (isConnected_ball_diff_closedBall hζ hρmem.1 hρr).isPreconnected
  calc diam (f '' (ball c r ∩ ball ζ ρ))
      ≤ diam K := diam_le_diam_of_subset_filledHull hKb
        (image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton
          isOpen_ball hρmem.1 hf hinj hAc hBc hK.isClosed hKb hγK hKsub hz (hKp z hz) hlt)
    _ ≤ ε := hdiamK.trans (min_le_left _ _)

/-! ## The boundary limit -/

/-- **Such a map has at most one cluster value at each point of the bounding circle.** The Cauchy
criterion `TauCeti.subsingleton_clusterSetOn_of_forall_exists` applied to the width bound of
`TauCeti.exists_diam_image_ball_inter_ball_le_of_locallyConnectedSpace_frontier`: two points of a
crosscut neighbourhood have images within its diameter of each other by
`Metric.dist_le_diam_of_mem`. -/
theorem subsingleton_clusterSetOn_of_locallyConnectedSpace_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) [LocallyConnectedSpace (frontier (f '' ball c r))]
    (hζ : dist ζ c = r) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, hdiam⟩ :=
    exists_diam_image_ball_inter_ball_le_of_locallyConnectedSpace_frontier hr hf hinj hb hζ hε
  exact ⟨ρ, hρ, fun _ hx _ hy => (dist_le_diam_of_mem
    (hb.subset (image_mono inter_subset_left))
    (mem_image_of_mem f hx) (mem_image_of_mem f hy)).trans hdiam⟩

/-- **Such a map has a boundary limit at each point of the bounding circle.** The values of `f`
converge as the argument approaches `ζ` from inside the disc.

The cluster set at `ζ` is a subsingleton by
`TauCeti.subsingleton_clusterSetOn_of_locallyConnectedSpace_frontier`, and it is nonempty because
`f` maps the disc into the compact closure of its bounded image, which is what
`TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` needs; `Metric.closure_ball` puts `ζ` in the
closure of the disc. This is the pointwise form of
`TauCeti.exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier`, and names the
limit. -/
theorem exists_tendsto_nhdsWithin_of_locallyConnectedSpace_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) [LocallyConnectedSpace (frontier (f '' ball c r))]
    (hζ : dist ζ c = r) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) :=
  exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩)
    (by rw [closure_ball c hr.ne']; exact mem_closedBall.mpr hζ.le)
    (subsingleton_clusterSetOn_of_locallyConnectedSpace_frontier hr hf hinj hb hζ)

/-- **Carathéodory's continuity theorem.** A holomorphic injection of a disc onto a bounded region
whose boundary is locally connected extends continuously to the closed disc.

Every boundary cluster set is a subsingleton by
`TauCeti.subsingleton_clusterSetOn_of_locallyConnectedSpace_frontier`, which is exactly what the
extension theorem `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` asks of a map into a
proper space with bounded image; `Metric.frontier_ball` and `Metric.closure_ball` turn its
`frontier` and `closure` into the circle and the closed disc.

No injectivity is claimed for the extension on the circle, and none is needed for continuity. -/
theorem exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) [LocallyConnectedSpace (frontier (f '' ball c r))] :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  have h := exists_continuousOn_closure_eqOn_of_isBounded isOpen_ball hf.continuousOn hb
    fun w hw => subsingleton_clusterSetOn_of_locallyConnectedSpace_frontier hr hf hinj hb
      (mem_sphere.mp (by rwa [frontier_ball c hr.ne'] at hw))
  rwa [closure_ball c hr.ne'] at h

/-- **Carathéodory's continuity theorem, as a characterization.** A holomorphic injection of a disc
onto a bounded region extends continuously to the closed disc if and only if the boundary of the
region is locally connected.

Sufficiency is `TauCeti.exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier`;
necessity is `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier_image`, the continuous extension
carrying the locally connected bounding circle onto the boundary of the image. -/
theorem exists_continuousOn_closedBall_eqOn_iff_locallyConnectedSpace_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) :
    (∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r)) ↔
      LocallyConnectedSpace (frontier (f '' ball c r)) := by
  refine ⟨fun ⟨F, hFc, hFf⟩ => ?_, fun _ =>
    exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier hr hf hinj hb⟩
  exact (isJordanDomain_ball c hr).locallyConnectedSpace_frontier_image hf hinj
    (by rwa [closure_ball c hr.ne']) hFf

/-! ## The Riemann-map form -/

/-- **A bounded simply connected domain with locally connected boundary is the image of the disc
under a holomorphic bijection continuous up to the closed disc.**

The Riemann mapping theorem, in the shape `TauCeti.exists_bijOn_ball_differentiableOn_invFunOn`,
supplies a holomorphic bijection of `Ω` onto the disc with holomorphic inverse; the inverse is the
map extended. That `Ω` is a proper subset of `ℂ` needs no separate hypothesis, `ℂ` being unbounded.

The extension is named as the map itself rather than beside it: replacing the inverse Riemann map by
its extension changes neither its holomorphy on the open disc nor its bijectivity onto `Ω`. -/
theorem exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩs : IsSimplyConnected Ω) (hΩb : IsBounded Ω)
    [LocallyConnectedSpace (frontier Ω)] :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) Ω := by
  have hΩne : Ω ≠ univ := by
    rintro rfl
    exact NormedSpace.unbounded_univ ℝ ℂ hΩb
  obtain ⟨φ, hφ, -, hgd, -, -⟩ :=
    exists_bijOn_ball_differentiableOn_invFunOn hΩo hΩs hΩne
  have hgbij : BijOn (Function.invFunOn φ Ω) (ball 0 1) Ω :=
    BijOn.symm hφ.invOn_invFunOn.symm hφ
  have himg : Function.invFunOn φ Ω '' ball 0 1 = Ω := hgbij.image_eq
  have hb : IsBounded (Function.invFunOn φ Ω '' ball 0 1) := by rw [himg]; exact hΩb
  have : LocallyConnectedSpace (frontier (Function.invFunOn φ Ω '' ball 0 1)) := by
    rw [himg]; infer_instance
  obtain ⟨G, hGc, hGeq⟩ :=
    exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier one_pos hgd
      hgbij.injOn hb
  exact ⟨G, hGc, hgd.congr fun _ hz => hGeq hz, hgbij.congr fun _ hz => (hGeq hz).symm⟩

/-- **A bounded Jordan domain is the image of the disc under a holomorphic bijection continuous up
to the closed disc.** This is the form the Carathéodory boundary correspondence for Jordan domains
is stated in, minus the injectivity of the boundary values.

A Jordan domain is simply connected (`TauCeti.IsJordanDomain.isSimplyConnected`) and a Jordan curve
is locally connected (`TauCeti.IsJordanCurve.locallyConnectedSpace`), so this is the case of
`TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier`. -/
theorem exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) Ω :=
  haveI := hΩJ.locallyConnectedSpace
  exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier hΩo
    (IsJordanDomain.mk hΩo hΩc hΩb hΩJ).isSimplyConnected hΩb

end TauCeti
