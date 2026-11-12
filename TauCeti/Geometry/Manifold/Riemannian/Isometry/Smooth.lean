/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Convex.StrictConvexBetween
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion

/-!
# Distance-preserving maps between Riemannian manifolds are smooth

Let `f : M → N` preserve the Riemannian distances, with `N` complete. Then `f` is smooth, and its
differential at every point is a linear isometry of tangent spaces. This is the theorem of Myers
and Steenrod, in the form of Palais. Hence an isometry equivalence of the Riemannian distances is
a smooth Riemannian isometry. Together with the converse, the `IsometryClass` instance of
`TauCeti.RiemannianIsometry`, this shows that the two notions of isometry coincide.

The proof reads `f` in normal coordinates. Fix `p` and a radius `δ` such that the tangent balls of
radius `δ` at `p` and at `f p` are normal domains, and put `A v = log_{f p} (f (exp_p v))` on the
first ball. By `Isometry.norm_riemannianLog_apply_riemannianExp` and
`Isometry.riemannianLog_apply_riemannianExp_smul`, `A` preserves norms and `A (t • v) = t • A v`
for `t ∈ [0, 1]`. On a small enough ball the exponential maps at `p` and at `f p` distort distances
by at most a factor `c > 1` in both directions
(`TauCeti.Manifold.exists_isNormalDomain_ball_dist_riemannianExp_le`), and `f` preserves
distances, so there `A` distorts distances by at most `c²`. Homogeneity moves this estimate to the
whole ball of radius `δ`, and letting `c` tend to `1` shows that `A` preserves distances there.
A distance-preserving map on a ball that is homogeneous along rays agrees there with a linear
isometry `L` (`TauCeti.exists_linearIsometry_eqOn_ball`).
So `f = exp_{f p} ∘ L ∘ log_p` near `p`, which is smooth with differential `L` at `p`.

## Main results

* `Isometry.exists_linearIsometry_apply_riemannianExp`: in normal coordinates at `p` and `f p`, a
  distance-preserving map is a linear isometry of tangent spaces.
* `Isometry.contMDiff`: a distance-preserving map is smooth.
* `Isometry.exists_linearIsometry_mfderiv_eq`: its differential is a linear isometry.
* `Isometry.exists_apply_riemannianExp_eq_mfderiv`: near `p`, it is determined by its value and
  differential at `p`, as `f (exp_p v) = exp_{f p} (d f_p v)`.
* `Isometry.norm_mfderiv` and `Isometry.inner_mfderiv`: its differential preserves norms and inner
  products.
* `IsometryEquiv.toRiemannianIsometry`: an isometry equivalence of the Riemannian distances is a
  smooth Riemannian isometry.
* `TauCeti.RiemannianIsometry.isometryEquivEquiv`: smooth Riemannian isometries are exactly the
  isometry equivalences of the Riemannian distances.
* `TauCeti.RiemannianIsometry.isometryEquivMulEquiv`: the isometry group `Isom(M)` of a complete
  Riemannian manifold is the group `M ≃ᵢ M` of isometries of its Riemannian distance.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. 40 (1939), 400–416.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

open Bundle Filter Manifold Set TauCeti TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]

namespace Isometry

variable {f : M → N} {p : M} {δ : ℝ}

/-- `f` read in normal coordinates at `p` and `f p`, with the logarithm on the tangent ball of
radius `δ`. -/
private def radialMap (f : M → N) (p : M) (δ : ℝ) (v : TangentSpace I p) :
    TangentSpace J (f p) :=
  riemannianLog J N (f p) (Metric.ball 0 δ) (f (riemannianExp I M p v))

variable [CompleteSpace N]

omit [CompleteSpace N] in
/-- On a normal ball at `p`, the radial map preserves norms. -/
private theorem norm_radialMap (hf : Isometry f) (hp : IsNormalDomain I M p (Metric.ball 0 δ))
    (hq : IsNormalDomain J N (f p) (Metric.ball 0 δ)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 δ) :
    ‖radialMap (J := J) f p δ v‖ = ‖v‖ :=
  hf.norm_riemannianLog_apply_riemannianExp hq subset_rfl
    (hp.dist_riemannianExp_eq_of_mem_ball subset_rfl hv).ge (mem_ball_zero_iff.1 hv)

/-- On a normal ball at `p`, the radial map is homogeneous along rays. -/
private theorem radialMap_smul (hf : Isometry f) (hp : IsNormalDomain I M p (Metric.ball 0 δ))
    (hq : IsNormalDomain J N (f p) (Metric.ball 0 δ)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    radialMap (J := J) f p δ (t • v) = t • radialMap (J := J) f p δ v :=
  hf.riemannianLog_apply_riemannianExp_smul hq subset_rfl
    (hp.dist_riemannianExp_eq_of_mem_ball subset_rfl hv).ge (mem_ball_zero_iff.1 hv) ht

/-- On a normal ball at `p`, `f ∘ exp_p` is the exponential map at `f p` of the radial map. -/
private theorem apply_riemannianExp_eq_radialMap (hf : Isometry f)
    (hp : IsNormalDomain I M p (Metric.ball 0 δ)) (hq : IsNormalDomain J N (f p) (Metric.ball 0 δ))
    {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 δ) :
    f (riemannianExp I M p v) = riemannianExp J N (f p) (radialMap (J := J) f p δ v) := by
  simpa [radialMap] using hf.apply_riemannianExp_smul hq subset_rfl
    (hp.dist_riemannianExp_eq_of_mem_ball subset_rfl hv).ge (mem_ball_zero_iff.1 hv)
    (t := 1) ⟨zero_le_one, le_rfl⟩

/-- On a small enough ball, the radial map distorts distances by at most a prescribed factor
`c > 1`, in both directions, because `f` preserves distances and the exponential maps at `p` and
at `f p` distort them by at most `√c`. -/
private theorem exists_dist_radialMap_le (hf : Isometry f)
    (hp : IsNormalDomain I M p (Metric.ball 0 δ)) (hq : IsNormalDomain J N (f p) (Metric.ball 0 δ))
    {c : ℝ} (hc : 1 < c) :
    ∃ ρ > 0, ρ ≤ δ ∧ ∀ v ∈ Metric.ball (0 : TangentSpace I p) ρ,
      ∀ w ∈ Metric.ball (0 : TangentSpace I p) ρ,
        dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w) ≤ c * dist v w ∧
        dist v w ≤ c * dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w) := by
  have hc₀ : 0 ≤ c := zero_le_one.trans hc.le
  have hs : 1 < √c := by simpa using Real.sqrt_lt_sqrt zero_le_one hc
  obtain ⟨r₁, hr₁, -, h₁⟩ := exists_isNormalDomain_ball_dist_riemannianExp_le (I := I) p hs
  obtain ⟨r₂, hr₂, -, h₂⟩ := exists_isNormalDomain_ball_dist_riemannianExp_le (I := J) (f p) hs
  have hδ : 0 < δ := by simpa using hp.zero_mem
  refine ⟨min δ (min r₁ r₂), lt_min hδ (lt_min hr₁ hr₂), min_le_left _ _, fun v hv w hw ↦ ?_⟩
  have hvw : ∀ u ∈ Metric.ball (0 : TangentSpace I p) (min δ (min r₁ r₂)),
      u ∈ Metric.ball 0 δ ∧ u ∈ Metric.ball 0 r₁ ∧ radialMap (J := J) f p δ u ∈ Metric.ball 0 r₂ :=
    fun u hu ↦ by
      simp only [Metric.mem_ball, dist_zero_right, lt_min_iff] at hu ⊢
      exact ⟨hu.1, hu.2.1, by rw [norm_radialMap hf hp hq (mem_ball_zero_iff.2 hu.1)]; exact hu.2.2⟩
  obtain ⟨hvδ, hv₁, hv₂⟩ := hvw v hv
  obtain ⟨hwδ, hw₁, hw₂⟩ := hvw w hw
  have hdist : dist (riemannianExp J N (f p) (radialMap (J := J) f p δ v))
      (riemannianExp J N (f p) (radialMap (J := J) f p δ w)) =
      dist (riemannianExp I M p v) (riemannianExp I M p w) := by
    rw [← apply_riemannianExp_eq_radialMap hf hp hq hvδ,
      ← apply_riemannianExp_eq_radialMap hf hp hq hwδ, hf.dist_eq]
  have hsq : √c * √c = c := Real.mul_self_sqrt hc₀
  constructor
  · calc dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w)
        ≤ √c * dist (riemannianExp I M p v) (riemannianExp I M p w) :=
          hdist ▸ (h₂ _ hv₂ _ hw₂).2
      _ ≤ √c * (√c * dist v w) := by gcongr; exact (h₁ v hv₁ w hw₁).1
      _ = c * dist v w := by rw [← mul_assoc, hsq]
  · calc dist v w ≤ √c * dist (riemannianExp I M p v) (riemannianExp I M p w) :=
          (h₁ v hv₁ w hw₁).2
      _ ≤ √c * (√c * dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w)) := by
          gcongr
          exact hdist ▸ (h₂ _ hv₂ _ hw₂).1
      _ = c * dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w) := by
          rw [← mul_assoc, hsq]

/-- On a normal ball at `p` whose radius also gives a normal ball at `f p`, the radial map
preserves distances. -/
private theorem dist_radialMap (hf : Isometry f) (hp : IsNormalDomain I M p (Metric.ball 0 δ))
    (hq : IsNormalDomain J N (f p) (Metric.ball 0 δ)) {v w : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 δ) (hw : w ∈ Metric.ball 0 δ) :
    dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w) = dist v w := by
  have hδ : 0 < δ := by simpa using hp.zero_mem
  -- For each `c > 1`, shrink `v` and `w` into the ball where the radial map distorts distances by
  -- at most `c`, and scale back by homogeneity.
  have key : ∀ c : ℝ, 1 < c →
      dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w) ≤ c * dist v w ∧
      dist v w ≤ c * dist (radialMap (J := J) f p δ v) (radialMap (J := J) f p δ w) := by
    intro c hc
    obtain ⟨ρ, hρ, hρδ, hdist⟩ := exists_dist_radialMap_le hf hp hq hc
    set t := ρ / δ with ht_def
    have ht₀ : 0 < t := div_pos hρ hδ
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht₀.le, (div_le_one hδ).2 hρδ⟩
    have hmem {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 δ) : t • u ∈ Metric.ball 0 ρ := by
      rw [mem_ball_zero_iff] at hu ⊢
      calc ‖t • u‖ = t * ‖u‖ := by simp [norm_smul, abs_of_pos ht₀]
        _ < t * δ := by gcongr
        _ = ρ := by simp [ht_def, hδ.ne']
    have h := hdist _ (hmem hv) _ (hmem hw)
    simp only [radialMap_smul hf hp hq hv ht, radialMap_smul hf hp hq hw ht, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos ht₀] at h
    constructor <;> nlinarith [h.1, h.2]
  -- Let `c` tend to `1`.
  exact le_antisymm
    ((le_iff_forall_one_lt_le_mul₀ dist_nonneg).2 fun c hc ↦ by
      simpa only [mul_comm] using (key c hc).1)
    ((le_iff_forall_one_lt_le_mul₀ dist_nonneg).2 fun c hc ↦ by
      simpa only [mul_comm] using (key c hc).2)

/-- **A distance-preserving map is a linear isometry in normal coordinates.** If `f` preserves the
Riemannian distances and `N` is complete, then for every `p` there are a linear isometry
`L : T_p M → T_{f p} N` and a radius `r > 0` such that the tangent balls of radius `r` at `p` and
at `f p` are normal domains and `f (exp_p v) = exp_{f p} (L v)` for `‖v‖ < r`. -/
theorem exists_linearIsometry_apply_riemannianExp (hf : Isometry f) (p : M) :
    ∃ (L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p)) (r : ℝ), 0 < r ∧
      IsNormalDomain I M p (Metric.ball 0 r) ∧ IsNormalDomain J N (f p) (Metric.ball 0 r) ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
        f (riemannianExp I M p v) = riemannianExp J N (f p) (L v) := by
  obtain ⟨r₁, hr₁, hn₁⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨r₂, hr₂, hn₂⟩ := exists_isNormalDomain_ball (I := J) (M := N) (f p)
  set δ := min r₁ r₂
  have hδ : 0 < δ := lt_min hr₁ hr₂
  have hp := hn₁.ball (Metric.ball_subset_ball (min_le_left r₁ r₂)) hδ
  have hq := hn₂.ball (Metric.ball_subset_ball (min_le_right r₁ r₂)) hδ
  obtain ⟨L, hL⟩ := exists_linearIsometry_eqOn_ball hδ
    (fun v hv t ht ↦ radialMap_smul (J := J) hf hp hq hv ht)
    (fun v hv w hw ↦ dist_radialMap hf hp hq hv hw)
  refine ⟨L, δ, hδ, hp, hq, fun v hv ↦ ?_⟩
  rw [hL hv]
  exact apply_riemannianExp_eq_radialMap hf hp hq hv

/-- Near `p`, a distance-preserving map is `exp_{f p} ∘ L ∘ log_p` for a linear isometry `L`. -/
private theorem exists_linearIsometry_eventuallyEq (hf : Isometry f) (p : M) :
    ∃ (L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p)) (r : ℝ), 0 < r ∧
      IsNormalDomain I M p (Metric.ball 0 r) ∧ IsNormalDomain J N (f p) (Metric.ball 0 r) ∧
      f =ᶠ[𝓝 p] riemannianExp J N (f p) ∘ L ∘ riemannianLog I M p (Metric.ball 0 r) := by
  obtain ⟨L, r, hr, hp, hq, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp (I := I) (J := J) p
  refine ⟨L, r, hr, hp, hq, ?_⟩
  filter_upwards [hp.image_mem_nhds] with x hx
  obtain ⟨v, hv, rfl⟩ := hx
  simp only [Function.comp_apply, hp.riemannianLog_riemannianExp hv, hL v hv]

/-- **A distance-preserving map is smooth** (Myers–Steenrod). -/
protected theorem contMDiff (hf : Isometry f) : ContMDiff I J ∞ f := fun p ↦ by
  obtain ⟨L, r, -, hp, -, heq⟩ := hf.exists_linearIsometry_eventuallyEq (I := I) (J := J) p
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace J (f p)) J ∞ (riemannianExp J N (f p))
      (L (riemannianLog I M p (Metric.ball 0 r) p)) := by
    rw [hp.riemannianLog_self, map_zero]
    exact contMDiffAt_riemannianExp (zero_mem_expDomain _)
  exact hexp.comp p (L.toContinuousLinearMap.contMDiff.contMDiffAt.comp p
    (hp.contMDiffOn_riemannianLog.contMDiffAt hp.image_mem_nhds))

/-- The differential of a distance-preserving map at `p` is the linear isometry through which it
acts in normal coordinates. -/
private theorem mfderiv_apply_eq_of_apply_riemannianExp (hf : Isometry f)
    {L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p)} {r : ℝ} (hr : 0 < r)
    (hL : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
      f (riemannianExp I M p v) = riemannianExp J N (f p) (L v))
    (v : TangentSpace I p) :
    mfderiv I J f p v = L v := by
  -- Differentiate `f ∘ exp_p = exp_{f p} ∘ L` at the origin, where both exponential maps have the
  -- identity as differential.
  let Lc : TangentSpace I p →L[ℝ] TangentSpace J (f p) := L.toContinuousLinearMap
  have heq : f ∘ riemannianExp I M p =ᶠ[𝓝 0] riemannianExp J N (f p) ∘ Lc := by
    filter_upwards [Metric.ball_mem_nhds 0 hr] with v hv using hL v hv
  have hexp₀ : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 :=
    (contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt (by simp)
  have hfp : MDifferentiableAt I J f p :=
    (hf.contMDiff (I := I) (J := J) p).mdifferentiableAt (by simp)
  have hexp₁ : MDifferentiableAt 𝓘(ℝ, TangentSpace J (f p)) J (riemannianExp J N (f p)) 0 :=
    (contMDiffAt_riemannianExp (zero_mem_expDomain (I := J) (M := N) (f p))).mdifferentiableAt
      (by simp)
  -- `v` as a tangent vector to `T_p M` at the origin.
  let v₀ : TangentSpace 𝓘(ℝ, TangentSpace I p) (0 : TangentSpace I p) := v
  have hd : mfderiv 𝓘(ℝ, TangentSpace I p) J (f ∘ riemannianExp I M p) 0 v₀ =
      mfderiv 𝓘(ℝ, TangentSpace I p) J (riemannianExp J N (f p) ∘ Lc) 0 v₀ := by
    -- `Filter.EventuallyEq.mfderiv_eq` inserts `tangentSpaceCast` between the tangent spaces at
    -- `(f ∘ exp_p) 0` and at `(exp_{f p} ∘ L) 0`, which is the identity map by definition.
    rw [heq.mfderiv_eq]
    rfl
  -- The chain rule on both sides; the tangent spaces at the base points `exp_p 0 = p` and
  -- `L 0 = 0` agree definitionally, so the steps are chained with `Eq.trans`.
  have h₁ : mfderiv I J f p v =
      mfderiv I J f p (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v₀) := by
    rw [mfderiv_riemannianExp_apply_zero]
  have h₂ : mfderiv 𝓘(ℝ, TangentSpace J (f p)) J (riemannianExp J N (f p)) 0
      (mfderiv 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, TangentSpace J (f p)) Lc 0 v₀) = L v := by
    rw [Lc.mfderiv_eq]
    exact mfderiv_riemannianExp_apply_zero (f p) (Lc v)
  exact h₁.trans <| (mfderiv_comp_apply_of_eq 0 hfp hexp₀ (riemannianExp_zero p) v₀).symm.trans <|
    hd.trans <| (mfderiv_comp_apply_of_eq 0 hexp₁ Lc.mdifferentiableAt (map_zero Lc) v₀).trans h₂

/-- **The differential of a distance-preserving map is a linear isometry.** -/
theorem exists_linearIsometry_mfderiv_eq (hf : Isometry f) (p : M) :
    ∃ L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p),
      ∀ v : TangentSpace I p, mfderiv I J f p v = L v := by
  obtain ⟨L, r, hr, -, -, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp (I := I) (J := J) p
  exact ⟨L, hf.mfderiv_apply_eq_of_apply_riemannianExp hr hL⟩

/-- **A distance-preserving map is determined near `p` by its value and differential at `p`.**
If `f` preserves the Riemannian distances and `N` is complete, then there is a radius `r > 0` such
that the tangent balls of radius `r` at `p` and at `f p` are normal domains and
`f (exp_p v) = exp_{f p} (d f_p v)` for `‖v‖ < r`. -/
theorem exists_apply_riemannianExp_eq_mfderiv (hf : Isometry f) (p : M) :
    ∃ r : ℝ, 0 < r ∧
      IsNormalDomain I M p (Metric.ball 0 r) ∧ IsNormalDomain J N (f p) (Metric.ball 0 r) ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
        f (riemannianExp I M p v) = riemannianExp J N (f p) (mfderiv I J f p v) := by
  obtain ⟨L, r, hr, hp, hq, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp (I := I) (J := J) p
  refine ⟨r, hr, hp, hq, fun v hv ↦ ?_⟩
  rw [hf.mfderiv_apply_eq_of_apply_riemannianExp hr hL]
  exact hL v hv

/-- **The differential of a distance-preserving map preserves inner products.** -/
@[simp]
theorem inner_mfderiv (hf : Isometry f) (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w := by
  obtain ⟨L, hL⟩ := hf.exists_linearIsometry_mfderiv_eq (I := I) (J := J) x
  rw [hL, hL, L.inner_map_map]

/-- **The differential of a distance-preserving map preserves norms.** -/
@[simp]
theorem norm_mfderiv (hf : Isometry f) (x : M) (v : TangentSpace I x) :
    ‖mfderiv I J f x v‖ = ‖v‖ := by
  obtain ⟨L, hL⟩ := hf.exists_linearIsometry_mfderiv_eq (I := I) (J := J) x
  rw [hL, L.norm_map]

end Isometry

namespace IsometryEquiv

variable [CompleteSpace N]

variable (I J) in
/-- **An isometry of the Riemannian distances is a smooth Riemannian isometry** (Myers–Steenrod),
when the target, hence also the source, is complete. -/
def toRiemannianIsometry (f : M ≃ᵢ N) : RiemannianIsometry I J M N :=
  haveI : CompleteSpace M := f.completeSpace
  { toEquiv := f.toEquiv
    contMDiff_toFun := f.isometry.contMDiff
    contMDiff_invFun := f.symm.isometry.contMDiff
    inner_mfderiv' := f.isometry.inner_mfderiv }

@[simp]
theorem coe_toRiemannianIsometry (f : M ≃ᵢ N) : ⇑(f.toRiemannianIsometry I J) = f :=
  (rfl)

end IsometryEquiv

namespace TauCeti.RiemannianIsometry

variable [CompleteSpace N]

variable (I J) in
/-- **Smooth Riemannian isometries are exactly the isometries of the Riemannian distances**, when
the target is complete. -/
def isometryEquivEquiv : RiemannianIsometry I J M N ≃ (M ≃ᵢ N) where
  toFun Φ := Φ
  invFun f := f.toRiemannianIsometry I J
  left_inv _ := by ext; exact (rfl)
  right_inv _ := by ext; exact (rfl)

@[simp]
theorem isometryEquivEquiv_apply (Φ : RiemannianIsometry I J M N) :
    isometryEquivEquiv I J Φ = Φ :=
  (rfl)

@[simp]
theorem isometryEquivEquiv_symm_apply (f : M ≃ᵢ N) :
    (isometryEquivEquiv I J).symm f = f.toRiemannianIsometry I J :=
  (rfl)

variable [CompleteSpace M]

variable (I M) in
/-- **The isometry group of a complete Riemannian manifold is the isometry group of its Riemannian
distance**: `Isom(M)` is isomorphic to `M ≃ᵢ M` by forgetting smoothness. -/
def isometryEquivMulEquiv : Isom I M ≃* (M ≃ᵢ M) where
  __ := isometryEquivEquiv I I
  map_mul' Φ Ψ := by
    ext x
    exact mul_apply Φ Ψ x

@[simp]
theorem isometryEquivMulEquiv_apply (Φ : Isom I M) : isometryEquivMulEquiv I M Φ = Φ :=
  (rfl)

@[simp]
theorem isometryEquivMulEquiv_symm_apply (f : M ≃ᵢ M) :
    (isometryEquivMulEquiv I M).symm f = f.toRiemannianIsometry I I :=
  (rfl)

end TauCeti.RiemannianIsometry
