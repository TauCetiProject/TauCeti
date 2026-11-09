/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
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
(`TauCeti.Manifold.exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp` and
`TauCeti.Manifold.exists_isNormalDomain_ball_antilipschitzWith_riemannianExp`), and `f` preserves
distances, so there `A` distorts distances by at most `c²`. Homogeneity moves this estimate to the
whole ball of radius `δ`, and letting `c` tend to `1` shows that `A` preserves distances there.
Extended to all of `T_p M` by homogeneity, `A` becomes a distance-preserving map fixing `0` between
inner product spaces, hence a linear isometry `L` (`Isometry.affineIsometryOfStrictConvexSpace`).
So `f = exp_{f p} ∘ L ∘ log_p` near `p`, which is smooth with differential `L` at `p`.

## Main results

* `Isometry.exists_linearIsometry_apply_riemannianExp`: in normal coordinates at `p` and `f p`, a
  distance-preserving map is a linear isometry of tangent spaces.
* `Isometry.contMDiff`: a distance-preserving map is smooth.
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

/-- On a small enough normal ball the exponential map distorts distances by at most a prescribed
factor `c > 1`, in both directions. -/
private theorem exists_isNormalDomain_ball_dist_riemannianExp_le (p : M) {c : ℝ} (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w ∈ Metric.ball (0 : TangentSpace I p) r,
        dist (riemannianExp I M p v) (riemannianExp I M p w) ≤ c * dist v w ∧
        dist v w ≤ c * dist (riemannianExp I M p v) (riemannianExp I M p w) := by
  have hc' : 1 < c.toNNReal := by simpa using hc
  obtain ⟨r₁, hr₁, hn₁, hlip⟩ :=
    exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp (I := I) p hc'
  obtain ⟨r₂, hr₂, -, hanti⟩ :=
    exists_isNormalDomain_ball_antilipschitzWith_riemannianExp (I := I) p hc'
  have hcc : (c.toNNReal : ℝ) = c := Real.coe_toNNReal c (zero_le_one.trans hc.le)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
    hn₁.ball (Metric.ball_subset_ball (min_le_left _ _)) (lt_min hr₁ hr₂), fun v hv w hw ↦ ?_⟩
  have h₁ : Metric.ball (0 : TangentSpace I p) (min r₁ r₂) ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball (min_le_left r₁ r₂)
  have h₂ : Metric.ball (0 : TangentSpace I p) (min r₁ r₂) ⊆ Metric.ball 0 r₂ :=
    Metric.ball_subset_ball (min_le_right r₁ r₂)
  constructor
  · simpa [hcc] using hlip.dist_le_mul v (h₁ hv) w (h₁ hw)
  · simpa [hcc, Subtype.dist_eq] using hanti.le_mul_dist ⟨v, h₂ hv⟩ ⟨w, h₂ hw⟩

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
  have hs₀ : 0 ≤ √c := Real.sqrt_nonneg c
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
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht₀.le, ht_def,
        div_mul_eq_mul_div, div_lt_iff₀ hδ]
      exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hu) hρ
    have h := hdist _ (hmem hv) _ (hmem hw)
    rw [radialMap_smul hf hp hq hv ht, radialMap_smul hf hp hq hw ht, dist_smul₀, dist_smul₀,
      Real.norm_of_nonneg ht₀.le, mul_left_comm c, mul_left_comm c] at h
    exact ⟨le_of_mul_le_mul_left h.1 ht₀, le_of_mul_le_mul_left h.2 ht₀⟩
  -- Let `c` tend to `1`.
  have hlim {a b : ℝ} (h : ∀ c : ℝ, 1 < c → a ≤ c * b) : a ≤ b := by
    have ht := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)) (a := 1))).mul_const b
    rw [one_mul] at ht
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall h)
  exact le_antisymm (hlim fun c hc ↦ (key c hc).1) (hlim fun c hc ↦ (key c hc).2)

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
  let A := radialMap (I := I) (J := J) f p δ
  have hAn {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 δ) : ‖A v‖ = ‖v‖ :=
    norm_radialMap hf hp hq hv
  have hAs {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      A (t • v) = t • A v :=
    radialMap_smul hf hp hq hv ht
  have hAd {v w : TangentSpace I p} (hv : v ∈ Metric.ball 0 δ) (hw : w ∈ Metric.ball 0 δ) :
      dist (A v) (A w) = dist v w :=
    dist_radialMap hf hp hq hv hw
  -- Extend `A` to all of `T_p M` by homogeneity: `B v = s⁻¹ • A (s • v)` with `s = δ / (‖v‖ + δ)`,
  -- which is the same for every smaller positive scale.
  let s : TangentSpace I p → ℝ := fun v ↦ δ / (‖v‖ + δ)
  have hs₀ (v : TangentSpace I p) : 0 < s v := div_pos hδ (by positivity)
  have hs₁ (v : TangentSpace I p) : s v ≤ 1 :=
    (div_le_one (by positivity)).2 (le_add_of_nonneg_left (norm_nonneg v))
  have hmem {v : TangentSpace I p} {u : ℝ} (hu₀ : 0 ≤ u) (hu : u ≤ s v) :
      u • v ∈ Metric.ball 0 δ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hu₀]
    calc u * ‖v‖ ≤ s v * ‖v‖ := by gcongr
      _ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
  let B : TangentSpace I p → TangentSpace J (f p) := fun v ↦ (s v)⁻¹ • A (s v • v)
  have hB {v : TangentSpace I p} {u : ℝ} (hu₀ : 0 < u) (hu : u ≤ s v) :
      B v = u⁻¹ • A (u • v) := by
    have hus : u / s v ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one (hs₀ v)).2 hu⟩
    have hA : A (u • v) = (u / s v) • A (s v • v) := by
      rw [← hAs (hmem (hs₀ v).le le_rfl) hus, smul_smul, div_mul_cancel₀ _ (hs₀ v).ne']
    simp only [B]
    rw [hA, smul_smul]
    congr 1
    field_simp
  have hBA {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 δ) : B v = A v := by
    simp only [B]
    rw [hAs hv ⟨(hs₀ v).le, hs₁ v⟩, smul_smul, inv_mul_cancel₀ (hs₀ v).ne', one_smul]
  have hB_isometry : Isometry B := by
    refine Isometry.of_dist_eq fun v w ↦ ?_
    have hu₀ : 0 < min (s v) (s w) := lt_min (hs₀ v) (hs₀ w)
    rw [hB hu₀ (min_le_left _ _), hB hu₀ (min_le_right _ _), dist_smul₀,
      hAd (hmem hu₀.le (min_le_left _ _)) (hmem hu₀.le (min_le_right _ _)),
      dist_smul₀, ← mul_assoc, Real.norm_of_nonneg (inv_nonneg.2 hu₀.le),
      Real.norm_of_nonneg hu₀.le, inv_mul_cancel₀ hu₀.ne', one_mul]
  have hB0 : B 0 = 0 := by
    rw [hBA (Metric.mem_ball_self hδ), ← norm_eq_zero, hAn (Metric.mem_ball_self hδ), norm_zero]
  -- A distance-preserving map between inner product spaces fixing `0` is a linear isometry.
  let T := Isometry.affineIsometryOfStrictConvexSpace (E := TangentSpace J (f p))
    (F := TangentSpace I p) hB_isometry
  let L := T.linearIsometry
  have hL (v : TangentSpace I p) : L v = B v := by
    simpa [T, hB0] using T.map_vsub v 0
  refine ⟨L, δ, hδ, hp, hq, fun v hv ↦ ?_⟩
  rw [hL, hBA hv]
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
private theorem exists_linearIsometry_mfderiv_eq (hf : Isometry f) (p : M) :
    ∃ L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p),
      ∀ v : TangentSpace I p, mfderiv I J f p v = L v := by
  obtain ⟨L, r, hr, -, -, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp (I := I) (J := J) p
  refine ⟨L, fun v ↦ ?_⟩
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

/-- **The differential of a distance-preserving map preserves inner products.** -/
theorem inner_mfderiv (hf : Isometry f) (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w := by
  obtain ⟨L, hL⟩ := hf.exists_linearIsometry_mfderiv_eq (I := I) (J := J) x
  rw [hL, hL, L.inner_map_map]

/-- **The differential of a distance-preserving map preserves norms.** -/
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
