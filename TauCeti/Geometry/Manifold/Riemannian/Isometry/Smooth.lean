/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Normed.Affine.Isometry.StrictConvex
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion

/-!
# Distance-preserving maps are smooth

Let `f : M → N` preserve the Riemannian distances of two boundaryless Riemannian manifolds, with
`N` complete. The theorem of Myers and Steenrod states that `f` is smooth and that its
differential preserves the Riemannian metric; no regularity of `f` is assumed. Consequently a
distance-preserving bijection between complete Riemannian manifolds is a smooth Riemannian
isometry. Conversely a smooth Riemannian isometry preserves distances (the `IsometryClass`
instance on `TauCeti.RiemannianIsometry`), so on complete Riemannian manifolds the two notions of
isometry agree.

The proof follows Palais. Distance-preserving maps send short radial geodesics to radial
geodesics (`Isometry.apply_riemannianExp_smul`), so the radial map
`A v = log_{f p} (f (exp_p v))` preserves norms and scales along rays. On small balls the
exponential map and the logarithm are Lipschitz with constants arbitrarily close to one, so near
the origin `A` changes distances by factors arbitrarily close to one; scaling along rays then
shows that `A` preserves distances on a ball. Hence `A` agrees there with a linear isometry `L`
(`TauCeti.exists_linearIsometry_eqOn_ball`), and `f = exp_{f p} ∘ L ∘ log_p` near `p`.

## Main results

* `Isometry.exists_linearIsometry_apply_riemannianExp_eq`: `f (exp_p v) = exp_{f p} (L v)` on a
  normal ball, for a linear isometry `L : T_p M →ₗᵢ[ℝ] T_{f p} N`.
* `Isometry.contMDiff`: a distance-preserving map into a complete manifold is smooth.
* `Isometry.inner_mfderiv`: its differential preserves inner products.
* `IsometryEquiv.toRiemannianIsometry`: a distance-preserving bijection between complete
  Riemannian manifolds as a smooth Riemannian isometry.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. 40 (1939), 400–416.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

open Bundle Filter Manifold Metric Set TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

noncomputable section

/-- A map between normed spaces which scales along rays on a ball, and which near the origin
changes distances by at most any factor `c > 1` in either direction, preserves distances on that
ball. -/
private theorem dist_eq_of_forall_norm_sub_bounds {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] {A : V → W} {ρ : ℝ}
    (hsmul : ∀ v ∈ ball (0 : V) ρ, ∀ t ∈ Icc (0 : ℝ) 1, A (t • v) = t • A v)
    (hbound : ∀ c : ℝ, 1 < c → ∃ s > 0, ∀ v ∈ ball (0 : V) s, ∀ w ∈ ball (0 : V) s,
      ‖A v - A w‖ ≤ c * ‖v - w‖ ∧ ‖v - w‖ ≤ c * ‖A v - A w‖)
    {v w : V} (hv : v ∈ ball (0 : V) ρ) (hw : w ∈ ball (0 : V) ρ) :
    dist (A v) (A w) = dist v w := by
  -- Rescaling `v` and `w` into the small ball transfers the bounds to them.
  have key (c : ℝ) (hc : 1 < c) :
      ‖A v - A w‖ ≤ c * ‖v - w‖ ∧ ‖v - w‖ ≤ c * ‖A v - A w‖ := by
    obtain ⟨s, hs, hb⟩ := hbound c hc
    have hsmall (u : V) : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • u ∈ ball (0 : V) s := by
      have h : Tendsto (fun t : ℝ ↦ t • u) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const u
      exact (h.mono_left nhdsWithin_le_nhds).eventually (isOpen_ball.mem_nhds (mem_ball_self hs))
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
    obtain ⟨t, ⟨ht0, ht1⟩, htv, htw⟩ := (hI.and ((hsmall v).and (hsmall w))).exists
    have h := hb _ htv _ htw
    rw [hsmul v hv t ⟨ht0.le, ht1⟩, hsmul w hw t ⟨ht0.le, ht1⟩, ← smul_sub, ← smul_sub,
      norm_smul, norm_smul, Real.norm_of_nonneg ht0.le] at h
    exact ⟨le_of_mul_le_mul_left (by linarith [h.1]) ht0,
      le_of_mul_le_mul_left (by linarith [h.2]) ht0⟩
  -- Letting `c` tend to `1` gives both inequalities without a factor.
  have hlim {a b : ℝ} (h : ∀ c : ℝ, 1 < c → a ≤ c * b) : a ≤ b := by
    have hb : Tendsto (fun c : ℝ ↦ c * b) (𝓝[>] 1) (𝓝 b) := by
      simpa using ((tendsto_id (x := 𝓝 (1 : ℝ))).mul_const b).mono_left
        (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    exact ge_of_tendsto hb (eventually_nhdsWithin_of_forall fun c hc ↦ h c hc)
  rw [dist_eq_norm, dist_eq_norm]
  exact le_antisymm (hlim fun c hc ↦ (key c hc).1) (hlim fun c hc ↦ (key c hc).2)

section

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

variable {f : M → N}

/-- On a small normal ball the exponential map changes distances by at most a factor `c > 1` in
either direction. -/
private theorem exists_isNormalDomain_ball_dist_riemannianExp_bounds (p : M) {c : ℝ≥0}
    (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (ball 0 r) ∧ ∀ v ∈ ball (0 : TangentSpace I p) r,
      ∀ w ∈ ball (0 : TangentSpace I p) r,
        ‖v - w‖ ≤ c * dist (riemannianExp I M p v) (riemannianExp I M p w) ∧
          dist (riemannianExp I M p v) (riemannianExp I M p w) ≤ c * ‖v - w‖ := by
  obtain ⟨r₁, hr₁, hn₁, hexp⟩ :=
    exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp (I := I) (M := M) p hc
  obtain ⟨r₂, hr₂, hn₂, hlog⟩ :=
    exists_isNormalDomain_ball_lipschitzOnWith_riemannianLog (I := I) (M := M) p hc
  have hr := lt_min hr₁ hr₂
  refine ⟨min r₁ r₂, hr, hn₁.ball (ball_subset_ball (min_le_left _ _)) hr,
    fun v hv w hw ↦ ⟨?_, ?_⟩⟩
  · have hv₂ := ball_subset_ball (min_le_right r₁ r₂) hv
    have hw₂ := ball_subset_ball (min_le_right r₁ r₂) hw
    have h := hlog.dist_le_mul _ (mem_image_of_mem _ hv₂) _ (mem_image_of_mem _ hw₂)
    rwa [hn₂.riemannianLog_riemannianExp hv₂, hn₂.riemannianLog_riemannianExp hw₂,
      dist_eq_norm] at h
  · rw [← dist_eq_norm]
    exact hexp.dist_le_mul _ (ball_subset_ball (min_le_left r₁ r₂) hv) _
      (ball_subset_ball (min_le_left r₁ r₂) hw)

/-- Let `A` be a norm-preserving map between tangent spaces of `M` at `p` and `N` at `f p` with
`f ∘ exp_p = exp_{f p} ∘ A` on a ball. If `f` preserves distances, then near the origin `A`
changes distances by at most any factor `c > 1` in either direction. -/
private theorem exists_pos_norm_sub_bounds (hf : Isometry f) {p : M}
    {A : TangentSpace I p → TangentSpace J (f p)} {ρ : ℝ} (hρ : 0 < ρ)
    (hexp : ∀ v ∈ ball (0 : TangentSpace I p) ρ,
      f (riemannianExp I M p v) = riemannianExp J N (f p) (A v))
    (hnorm : ∀ v ∈ ball (0 : TangentSpace I p) ρ, ‖A v‖ = ‖v‖) {c : ℝ} (hc : 1 < c) :
    ∃ s > 0, ∀ v ∈ ball (0 : TangentSpace I p) s, ∀ w ∈ ball (0 : TangentSpace I p) s,
      ‖A v - A w‖ ≤ c * ‖v - w‖ ∧ ‖v - w‖ ≤ c * ‖A v - A w‖ := by
  -- Apply the exponential distance bounds with the constant `√c` at `p` and at `f p`.
  set c' : ℝ≥0 := (√c).toNNReal
  have hc'c : (c' : ℝ) * c' = c := by
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg c), Real.mul_self_sqrt (zero_le_one.trans hc.le)]
  have hc' : 1 < c' := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal _ (Real.sqrt_nonneg c)]
    exact Real.lt_sqrt_of_sq_lt (by simpa using hc)
  obtain ⟨sM, hsM, -, hM⟩ :=
    exists_isNormalDomain_ball_dist_riemannianExp_bounds (I := I) (M := M) p hc'
  obtain ⟨sN, hsN, -, hN⟩ :=
    exists_isNormalDomain_ball_dist_riemannianExp_bounds (I := J) (M := N) (f p) hc'
  refine ⟨min (min sM sN) ρ, lt_min (lt_min hsM hsN) hρ, fun v hv w hw ↦ ?_⟩
  have hsub (s : ℝ) (hs : min (min sM sN) ρ ≤ s) {u : TangentSpace I p}
      (hu : u ∈ ball (0 : TangentSpace I p) (min (min sM sN) ρ)) :
      u ∈ ball (0 : TangentSpace I p) s :=
    ball_subset_ball hs hu
  have hvρ := hsub ρ (min_le_right _ _) hv
  have hwρ := hsub ρ (min_le_right _ _) hw
  have hAN {u : TangentSpace I p} (hu : u ∈ ball (0 : TangentSpace I p) (min (min sM sN) ρ)) :
      A u ∈ ball (0 : TangentSpace J (f p)) sN := by
    rw [mem_ball_zero_iff, hnorm u (hsub ρ (min_le_right _ _) hu), ← mem_ball_zero_iff]
    exact hsub sN ((min_le_left _ _).trans (min_le_right _ _)) hu
  have hd : dist (riemannianExp J N (f p) (A v)) (riemannianExp J N (f p) (A w)) =
      dist (riemannianExp I M p v) (riemannianExp I M p w) := by
    rw [← hexp v hvρ, ← hexp w hwρ, hf.dist_eq]
  obtain ⟨hM₁, hM₂⟩ := hM v (hsub sM ((min_le_left _ _).trans (min_le_left _ _)) hv) w
    (hsub sM ((min_le_left _ _).trans (min_le_left _ _)) hw)
  obtain ⟨hN₁, hN₂⟩ := hN _ (hAN hv) _ (hAN hw)
  rw [hd] at hN₁ hN₂
  rw [← hc'c]
  constructor
  · calc ‖A v - A w‖ ≤ c' * dist (riemannianExp I M p v) (riemannianExp I M p w) := hN₁
      _ ≤ c' * (c' * ‖v - w‖) := by gcongr
      _ = c' * c' * ‖v - w‖ := by ring
  · calc ‖v - w‖ ≤ c' * dist (riemannianExp I M p v) (riemannianExp I M p w) := hM₁
      _ ≤ c' * (c' * ‖A v - A w‖) := by gcongr
      _ = c' * c' * ‖A v - A w‖ := by ring

variable [CompleteSpace N]

/-- **A distance-preserving map is a linear isometry in normal coordinates.** Let `f` preserve
the Riemannian distances, with `N` complete. Then there are a normal ball of some radius `ρ > 0`
at `p` and a linear isometry `L` from `T_p M` to `T_{f p} N` such that
`f (exp_p v) = exp_{f p} (L v)` for every `v` in that ball. -/
theorem exists_linearIsometry_apply_riemannianExp_eq (hf : Isometry f) (p : M) :
    ∃ ρ > 0, IsNormalDomain I M p (ball 0 ρ) ∧
      ∃ L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p),
        ∀ v ∈ ball (0 : TangentSpace I p) ρ,
          f (riemannianExp I M p v) = riemannianExp J N (f p) (L v) := by
  obtain ⟨r₁, hr₁, hn₁⟩ := exists_isNormalDomain_ball (I := J) (M := N) (f p)
  obtain ⟨r₂, hr₂, hn₂⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  have hρ : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  -- Short radial geodesics at `p` are minimizing and shorter than `r₁`.
  have hmin (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) :
      ‖v‖ ≤ dist p (riemannianExp I M p v) :=
    (hn₂.dist_riemannianExp_eq_of_mem_ball subset_rfl
      (ball_subset_ball (min_le_right _ _) hv)).ge
  have hlt (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) : ‖v‖ < r₁ :=
    (mem_ball_zero_iff.1 hv).trans_le (min_le_left _ _)
  -- The radial map `A v = log_{f p} (f (exp_p v))`.
  set A : TangentSpace I p → TangentSpace J (f p) :=
    fun v ↦ riemannianLog J N (f p) (ball 0 r₁) (f (riemannianExp I M p v)) with hA
  have hexp (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) :
      f (riemannianExp I M p v) = riemannianExp J N (f p) (A v) := by
    simpa using hf.apply_riemannianExp_smul hn₁ subset_rfl (hmin v hv) (hlt v hv)
      (t := 1) ⟨zero_le_one, le_rfl⟩
  have hA0 : A 0 = 0 := by simp [hA, hn₁.riemannianLog_self]
  have hdist (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) (w : TangentSpace I p)
      (hw : w ∈ ball 0 (min r₁ r₂)) : dist (A v) (A w) = dist v w :=
    dist_eq_of_forall_norm_sub_bounds
      (fun v hv t ht ↦ hf.riemannianLog_apply_riemannianExp_smul hn₁ subset_rfl (hmin v hv)
        (hlt v hv) ht)
      (fun c hc ↦ hf.exists_pos_norm_sub_bounds hρ hexp
        (fun v hv ↦ hf.norm_riemannianLog_apply_riemannianExp hn₁ subset_rfl (hmin v hv)
          (hlt v hv)) hc) hv hw
  obtain ⟨L, hL⟩ := TauCeti.exists_linearIsometry_eqOn_ball hρ hA0 hdist
  exact ⟨min r₁ r₂, hρ, hn₂.ball (ball_subset_ball (min_le_right _ _)) hρ, L,
    fun v hv ↦ by rw [hexp v hv, hL hv]⟩

/-- **Myers–Steenrod: a distance-preserving map is smooth.** A map between Riemannian manifolds
which preserves their Riemannian distances, into a complete manifold, is smooth. -/
theorem contMDiff (hf : Isometry f) : ContMDiff I J ∞ f := by
  intro p
  obtain ⟨ρ, -, hn, L, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp_eq (I := I) (J := J) p
  -- Near `p`, `f` is `exp_{f p} ∘ L ∘ log_p`.
  have heq : f =ᶠ[𝓝 p]
      riemannianExp J N (f p) ∘ L ∘ riemannianLog I M p (ball 0 ρ) := by
    filter_upwards [hn.image_mem_nhds] with q hq
    obtain ⟨v, hv, rfl⟩ := hq
    simp only [Function.comp_apply, hn.riemannianLog_riemannianExp hv, hL v hv]
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ (riemannianLog I M p (ball 0 ρ)) p :=
    hn.contMDiffOn_riemannianLog.contMDiffAt hn.image_mem_nhds
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace J (f p)) J ∞ (riemannianExp J N (f p))
      (L (riemannianLog I M p (ball 0 ρ) p)) := by
    rw [hn.riemannianLog_self, map_zero]
    exact contMDiffAt_riemannianExp (zero_mem_expDomain _)
  have hL' := L.toContinuousLinearMap.contMDiff.contMDiffAt.comp p hlog
  exact (hexp.comp p hL').congr_of_eventuallyEq heq

/-- **A distance-preserving map preserves the Riemannian metric.** The differential of a map
between Riemannian manifolds which preserves their Riemannian distances, into a complete
manifold, preserves inner products of tangent vectors. -/
theorem inner_mfderiv (hf : Isometry f) (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w := by
  obtain ⟨ρ, hρ, -, L, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp_eq (I := I) (J := J) x
  have heq : f ∘ riemannianExp I M x =ᶠ[𝓝 (0 : TangentSpace I x)]
      riemannianExp J N (f x) ∘ L :=
    eventually_of_mem (ball_mem_nhds 0 hρ) fun v hv ↦ hL v hv
  -- Differentiating `f ∘ exp_x = exp_{f x} ∘ L` at the origin identifies `d f_x` with `L`.
  have hmf (u : TangentSpace I x) : mfderiv I J f x u = L u := by
    have h1 : HasMFDerivAt I J f (riemannianExp I M x 0)
        (mfderiv I J f (riemannianExp I M x 0)) :=
      ((hf.contMDiff (I := I) (J := J) _).mdifferentiableAt (by simp)).hasMFDerivAt
    have h2 := ((contMDiffAt_riemannianExp (I := I) (M := M)
      (zero_mem_expDomain x)).mdifferentiableAt (by simp)).hasMFDerivAt
    have h3 : HasMFDerivAt 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) (L 0)
        (mfderiv 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) (L 0)) := by
      refine ((contMDiffAt_riemannianExp ?_).mdifferentiableAt (by simp)).hasMFDerivAt
      rw [map_zero]
      exact zero_mem_expDomain (f x)
    have huniq := hasMFDerivAt_unique (h1.comp 0 h2)
      ((h3.comp 0 (L.toContinuousLinearMap.hasMFDerivAt (x := 0))).congr_of_eventuallyEq_abuse
        heq)
    have hu : mfderiv I J f (riemannianExp I M x 0)
        (mfderiv 𝓘(ℝ, TangentSpace I x) I (riemannianExp I M x) 0 u) =
        mfderiv 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) (L 0) (L u) :=
      congr($huniq u)
    rw [mfderiv_riemannianExp_apply_zero] at hu
    -- Move the base points `exp_x 0 = x` and `L 0 = 0` of the two differentials.
    have hexp0 (a : TangentSpace J (f x)) (ha : a = 0) (z : TangentSpace J (f x)) :
        mfderiv 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) a z = z := by
      subst ha
      exact mfderiv_riemannianExp_apply_zero (f x) z
    have hf0 (y : M) (hy : y = x) (z : TangentSpace I x) :
        mfderiv I J f y z = mfderiv I J f x z := by
      subst hy
      rfl
    rw [hf0 _ (riemannianExp_zero x), hexp0 _ (map_zero L)] at hu
    exact hu
  rw [hmf, hmf, L.inner_map_map]

end Isometry

namespace IsometryEquiv

variable [CompleteSpace M] [CompleteSpace N]

variable (I J) in
/-- **A distance-preserving bijection is a Riemannian isometry.** A bijection between complete
Riemannian manifolds which preserves their Riemannian distances is a smooth Riemannian isometry. -/
def toRiemannianIsometry (e : M ≃ᵢ N) : TauCeti.RiemannianIsometry I J M N where
  toEquiv := e.toEquiv
  contMDiff_toFun := e.isometry.contMDiff
  contMDiff_invFun := e.symm.isometry.contMDiff
  inner_mfderiv' := e.isometry.inner_mfderiv

/-- The Riemannian isometry of `e` is `e` as a map. -/
@[simp]
theorem coe_toRiemannianIsometry (e : M ≃ᵢ N) : ⇑(e.toRiemannianIsometry I J) = e :=
  (rfl)

/-- The metric equivalence of the Riemannian isometry of `e` is `e`. -/
@[simp]
theorem toIsometryEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    ((e.toRiemannianIsometry I J : TauCeti.RiemannianIsometry I J M N) : M ≃ᵢ N) = e := by
  ext x
  simp

end IsometryEquiv

/-- The Riemannian isometry of the metric equivalence of a Riemannian isometry `Φ` is `Φ`. -/
@[simp]
theorem TauCeti.RiemannianIsometry.toRiemannianIsometry_toIsometryEquiv [CompleteSpace M]
    [CompleteSpace N] (Φ : TauCeti.RiemannianIsometry I J M N) :
    (Φ : M ≃ᵢ N).toRiemannianIsometry I J = Φ := by
  ext x
  simp

end
