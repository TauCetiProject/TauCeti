/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Rigidity
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length

/-!
# Uniqueness of constant-speed minimizers in a normal neighbourhood

A length minimizer from the centre `p` of a normal neighbourhood to `exp_p v` is the radial
geodesic `t ↦ exp_p (t • v)` up to a nondecreasing reparametrization
(`TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Rigidity`). This file proves the
parametrized form of that equality case: a minimizer parametrized proportionally to arc length is
the radial geodesic itself, traversed affinely. Along a minimizer the norm of the logarithm is the
arc length travelled so far, so constant speed fixes the radius `‖log_p (γ t)‖` at each time, and
rigidity fixes the direction.

Geodesics have constant speed, so a geodesic segment from `p` that stays in the normal
neighbourhood and is no longer than the radial segment is the radial segment. A second argument
avoids the hypothesis that the competitor stays in the neighbourhood: a geodesic on an open
interval containing `[0, 1]` with the radial length has the same initial speed, its initial
velocity therefore lies in the normal ball, and injectivity of `exp_p` there identifies the two
geodesics.

## Main results

* `TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_pathELength_eq_of_piecewise` and
  its `_le` variant: a piecewise `C¹` minimizer parametrized proportionally to arc length is the
  affinely parametrized radial geodesic.
* `TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_geodesic_pathELength_le`: a geodesic
  segment in a normal neighbourhood that is no longer than the radial segment is the radial
  segment.
* `TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_geodesic_pathELength_eq`: the same
  for a geodesic on an open interval containing `[0, 1]` that need not stay in a normal ball.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6.
-/

public section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable {p : M} {U : Set (TangentSpace I p)} {γ : ℝ → M} {v : TangentSpace I p} {a b : ℝ}

/-- **Uniqueness of the constant-speed radial minimizer.** A piecewise `C¹` curve on `[a, b]` from
the centre `p` of a normal neighbourhood to `exp_p v`, staying in the neighbourhood, having the
length of the radial segment, and parametrized proportionally to arc length, is the radial
geodesic traversed affinely: `γ t = exp_p (((t - a) / (b - a)) • v)` on `[a, b]`. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_pathELength_eq_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1)
    (hspeed : ∀ t ∈ Icc a b,
      pathELength I γ a t = ENNReal.ofReal ((t - a) / (b - a)) * pathELength I γ a b) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (((t - a) / (b - a)) • v)) (Icc a b) := by
  intro t ht
  have hcb : riemannianLog I M p U (γ b) = v := by
    rw [hγb, h.riemannianLog_riemannianExp hv]
  have hlen' : pathELength I γ a b = ‖riemannianLog I M p U (γ b)‖ₑ := by
    rw [hlen, pathELength_riemannianExp_smul_zero_one h hv, hcb]
  have hτ : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 hγ.lt.le)
  -- the radius of the logarithm is the arc length travelled, which constant speed makes affine
  have hnorm : ‖riemannianLog I M p U (γ t)‖ = (t - a) / (b - a) * ‖v‖ := by
    have he := h.enorm_riemannianLog_eq_pathELength_of_piecewise hγ hγU hγa hlen' ht
    rw [hspeed t ht, hlen', hcb, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul hτ] at he
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (by positivity)).1 he
  dsimp only
  rw [h.eq_riemannianExp_smul_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb hlen ht, hnorm]
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · rw [mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hv0)]

/-- A piecewise `C¹` curve on `[a, b]` from the centre `p` of a normal neighbourhood to `exp_p v`,
staying in the neighbourhood, no longer than the radial segment, and parametrized proportionally
to arc length, is the radial geodesic traversed affinely. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_pathELength_le_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b ≤
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1)
    (hspeed : ∀ t ∈ Icc a b,
      pathELength I γ a t = ENNReal.ofReal ((t - a) / (b - a)) * pathELength I γ a b) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (((t - a) / (b - a)) • v)) (Icc a b) :=
  h.eqOn_riemannianExp_smul_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb
    (le_antisymm hlen (h.pathELength_riemannianExp_smul_le_of_piecewise hv hγ hγU hγa hγb)) hspeed

/-- **Uniqueness of minimizing geodesics in a normal neighbourhood.** A geodesic segment on
`[0, 1]` from the centre `p` of a normal neighbourhood to `exp_p v` that stays in the
neighbourhood and is no longer than the radial segment is the radial segment
`t ↦ exp_p (t • v)`. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_geodesic_pathELength_le
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsGeodesicCurveOn I γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 ≤
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  have hγ' : IsPiecewiseContMDiffOn I 1 γ 0 1 :=
    .of_contMDiffOn zero_lt_one (hγ.contMDiffOn.of_le (by norm_num))
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      pathELength I γ 0 t = ENNReal.ofReal ((t - 0) / (1 - 0)) * pathELength I γ 0 1 := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Icc 0 1 := left_mem_Icc.2 zero_le_one
    rw [hγ.pathELength_eq isPreconnected_Icc h0 ht h0,
      hγ.pathELength_eq isPreconnected_Icc h0 (right_mem_Icc.2 zero_le_one) h0]
    simp [mul_comm]
  simpa using h.eqOn_riemannianExp_smul_of_pathELength_le_of_piecewise hv hγ' hγU hγ0 hγ1 hlen
    hspeed

/-- A geodesic from the centre of a normal ball that reaches `exp_p v` with the same length
as the radial segment to `v` agrees with that radial segment on `[0, 1]`. The initial velocity
of the competitor need not be assumed to lie in the normal ball: equality of lengths implies
that it has the same norm as `v`. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_geodesic_pathELength_eq
    {p : M} {r : ℝ} (h : IsNormalDomain I M p
      (Metric.ball (0 : TangentSpace I p) r))
    {v u : TangentSpace I p} (hv : v ∈ Metric.ball (0 : TangentSpace I p) r)
    {γ : ℝ → M} {a b : ℝ} (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p u)
    (hb : 1 < b) (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hγ.zero_mem.1 ht.1, lt_of_le_of_lt ht.2 hb⟩
  have heq : EqOn (maximalGeodesic I M p u) γ (Icc 0 1) :=
    (hγ.eqOn_maximalGeodesic).mono hIcc
  have hu1 : 1 ∈ geodesicInterval I M p u :=
    hγ.subset_geodesicInterval (hIcc ⟨zero_le_one, le_rfl⟩)
  have hlength : pathELength I γ 0 1 = ‖u‖ₑ := by
    rw [← pathELength_congr heq]
    simpa using pathELength_maximalGeodesic
      (zero_mem_geodesicInterval (I := I) (M := M) (p := p) (v := u)) hu1
  have hnorm : ‖u‖ = ‖v‖ := by
    have he : ‖u‖ₑ = ‖v‖ₑ := by
      rw [← hlength, hlen, pathELength_riemannianExp_smul_zero_one h hv]
    exact enorm_eq_iff_norm_eq.mp he
  have hu : u ∈ Metric.ball (0 : TangentSpace I p) r := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hv
  have huv : u = v := h.injOn hu hv (by
    rw [riemannianExp_def p u, heq ⟨zero_le_one, le_rfl⟩, hγ1])
  intro t ht
  rw [← heq ht, huv]
  exact (riemannianExp_smul p v t).symm

end TauCeti.Manifold

end
