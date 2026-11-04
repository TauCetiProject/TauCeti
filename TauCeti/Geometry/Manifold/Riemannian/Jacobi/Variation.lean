/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface

/-!
# Variations through geodesics give Jacobi fields

Let `F : ℝ → ℝ → M` be a smooth family of curves `F q` in a Riemannian manifold, each of which is
a geodesic. Its variation field `V(t) = ∂_q F (0, t)` along the geodesic `γ = F 0` is a Jacobi
field: `D_t² V + R(V, γ')γ' = 0`. The symmetry lemma `D_t ∂_q F = D_q ∂_t F` turns `D_t² V` into
`D_t D_q ∂_t F`; exchanging the two covariant derivatives costs the curvature term
`R(∂_q F, ∂_t F)∂_t F`, and the remaining `D_q D_t ∂_t F` vanishes because every curve of the family
is a geodesic.

The hypotheses are local in the variation parameter: the family only needs to be `C³` at the
points of `{0} × s` and, at each parameter `t` of the open set `s`, to consist of curves with
vanishing acceleration at `t` for `q` near `0`. Radial families `exp_p (t • (v + q • w))`, which
are only defined on the natural domain of the exponential map, are of this kind.

## Main results

* `TauCeti.Manifold.isJacobiFieldOn_variationField`: the variation field of a family of geodesics
  is a Jacobi field.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 10.1.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 5, §2.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M} {s : Set ℝ}

/-- **The variation field of a family of geodesics is a Jacobi field.** Let `F : ℝ → ℝ → M` be
`C³` at every point of `{0} × s` for an open set `s`, and suppose that at every `t ∈ s` the curves
`F q` have vanishing acceleration for all `q` near `0`. Then the variation field
`t ↦ ∂_q F (0, t)` is a Jacobi field along the geodesic `F 0` on `s`. -/
theorem isJacobiFieldOn_variationField (hs : IsOpen s)
    (hF : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hgeod : ∀ t ∈ s, ∀ᶠ q in 𝓝 0, acceleration (leviCivitaConnection I M) (F q) t = 0) :
    IsJacobiFieldOn I (F 0) (variationField I F) s := by
  set cov := leviCivitaConnection I M
  have htor : cov.IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)
  -- The velocity fields of the curves `F q` and of the transverse curves `q ↦ F q t` are `C²`.
  have hW (t : ℝ) (ht : t ∈ s) : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (F z.1 z.2) (curveVelocity I (F z.1) z.2)) (0, t) :=
    (hF t ht).contMDiffAt_curveVelocity_snd (by norm_num)
  have hV (t : ℝ) (ht : t ∈ s) : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) t := by
    have hswap : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.2 z.1) (t, 0) :=
      (hF t ht).comp (t, 0) (contMDiff_iff_contDiff.mpr
        (by fun_prop : ContDiff ℝ 3 fun z : ℝ × ℝ ↦ (z.2, z.1))).contMDiffAt
    rw [variationField_def]
    exact (hswap.contMDiffAt_curveVelocity_snd (f := fun a b ↦ F b a) (by norm_num)).comp t
      (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 2) (0 : ℝ))).contMDiffAt
  have hgeo : IsGeodesicCurveOn I (F 0) s := by
    refine (isGeodesicCurveOn_iff_of_isOpen hs).2
      ⟨fun t ht ↦ ?_, fun t ht ↦ (hgeod t ht).self_of_nhds⟩
    exact ((hF t ht).comp t (contMDiff_iff_contDiff.mpr
      (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt).of_le (by norm_num)
      |>.contMDiffWithinAt
  refine ⟨hgeo, fun t ht ↦ (hV t ht).contMDiffWithinAt, fun r hr ↦ ?_⟩
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- On the open set `s` the derivatives within `s` are the unrestricted ones, and by the symmetry
  -- lemma `D_t V = D_q ∂_t F` near `r`.
  have hinner : ∀ᶠ t in 𝓝 r, alongCurveWithin cov (F 0) (variationField I F) s t =
      alongCurve cov (fun q ↦ F q t) (fun q ↦ curveVelocity I (F q) t) 0 := by
    filter_upwards [hs.mem_nhds hr] with t ht
    rw [alongCurveWithin_of_mem_nhds _ _ _ (hs.mem_nhds ht), variationField_def]
    exact alongCurve_curveVelocity_comm cov htor (f := F) (u := 0) (v := t)
      ((hF t ht).of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))
  rw [curveVelocityWithin_of_mem_nhds (hs.mem_nhds hr),
    alongCurveWithin_of_mem_nhds _ _ _ (hs.mem_nhds hr), alongCurve_congr _ _ _ hinner]
  -- Exchanging the covariant derivatives costs the curvature term; `D_q D_t ∂_t F` vanishes since
  -- the curves `F q` are geodesics near `q = 0`.
  have hcomm := alongCurve_alongCurve_sub_alongCurve_alongCurve cov
    (W := fun q t ↦ curveVelocity I (F q) t) (hW r hr)
  have hzero : alongCurve cov (fun q ↦ F q r)
      (fun q ↦ alongCurve cov (F q) (fun t ↦ curveVelocity I (F q) t) r) 0 = 0 := by
    have h0 : ∀ᶠ q in 𝓝 0,
        alongCurve cov (F q) (fun t ↦ curveVelocity I (F q) t) r = (0 : TangentSpace I (F q r)) :=
      (hgeod r hr).mono fun q hq ↦ by rw [acceleration_def] at hq; exact hq
    rw [alongCurve_congr cov (fun q ↦ F q r) _ h0]
    exact alongCurve_zero _ _ _
  rw [hzero, zero_sub, neg_eq_iff_eq_neg] at hcomm
  rw [hcomm, variationField_apply, neg_add_cancel]

end TauCeti.Manifold
