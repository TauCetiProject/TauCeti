/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Minimization
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length

/-!
# Uniqueness of minimizing geodesics in a normal ball

The exponential map is injective on a normal ball. A geodesic segment starting at the centre
and having the length of the radial segment to its endpoint has the same initial speed. Its
initial velocity therefore lies in the normal ball, and injectivity identifies the two
geodesics. This is the geodesic case of rigidity in the local radial length comparison.

The competitor is assumed to be a geodesic on an open interval containing `[0, 1]`, so its
initial velocity and endpoint are supplied by the maximal-geodesic API. The equality case for
arbitrary length-minimizing curves requires a separate argument that such curves are geodesics.

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
  [T2Space (TangentBundle I M)]

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

/-- Among geodesics inside a normal ball from its centre to `exp_p v`, the radial segment is
the only one whose length is no greater than the radial length. In particular, it is the only
minimizing geodesic with that endpoint that stays in the normal ball. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_geodesic_pathELength_le
    {p : M} {r : ℝ} (h : IsNormalDomain I M p
      (Metric.ball (0 : TangentSpace I p) r))
    {v u : TangentSpace I p} (hv : v ∈ Metric.ball (0 : TangentSpace I p) r)
    {γ : ℝ → M} {a b : ℝ} (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p u)
    (hb : 1 < b)
    (hγU : MapsTo γ (Icc 0 1)
      (riemannianExp I M p '' Metric.ball (0 : TangentSpace I p) r))
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 ≤
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hγ.zero_mem.1 ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hγdiff : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (hγ.isGeodesicCurveOn.contMDiffOn.of_le (by norm_num)).mono hIcc
  have hle := h.pathELength_riemannianExp_smul_le hv zero_le_one hγdiff hγU
    hγ.base_eq hγ1
  exact h.eqOn_riemannianExp_smul_of_geodesic_pathELength_eq hv hγ hb hγ1
    (le_antisymm hlen hle)

end TauCeti.Manifold

end
