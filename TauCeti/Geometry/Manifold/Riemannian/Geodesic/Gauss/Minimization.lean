/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.EDistComparison
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.RadialLength

/-!
# Radial minimization inside a normal neighbourhood

The radial geodesic from the centre of a normal neighbourhood to one of its points minimizes
Riemannian length among the `C¹` curves that stay in that neighbourhood. The Gauss lemma gives a
lower bound by the change in the norm of the logarithm; the radial geodesic attains that bound.
Corner smoothing extends the comparison to piecewise `C¹` competitors without changing their
endpoints or length while keeping them inside the normal neighbourhood.

This local comparison is the input for the escape argument that turns radial length into the
Riemannian distance, whose infimum ranges over paths that may leave the normal neighbourhood.

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

/-- **A radial geodesic minimizes length inside a normal neighbourhood.** Any `C¹` curve from
`p` to `exp_p v` that remains in the image of a normal domain containing `v` has length at least
that of the radial geodesic. -/
theorem IsNormalDomain.pathELength_riemannianExp_smul_le
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    {v : TangentSpace I p} (hv : v ∈ U)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U))
    (hγa : γ a = p) (hγb : γ b = riemannianExp I M p v) :
    pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 ≤
      pathELength I γ a b := by
  rw [pathELength_riemannianExp_smul_zero_one h hv]
  have hbound := h.ofReal_norm_riemannianLog_le_pathELength
    hab hγ hγU hγa
  simpa only [hγb, h.riemannianLog_riemannianExp hv, ofReal_norm] using hbound

/-- A radial geodesic also minimizes against piecewise `C¹` competitors in the normal
neighbourhood, including broken paths with finitely many corners. The competitor may have any
nondegenerate compact parameter interval. -/
theorem IsNormalDomain.pathELength_riemannianExp_smul_le_of_piecewise
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    {v : TangentSpace I p} (hv : v ∈ U)
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U))
    (hγa : γ a = p) (hγb : γ b = riemannianExp I M p v) :
    pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 ≤
      pathELength I γ a b := by
  obtain ⟨η, hη, hη0, hη1, hlength, hηU⟩ :=
    hγ.exists_contMDiff_pathELength_eq_of_mapsTo hγU
  rw [← hlength]
  exact h.pathELength_riemannianExp_smul_le hv zero_le_one hη.contMDiffOn hηU
    (hη0.trans hγa) (hη1.trans hγb)

end TauCeti.Manifold

end
