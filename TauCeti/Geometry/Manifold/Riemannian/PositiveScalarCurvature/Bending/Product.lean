/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Bending.Reparametrization
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Rotational
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod

/-!
# Bending in a product neighbourhood

A Gromov–Lawson bending curve `u ↦ (r u, h u)` (`TauCeti.IsGromovLawsonBendingCurve`) sweeps out
the hypersurface `{(r(u) x, h(u)) | x ∈ S^(q - 1)}` of `ℝ^q × ℝ`. When the curve is parametrised
with speed equal to its radius, the induced metric is the rotationally symmetric metric
`r² (g_(S^(q - 1)) + du²)` (`TauCeti.inner_mvfderiv_smul_coe_sphere_add_mul_mvfderiv`), whose
scalar curvature is the bending term
`(q - 1) (q - 2) sin² θ / r² - 2 (q - 1) k sin θ / r`
(`TauCeti.scalarCurvature_rotationalMetric_log`).

Every bending curve can be reparametrised to have speed equal to its radius
(`TauCeti.IsGromovLawsonBendingCurve.exists_orderIso_speed_eq_radius`).

Suppose that near a sphere `S^k` of codimension `q ≥ 3` in a Riemannian manifold the metric is a
product `g_N + g_(ℝ^q)` of a metric `g_N` on `N` with scalar curvature at least `R₀ > 0` and the
flat metric on the normal disc. Then the tube of radius `r` around `S^k` is a product
`N × S^(q - 1)(r)`, all errors in the principal curvatures of the tube vanish, and the hypersurface
of `M × ℝ` obtained by bending is `N × T`, where `T` is the hypersurface swept out by the curve.
Its induced metric is the product of `g_N` with the rotationally symmetric metric above, and its
scalar curvature is `Scal(g_N)` plus the bending term. The bending inequality makes this positive
(`TauCeti.IsGromovLawsonBendingCurve.hasPositiveScalarCurvature_rotationalMetric_prodTangentSpace`).
The theorem is stated for that product metric on `S^(q - 1) × ℝ × N`; the identification of the
first factor with the induced metric of `T` is
`TauCeti.inner_mvfderiv_smul_coe_sphere_add_mul_mvfderiv`. Since the curve is the `r`-axis for
`u ≤ 0` and ends in a vertical line `r = ρ` with `ρ < r₀`
(`TauCeti.IsGromovLawsonBendingCurve.exists_radius_eq`), the bent hypersurface agrees with
`N × ℝ^q × {0}` outside the tube of radius `r₀` and ends in the cylinder over `N × S^(q - 1)(ρ)`.

## Main results

* `TauCeti.IsGromovLawsonBendingCurve.hasPositiveScalarCurvature_rotationalMetric_prodTangentSpace`:
  the bent metric in a product neighbourhood has positive scalar curvature.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
* J. Rosenberg, S. Stolz, *Metrics of positive scalar curvature and connections with surgery*,
  Surveys on surgery theory, Vol. 2, Ann. of Math. Stud. 149 (2001), 353–386, Section 3.
-/

public section

noncomputable section

open Real Set Filter Metric Module Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace IsGromovLawsonBendingCurve

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H N] [IsManifold J ∞ N]
  {R₀ C r₀ : ℝ} {r h θ : ℝ → ℝ}

/-- **Bending in a product neighbourhood.** Let `g` be a metric on `N` with scalar curvature at
least `R₀`, and let `(r, h)` be a bending curve in codimension `q = n + 1` for the lower bound `R₀`
and an error constant `C ≥ 0`, with speed equal to its radius. The product of the rotationally
symmetric metric `r² (g_(Sⁿ) + du²)` on `Sⁿ × ℝ`, which is the metric induced on the hypersurface
of `ℝ^(n + 1) × ℝ` swept out by the curve, with `g` has positive scalar curvature. This is the
metric of the hypersurface obtained by bending `N × ℝ^(n + 1)`, with the product of `g` and the
flat metric, around `N × {0}`, read in the coordinates `Sⁿ × ℝ × N` of that hypersurface. -/
theorem hasPositiveScalarCurvature_rotationalMetric_prodTangentSpace
    (hγ : IsGromovLawsonBendingCurve (n + 1) R₀ C r₀ r h θ r) (hC : 0 ≤ C)
    {g : ContMDiffRiemannianMetric J ∞ E (fun x : N ↦ TangentSpace J x)}
    (hg : ∀ x, R₀ ≤ g.scalarCurvature x) :
    ((rotationalMetric (n := n) V
      (hγ.contDiff_radius.log fun u ↦ (hγ.radius_pos u).ne')).prodTangentSpace
        g).HasPositiveScalarCurvature := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  rw [ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff]
  intro p
  rw [ContMDiffRiemannianMetric.scalarCurvature_prodTangentSpace,
    scalarCurvature_rotationalMetric_log hγ.contDiff_radius hγ.radius_pos p.1
      (Eventually.of_forall hγ.hasDerivAt_radius)
      ((hγ.contDiff_angle.differentiable (by simp)) p.1.2)]
  have hpos := (hγ.mono le_rfl hC le_rfl).scalar_pos p.1.2
  push_cast at hpos
  rw [show (n : ℝ) + 1 - 1 = n by ring, show (n : ℝ) + 1 - 2 = n - 1 by ring] at hpos
  linarith [hg p.2]

end IsGromovLawsonBendingCurve

end TauCeti
