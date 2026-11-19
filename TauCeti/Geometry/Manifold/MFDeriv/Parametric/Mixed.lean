/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Mixed derivatives in a vector-space parameter

Let `F : G → M → F'` be a family of functions on a manifold `M`, parametrized by a normed space
`G` and jointly `C²` at `(a, x)`. The differential of `F r` at `x`, applied to a tangent vector
`v`, is a function of the parameter `r`, and the parameter derivative `y ↦ ∂_b F (a, y)` in a
direction `b` is a function on `M`. This file proves that the two mixed derivatives agree:

`∂_b (d (F r) x v) |_(r = a) = d (∂_b F (a, ·)) x v`

(`TauCeti.Manifold.fderiv_mvfderiv_apply`). It is the symmetry of the mixed second derivative of
a function on the product `G × M`, read with the manifold differential in the `M` variable. The
proof restricts the family to the line `t ↦ a + t • b` through `a` and applies the one-parameter
statement `TauCeti.Manifold.hasDerivAt_mvfderiv_apply`.
-/

public section

open Filter Function
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {F : G → M → F'} {a : G} {x : M}

/-- **Mixed derivatives in a vector-space parameter.** If a family `F : G → M → F'` is jointly
`C²` at `(a, x)` (analytic, over a field other than `ℝ` or `ℂ`), then the derivative at `a` in
the direction `b` of the differential of `F r` at `x`, applied to `v`, is the differential at `x`
of the parameter derivative `y ↦ ∂_b F (a, y)`, applied to `v`. -/
theorem fderiv_mvfderiv_apply
    (hF : ContMDiffAt (𝓘(𝕜, G).prod I) 𝓘(𝕜, F') (minSmoothness 𝕜 2) (uncurry F) (a, x))
    (v : TangentSpace I x) (b : G) :
    fderiv 𝕜 (fun r ↦ mvfderiv I (F r) x v) a b =
      mvfderiv I (fun y ↦ fderiv 𝕜 (fun r ↦ F r y) a b) x v := by
  have h1 : (1 : WithTop ℕ∞) ≤ minSmoothness 𝕜 2 := le_trans (by norm_num) le_minSmoothness
  have h2 : (1 : WithTop ℕ∞) + 1 ≤ minSmoothness 𝕜 2 := le_trans (by norm_num) le_minSmoothness
  -- The line `t ↦ a + t • b` through `a` in the direction `b`.
  have hline (t : 𝕜) : HasDerivAt (fun s : 𝕜 ↦ a + s • b) b t := by
    simpa using ((hasDerivAt_id t).smul_const b).const_add a
  have hFline : ContMDiffAt (𝓘(𝕜).prod I) 𝓘(𝕜, F') (minSmoothness 𝕜 2)
      (uncurry fun t ↦ F (a + t • b)) ((0 : 𝕜), x) := by
    have hL : ContMDiff (𝓘(𝕜).prod I) (𝓘(𝕜, G).prod I) (minSmoothness 𝕜 2)
        (fun p : 𝕜 × M ↦ (a + p.1 • b, p.2)) :=
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.comp contMDiff_fst).prodMk
        contMDiff_snd
    exact hF.comp_of_eq (hL ((0 : 𝕜), x)) (by simp)
  -- The parameter derivative of the differential, along the line.
  have hmv : DifferentiableAt 𝕜 (fun r ↦ (mvfderiv I (F r) x : E →L[𝕜] F')) a :=
    ((contMDiffAt_mvfderiv_of_contMDiffAt_uncurry (m := 1) hF h2).mdifferentiableAt
      one_ne_zero).differentiableAt
  -- `TangentSpace I x` is `E` by definition but carries no normed-space instances, so `v` is
  -- read in `E` to evaluate at it.
  have hdiff : DifferentiableAt 𝕜 (fun r ↦ mvfderiv I (F r) x v) a :=
    (ContinuousLinearMap.apply 𝕜 F' (show E from v)).differentiableAt.comp a hmv
  have hlhs : HasDerivAt (fun t : 𝕜 ↦ mvfderiv I (F (a + t • b)) x v)
      (fderiv 𝕜 (fun r ↦ mvfderiv I (F r) x v) a b) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) (by simp)
  rw [hlhs.unique (hasDerivAt_mvfderiv_apply hFline v)]
  -- Near `x`, each `F · y` is differentiable at `a`, so its derivative along the line at `0` is
  -- its derivative at `a` in the direction `b`.
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hF.of_le h1)
  have hgerm : (fun y ↦ deriv (fun t : 𝕜 ↦ F (a + t • b) y) 0) =ᶠ[𝓝 x]
      fun y ↦ fderiv 𝕜 (fun r ↦ F r y) a b := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hnear]
      with y hy
    have hy' : DifferentiableAt 𝕜 (fun r ↦ F r y) a :=
      ((hy.comp a (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        one_ne_zero).differentiableAt
    exact (hy'.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) (by simp)).deriv
  rw [hgerm.mvfderiv_eq]

end TauCeti.Manifold
