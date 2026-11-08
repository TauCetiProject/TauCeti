/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Two-forms on surfaces with an almost complex structure

On a surface oriented so that the frames `(e, j e)` of an almost complex structure `j` are
positive, a two-form evaluated on a basis is its value on a frame `(e, j e)` times the
determinant of the basis in that frame. So it is nonnegative on positively oriented bases as soon
as it is nonnegative on the frames `(e, j e)`
(`TauCeti.SmoothTwoForm.apply_nonneg_of_eval₂_nonneg`).

## Main statements

* `TauCeti.SmoothTwoForm.apply_nonneg_of_eval₂_nonneg`: on a surface whose complex frames
  `(e, j e)` are positively oriented, a two-form that is nonnegative on those frames is
  nonnegative on every positively oriented basis.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {j : SmoothAlmostComplexStructure I M} {o : Manifold.Orientation I M (Fin 2)}

/-- A two-form on a surface that is nonnegative on the complex frames `(e, j e)` is nonnegative on
every positively oriented basis, when the frames `(e, j e)` are positively oriented. -/
theorem apply_nonneg_of_eval₂_nonneg (α : SmoothTwoForm I M) {c : M}
    (ho : ∀ (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hα : ∀ e, 0 ≤ SmoothBundleForm.eval₂ α c e (j c e))
    (b : Basis (Fin 2) ℝ (TangentSpace I c)) (hb : b.orientation = o.orientationAt c) :
    0 ≤ α.1 c b := by
  -- The complex frame `b₀ = (b 0, j (b 0))`.
  set b₀ := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt c).linearIndependent_pair (b.ne_zero 0))
    (by simpa using (o.finrank_tangentSpace_eq c).symm)
  have hb₀ : ⇑b₀ = ![b 0, j c (b 0)] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  -- A top form on the plane is `det_{b₀}` times its value on the frame `b₀`.
  rw [ContinuousAlternatingMap.apply_eq_det_mul (α.1 c) b₀ b]
  refine mul_nonneg ((b₀.orientation_eq_iff_det_pos b).1 ?_).le ?_
  · rw [hb, ho b₀ (by rw [hb₀]; simp)]
  · rw [hb₀, ← SmoothBundleForm.eval₂_apply]
    exact hα _

end SmoothTwoForm

end TauCeti
