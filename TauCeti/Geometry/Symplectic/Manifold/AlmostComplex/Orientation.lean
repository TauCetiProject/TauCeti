/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# Top forms on the complex frames of an oriented almost complex surface

Let `j` be an almost complex structure on a surface `C`, oriented at a point `c` so that every
frame `(e, j e)` of the tangent plane is positive. Every nonzero `e` gives such a frame, so a
top form `η` on the tangent plane is determined by its values `η (e, j e)`: on any basis `b`,

`η b = η (b₀, j b₀) · det_{(b₀, j b₀)} b`,  `b₀ = b 0`.

The determinant is positive when `b` is positively oriented. Hence a top form that is nonnegative
on every frame `(e, j e)` is nonnegative on every positively oriented basis
(`TauCeti.SmoothAlmostComplexStructure.apply_basis_nonneg_of_forall_nonneg`). This is the
pointwise input to the positivity of energy integrals `∫_C u^* ω` of pseudoholomorphic curves,
whose densities `(u^* ω)(e, j e)` are nonnegative when `ω` tames the target structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (energy of holomorphic curves).
-/

public section

noncomputable section

open Module
open scoped ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] (j : SmoothAlmostComplexStructure I C) {o : Manifold.Orientation I C (Fin 2)}

/-- **Top forms nonnegative on complex frames.** Let `j` be an almost complex structure on a
surface `C`, oriented at `c` so that every frame `(e, j e)` is positive. A top form `η` on the
tangent plane at `c` with `η (e, j e) ≥ 0` for every `e` is nonnegative on every positively
oriented basis. Indeed `η b = η (b₀, j b₀) det_{(b₀, j b₀)} b` for `b₀ = b 0`, and the
determinant is positive because both frames are positive. -/
theorem apply_basis_nonneg_of_forall_nonneg {c : C}
    (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace I c), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    {η : TangentSpace I c [⋀^Fin 2]→L[ℝ] ℝ} (hη : ∀ e, 0 ≤ η ![e, j c e])
    (b : Basis (Fin 2) ℝ (TangentSpace I c)) (hb : b.orientation = o.orientationAt c) :
    0 ≤ η b := by
  -- The frame `b₀ = (b 0, j (b 0))`.
  set b₀ := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt c).linearIndependent_pair (b.ne_zero 0))
    (by simpa using (o.finrank_tangentSpace_eq c).symm)
  have hb₀ : ⇑b₀ = ![b 0, j c (b 0)] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, almostComplexStructureAt_apply]
  -- A top form on the plane is its value on the frame `b₀` times `det_{b₀}`.
  have hη' : η b = η b₀ * b₀.det b := by
    simpa using congrArg (fun f ↦ f b) (η.toAlternatingMap.eq_smul_basis_det b₀)
  rw [hη']
  refine mul_nonneg ?_ ((b₀.orientation_eq_iff_det_pos b).1 ?_).le
  · rw [hb₀]
    exact hη (b 0)
  · rw [hb, ho b₀ (by rw [hb₀]; simp)]

end SmoothAlmostComplexStructure

end TauCeti
