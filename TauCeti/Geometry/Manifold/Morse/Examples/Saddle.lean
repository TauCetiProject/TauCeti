/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormSq
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# The quadratic model of a Morse critical point and the saddle of the plane

On a product `E × F` of finite-dimensional real inner product spaces, with its self-model, the
function `q (u, v) = -‖u‖ ^ 2 + ‖v‖ ^ 2` is the model of a nondegenerate critical point of index
`dim E`, in the normalization of a normalized Morse chart, `f = f(p) - Σ_{i<λ} yᵢ² + Σ_{i≥λ} yᵢ²`,
which has no factor `1/2`. This file reads off its critical data as a function on a manifold.

* **The model.** The origin is the only critical point of `q`
  (`TauCeti.criticalPoints_neg_norm_sq_add_norm_sq`), so `q` has one critical point
  (`TauCeti.totalCriticalCount_neg_norm_sq_add_norm_sq`), and it is nondegenerate, so `q` is a
  Morse function (`TauCeti.isMorse_neg_norm_sq_add_norm_sq`). Its critical Hessian is
  `((u, v), (u', v')) ↦ -2 ⟪u, u'⟫ + 2 ⟪v, v'⟫`
  (`TauCeti.criticalHessian_neg_norm_sq_add_norm_sq_apply`) and its Morse index is `dim E`
  (`TauCeti.manifoldMorseIndex_neg_norm_sq_add_norm_sq`), so its only critical point is counted in
  index `dim E` (`TauCeti.criticalCount_neg_norm_sq_add_norm_sq`).
* **The saddle of the plane.** For `E = F = ℝ` this is `f (x, y) = -x² + y²` on `ℝ × ℝ`. Its only
  critical point is the origin (`TauCeti.criticalPoints_neg_sq_add_sq`), so it has one critical
  point (`TauCeti.totalCriticalCount_neg_sq_add_sq`), which is nondegenerate
  (`TauCeti.isMorse_neg_sq_add_sq`). In the coordinates of the plane its Hessian is `diag(-2, 2)`,
  the bilinear form `(v, w) ↦ -2 v₁ w₁ + 2 v₂ w₂` (`TauCeti.criticalHessian_neg_sq_add_sq_apply`),
  and its Morse index is `1` (`TauCeti.manifoldMorseIndex_neg_sq_add_sq`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, Lemma 2.2 (the Morse lemma), whose normal form this model is.
-/

public section

open Set Module
open scoped Manifold RealInnerProductSpace

namespace TauCeti

/-! ### The model on a product of inner product spaces -/

section Model

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- **The origin is the only critical point** of the model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2`. -/
@[simp]
theorem criticalPoints_neg_norm_sq_add_norm_sq :
    criticalPoints 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) = {0} := by
  ext p
  rw [mem_criticalPoints_iff_fderiv_eq_zero, fderiv_neg_norm_sq_add_norm_sq_eq_zero_iff,
    mem_singleton_iff]

/-- The model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` has exactly one critical point. -/
@[simp]
theorem totalCriticalCount_neg_norm_sq_add_norm_sq :
    totalCriticalCount 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) = 1 := by
  rw [totalCriticalCount_def, criticalPoints_neg_norm_sq_add_norm_sq, encard_singleton]

/-- **The critical Hessian of the model** `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` is
`((u, v), (u', v')) ↦ -2 ⟪u, u'⟫ + 2 ⟪v, v'⟫` at every point. -/
theorem criticalHessian_neg_norm_sq_add_norm_sq_apply (p v w : E × F) :
    criticalHessian 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) p v w =
      -2 * ⟪v.1, w.1⟫ + 2 * ⟪v.2, w.2⟫ := by
  rw [criticalHessian_modelSpace]
  exact fderiv_fderiv_neg_norm_sq_add_norm_sq_apply p v w

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` is a Morse function**: its only critical point,
the origin, is nondegenerate. -/
theorem isMorse_neg_norm_sq_add_norm_sq :
    IsMorse 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) := by
  refine isMorse_modelSpace_iff.2 ⟨((contDiff_norm_sq ℝ).comp contDiff_fst).neg.add
    ((contDiff_norm_sq ℝ).comp contDiff_snd), hasNondegenerateCriticalPointsOn_iff.2
      fun p _ hp ↦ ?_⟩
  rw [fderiv_neg_norm_sq_add_norm_sq_eq_zero_iff.1 hp]
  exact isNondegenerateCriticalPoint_neg_norm_sq_add_norm_sq

/-- **The model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` has Morse index `dim E`** at every point. -/
theorem manifoldMorseIndex_neg_norm_sq_add_norm_sq (p : E × F) :
    manifoldMorseIndex 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) p = finrank ℝ E := by
  rw [manifoldMorseIndex_modelSpace, morseIndex_neg_norm_sq_add_norm_sq]

/-- The only critical point of the model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` has index `dim E`: the
critical count is `1` in index `dim E` and `0` in every other index. -/
theorem criticalCount_neg_norm_sq_add_norm_sq (j : ℕ) :
    criticalCount 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) j =
      if j = finrank ℝ E then 1 else 0 := by
  rw [criticalCount_def, criticalPoints_neg_norm_sq_add_norm_sq]
  simp only [manifoldMorseIndex_neg_norm_sq_add_norm_sq]
  split_ifs with hj
  · simp [hj]
  · simp [Ne.symm hj]

end Model

/-! ### The saddle of the plane -/

section Plane

/-- The saddle `-x² + y²` of the plane is the model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` on `ℝ × ℝ`. -/
private theorem neg_sq_add_sq_eq :
    (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) = fun p : ℝ × ℝ ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  ext p
  simp [Real.norm_eq_abs, sq_abs]

/-- **The origin is the only critical point of the saddle** `-x² + y²` of the plane. -/
@[simp]
theorem criticalPoints_neg_sq_add_sq :
    criticalPoints 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) = {0} := by
  rw [neg_sq_add_sq_eq, criticalPoints_neg_norm_sq_add_norm_sq]

/-- The saddle `-x² + y²` of the plane has exactly one critical point. -/
@[simp]
theorem totalCriticalCount_neg_sq_add_sq :
    totalCriticalCount 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) = 1 := by
  rw [neg_sq_add_sq_eq, totalCriticalCount_neg_norm_sq_add_norm_sq]

/-- The saddle `-x² + y²` of the plane is a Morse function. -/
theorem isMorse_neg_sq_add_sq : IsMorse 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) := by
  rw [neg_sq_add_sq_eq]
  exact isMorse_neg_norm_sq_add_norm_sq

/-- **The saddle `-x² + y²` of the plane has Morse index `1`.** -/
theorem manifoldMorseIndex_neg_sq_add_sq (p : ℝ × ℝ) :
    manifoldMorseIndex 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) p = 1 := by
  rw [neg_sq_add_sq_eq, manifoldMorseIndex_neg_norm_sq_add_norm_sq, finrank_self]

/-- **The Hessian of the saddle `-x² + y²` of the plane is `diag(-2, 2)`**: at every point it is
the bilinear form `(v, w) ↦ -2 v₁ w₁ + 2 v₂ w₂` in the coordinates of `ℝ × ℝ`. -/
theorem criticalHessian_neg_sq_add_sq_apply (p v w : ℝ × ℝ) :
    criticalHessian 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) p v w =
      -2 * (v.1 * w.1) + 2 * (v.2 * w.2) := by
  rw [neg_sq_add_sq_eq, criticalHessian_neg_norm_sq_add_norm_sq_apply]
  simp [mul_comm]

end Plane

end TauCeti
