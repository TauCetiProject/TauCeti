/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The faces of the Euclidean quadrant model

A face `{z | z i = 0}` of the quadrant `[0, ∞)^(m + 1)` is a copy of the quadrant `[0, ∞)^m` one
dimension down: deleting the vanishing coordinate `i` identifies them. This file provides the
coordinate maps realising this identification, for use by charts of faces of manifolds modelled on
the quadrant `𝓡c (m + 1)`, in the same way as `TauCeti.Geometry.Manifold.Boundary.Model` does for
the boundary hyperplane of the half-space model `𝓡∂ (n + 1)`.

## Main definitions

* `TauCeti.euclideanQuadrantFaceParam i`: insertion of a zero coordinate in slot `i`, the extension
  by zero along `Fin.succAboveEmb i`.
* `TauCeti.euclideanQuadrantFaceProj i`: deletion of the coordinate `i`. On the hyperplane
  `z i = 0` it inverts `TauCeti.euclideanQuadrantFaceParam i`.
* `TauCeti.euclideanQuadrantFaceInclusion i`: the inclusion of the quadrant of dimension `m` onto
  the face `z i = 0` of the quadrant of dimension `m + 1`.
-/

public section

noncomputable section

open Set

open scoped Manifold

namespace TauCeti

variable {m : ℕ}

/-- Insert a zero in slot `i`. This parametrizes the coordinate hyperplane `z i = 0` of
`EuclideanSpace ℝ (Fin (m + 1))` by `EuclideanSpace ℝ (Fin m)`, and maps the quadrant of
dimension `m` onto the face `z i = 0` of the quadrant of dimension `m + 1`. It is the extension by
zero `LinearIsometry.piLpExtendByZero` along `Fin.succAboveEmb i`. -/
def euclideanQuadrantFaceParam (i : Fin (m + 1)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (LinearIsometry.piLpExtendByZero 2 ℝ ℝ i.succAboveEmb).toContinuousLinearMap

@[simp]
theorem euclideanQuadrantFaceParam_apply_self (i : Fin (m + 1)) (q : EuclideanSpace ℝ (Fin m)) :
    euclideanQuadrantFaceParam i q i = 0 := by
  simp [euclideanQuadrantFaceParam, Function.extend_apply']

@[simp]
theorem euclideanQuadrantFaceParam_apply_succAbove (i : Fin (m + 1))
    (q : EuclideanSpace ℝ (Fin m)) (k : Fin m) :
    euclideanQuadrantFaceParam i q (i.succAbove k) = q k := by
  simp [euclideanQuadrantFaceParam, Fin.succAbove_right_injective.extend_apply]

/-- Delete the coordinate `i`. On the hyperplane `z i = 0` this inverts
`TauCeti.euclideanQuadrantFaceParam i`. -/
def euclideanQuadrantFaceProj (i : Fin (m + 1)) :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun z := WithLp.toLp 2 (Fin.removeNth i z)
      map_add' z z' := by ext k; simp [Fin.removeNth]
      map_smul' c z := by ext k; simp [Fin.removeNth] }

@[simp]
theorem euclideanQuadrantFaceProj_apply (i : Fin (m + 1)) (z : EuclideanSpace ℝ (Fin (m + 1)))
    (k : Fin m) : euclideanQuadrantFaceProj i z k = z (i.succAbove k) := by
  simp [euclideanQuadrantFaceProj, Fin.removeNth]

@[simp]
theorem euclideanQuadrantFaceProj_faceParam (i : Fin (m + 1)) (q : EuclideanSpace ℝ (Fin m)) :
    euclideanQuadrantFaceProj i (euclideanQuadrantFaceParam i q) = q := by
  ext k
  simp

theorem euclideanQuadrantFaceParam_faceProj {i : Fin (m + 1)}
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : z i = 0) :
    euclideanQuadrantFaceParam i (euclideanQuadrantFaceProj i z) = z := by
  ext j
  refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp [hz]

/-- On the quadrant, `TauCeti.euclideanQuadrantFaceParam i` takes values in the quadrant. -/
theorem euclideanQuadrantFaceParam_nonneg (i : Fin (m + 1)) (q : EuclideanQuadrant m)
    (j : Fin (m + 1)) : 0 ≤ euclideanQuadrantFaceParam i q.1 j := by
  refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
  · simp
  · simpa using q.2 k

/-- The inclusion of the quadrant of dimension `m` onto the face `z i = 0` of the quadrant of
dimension `m + 1`: reinsert a zero coordinate in slot `i`. -/
@[expose] def euclideanQuadrantFaceInclusion (i : Fin (m + 1)) (q : EuclideanQuadrant m) :
    EuclideanQuadrant (m + 1) :=
  ⟨euclideanQuadrantFaceParam i q.1, euclideanQuadrantFaceParam_nonneg i q⟩

@[simp]
theorem coe_euclideanQuadrantFaceInclusion (i : Fin (m + 1)) (q : EuclideanQuadrant m) :
    (euclideanQuadrantFaceInclusion i q).1 = euclideanQuadrantFaceParam i q.1 :=
  rfl

theorem continuous_euclideanQuadrantFaceInclusion (i : Fin (m + 1)) :
    Continuous (euclideanQuadrantFaceInclusion (m := m) i) :=
  ((euclideanQuadrantFaceParam i).continuous.comp continuous_subtype_val).subtype_mk _

/-- Reinserting the zero coordinate commutes with the model embeddings. -/
theorem modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam (i : Fin (m + 1))
    (q : EuclideanQuadrant m) :
    (𝓡c (m + 1)).symm (euclideanQuadrantFaceParam i ((𝓡c m) q)) =
      euclideanQuadrantFaceInclusion i q :=
  (𝓡c (m + 1)).left_inv (euclideanQuadrantFaceInclusion i q)

end TauCeti

/-- Every coordinate is nonnegative on the quadrant, so every coordinate gives faces. -/
theorem ModelWithCorners.nonneg_of_mem_range_modelWithCornersEuclideanQuadrant {m : ℕ}
    (i : Fin m) : ∀ z ∈ range (𝓡c m), 0 ≤ z i := by
  rintro _ ⟨y, rfl⟩
  exact y.2 i
