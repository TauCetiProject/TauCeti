/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# The full-dimensional standard simplex

The simplex with nonnegative coordinates whose sum is at most one is an integration domain in
Euclidean space. Its homeomorphism with Mathlib's barycentric `Convexity.StdSimplex` adds the
zeroth weight, equal to one minus the sum of the coordinates. The face inclusions are transported
from Mathlib's maps of barycentric simplices. The bridge reuses
`AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex` and
`AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex`; `finRotate` moves the omitted
last coordinate to the zeroth position.

This is the full-dimensional simplex convention used in Lee, *Introduction to Smooth Manifolds*,
Chapter 18. The barycentric simplex, its topology, and its maps are those of Mathlib.
-/

public section

open scoped BigOperators
open Convexity

namespace TauCeti

/-- The full-dimensional standard simplex in Euclidean `p`-space. -/
noncomputable def fullSimplex (p : ℕ) : Set (EuclideanSpace ℝ (Fin p)) :=
  (EuclideanSpace.equiv (Fin p) ℝ) ⁻¹' coordinateSimplex (Fin p)

/-- Membership in the full-dimensional simplex is coordinate nonnegativity and a sum bound. -/
@[simp]
theorem mem_fullSimplex_iff {p : ℕ} {x : EuclideanSpace ℝ (Fin p)} :
    x ∈ fullSimplex p ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  exact mem_coordinateSimplex _ _

/-- Adding the missing zeroth weight identifies the full-dimensional and barycentric simplices. -/
noncomputable def fullSimplexEquivStdSimplex (p : ℕ) :
    fullSimplex p ≃ₜ StdSimplex ℝ (Fin (p + 1)) := by
  exact ((EuclideanSpace.equiv (Fin p) ℝ).toHomeomorph.subtype
    (p := fun x ↦ x ∈ fullSimplex p) (q := fun x ↦ x ∈ coordinateSimplex (Fin p))
    (fun _ ↦ Iff.rfl)).trans
    ((AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex p).symm.trans
      (AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex.trans
        ((finRotate (p + 1)).stdSimplexHomeomorph (R := ℝ))))

/-- The positive-index weights are precisely the original Euclidean coordinates. -/
@[simp]
theorem fullSimplexEquivStdSimplex_weights_succ {p : ℕ} (x : fullSimplex p) (i : Fin p) :
    (fullSimplexEquivStdSimplex p x).weights i.succ = x.val i := by
  have hrot : finRotate (p + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [fullSimplexEquivStdSimplex, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply, ← hrot]
  simp only [Equiv.coe_stdSimplexHomeomorph, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (finRotate (p + 1)).injective,
    AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex_apply,
    AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex_symm_castSucc]
  rfl

/-- The zeroth weight is the unused part of the coordinate sum. -/
@[simp]
theorem fullSimplexEquivStdSimplex_weights_zero {p : ℕ} (x : fullSimplex p) :
    (fullSimplexEquivStdSimplex p x).weights 0 = 1 - ∑ i, x.val i := by
  rw [fullSimplexEquivStdSimplex, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply, ← finRotate_last (n := p)]
  simp only [Equiv.coe_stdSimplexHomeomorph, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (finRotate (p + 1)).injective,
    AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex_apply,
    AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex_symm_last]
  rfl

/-- The inverse bridge forgets the zeroth barycentric coordinate. -/
@[simp]
theorem fullSimplexEquivStdSimplex_symm_apply {p : ℕ}
    (w : StdSimplex ℝ (Fin (p + 1))) (i : Fin p) :
    ((fullSimplexEquivStdSimplex p).symm w).val i = w.weights i.succ := by
  rw [← fullSimplexEquivStdSimplex_weights_succ]
  simp

/-- The `i`-th face inclusion, obtained by inserting a zero barycentric weight at `i`. -/
noncomputable def simplexFace (p : ℕ) (i : Fin (p + 2)) :
    fullSimplex p → fullSimplex (p + 1) :=
  (fullSimplexEquivStdSimplex (p + 1)).symm ∘ StdSimplex.map i.succAbove ∘
    fullSimplexEquivStdSimplex p

/-- The bridge intertwines a face inclusion with the barycentric coface map. -/
theorem fullSimplexEquivStdSimplex_simplexFace {p : ℕ} (i : Fin (p + 2))
    (x : fullSimplex p) :
    fullSimplexEquivStdSimplex (p + 1) (simplexFace p i x) =
      (fullSimplexEquivStdSimplex p x).map i.succAbove := by
  exact (fullSimplexEquivStdSimplex (p + 1)).apply_symm_apply _

/-- The face inclusion preserves the weights away from its missing vertex. -/
@[simp]
theorem fullSimplexEquivStdSimplex_simplexFace_succAbove {p : ℕ} (i : Fin (p + 2))
    (x : fullSimplex p) (j : Fin (p + 1)) :
    (fullSimplexEquivStdSimplex (p + 1) (simplexFace p i x)).weights (i.succAbove j) =
      (fullSimplexEquivStdSimplex p x).weights j := by
  rw [fullSimplexEquivStdSimplex_simplexFace, StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective i.succAbove_right_injective _ _

/-- The weight at the missing vertex of a face is zero. -/
@[simp]
theorem fullSimplexEquivStdSimplex_simplexFace_self {p : ℕ} (i : Fin (p + 2))
    (x : fullSimplex p) :
    (fullSimplexEquivStdSimplex (p + 1) (simplexFace p i x)).weights i = 0 := by
  rw [fullSimplexEquivStdSimplex_simplexFace, StdSimplex.weights_map]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

/-- Every face inclusion is continuous in the full-dimensional topology. -/
@[fun_prop]
theorem continuous_simplexFace (p : ℕ) (i : Fin (p + 2)) : Continuous (simplexFace p i) :=
  (fullSimplexEquivStdSimplex (p + 1)).symm.continuous.comp
    ((StdSimplex.continuous_map ℝ i.succAbove).comp
      (fullSimplexEquivStdSimplex p).continuous)

/-- The affine extension of a face inclusion to the whole Euclidean ambient space.
It inserts a zero into the barycentric coordinates and then drops the zeroth coordinate. -/
noncomputable def simplexFaceAmbient (p : ℕ) (i : Fin (p + 2)) :
    EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (p + 1)) := by
  let coordinates : Fin p → EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] ℝ :=
    fun k ↦ (EuclideanSpace.proj k).toContinuousAffineMap
  let weights : Fin (p + 1) → EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] ℝ :=
    Fin.cons (ContinuousAffineMap.const ℝ _ 1 -
      (∑ k, (EuclideanSpace.proj k :
        EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)).toContinuousAffineMap)
      coordinates
  let face : EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] (Fin (p + 1) → ℝ) := {
    toAffineMap := AffineMap.pi fun j ↦
      (Fin.insertNth (α := fun _ ↦ EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] ℝ) i
        (ContinuousAffineMap.const ℝ _ (0 : ℝ)) weights j.succ).toAffineMap
    cont := continuous_pi fun j ↦
      (Fin.insertNth (α := fun _ ↦ EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] ℝ) i
        (ContinuousAffineMap.const ℝ _ (0 : ℝ)) weights j.succ).continuous }
  exact ContinuousAffineMap.comp
    (EuclideanSpace.equiv (Fin (p + 1)) ℝ).symm.toContinuousLinearMap.toContinuousAffineMap face

/-- The ambient extension has the explicit coordinate formula obtained by inserting a zero. -/
theorem simplexFaceAmbient_apply (p : ℕ) (i : Fin (p + 2))
    (x : EuclideanSpace ℝ (Fin p)) (j : Fin (p + 1)) :
    simplexFaceAmbient p i x j =
      Fin.insertNth (α := fun _ ↦ ℝ) i 0
        (Fin.cons (1 - ∑ k, x k) (fun k ↦ x k)) j.succ := by
  have h (k : Fin (p + 2)) :
      (Fin.insertNth (α := fun _ ↦ EuclideanSpace ℝ (Fin p) →ᴬ[ℝ] ℝ) i
        (ContinuousAffineMap.const ℝ _ (0 : ℝ))
        (Fin.cons (ContinuousAffineMap.const ℝ _ 1 -
          (∑ k, (EuclideanSpace.proj k :
            EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)).toContinuousAffineMap)
          (fun k ↦ (EuclideanSpace.proj k).toContinuousAffineMap)) k) x =
        Fin.insertNth (α := fun _ ↦ ℝ) i 0
          (Fin.cons (1 - ∑ k, x k) (fun k ↦ x k)) k := by
    induction k using i.succAboveCases with
    | x => simp
    | p k =>
      simp only [Fin.insertNth_apply_succAbove]
      cases k using Fin.cases with
      | zero => simp
      | succ k => simp
  convert h j.succ using 1
  -- The ambient construction conjugates this coordinate map by the Euclidean/Pi equivalence.
  rfl

/-- The affine ambient extension restricts to the face map on the simplex. -/
theorem simplexFaceAmbient_coe {p : ℕ} (i : Fin (p + 2)) (x : fullSimplex p) :
    simplexFaceAmbient p i x.val = (simplexFace p i x).val := by
  ext j
  rw [simplexFaceAmbient_apply, ← fullSimplexEquivStdSimplex_weights_succ]
  induction j.succ using i.succAboveCases with
  | x => simp
  | p j =>
    rw [fullSimplexEquivStdSimplex_simplexFace_succAbove, Fin.insertNth_apply_succAbove]
    cases j using Fin.cases <;> simp

end TauCeti
