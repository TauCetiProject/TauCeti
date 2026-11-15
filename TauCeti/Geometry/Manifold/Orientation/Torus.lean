/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Orientation.Sign
public import TauCeti.Geometry.Manifold.Orientation.TopForm

/-!
# The orientation of a torus

For positive periods `p 0, …, p (n - 1)`, the volume form `dt_0 ∧ ⋯ ∧ dt_(n-1)` of the torus
`Tⁿ = ∀ i : Fin n, AddCircle (p i)` (`TauCeti.torusVolumeForm p`), the ordered wedge product of its
coordinate time forms, vanishes nowhere. It therefore determines an orientation of the torus
(`TauCeti.torusOrientation p`): a tangent basis, a family of vectors in `Fin n → ℝ`, is positive
exactly when the determinant of its coordinate matrix is positive. In particular the coordinate
basis is positive at every point (`TauCeti.orientationAt_torusOrientation`). Its `i`-th vector is
the positive time direction of the `i`-th coordinate circle, positive for `AddCircle.orientation`.
Informally, this is the product orientation of the oriented circles, taken in the order of
`Fin n`; no comparison with a product of orientations is formalised here.

The orientation depends on that order. Reordering the factors by a permutation `σ`, through
`x ↦ (j ↦ x (σ j))`, pulls the volume form back to `sign σ` times itself, so it has orientation sign
`sign σ` at every point (`TauCeti.orientationSign_torusOrientation_reindex`). The diagonal
rescaling of the periods by the rescaling diffeomorphisms `AddCircle (p i) ≃ AddCircle (q i)`
pulls the volume form back to a positive multiple of itself, so it preserves the orientations
(`TauCeti.isOrientationPreservingAt_piMap_diffeomorphAddCircle`).

## Main definitions

* `TauCeti.torusOrientation p`: the orientation of the torus on which the volume form is
  positive.

## Main results

* `TauCeti.orientation_eq_orientationAt_torusOrientation_iff`,
  `TauCeti.orientationAt_torusOrientation`: the tangent orientations of the torus.
* `TauCeti.orientationSign_torusOrientation_reindex`: the permutation sign law.
* `TauCeti.isOrientationPreservingAt_piMap_diffeomorphAddCircle`: the diagonal rescaling of the
  periods preserves orientation.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (orientations from nonvanishing top forms, product
  orientations).
-/

public section

noncomputable section

open Function Matrix TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} (p : Fin n → ℝ) [∀ i, Fact (0 < p i)]

/-! ### The orientation -/

/-- The **orientation of the torus** `∀ i : Fin n, AddCircle (p i)`: the orientation on which the
nowhere-vanishing volume form `dt_0 ∧ ⋯ ∧ dt_(n-1)` is positive. -/
def torusOrientation :
    Manifold.Orientation (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))
      (Fin n) :=
  ofTopForm (Module.finrank_fin_fun ℝ) (torusVolumeForm p).1
    ((torusVolumeForm p).isSmoothForm.of_le zero_le) (torusVolumeForm_apply_ne_zero p)

/-- A tangent basis `b` of the torus is positive exactly when the determinant of the matrix
`(b j i)` of the coordinates of its vectors is positive. -/
theorem orientation_eq_orientationAt_torusOrientation_iff {x : ∀ i, AddCircle (p i)}
    (b : Module.Basis (Fin n) ℝ (TangentSpace (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) x)) :
    b.orientation = (torusOrientation p).orientationAt x ↔
      0 < (Matrix.of fun i j ↦ b j i).det := by
  rw [torusOrientation, orientation_eq_orientationAt_ofTopForm_iff, torusVolumeForm_apply]

/-- At every point of the torus, whose tangent spaces are `Fin n → ℝ`, the coordinate basis is
positive: the positive time directions of the coordinate circles, in order, form a positive
basis. -/
@[simp]
theorem orientationAt_torusOrientation (x : ∀ i, AddCircle (p i)) :
    (torusOrientation p).orientationAt x = (Pi.basisFun ℝ (Fin n)).orientation :=
  ((orientation_eq_orientationAt_ofTopForm_iff _ _ _ _).mpr
    (one_pos.trans_eq (torusVolumeForm_apply_basisFun p x).symm)).symm

/-! ### Reordering the factors -/

/-- **The permutation sign law for orientations.** Reordering the factors of the torus by a
permutation `σ` has orientation sign `sign σ` at every point: it preserves the orientations when
`σ` is even and reverses them when `σ` is odd. -/
theorem orientationSign_torusOrientation_reindex (σ : Equiv.Perm (Fin n))
    (x : ∀ i, AddCircle (p i)) :
    orientationSign (torusOrientation p) (torusOrientation fun j ↦ p (σ j))
      (fun (x : ∀ i, AddCircle (p i)) (j : Fin n) ↦ x (σ j)) x = Equiv.Perm.sign σ := by
  have hf : mpullback _ _ (fun (x : ∀ i, AddCircle (p i)) (j : Fin n) ↦ x (σ j))
      (torusVolumeForm fun j ↦ p (σ j)).1 x =
        (Equiv.Perm.sign σ : ℝ) • (torusVolumeForm p).1 x :=
    SmoothForm.mpullback_apply_eq_smul_of_mpullback_eq_smul
      (mpullback_reindex_torusVolumeForm p σ) x
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] at hf ⊢
  · exact orientationSign_of_isOrientationPreservingAt
      (isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
        (by norm_num) hf)
  · exact orientationSign_of_isOrientationReversingAt
      (isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
        (by norm_num) hf)

/-! ### Rescaling the periods -/

/-- The diagonal rescaling of the periods, by the rescaling diffeomorphisms
`AddCircle (p i) ≃ AddCircle (q i)` of all coordinates, preserves the orientations of the tori. -/
theorem isOrientationPreservingAt_piMap_diffeomorphAddCircle (q : Fin n → ℝ)
    [∀ i, Fact (0 < q i)] (x : ∀ i, AddCircle (p i)) :
    IsOrientationPreservingAt (torusOrientation p) (torusOrientation q)
      (Pi.map fun j ↦ AddCircle.diffeomorphAddCircle (p j) (q j) ∞) x := by
  refine isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    (c := ∏ i, (p i)⁻¹ * q i) (Finset.prod_pos fun i _ ↦
      mul_pos (inv_pos.mpr (Fact.out : 0 < p i)) (Fact.out : 0 < q i))
    (SmoothForm.mpullback_apply_eq_smul_of_mpullback_eq_smul
      (mpullback_piMap_diffeomorphAddCircle_torusVolumeForm p q) x)

end TauCeti
