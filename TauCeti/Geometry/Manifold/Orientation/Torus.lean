/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Diffeomorph.Pi
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
public import TauCeti.Geometry.Manifold.Orientation.Sign
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.LinearAlgebra.Basis.Fin

/-!
# The orientation of a torus

For positive periods `p 0, …, p (n - 1)`, the volume form `dt_0 ∧ ⋯ ∧ dt_(n-1)` of the torus
`Tⁿ = ∀ i : Fin n, AddCircle (p i)` (`TauCeti.torusVolumeForm p`), the ordered wedge product of its
coordinate time forms, vanishes nowhere. It therefore determines an orientation of the torus
(`TauCeti.torusOrientation p`): a tangent basis, a family of vectors in `Fin n → ℝ`, is positive
exactly when the determinant of its coordinate matrix is positive. In particular the coordinate
basis is positive at every point (`TauCeti.orientationAt_torusOrientation`). Its `i`-th vector is
the positive time direction of the `i`-th coordinate circle, positive for `AddCircle.orientation`.

This orientation is the product orientation of the oriented circles, taken in the order of `Fin n`.
Splitting the factors into the first `m` and the last `k`, the concatenation diffeomorphism
`T^m × T^k → T^(m + k)`, `(x, y) ↦ Fin.addCases x y` (`Diffeomorph.piAddCases`), preserves
orientation from the product of the two torus orientations to the torus orientation
(`TauCeti.isOrientationPreservingAt_piAddCases_torusOrientation`). Informally, applying this
twice relates the two ways of grouping three tori; no declaration states that comparison.
Appending one circle, `(x, t) ↦ Fin.snoc x t` from `T^m × AddCircle (p m)` (`Diffeomorph.piSnoc`),
preserves orientation from the product of the torus orientation with the
positive orientation of the circle (`AddCircle.orientation`)
(`TauCeti.isOrientationPreservingAt_piSnoc_torusOrientation`), and the one-factor torus is its
circle (`TauCeti.isOrientationPreservingAt_piUnique_torusOrientation`). So, by induction on `n`,
`torusOrientation p` is the iterated product orientation
`((S¹_(p 0) × S¹_(p 1)) × ⋯) × S¹_(p (n - 1))`. Grouping the other way, the association map
`x ↦ (x 0, Fin.tail x)` from `T^(m + 1)` to `AddCircle (p 0) × T^m` (the inverse of
`Diffeomorph.piCons`) preserves orientation from the torus orientation to the product of the
positive orientation of the first circle with the torus orientation of the remaining factors
(`TauCeti.isOrientationPreservingAt_piCons_symm_torusOrientation`). The product orientation has
degree `1 + m`, and is read in degree `m + 1` through `TauCeti.Manifold.Orientation.reindex`. By
induction, `torusOrientation p` is also the iterated product orientation
`S¹_(p 0) × (S¹_(p 1) × ⋯ × (S¹_(p (n - 1)) × T^0))`, ending in the point factor. The empty
torus is a point, whose orientation is the positive orientation of the zero-dimensional tangent
space
(`TauCeti.orientationAt_torusOrientation_fin_zero`); with `k = 0` or `m = 0` the concatenation
theorem says that inserting or deleting this point factor does not change the orientation.

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
* `TauCeti.isOrientationPreservingAt_piAddCases_torusOrientation`: concatenating two tori
  preserves orientation from the product orientation.
* `TauCeti.isOrientationPreservingAt_piSnoc_torusOrientation`: appending a circle preserves
  orientation from the product of the torus orientation with `AddCircle.orientation`.
* `TauCeti.isOrientationPreservingAt_piCons_torusOrientation`: prepending a circle preserves
  orientation from the product of `AddCircle.orientation` with the torus orientation, read in
  degree `m + 1`, to the torus orientation.
* `TauCeti.isOrientationPreservingAt_piCons_symm_torusOrientation`: the association map
  splitting off the first circle preserves orientation from the torus orientation to that
  product.
* `TauCeti.isOrientationPreservingAt_piUnique_torusOrientation`: the one-factor torus is its
  circle.
* `TauCeti.orientationAt_torusOrientation_fin_zero`: the empty torus carries the positive
  orientation of a point.

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
  ofTopForm (Module.finrank_fin_fun ℝ) (torusVolumeForm p).val
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
      (torusVolumeForm fun j ↦ p (σ j)).val x =
        (Equiv.Perm.sign σ : ℝ) • (torusVolumeForm p).val x :=
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

/-! ### Products of tori -/

/-- **The empty torus is a point with its positive orientation.** For `n = 0` the torus is a
point, and its orientation is the positive orientation of the zero-dimensional tangent space. -/
theorem orientationAt_torusOrientation_fin_zero (p : Fin 0 → ℝ) [∀ i, Fact (0 < p i)]
    (x : ∀ i, AddCircle (p i)) :
    (torusOrientation p).orientationAt x = positiveOrientation := by
  rw [orientationAt_torusOrientation]
  exact Module.Basis.orientation_isEmpty _

variable {m k : ℕ}

/-- **Concatenating tori preserves orientation.** Concatenating the factors,
`(x, y) ↦ Fin.addCases x y` from `T^m × T^k` to `T^(m + k)`, preserves orientation from the
product of the orientations of the two tori to the orientation of the concatenated torus. -/
theorem isOrientationPreservingAt_piAddCases_torusOrientation (p : Fin (m + k) → ℝ)
    [∀ i, Fact (0 < p i)] (n : ℕ∞ω)
    (x : (∀ i : Fin m, AddCircle (p (Fin.castAdd k i))) ×
      (∀ j : Fin k, AddCircle (p (Fin.natAdd m j)))) :
    IsOrientationPreservingAt
      ((torusOrientation fun i : Fin m ↦ p (Fin.castAdd k i)).prod
        (torusOrientation fun j : Fin k ↦ p (Fin.natAdd m j)))
      (torusOrientation p)
      (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n) x := by
  -- The differential concatenates the components, so it sends the ordered product of the two
  -- coordinate bases to the coordinate basis of the concatenated torus. The tangent spaces of the
  -- tori are their model spaces `Fin _ → ℝ`, so the coordinate bases are tangent bases; both are
  -- positive, by the coordinate description of the orientations.
  refine (isOrientationPreservingAt_iff_of_basis
    (((Pi.basisFun ℝ (Fin m)).prod (Pi.basisFun ℝ (Fin k))).reindex finSumFinEquiv)
    (Pi.basisFun ℝ (Fin (m + k)))
    fun i ↦ (Diffeomorph.mfderiv_piAddCases_apply (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n x
      _ _).trans (Module.Basis.addCases_basisFun_prod_reindex_finSumFinEquiv i)).2
    (iff_of_true ((orientation_eq_orientationAt_prod_iff _ _ (Pi.basisFun ℝ (Fin m))
      (Pi.basisFun ℝ (Fin k))).2 (iff_of_true (orientationAt_torusOrientation _ _).symm
        (orientationAt_torusOrientation _ _).symm)) (orientationAt_torusOrientation p _).symm)

/-- **Appending a circle.** The map `(x, t) ↦ Fin.snoc x t` from `T^m × AddCircle (p m)` to
`T^(m + 1)` preserves orientation from the product of the torus orientation with the positive
orientation of the circle to the torus orientation. -/
theorem isOrientationPreservingAt_piSnoc_torusOrientation (p : Fin (m + 1) → ℝ)
    [∀ i, Fact (0 < p i)] (n : ℕ∞ω)
    (x : (∀ i : Fin m, AddCircle (p i.castSucc)) × AddCircle (p (Fin.last m))) :
    IsOrientationPreservingAt
      ((torusOrientation fun i : Fin m ↦ p i.castSucc).prod
        (AddCircle.orientation (p (Fin.last m))))
      (torusOrientation p)
      (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n) x := by
  -- The differential appends the circle component, so it sends the ordered product of the
  -- coordinate basis and the unit vector of the circle to the coordinate basis.
  have hb (i : Fin (m + 1)) :
      Fin.snoc (α := fun _ ↦ ℝ)
        (((Pi.basisFun ℝ (Fin m)).prod (Module.Basis.singleton (Fin 1) ℝ)).reindex
          finSumFinEquiv i).1
        (((Pi.basisFun ℝ (Fin m)).prod (Module.Basis.singleton (Fin 1) ℝ)).reindex
          finSumFinEquiv i).2 =
        Pi.basisFun ℝ (Fin (m + 1)) i := by
    funext l
    induction i using Fin.lastCases <;> induction l using Fin.lastCases <;>
      simp [Module.Basis.prod_apply, Pi.single_apply]
  -- The tangent spaces are the model spaces `Fin m → ℝ`, `ℝ` and `Fin (m + 1) → ℝ`, so these
  -- bases are tangent bases; both are positive, by the coordinate description of the orientations.
  refine (isOrientationPreservingAt_iff_of_basis
    (((Pi.basisFun ℝ (Fin m)).prod (Module.Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv)
    (Pi.basisFun ℝ (Fin (m + 1)))
    fun i ↦ (Diffeomorph.mfderiv_piSnoc_apply (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n x
      _ _).trans (hb i)).2
    (iff_of_true ((orientation_eq_orientationAt_prod_iff _ _ (Pi.basisFun ℝ (Fin m))
      (Module.Basis.singleton (Fin 1) ℝ)).2 (iff_of_true (orientationAt_torusOrientation _ _).symm
        (AddCircle.orientationAt_orientation _ _).symm)) (orientationAt_torusOrientation p _).symm)

/-- **Splitting off the first circle.** The map `(t, x) ↦ Fin.cons t x` from
`AddCircle (p 0) × T^m` to `T^(m + 1)`, inverse to the association map splitting off the first
circle, preserves orientation from the product of the positive orientation of the circle with the
torus orientation, read in degree `m + 1`, to the torus orientation. -/
theorem isOrientationPreservingAt_piCons_torusOrientation (p : Fin (m + 1) → ℝ)
    [∀ i, Fact (0 < p i)] (n : ℕ∞ω) (x : AddCircle (p 0) × ∀ i : Fin m, AddCircle (p i.succ)) :
    IsOrientationPreservingAt
      (((AddCircle.orientation (p 0)).prod (torusOrientation fun i : Fin m ↦ p i.succ)).reindex
        (finCongr (add_comm 1 m)))
      (torusOrientation p)
      (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n) x := by
  -- The product of the unit vector of the circle and the coordinate basis, the circle first.
  let b₀ := ((Module.Basis.singleton (Fin 1) ℝ).prod (Pi.basisFun ℝ (Fin m))).reindex
    finSumFinEquiv
  -- The differential prepends the circle component, so it sends `b₀`, read in degree `m + 1`, to
  -- the coordinate basis.
  have hb (i : Fin (m + 1)) :
      Fin.cons (α := fun _ ↦ ℝ) (b₀.reindex (finCongr (add_comm 1 m)) i).1
        (b₀.reindex (finCongr (add_comm 1 m)) i).2 = Pi.basisFun ℝ (Fin (m + 1)) i := by
    simpa only [b₀, Module.Basis.reindex_apply, Equiv.symm_trans_apply] using
      Module.Basis.cons_singleton_prod_basisFun_reindex_finSumFinEquiv_trans_finCongr (R := ℝ) i
  -- The tangent spaces are the model spaces `ℝ`, `Fin m → ℝ` and `Fin (m + 1) → ℝ`, so these
  -- bases are tangent bases; both are positive, by the coordinate description of the orientations.
  refine (isOrientationPreservingAt_iff_of_basis (b₀.reindex (finCongr (add_comm 1 m)))
    (Pi.basisFun ℝ (Fin (m + 1)))
    fun i ↦ (Diffeomorph.mfderiv_piCons_apply (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n x
      _ _).trans (hb i)).2
    (iff_of_true ?_ (orientationAt_torusOrientation p _).symm)
  refine (Module.Basis.orientation_reindex b₀ _).trans ?_
  rw [orientationAt_reindex]
  exact congrArg _ ((orientation_eq_orientationAt_prod_iff _ _
    (Module.Basis.singleton (Fin 1) ℝ) (Pi.basisFun ℝ (Fin m))).2
    (iff_of_true (AddCircle.orientationAt_orientation _ _).symm
      (orientationAt_torusOrientation _ _).symm))

/-- **The association map preserves orientation.** The association map
`x ↦ (x 0, Fin.tail x)` from `T^(m + 1)` to `AddCircle (p 0) × T^m`, splitting off the first
circle, preserves orientation from the torus orientation to the product of the positive orientation
of the circle with the torus orientation of the remaining factors, read in degree `m + 1`. -/
theorem isOrientationPreservingAt_piCons_symm_torusOrientation (p : Fin (m + 1) → ℝ)
    [∀ i, Fact (0 < p i)] {n : ℕ∞ω} (hn : n ≠ 0) (x : ∀ i, AddCircle (p i)) :
    IsOrientationPreservingAt (torusOrientation p)
      (((AddCircle.orientation (p 0)).prod (torusOrientation fun i : Fin m ↦ p i.succ)).reindex
        (finCongr (add_comm 1 m)))
      (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n).symm x :=
  (isOrientationPreservingAt_piCons_torusOrientation p n _).diffeomorph_symm hn

/-- **The one-factor torus is its circle.** Evaluation at the single index, from the torus
`∀ i : Fin 1, AddCircle (p i)` to the circle `AddCircle (p 0)`, preserves orientation from the
torus orientation to the positive orientation of the circle. -/
theorem isOrientationPreservingAt_piUnique_torusOrientation (p : Fin 1 → ℝ) [∀ i, Fact (0 < p i)]
    (n : ℕ∞ω) (x : ∀ i, AddCircle (p i)) :
    IsOrientationPreservingAt (torusOrientation p) (AddCircle.orientation (p 0))
      (Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n) x := by
  -- The diffeomorphism is evaluation at the single index, whose differential is the projection.
  have hf : ⇑(Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) n) = fun y ↦ y 0 :=
    funext fun y ↦ Diffeomorph.piUnique_apply _ _ n y
  refine (isOrientationPreservingAt_iff_of_basis (Pi.basisFun ℝ (Fin 1))
    (Module.Basis.singleton (Fin 1) ℝ) fun i ↦ ?_).2
    (iff_of_true (orientationAt_torusOrientation p x).symm
      (AddCircle.orientationAt_orientation _ _).symm)
  have h : ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0 (Pi.basisFun ℝ (Fin 1) 0) =
      Module.Basis.singleton (Fin 1) ℝ 0 := by
    simp
  rw [hf, TauCeti.mfderiv_apply (I := fun _ : Fin 1 ↦ 𝓘(ℝ)) 0 x, Subsingleton.elim i 0]
  -- The tangent spaces of the torus and of the circle are the model spaces `Fin 1 → ℝ` and `ℝ`.
  exact h

end TauCeti
