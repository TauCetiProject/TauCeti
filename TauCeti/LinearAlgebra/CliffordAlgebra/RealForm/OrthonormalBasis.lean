/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic

/-!
# Orthonormal bases as isometries from the negated compact coordinate form

Let `V` be a real inner product space and `Q` a quadratic form on `V` with `Q v = -‖v‖²`, the sign
convention of geometric Clifford multiplication. The coordinates `x ↦ ∑ i, x i • b i` of an
orthonormal basis `b` of `V` are an isometry from the negated positive-definite coordinate form
`-realCliffordForm n 0` to `Q`. Composed with the comparisons of a form with its negative, it
compares the even Clifford algebra and the Spin group of the compact coordinate form with those of
`Q`, along the frame `b` (`OrthonormalBasis.realEvenCliffordEquiv` and
`OrthonormalBasis.realSpinGroupEquiv`).

## Main definitions

* `OrthonormalBasis.negRealCliffordFormIsometryEquiv b hQ`: the coordinates of an orthonormal
  basis `b`, as an isometry from `-realCliffordForm n 0` to a form `Q v = -‖v‖²`.
* `OrthonormalBasis.realEvenCliffordEquiv b hQ`: the comparison of the even Clifford algebras of
  the positive-definite coordinate form and of `Q` along `b`.

## Main results

* `OrthonormalBasis.negRealCliffordFormIsometryEquiv_apply`: the isometry sends `x` to
  `∑ i, x i • b i`.
* `OrthonormalBasis.negRealCliffordFormIsometryEquiv_single`: it sends the `i`-th coordinate vector
  to `b i`.
* `OrthonormalBasis.negRealCliffordFormIsometryEquiv_symm_apply`: its inverse takes coordinates in
  `b`.
* `OrthonormalBasis.coe_realEvenCliffordEquiv_apply`: the even frame comparison is
  `evenEquivEvenNeg` followed by the map induced by the coordinates of `b`.
* `OrthonormalBasis.realEvenCliffordEquiv_ι`: the even frame comparison sends a bivector `eᵢ eⱼ` to
  `-c(bᵢ) c(bⱼ)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

noncomputable section

open TauCeti

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- The coordinates of an orthonormal basis `b`, `x ↦ ∑ i, x i • b i`, as an isometry from the
negated positive-definite coordinate form `-realCliffordForm n 0` to a form `Q v = -‖v‖²`. -/
def negRealCliffordFormIsometryEquiv : (-realCliffordForm n 0).IsometryEquiv Q where
  toLinearEquiv := b.toBasis.equivFun.symm
  map_app' x := by
    rw [hQ, ← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq,
      realCliffordForm_zero_eq_weightedSumSquares_one]
    simp [QuadraticMap.weightedSumSquares_apply, sq]

/-- `OrthonormalBasis.negRealCliffordFormIsometryEquiv` sends `x` to `∑ i, x i • b i`. -/
theorem negRealCliffordFormIsometryEquiv_apply (x : Fin (n + 0) → ℝ) :
    b.negRealCliffordFormIsometryEquiv hQ x = ∑ i, x i • b i :=
  (b.toBasis.equivFun_symm_apply x).trans (by simp)

/-- `OrthonormalBasis.negRealCliffordFormIsometryEquiv` sends the `i`-th coordinate vector to
`b i`. -/
@[simp]
theorem negRealCliffordFormIsometryEquiv_single (i : Fin n) :
    b.negRealCliffordFormIsometryEquiv hQ (Pi.single i 1) = b i := by
  simp [negRealCliffordFormIsometryEquiv_apply, Pi.single_apply]

/-- The inverse of `OrthonormalBasis.negRealCliffordFormIsometryEquiv` takes the coordinates
`b.repr v` of a vector `v`. -/
@[simp]
theorem negRealCliffordFormIsometryEquiv_symm_apply (v : V) (i : Fin n) :
    (b.negRealCliffordFormIsometryEquiv hQ).symm v i = b.repr v i :=
  (congrFun (b.toBasis.equivFun_apply v) i).trans (b.coe_toBasis_repr_apply v i)

open CliffordAlgebra

/-- The comparison of the even Clifford algebras of the positive-definite coordinate form and of
a form `Q v = -‖v‖²`, along the orthonormal basis `b`. It sends a bivector `eᵢ eⱼ` to
`-c(bᵢ) c(bⱼ)` (`OrthonormalBasis.realEvenCliffordEquiv_ι`). -/
def realEvenCliffordEquiv : even (realCliffordForm n 0) ≃ₐ[ℝ] even Q :=
  (evenEquivEvenNeg (realCliffordForm n 0)).trans
    (evenEquivOfIsometry (b.negRealCliffordFormIsometryEquiv hQ))

/-- The Clifford value of `OrthonormalBasis.realEvenCliffordEquiv b hQ x` is obtained by applying
`evenEquivEvenNeg` and then the map induced by the coordinates of `b`. -/
theorem coe_realEvenCliffordEquiv_apply (x : even (realCliffordForm n 0)) :
    (b.realEvenCliffordEquiv hQ x : CliffordAlgebra Q) =
      map (b.negRealCliffordFormIsometryEquiv hQ).toIsometry
        (evenEquivEvenNeg (realCliffordForm n 0) x) := by
  rw [realEvenCliffordEquiv, AlgEquiv.trans_apply, coe_evenEquivOfIsometry_apply,
    equivOfIsometry_apply]

/-- `OrthonormalBasis.realEvenCliffordEquiv` sends a bivector `m n` to `-c(m') c(n')`, where `m'`
and `n'` are the vectors with coordinates `m` and `n` in the basis `b`. -/
@[simp]
theorem realEvenCliffordEquiv_ι (x y : Fin (n + 0) → ℝ) :
    b.realEvenCliffordEquiv hQ ((even.ι (realCliffordForm n 0)).bilin x y) =
      -(even.ι Q).bilin (b.negRealCliffordFormIsometryEquiv hQ x)
        (b.negRealCliffordFormIsometryEquiv hQ y) := by
  rw [realEvenCliffordEquiv, AlgEquiv.trans_apply, evenEquivEvenNeg_apply, evenToNeg_ι, map_neg,
    evenEquivOfIsometry_ι]

end OrthonormalBasis
