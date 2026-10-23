/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Euler
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Liouville.VectorField

/-!
# The Liouville vector field of a cotangent bundle

The cotangent bundle `T*M = TauCeti.CotangentBundle I M` carries the Liouville form `λ = p dq` and
the canonical symplectic form `ω = -dλ`. Its fibres are vector spaces, and the Euler vector field
of the bundle (`TauCeti.vectorBundleEulerField`) is the radial field `Z = p ∂_p`: in the bundle
chart at a covector with coordinates `(q, p)` it is `(0, p)`.

This file proves that `Z` is the Liouville vector field of the primitive `-λ` of `ω`:
contracting `ω` with `Z` gives `ι_Z ω = -λ`
(`TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`), and therefore
`L_Z ω = ω` by Cartan's formula
(`TauCeti.CotangentBundle.isLiouvilleVectorField_vectorBundleEulerField`). This is the global form
of `TauCeti.isLiouvilleVectorField_cotangentLiouvilleField` on the linear cotangent space, and the
sign convention is the same: with `ω = -dλ`, the Liouville primitive is `-λ` and its Liouville field
is `p ∂_p`. Since `Z` is vertical, `λ` vanishes on it
(`TauCeti.CotangentBundle.liouvilleForm_interior_vectorBundleEulerField`). The flow of `Z` is the
fibre dilation by `e^t` (`TauCeti.isMIntegralCurve_vectorBundleEulerField`), under which `ω` scales
by `e^t` (`TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_symplecticForm`).

## Main results

* `TauCeti.CotangentBundle.liouvilleForm_interior_vectorBundleEulerField`: `ι_Z λ = 0`.
* `TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`: `ι_Z ω = -λ`.
* `TauCeti.CotangentBundle.isLiouvilleVectorField_vectorBundleEulerField`: `L_Z ω = ω`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 3 (cotangent bundles, Liouville vector fields and hypersurfaces of contact type).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The radial field `p ∂_p` is vertical, so the Liouville form vanishes on it: `ι_Z λ = 0`. -/
@[simp]
theorem liouvilleForm_interior_vectorBundleEulerField [IsManifold I 2 M] :
    (liouvilleForm I M).1.interior (vectorBundleEulerField I) = 0 := by
  funext z
  ext v
  simp [RoughForm.interior_apply, liouvilleForm_apply]

variable [IsManifold I ∞ M]

/-- **The radial field `p ∂_p` is the Liouville field of `-λ`.** Contracting the canonical
symplectic form `ω = -dλ` of the cotangent bundle with its Euler vector field gives minus the
Liouville form: `ι_Z ω = -λ`. -/
theorem symplecticForm_interior_vectorBundleEulerField :
    (symplecticForm I M).1.interior (vectorBundleEulerField I) = -(liouvilleForm I M).1 := by
  funext z
  ext v
  -- Read both sides in the chart at `z`, where the Euler field is `(0, p)`.
  have hl := inChartAt_liouvilleForm z (mem_extChartAt_target z)
  rw [RoughForm.inChartAt_extChartAt_self] at hl
  -- This is the linear identity `ι_{p ∂_p} ω = -λ` at the chart point.
  have h := strongDualCotangentSymplecticForm_cotangentLiouvilleField
    (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z z) (v 0)
  -- `symplecticForm_apply` is stated on `Fin 2`, so `simp` cannot use it at `Fin (1 + 1)`.
  rw [RoughForm.interior_apply, symplecticForm_apply]
  -- A family `v` indexed by `Fin 1` is the constant family at `v 0`.
  simp only [Pi.neg_apply, hl, vectorBundleEulerField_eq_trivializationAt,
    ← Manifold.extChartAt_totalSpace_apply_snd (IB := I), cotangentLiouvilleField_apply,
    show (fun _ ↦ v 0) = v from (eq_const_of_subsingleton v 0).symm] at h ⊢
  -- The two sides now agree up to definitional unfolding: `Bundle.Trivial _ ℝ z` is `ℝ`.
  exact h

/-- **The radial field `p ∂_p` is a Liouville vector field** of the canonical symplectic form of
the cotangent bundle: `L_Z ω = ω`, for the Euler vector field `Z` of `T*M`. -/
theorem isLiouvilleVectorField_vectorBundleEulerField :
    IsLiouvilleVectorField (symplecticForm I M).1 (vectorBundleEulerField I) := by
  have h := isLiouvilleVectorField_mextDeriv_of_interior_eq
    ((liouvilleForm I M).isSmoothForm.neg.of_le (by simp))
    ((contMDiff_vectorBundleEulerField (m := 1)).mdifferentiable one_ne_zero)
    (by rw [mextDeriv_neg, ← symplecticForm_eq_neg_mextDeriv,
      symplecticForm_interior_vectorBundleEulerField])
  rwa [mextDeriv_neg, ← symplecticForm_eq_neg_mextDeriv] at h

end CotangentBundle

end TauCeti
