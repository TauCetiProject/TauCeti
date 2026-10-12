/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Class
public import TauCeti.RingTheory.Norm.Units

/-!
# The discriminant of a transferred line

Let `L/K` be a finite extension and `s : L → K` a `K`-linear functional. The Scharlau transfer
of the line `⟨a⟩` over `L` is the form `x ↦ s(a x²)` on `L` regarded as a `K`-space, with Gram
matrix `(s(a bᵢ bⱼ))ᵢⱼ` in a basis `b`. Since `s(a bᵢ bⱼ) = s(bᵢ · a bⱼ)`, that matrix is the
Gram matrix of `s_*⟨1⟩` multiplied by the matrix of multiplication by `a`, whose determinant is
the norm of `a`. Hence

```text
d(s_*⟨a⟩) = d(s_*⟨1⟩) · N_{L/K}(a)   modulo squares.
```

Read through the Kummer isomorphism, this is the degree-one case of the relative
Stiefel–Whitney formula for the transfer.

## Main results

* `QuadraticMap.discr_scharlauTransfer_smul_sq`: the Gram determinant of `s_*⟨a⟩` in any basis
  is `N_{L/K}(a)` times that of `s_*⟨1⟩`.
* `TauCeti.discr_formClass_scharlauTransfer_smul_sq`: the discriminant of `s_*⟨a⟩` is that of
  `s_*⟨1⟩` plus the square class of `N_{L/K}(a)`.
* `TauCeti.RegularFormClass.discr_scharlauTransfer_mk_rankOne`: the same identity on isometry
  classes, for the class-level transfer of the class `⟨a⟩`.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. 78 (1984), 223–256, Théorème 2.
-/

public section

noncomputable section

open QuadraticMap QuadraticForm

namespace QuadraticMap

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Invertible (2 : K)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Gram determinant of a transferred line**: in any basis of `L` over `K`, the Gram
determinant of `x ↦ s(a x²)` is `N_{L/K}(a)` times the Gram determinant of `x ↦ s(x²)`. -/
theorem discr_scharlauTransfer_smul_sq (b : Module.Basis ι K L) (s : L →ₗ[K] K) (a : L) :
    ((a • QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).discr b =
      Algebra.norm K a * ((QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).discr b := by
  have hsq : ∀ x y : L,
      associated ((QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s) x y = s (x * y) := by
    intro x y
    rw [associated_apply, invOf_smul_eq_iff]
    simp only [scharlauTransfer_apply, sq_apply, ← map_sub, two_smul, ← map_add]
    congr 1
    ring
  have hsmul : ∀ x y : L,
      associated ((a • QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s) x y =
        s (x * (a * y)) := by
    intro x y
    rw [← hsq]
    simp only [associated_apply, scharlauTransfer_apply, smul_apply, sq_apply, smul_eq_mul,
      ← map_sub]
    congr 2
    ring
  -- The Gram matrix of `s_*⟨a⟩` is that of `s_*⟨1⟩` times the matrix of multiplication by `a`.
  have hM : ((a • QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).toMatrix b =
      ((QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).toMatrix b *
        Algebra.leftMulMatrix b a := by
    ext i j
    simp only [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply, Matrix.mul_apply,
      Algebra.leftMulMatrix_eq_repr_mul, hsmul, hsq]
    conv_lhs => rw [← b.sum_repr (a * b j)]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [QuadraticForm.discr, hM, Matrix.det_mul, ← Algebra.norm_eq_matrix_det, mul_comm,
    QuadraticForm.discr]

end QuadraticMap

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)]

/-- **The discriminant of a transferred line**: `d(s_*⟨a⟩) = d(s_*⟨1⟩) + [N_{L/K}(a)]` in the
additively written square-class group of `K`, for the transferred forms `x ↦ s(a x²)` and
`x ↦ s(x²)` on `L` regarded as a `K`-space. -/
theorem discr_formClass_scharlauTransfer_smul_sq (s : L →ₗ[K] K) (a : Lˣ)
    (ha : (((a : L) • QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).Nondegenerate)
    (h1 : ((QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).Nondegenerate) :
    RegularFormClass.discr (formClass _ ha) =
      RegularFormClass.discr (formClass _ h1) + squareClass (Algebra.normUnits K a) := by
  let b := Module.finBasis K L
  have hu : IsUnit (((QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).discr b) :=
    isUnit_iff_ne_zero.mpr ((LinearMap.nondegenerate_iff_det_ne_zero b).mp
      (QuadraticMap.nondegenerate_associated_iff.mpr h1))
  rw [discr_formClass_eq_squareClass _ h1 b hu.unit_spec,
    discr_formClass_eq_squareClass _ ha b (u := Algebra.normUnits K a * hu.unit)
      (by rw [Units.val_mul, Algebra.coe_normUnits, IsUnit.unit_spec,
        QuadraticMap.discr_scharlauTransfer_smul_sq]),
    squareClass_mul, add_comm]

/-- The transfer of the class `⟨a⟩` is the class of the transferred form `x ↦ s(a x²)` on `L`
itself, together with the nondegeneracy of that form. -/
private theorem exists_scharlauTransfer_mk_rankOne_eq_formClass (s : L →ₗ[K] K) (hs : s ≠ 0)
    (a : Lˣ) :
    ∃ h : (((a : L) • QuadraticMap.sq (R := L) (A := L)).scharlauTransfer s).Nondegenerate,
      RegularFormClass.scharlauTransfer s hs (Quotient.mk (regularFormSetoid L) ⟨1, fun _ => a⟩) =
        formClass _ h := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  let e : (presentedForm (⟨1, fun _ => a⟩ : RegularFormPresentation L)).IsometryEquiv
      ((a : L) • QuadraticMap.sq (R := L) (A := L)) :=
    { toLinearEquiv := LinearEquiv.funUnique (Fin 1) L L
      map_app' x := by
        rw [presentedForm_apply, Fin.sum_univ_one]
        simp }
  have hnd := (presentedForm _).nondegenerate_scharlauTransfer_iff_of_ne_zero s hs |>.mpr
    (nondegenerate_presentedForm (⟨1, fun _ => a⟩ : RegularFormPresentation L))
  refine ⟨(e.scharlauTransfer s).nondegenerate_iff.mp hnd, ?_⟩
  rw [RegularFormClass.scharlauTransfer_mk, formClass_eq_iff]
  exact ⟨e.scharlauTransfer s⟩

/-- **The discriminant of the transfer of `⟨a⟩`**: `d(s_*⟨a⟩) = d(s_*⟨1⟩) + [N_{L/K}(a)]` on
isometry classes. -/
theorem RegularFormClass.discr_scharlauTransfer_mk_rankOne (s : L →ₗ[K] K) (hs : s ≠ 0)
    (a : Lˣ) :
    discr (scharlauTransfer s hs (Quotient.mk (regularFormSetoid L) ⟨1, fun _ => a⟩)) =
      discr (scharlauTransfer s hs 1) + squareClass (Algebra.normUnits K a) := by
  obtain ⟨ha, hca⟩ := exists_scharlauTransfer_mk_rankOne_eq_formClass s hs a
  obtain ⟨h1, hc1⟩ := exists_scharlauTransfer_mk_rankOne_eq_formClass s hs 1
  simp only [Units.val_one, one_smul] at h1 hc1
  rw [← RegularFormClass.mk_rankOne_one, hca, hc1,
    discr_formClass_scharlauTransfer_smul_sq s a ha h1]

end TauCeti
