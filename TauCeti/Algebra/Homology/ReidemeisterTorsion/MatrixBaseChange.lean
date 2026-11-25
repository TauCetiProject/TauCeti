/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.MatrixBaseChange
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic

/-!
# The torsion of the coordinate base change of a based complex

Let `C` be a `ℤ`-graded chain complex of modules over a commutative ring `A`, with an ordered
basis `c i : Basis (Fin (n i)) A (C.X i)` in each degree, and let `φ : A →+* K` be a ring
homomorphism into a field. The torsion of the coordinate base change
`HomologicalComplex.matrixBaseChange c φ` is natural in `φ`: a homomorphism of fields
`ψ : K →+* L` sends the torsion of the base change along `φ` to the torsion of the base change
along `ψ ∘ φ` (`HomologicalComplex.map_reidemeisterTorsion_matrixBaseChange`). This follows from
the scalar extension theorem `HomologicalComplex.map_reidemeisterTorsion`, because the matrices of
the differentials of the coordinate base change are the images of those of `C` by construction.
The same holds for the torsion of a based two-periodic complex
(`HomologicalComplex.map_parityTorsion_matrixBaseChange`), by
`HomologicalComplex.map_parityTorsion`.

Changing the bases `c i` of `C` to `c' i` changes the torsion of the coordinate base change by the
images under `φ` of the determinants `[c'ᵢ / cᵢ]` of the new bases with respect to the old ones,
with the exponents of the basis-change formulas over a field
(`HomologicalComplex.reidemeisterTorsion_matrixBaseChange_eq_mul_finprod_det`,
`HomologicalComplex.parityTorsion_matrixBaseChange_eq_mul_det`). The coordinate base changes of
`(C, c)` and `(C, c')` are different complexes, but the first, in the basis given by the columns
of the image under `φ` of the matrix of `c' i` in `c i`, has the differential matrices of the
second.

## Main results

* `HomologicalComplex.map_reidemeisterTorsion_matrixBaseChange`: naturality of the torsion of the
  coordinate base change in the field.
* `HomologicalComplex.map_parityTorsion_matrixBaseChange`: naturality of the torsion of the
  coordinate base change of a two-periodic complex in the field.
* `HomologicalComplex.reidemeisterTorsion_matrixBaseChange_eq_mul_finprod_det`,
  `HomologicalComplex.parityTorsion_matrixBaseChange_eq_mul_det`: the change of the torsion of the
  coordinate base change under a change of the bases of `C`.
-/

public section

open Module

namespace HomologicalComplex

variable {A : Type*} [CommRing A] {K L : Type*} [Field K] [Field L] (φ : A →+* K) (ψ : K →+* L)

/-- The torsion of the coordinate base change is natural in the field: a homomorphism of fields
`ψ : K →+* L` sends the torsion of the base change along `φ` to the torsion of the base change
along `ψ ∘ φ`. -/
theorem map_reidemeisterTorsion_matrixBaseChange {C : ChainComplex (ModuleCat A) ℤ} {n : ℤ → ℕ}
    {c : ∀ i, Basis (Fin (n i)) A (C.X i)} :
    ψ ((C.matrixBaseChange c φ).reidemeisterTorsion (C.matrixBaseChangeBasis c φ)) =
      (C.matrixBaseChange c (ψ.comp φ)).reidemeisterTorsion
        (C.matrixBaseChangeBasis c (ψ.comp φ)) :=
  map_reidemeisterTorsion ψ fun i ↦ by
    rw [toMatrix_matrixBaseChange_d, toMatrix_matrixBaseChange_d, Matrix.map_map, RingHom.coe_comp]

/-- The torsion of the coordinate base change of a two-periodic complex is natural in the field: a
homomorphism of fields `ψ : K →+* L` sends the torsion of the base change along `φ` to the torsion
of the base change along `ψ ∘ φ`. -/
theorem map_parityTorsion_matrixBaseChange
    {C : HomologicalComplex (ModuleCat A) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
    {c : ∀ i, Basis (Fin (n i)) A (C.X i)} :
    ψ ((C.matrixBaseChange c φ).parityTorsion (C.matrixBaseChangeBasis c φ)) =
      (C.matrixBaseChange c (ψ.comp φ)).parityTorsion (C.matrixBaseChangeBasis c (ψ.comp φ)) :=
  map_parityTorsion ψ fun i j ↦ by
    rw [toMatrix_matrixBaseChange_d, toMatrix_matrixBaseChange_d, Matrix.map_map, RingHom.coe_comp]

/-! ### Changing the bases of the complex -/

section BasisChange

variable {ι : Type*} {s : ComplexShape ι} {C : HomologicalComplex (ModuleCat A) s} {n : ι → ℕ}
  (c c' : ∀ i, Basis (Fin (n i)) A (C.X i))

/-- The automorphism of the coordinate base change of `(C, c)` along `φ` in degree `i` whose
matrix in the standard basis is the image under `φ` of the matrix of `c' i` in the basis `c i`. -/
private noncomputable def basisChangeEquiv (i : ι) :
    (C.matrixBaseChange c φ).X i ≃ₗ[K] (C.matrixBaseChange c φ).X i :=
  Matrix.toLinearEquiv (C.matrixBaseChangeBasis c φ i) (((c i).toMatrix (c' i)).map φ) <| by
    simpa [Basis.det_apply, RingHom.map_det] using ((c i).isUnit_det (c' i)).map φ

/-- The basis of the coordinate base change of `(C, c)` along `φ` corresponding to the basis
`c' i` of `C.X i`: its vectors are the columns of the image under `φ` of the matrix of `c' i` in
`c i`. -/
private noncomputable def basisChangeBasis (i : ι) :
    Basis (Fin (n i)) K ((C.matrixBaseChange c φ).X i) :=
  (C.matrixBaseChangeBasis c φ i).map (basisChangeEquiv φ c c' i)

/-- The automorphism `basisChangeEquiv` is `Matrix.toLin` of the image under `φ` of the matrix of
`c' i` in `c i`. -/
private theorem basisChangeEquiv_toLinearMap (i : ι) :
    (basisChangeEquiv φ c c' i).toLinearMap =
      Matrix.toLin (C.matrixBaseChangeBasis c φ i) (C.matrixBaseChangeBasis c φ i)
        (((c i).toMatrix (c' i)).map φ) :=
  LinearMap.ext fun x ↦ by simp [basisChangeEquiv]

/-- The inverse of `basisChangeEquiv` is `Matrix.toLin` of the image under `φ` of the matrix of
`c i` in `c' i`. -/
private theorem basisChangeEquiv_symm_toLinearMap (i : ι) :
    (basisChangeEquiv φ c c' i).symm.toLinearMap =
      Matrix.toLin (C.matrixBaseChangeBasis c φ i) (C.matrixBaseChangeBasis c φ i)
        (((c' i).toMatrix (c i)).map φ) := by
  refine LinearMap.ext fun x ↦ (LinearEquiv.symm_apply_eq _).2 ?_
  rw [← LinearEquiv.coe_toLinearMap, basisChangeEquiv_toLinearMap, ← LinearMap.comp_apply,
    ← Matrix.toLin_mul]
  simp [← Matrix.map_mul]

/-- In the bases `basisChangeBasis`, the matrices of the differentials of the coordinate base
change of `(C, c)` are those of the coordinate base change of `(C, c')`. -/
private theorem toMatrix_basisChangeBasis_d (i j : ι) :
    LinearMap.toMatrix (basisChangeBasis φ c c' i) (basisChangeBasis φ c c' j)
        ((C.matrixBaseChange c φ).d i j).hom =
      (LinearMap.toMatrix (c' i) (c' j) (C.d i j).hom).map φ := by
  -- Both sides are the conjugate of the matrix of `d` in `c` by the matrix of `c'` in `c`: on the
  -- left as matrices of `basisChangeEquiv` and its inverse, on the right by `Basis.toMatrix`.
  simp [basisChangeBasis, LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right,
    LinearMap.toMatrix_comp _ (C.matrixBaseChangeBasis c φ _), toMatrix_matrixBaseChange_d,
    basisChangeEquiv_toLinearMap, basisChangeEquiv_symm_toLinearMap, ← Matrix.map_mul]

/-- The determinant of `basisChangeBasis` with respect to the standard basis is the image under
`φ` of the determinant of `c' i` with respect to `c i`. -/
private theorem det_basisChangeBasis (i : ι) :
    (C.matrixBaseChangeBasis c φ i).det (basisChangeBasis φ c c' i) =
      φ ((c i).det (c' i)) := by
  rw [basisChangeBasis, Basis.coe_map, ← LinearEquiv.coe_coe, Basis.det_comp]
  simp [basisChangeEquiv_toLinearMap, Basis.det_apply, RingHom.map_det]

/-- The basis-change formula for the torsion of a coordinate base change: replacing the bases
`c i` of a based two-periodic complex `C` over a commutative ring `A` by `c' i` multiplies the
torsion of its coordinate base change along `φ : A →+* K` by
`φ [c'₀ / c₀] · φ [c₁ / c'₁]`, where `[c'ᵢ / cᵢ]` is the determinant of `c' i` with respect to
`c i`. -/
theorem parityTorsion_matrixBaseChange_eq_mul_det
    {C : HomologicalComplex (ModuleCat A) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
    (c c' : ∀ i, Basis (Fin (n i)) A (C.X i)) :
    (C.matrixBaseChange c' φ).parityTorsion (C.matrixBaseChangeBasis c' φ) =
      (C.matrixBaseChange c φ).parityTorsion (C.matrixBaseChangeBasis c φ) *
        (φ ((c 0).det (c' 0)) * φ ((c' 1).det (c 1))) := by
  rw [← map_parityTorsion (RingHom.id K) (c := basisChangeBasis φ c c') fun i j ↦ by
      rw [toMatrix_matrixBaseChange_d, toMatrix_basisChangeBasis_d, RingHom.coe_id, Matrix.map_id],
    RingHom.id_apply, parityTorsion_eq_mul_det (C.matrixBaseChangeBasis c φ),
    det_basisChangeBasis, det_basisChangeBasis]
  rw [← (c 1).det_inv (c' 1), map_units_inv, IsUnit.unit_spec]

/-- The basis-change formula for the torsion of a coordinate base change: replacing the bases
`c i` of a based complex `C` over a commutative ring `A` by `c' i` multiplies the torsion of its
coordinate base change along `φ : A →+* K` by `∏ᵢ φ [c'ᵢ / cᵢ] ^ ((-1) ^ i)`, where `[c'ᵢ / cᵢ]`
is the determinant of `c' i` with respect to `c i`. -/
theorem reidemeisterTorsion_matrixBaseChange_eq_mul_finprod_det
    {C : ChainComplex (ModuleCat A) ℤ} {n : ℤ → ℕ} (c c' : ∀ i, Basis (Fin (n i)) A (C.X i)) :
    (C.matrixBaseChange c' φ).reidemeisterTorsion (C.matrixBaseChangeBasis c' φ) =
      (C.matrixBaseChange c φ).reidemeisterTorsion (C.matrixBaseChangeBasis c φ) *
        ∏ᶠ i : ℤ, φ ((c i).det (c' i)) ^ (i.negOnePow : ℤ) := by
  rw [← map_reidemeisterTorsion (RingHom.id K) (c := basisChangeBasis φ c c') fun i ↦ by
      rw [toMatrix_matrixBaseChange_d, toMatrix_basisChangeBasis_d, RingHom.coe_id, Matrix.map_id],
    RingHom.id_apply, reidemeisterTorsion_eq_mul_finprod_det _ (C.matrixBaseChangeBasis c φ)]
  simp_rw [det_basisChangeBasis]

end BasisChange

end HomologicalComplex
