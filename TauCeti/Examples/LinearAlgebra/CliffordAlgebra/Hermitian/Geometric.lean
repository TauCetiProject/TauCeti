/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Pauli

/-!
# Concrete low-dimensional models and negative controls for `AlgHom.IsGeometricClifford`

This file supplies concrete models of `AlgHom.IsGeometricClifford` in dimensions `1` and `2`,
together with counterexamples showing that the two clauses of `AlgHom.IsGeometricClifford`
(`Q v = -‖v‖²` and skew-Hermitianness of `c(v)`) are independent:

* `TauCeti.realLineGeometricClifford`: `ℝ` with `Q r = -r²` acting on `ℂ` via `r ↦ (r * i) • 1`,
  built from `CliffordAlgebraComplex.toComplex`.
* `TauCeti.pauliPlaneClifford`: `EuclideanSpace ℝ (Fin 2)` with `Q v = -‖v‖²` acting on
  `EuclideanSpace ℂ (Fin 2)` via `v ↦ i (v₁ σ₂ + v₀ σ₃)` (`e₀ ↦ i σ₃`, `e₁ ↦ i σ₂`, bivector
  `c(e₀) c(e₁) = i σ₁`, chirality `Γ = -σ₁`), built from
  `TauCeti.realCliffordZeroTwoEquivQuaternion` and `Quaternion.toComplexMatrix`.
* `AlgHom.not_isGeometricClifford_zero_of_norm_ne_zero` and `TauCeti.zeroRealLineClifford`: on
  `CliffordAlgebra (0 : QuadraticForm ℝ ℝ)` acting trivially on `ℂ`, every generator acts
  skew-Hermitianly (`0`), yet `IsGeometricClifford` fails because `Q 1 = 0 ≠ -‖(1 : ℝ)‖²`.
* `TauCeti.nonSkewRealLineClifford`: on `ℝ` with `Q r = -‖r‖²`, sending `1 : ℝ` to the non-normal
  square root `Matrix.toEuclideanLin !![0, 2; -2⁻¹, 0]` of `-1` on `EuclideanSpace ℂ (Fin 2)`
  satisfies `Q r = -‖r‖²` everywhere, yet fails `IsGeometricClifford` because `1` does not act
  skew-Hermitianly.
-/

public section

noncomputable section

open CliffordAlgebra Module

namespace TauCeti

/-! ### One-dimensional model on `ℝ` acting on `ℂ` -/

section RealLine

/-- Isometry from `-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)` on `ℝ` to
`CliffordAlgebraComplex.Q = -QuadraticMap.sq`. -/
private def realLineToComplexIsometry :
    (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) →qᵢ CliffordAlgebraComplex.Q where
  toLinearMap := LinearMap.id
  map_app' r := by
    simp [CliffordAlgebraComplex.Q_apply, LinearMap.BilinMap.toQuadraticMap_apply, sq]

@[simp]
private theorem realLineToComplexIsometry_apply (r : ℝ) : realLineToComplexIsometry r = r :=
  (rfl)

/-- **One-dimensional geometric Clifford model**: `ℝ` with `Q r = -r²` acting on `ℂ` via
`r ↦ (r * i) • 1`, constructed from `CliffordAlgebraComplex.toComplex`. -/
def realLineGeometricClifford :
    CliffordAlgebra (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) →ₐ[ℝ] Module.End ℂ ℂ :=
  (Algebra.lsmul ℝ ℂ ℂ).comp
    (CliffordAlgebraComplex.toComplex.comp (CliffordAlgebra.map realLineToComplexIsometry))

/-- Any `r : ℝ` acts on `ℂ` as multiplication by `(r : ℂ) * i`. -/
@[simp]
theorem realLineGeometricClifford_ι (r : ℝ) :
    realLineGeometricClifford (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) r) =
      ((r : ℂ) * Complex.I) • 1 := by
  ext
  simp [realLineGeometricClifford, Complex.real_smul]

/-- The unit generator `1 : ℝ` acts on `ℂ` as multiplication by `i`. -/
theorem realLineGeometricClifford_ι_one :
    realLineGeometricClifford (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) 1) =
      Complex.I • 1 := by
  simp

/-- `TauCeti.realLineGeometricClifford` satisfies `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_realLineGeometricClifford :
    realLineGeometricClifford.IsGeometricClifford where
  map_eq_neg_norm_sq r := by
    simp [LinearMap.BilinMap.toQuadraticMap_apply, sq]
  inner_map_ι_left r z w := by
    simp only [realLineGeometricClifford_ι, LinearMap.smul_apply, one_apply_eq_self,
      inner_smul_left, inner_smul_right, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

end RealLine

/-! ### Two-dimensional Pauli negative-plane model -/

section PauliPlane

/-- Coordinate isometry from `EuclideanSpace ℝ (Fin 2)` with `Q v = -‖v‖²` to
`TauCeti.realCliffordForm 0 2`. -/
private def euclideanPlaneToRealCliffordZeroTwo :
    (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) →qᵢ
      realCliffordForm 0 2 where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap
  map_app' v := by
    simp [LinearMap.BilinMap.toQuadraticMap_apply, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    ring

@[simp]
private theorem euclideanPlaneToRealCliffordZeroTwo_apply (v : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneToRealCliffordZeroTwo v = v.ofLp :=
  (rfl)

/-- **Two-dimensional Pauli negative-plane model**: `EuclideanSpace ℝ (Fin 2)` with `Q v = -‖v‖²`
acting on `EuclideanSpace ℂ (Fin 2)` via `v ↦ i (v₁ σ₂ + v₀ σ₃)` (`e₀ ↦ i σ₃`, `e₁ ↦ i σ₂`),
constructed from `TauCeti.realCliffordZeroTwoEquivQuaternion` and `Quaternion.toComplexMatrix`. -/
def pauliPlaneClifford :
    CliffordAlgebra (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) →ₐ[ℝ]
      Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  ((Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).toAlgHom.restrictScalars
      ℝ).comp
    (Quaternion.toComplexMatrix.toAlgHom.comp
      (realCliffordZeroTwoEquivQuaternion.toAlgHom.comp
        (CliffordAlgebra.map euclideanPlaneToRealCliffordZeroTwo)))

/-- On any vector `v`, `pauliPlaneClifford` acts as `Matrix.toEuclideanLin` of
`i • pauli ![0, v 1, v 0]`. -/
@[simp]
theorem pauliPlaneClifford_ι (v : EuclideanSpace ℝ (Fin 2)) :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) v) =
      Matrix.toEuclideanLin (Complex.I • pauli ![0, v 1, v 0]) := by
  rw [pauliPlaneClifford, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom, StarAlgHom.coe_toAlgHom,
    AlgEquiv.coe_toAlgHom, map_apply_ι, euclideanPlaneToRealCliffordZeroTwo_apply,
    toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι,
    Matrix.toEuclideanLin_eq_toLin_orthonormal]
  ext w
  simp [Matrix.toLinAlgEquiv_apply, Matrix.toLin_apply]

/-- The first standard basis vector `e₀` acts as `i σ₃`. -/
theorem pauliPlaneClifford_ι_single_zero :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 0 1)) =
      Complex.I • Matrix.toEuclideanLin (pauli ![0, 0, 1]) := by
  have hv0 : (![0, (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1,
      (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0] : Fin 3 → ℝ) =
      ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [pauliPlaneClifford_ι, hv0, map_smul]

/-- The second standard basis vector `e₁` acts as `i σ₂`. -/
theorem pauliPlaneClifford_ι_single_one :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 1 1)) =
      Complex.I • Matrix.toEuclideanLin (pauli ![0, 1, 0]) := by
  have hv1 : (![0, (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1,
      (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0] : Fin 3 → ℝ) =
      ![0, 1, 0] := by
    ext i
    fin_cases i <;> simp
  rw [pauliPlaneClifford_ι, hv1, map_smul]

/-- The plane bivector `c(e₀) c(e₁)` acts as `i σ₁`: `(i σ₃) (i σ₂) = i σ₁`. -/
theorem pauliPlaneClifford_ι_single_zero_mul_ι_single_one :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 0 1)) *
      pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 1 1)) =
      Complex.I • Matrix.toEuclideanLin (pauli ![1, 0, 0]) := by
  have hs0 : euclideanPlaneToRealCliffordZeroTwo (EuclideanSpace.single 0 1) = Pi.single 0 1 := by
    simp
  have hs1 : euclideanPlaneToRealCliffordZeroTwo (EuclideanSpace.single 1 1) = Pi.single 1 1 := by
    simp
  rw [← map_mul, pauliPlaneClifford, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom, StarAlgHom.coe_toAlgHom,
    AlgEquiv.coe_toAlgHom, map_mul, map_apply_ι, map_apply_ι, hs0, hs1,
    toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι_mul_ι, map_smul,
    Matrix.toEuclideanLin_eq_toLin_orthonormal]
  ext w
  simp [Matrix.toLinAlgEquiv_apply, Matrix.toLin_apply]

/-- **The Pauli negative-plane model satisfies `AlgHom.IsGeometricClifford`.** -/
theorem isGeometricClifford_pauliPlaneClifford : pauliPlaneClifford.IsGeometricClifford := by
  refine AlgHom.isGeometricClifford_iff_adjoint.mpr ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · simp [LinearMap.BilinMap.toQuadraticMap_apply]
  · rw [pauliPlaneClifford_ι, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
      (isHermitian_pauli _).eq, neg_smul, map_neg]

local instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

/-- **Chirality of the Pauli negative-plane model**: for the standard orientation of
`EuclideanSpace ℝ (Fin 2)`, the chirality operator `Γ = i c(e₀) c(e₁)` is `-σ₁`. -/
theorem liftBaseChange_pauliPlaneClifford_complexVolume :
    liftBaseChange ℂ (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
        pauliPlaneClifford
        (complexVolume (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) =
      -Matrix.toEuclideanLin (pauli ![1, 0, 0]) := by
  rw [liftBaseChange_complexVolume_eq_of_neg_norm_sq pauliPlaneClifford _
    isGeometricClifford_pauliPlaneClifford.map_eq_neg_norm_sq (EuclideanSpace.basisFun (Fin 2) ℝ)
    rfl]
  simp only [show (2 + 1) / 2 = 1 from rfl, List.finRange_succ, List.finRange_zero, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one, EuclideanSpace.basisFun_apply,
    Fin.succ_zero_eq_one, pauliPlaneClifford_ι_single_zero_mul_ι_single_one, smul_smul,
    Complex.I_mul_I, neg_one_smul]

end PauliPlane

end TauCeti

/-! ### Clause-independence negative controls -/

namespace AlgHom

/-- **Negative control for the metric-form clause**: on any seminormed real module containing a
vector of nonzero norm, no real algebra map out of the exterior algebra `CliffordAlgebra 0`
satisfies `AlgHom.IsGeometricClifford`. -/
theorem not_isGeometricClifford_zero_of_norm_ne_zero
    {V S : Type*} [SeminormedAddCommGroup V] [Module ℝ V]
    [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
    {v : V} (hv : ‖v‖ ≠ 0) (ρ : CliffordAlgebra (0 : QuadraticForm ℝ V) →ₐ[ℝ] Module.End ℂ S) :
    ¬ ρ.IsGeometricClifford := fun hρ ↦ by
  have h := hρ.map_eq_neg_norm_sq v
  have h0 : ‖v‖ = 0 := by simpa using h.symm
  exact hv h0

end AlgHom

namespace TauCeti

/-- Trivial generator action of `CliffordAlgebra (0 : QuadraticForm ℝ ℝ)` on `ℂ`, sending every real
vector to `0`. -/
def zeroRealLineClifford : CliffordAlgebra (0 : QuadraticForm ℝ ℝ) →ₐ[ℝ] Module.End ℂ ℂ :=
  CliffordAlgebra.lift 0 ⟨0, fun _ ↦ by simp⟩

/-- Every generator of `TauCeti.zeroRealLineClifford` acts as `0`. -/
@[simp]
theorem zeroRealLineClifford_ι (r : ℝ) : zeroRealLineClifford (ι 0 r) = 0 :=
  lift_ι_apply _ _ r

/-- Every generator of `TauCeti.zeroRealLineClifford` is skew-Hermitian, yet
`TauCeti.zeroRealLineClifford` fails `AlgHom.IsGeometricClifford` because `Q = 0` violates
`Q r = -‖r‖²`. -/
theorem inner_zeroRealLineClifford_ι_and_not_isGeometricClifford :
    (∀ (r : ℝ) (x y : ℂ),
        inner ℂ (zeroRealLineClifford (ι 0 r) x) y =
          -inner ℂ x (zeroRealLineClifford (ι 0 r) y)) ∧
      ¬ zeroRealLineClifford.IsGeometricClifford :=
  ⟨fun _ _ _ ↦ by simp,
    zeroRealLineClifford.not_isGeometricClifford_zero_of_norm_ne_zero
      (norm_ne_zero_iff.mpr (one_ne_zero : (1 : ℝ) ≠ 0))⟩

/-- Non-unitary `2 × 2` square root `!![0, 2; -2⁻¹, 0]` of `-1`. -/
private def nonSkewSqrtNegOne : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 2; -(2 : ℂ)⁻¹, 0]

private theorem nonSkewSqrtNegOne_mul_self :
    nonSkewSqrtNegOne * nonSkewSqrtNegOne = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nonSkewSqrtNegOne]

/-- Real Clifford action over `Q r = -r²` on `EuclideanSpace ℂ (Fin 2)` sending `1 : ℝ` to the
non-skew-Hermitian square root `!![0, 2; -2⁻¹, 0]` of `-1`. -/
def nonSkewRealLineClifford :
    CliffordAlgebra (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) →ₐ[ℝ]
      Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  ((Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).toAlgHom.restrictScalars
      ℝ).comp
    ((Complex.lift ⟨nonSkewSqrtNegOne, nonSkewSqrtNegOne_mul_self⟩).comp
      (CliffordAlgebraComplex.toComplex.comp (CliffordAlgebra.map realLineToComplexIsometry)))

/-- Generator evaluation of `TauCeti.nonSkewRealLineClifford`. -/
@[simp]
theorem nonSkewRealLineClifford_ι (r : ℝ) :
    nonSkewRealLineClifford (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) r) =
      r • Matrix.toEuclideanLin !![0, 2; -(2 : ℂ)⁻¹, 0] := by
  have hlI : (Complex.lift ⟨nonSkewSqrtNegOne, nonSkewSqrtNegOne_mul_self⟩) Complex.I =
      nonSkewSqrtNegOne :=
    Complex.liftAux_apply_I nonSkewSqrtNegOne nonSkewSqrtNegOne_mul_self
  rw [nonSkewRealLineClifford, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
    map_apply_ι, realLineToComplexIsometry_apply, CliffordAlgebraComplex.toComplex_ι, map_smul,
    hlI, map_smul, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, nonSkewSqrtNegOne]
  ext w
  simp [Matrix.toLinAlgEquiv_apply, Matrix.toLin_apply]

/-- **Independence of the skew-Hermitian clause**: `TauCeti.nonSkewRealLineClifford` has metric
form `Q r = -‖r‖²` for every `r : ℝ`, yet fails `AlgHom.IsGeometricClifford`. -/
theorem map_eq_neg_norm_sq_and_not_isGeometricClifford_nonSkewRealLineClifford :
    (∀ r : ℝ, (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) r = -‖r‖ ^ 2) ∧
      ¬ nonSkewRealLineClifford.IsGeometricClifford := by
  refine ⟨fun r ↦ by simp [LinearMap.BilinMap.toQuadraticMap_apply, sq], fun hρ ↦ ?_⟩
  have hadj := hρ.adjoint_map_ι 1
  rw [nonSkewRealLineClifford_ι, one_smul,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← map_neg] at hadj
  have hmat := Matrix.toEuclideanLin.injective hadj
  have h01 := congr_fun (congr_fun hmat 0) 1
  simp at h01
  norm_num at h01

end TauCeti
