/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# The carrier of complex Hermitian-matrix distributions

Distributions on complex Hermitian matrices live on Mathlib's real self-adjoint subspace
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)`, where `star` is conjugate transposition and
membership is equivalent to `Matrix.IsHermitian`.

Parallel to `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic`, this file equips that subspace
with the ambient Frobenius norm and real inner product `⟪A, B⟫ = Re tr(B * A)` while keeping the
subtype topology and uniformity definitionally equal to the induced product ones. It also defines
the real coordinate equivalence `TauCeti.hermitianCoordinates` (`(A i i).re` at `(i, i)`,
`(A i j).re` at `(i, j)` for `i < j`, `(A j i).im` at `(i, j)` for `j < i`) and unitary conjugation
`Matrix.unitaryGroup.hermitianConj`.

## Main declarations

* `TauCeti.hermitianMatrixNormedAddCommGroup`, `TauCeti.hermitianMatrixInnerProductSpace` —
  Frobenius norm and real trace inner product on the Hermitian subspace.
* `selfAdjoint.coe_inner_complex`, `selfAdjoint.inner_eq_re_trace_mul`,
  `selfAdjoint.norm_sq_eq_re_trace_sq` — subspace inner product and squared norm via `Re tr`.
* `TauCeti.hermitianCoordinates`, `TauCeti.hermitianCoordinatesMeasurableEquiv`,
  `TauCeti.finrank_hermitianMatrix`, `TauCeti.hermitianBasis`, `TauCeti.hermitianFinOneEquiv` —
  real coordinates, dimension `p ^ 2`, coordinate basis, and `1 × 1` equivalence.
* `Matrix.unitaryGroup.hermitianConj` — unitary conjugation `A ↦ U * A * Uᴴ`.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate Matrix RealInnerProductSpace

namespace TauCeti

/-! ### The Frobenius structure on the Hermitian subspace -/

section instances

variable (p : ℕ)

/-- The Hermitian subspace carries the Frobenius norm induced from ambient complex matrices, with
its metric rebuilt on the subtype uniformity so that the uniform and topological structures are
the subtype ones definitionally. -/
instance hermitianMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
    Submodule.normedAddCommGroup _
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

/-- The Hermitian subspace carries the real Frobenius inner product
`⟪A, B⟫ = ∑ i, ∑ j, (B i j * conj (A i j)).re`, which on Hermitian matrices equals the real trace
pairing `selfAdjoint.inner_eq_re_trace_mul`. -/
instance hermitianMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusInnerProductSpace
  { __ := (inferInstance : Module ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)))
    norm_smul_le r A := norm_smul_le r (A : Matrix (Fin p) (Fin p) ℂ)
    inner A B := ⟪(A : Matrix (Fin p) (Fin p) ℂ), (B : Matrix (Fin p) (Fin p) ℂ)⟫
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℂ)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℂ) ↑B
    add_left A B C := by
      rw [Submodule.coe_add]
      exact InnerProductSpace.add_left (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℂ) ↑B ↑C
    smul_left A B r := Matrix.frobenius_inner_smul_left r (A : Matrix (Fin p) (Fin p) ℂ) ↑B }

instance hermitianMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance hermitianMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  secondCountable_of_proper

instance hermitianMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  FiniteDimensional.completeSpace ℝ _

instance hermitianMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  ESeminormedAddMonoid.toContinuousENorm

/-- The measurable structure is the Borel structure of the subtype topology. -/
instance hermitianMatrixBorelSpace :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  Subtype.borelSpace _

/-- The uniformity of the Frobenius structure is definitionally the subtype uniformity. -/
example : (hermitianMatrixNormedAddCommGroup p).toMetricSpace.toUniformSpace =
    (instUniformSpaceSubtype :
      UniformSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  with_reducible_and_instances rfl

/-- The uniformity of the Frobenius structure induces the subtype topology definitionally. -/
example : (hermitianMatrixNormedAddCommGroup p).toMetricSpace.toUniformSpace.toTopologicalSpace =
    (instTopologicalSpaceSubtype :
      TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  with_reducible_and_instances rfl

/-- The selected topology is the subtype topology. -/
example : (inferInstance : TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
    @instTopologicalSpaceSubtype _ _ inferInstance := by
  with_reducible_and_instances rfl

/-- `volume` is supplied by `measureSpaceOfInnerProductSpace`. -/
example : (inferInstance : MeasureSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
    measureSpaceOfInnerProductSpace := rfl

end instances

end TauCeti

/-! ### Entries and trace inner product on the Hermitian subspace -/

namespace selfAdjoint

open scoped Matrix.Norms.Frobenius in
/-- The inner product on the Hermitian subspace is the real Frobenius inner product of the
underlying complex matrices. -/
@[simp]
theorem coe_inner_complex {p : ℕ}
    (A B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ⟪A, B⟫ = ⟪(A : Matrix (Fin p) (Fin p) ℂ), (B : Matrix (Fin p) (Fin p) ℂ)⟫ := (rfl)

/-- Every element of `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)` is a Hermitian matrix. -/
theorem isHermitian_coe_complex {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (A : Matrix (Fin p) (Fin p) ℂ).IsHermitian := A.2

/-- An element of the Hermitian subspace equals its conjugate transpose. -/
@[simp]
theorem conjTranspose_coe {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (A : Matrix (Fin p) (Fin p) ℂ)ᴴ = (A : Matrix (Fin p) (Fin p) ℂ) :=
  (isHermitian_coe_complex A).eq

/-- Swapping indices conjugates the entry of a Hermitian matrix. -/
theorem coe_apply_conj {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (i j : Fin p) :
    conj ((A : Matrix (Fin p) (Fin p) ℂ) j i) = (A : Matrix (Fin p) (Fin p) ℂ) i j := by
  simpa using (isHermitian_coe_complex A).apply i j

/-- Diagonal entries of a Hermitian matrix have zero imaginary part. -/
@[simp]
theorem im_coe_apply_self {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (i : Fin p) :
    ((A : Matrix (Fin p) (Fin p) ℂ) i i).im = 0 :=
  Complex.conj_eq_iff_im.mp (coe_apply_conj A i i)

/-- On the Hermitian subspace, the real Frobenius inner product is the real part of the trace of
the matrix product. -/
theorem inner_eq_re_trace_mul {p : ℕ}
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ⟪A, Θ⟫ = ((Θ : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ)).trace.re := by
  let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusInnerProductSpace
  rw [coe_inner_complex, Matrix.frobenius_inner_def]
  simp only [Complex.inner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [coe_apply_conj A j i, mul_comm]

/-- The squared Frobenius norm of an element of the Hermitian subspace is `Re tr(A ^ 2)`. -/
theorem norm_sq_eq_re_trace_sq {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ‖A‖ ^ 2 = ((A : Matrix (Fin p) (Fin p) ℂ) ^ 2).trace.re := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_re_trace_mul, sq]

/-- Reading off an entry of a Hermitian matrix is continuous. -/
theorem continuous_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j :=
  continuous_subtype_val.matrix_elem i j

/-- Reading off an entry of a Hermitian matrix is measurable. -/
@[fun_prop]
theorem measurable_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j :=
  (continuous_coe_apply_complex i j).measurable

end selfAdjoint

namespace TauCeti

/-! ### Diagonal and upper-triangular real coordinates -/

section coordinates

variable (p : ℕ)

/-- The continuous real linear equivalence reading off the real coordinates of a complex Hermitian
matrix: at `(i, i)` the diagonal real entry `(A i i).re`, at `(i, j)` with `i < j` the upper
off-diagonal real part `(A i j).re`, and at `(i, j)` with `j < i` the upper off-diagonal imaginary
part `(A j i).im`. This coordinate system fixes the normalization of `TauCeti.hermitianLebesgue`. -/
def hermitianCoordinates :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃L[ℝ] (Fin p × Fin p → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A ij :=
        if ij.1 ≤ ij.2 then ((A : Matrix (Fin p) (Fin p) ℂ) ij.1 ij.2).re
        else ((A : Matrix (Fin p) (Fin p) ℂ) ij.2 ij.1).im
      map_add' A B := funext fun ij ↦ by by_cases h : ij.1 ≤ ij.2 <;> simp [h]
      map_smul' c A := funext fun ij ↦ by by_cases h : ij.1 ≤ ij.2 <;> simp [h]
      invFun x :=
        ⟨Matrix.of fun i j ↦
            if i = j then (x (i, i) : ℂ)
            else if i < j then (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ)
            else (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ),
          Matrix.isHermitian_iff_isSelfAdjoint.mp <| Matrix.IsHermitian.ext fun i j ↦ by
            rcases lt_trichotomy i j with h | rfl | h
            · simp [h, h.ne, h.ne', h.not_gt]
            · simp
            · simp [h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]⟩
      left_inv A := Subtype.ext <| Matrix.ext fun i j ↦ by
        simp only [Matrix.of_apply]
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.ne, h.le, not_le.2 h, mul_comm Complex.I, Complex.re_add_im]
        · simp [Complex.ext_iff, selfAdjoint.im_coe_apply_self]
        · simp only [h.ne', ↓reduceIte, h.not_gt, h.le, not_le.2 h]
          rw [← selfAdjoint.coe_apply_conj A i j]
          simp [Complex.ext_iff]
      right_inv x := funext fun ⟨i, j⟩ ↦ by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.le, h.ne]
        · simp
        · simp [h, h.ne, not_le.2 h] }

/-- On or above the diagonal (`i ≤ j`), `TauCeti.hermitianCoordinates` reads the real part of the
`(i, j)` entry. -/
@[simp]
theorem hermitianCoordinates_apply_of_le
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) {i j : Fin p} (h : i ≤ j) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) i j).re := ite_eq_left h

/-- Below the diagonal (`j < i`), `TauCeti.hermitianCoordinates` reads the imaginary part of the
upper-triangular `(j, i)` entry. -/
@[simp]
theorem hermitianCoordinates_apply_of_gt
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) {i j : Fin p} (h : j < i) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) j i).im :=
  ite_eq_right (not_le.2 h)

/-- Reconstructing a Hermitian matrix from real coordinates places `x (i, i)` on the diagonal. -/
@[simp]
theorem coe_hermitianCoordinates_symm_apply_self (x : Fin p × Fin p → ℝ) (i : Fin p) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i i = x (i, i) := by
  simp [hermitianCoordinates]

/-- Above the diagonal (`i < j`), `(TauCeti.hermitianCoordinates p).symm x` has entry
`x (i, j) + I * x (j, i)`. -/
@[simp]
theorem coe_hermitianCoordinates_symm_apply_of_lt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : i < j) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ) := by simp [hermitianCoordinates, h.ne, h]

/-- Below the diagonal (`j < i`), `(TauCeti.hermitianCoordinates p).symm x` has entry
`x (j, i) - I * x (i, j)`. -/
@[simp]
theorem coe_hermitianCoordinates_symm_apply_of_gt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : j < i) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ) := by simp [hermitianCoordinates, h.ne', h.not_gt]

/-- The measurable equivalence induced by `TauCeti.hermitianCoordinates`. -/
def hermitianCoordinatesMeasurableEquiv :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ᵐ (Fin p × Fin p → ℝ) :=
  (hermitianCoordinates p).toHomeomorph.toMeasurableEquiv

/-- Underlying function of `TauCeti.hermitianCoordinatesMeasurableEquiv`. -/
@[simp]
theorem hermitianCoordinatesMeasurableEquiv_coe :
    (hermitianCoordinatesMeasurableEquiv p : _ → Fin p × Fin p → ℝ) = hermitianCoordinates p :=
  (rfl)

/-- Underlying inverse function of `TauCeti.hermitianCoordinatesMeasurableEquiv`. -/
@[simp]
theorem hermitianCoordinatesMeasurableEquiv_symm_coe :
    ((hermitianCoordinatesMeasurableEquiv p).symm : (Fin p × Fin p → ℝ) → _) =
      (hermitianCoordinates p).symm := (rfl)

/-- The real space of `p × p` complex Hermitian matrices has dimension `p ^ 2`. -/
theorem finrank_hermitianMatrix :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) = p ^ 2 := by
  rw [(hermitianCoordinates p).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin, sq]

/-- The real basis of the Hermitian subspace dual to `TauCeti.hermitianCoordinates`: `Eᵢᵢ` at
`(i, i)`, `Eᵢⱼ + Eⱼᵢ` at `(i, j)` for `i < j`, and `I • Eⱼᵢ - I • Eᵢⱼ` at `(i, j)` for `j < i`. -/
def hermitianBasis :
    Basis (Fin p × Fin p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (Pi.basisFun ℝ (Fin p × Fin p)).map (hermitianCoordinates p).symm.toLinearEquiv

/-- `TauCeti.hermitianBasis` sends `ij` to the matrix with a single unit coordinate at `ij`. -/
theorem hermitianBasis_apply (ij : Fin p × Fin p) :
    hermitianBasis p ij = (hermitianCoordinates p).symm (Pi.single ij 1) := by simp [hermitianBasis]

/-- Coordinates in `TauCeti.hermitianBasis` agree with `TauCeti.hermitianCoordinates`. -/
@[simp]
theorem hermitianBasis_repr (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (ij : Fin p × Fin p) :
    (hermitianBasis p).repr A ij = hermitianCoordinates p A ij := by simp [hermitianBasis]

/-- On the diagonal, the coordinate basis vector is a single real matrix unit `Eᵢᵢ`. -/
theorem coe_hermitianBasis_diag (i : Fin p) :
    ((hermitianBasis p (i, i) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i i 1 := by
  ext k l; rw [hermitianBasis_apply]
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, show ¬(k = i ∧ l = i) from fun ⟨hk, hl⟩ ↦ h.ne (hk.trans hl.symm),
      show ¬(l = i ∧ k = i) from fun ⟨hl, hk⟩ ↦ h.ne (hk.trans hl.symm),
      show ¬(i = k ∧ i = l) from fun ⟨hk, hl⟩ ↦ h.ne (hk.symm.trans hl)]
  · rcases eq_or_ne k i with rfl | hk
    · simp
    · simp [hk, Ne.symm hk]
  · simp [h, show ¬(l = i ∧ k = i) from fun ⟨hl, hk⟩ ↦ h.ne (hl.trans hk.symm),
      show ¬(k = i ∧ l = i) from fun ⟨hk, hl⟩ ↦ h.ne (hl.trans hk.symm),
      show ¬(i = k ∧ i = l) from fun ⟨hk, hl⟩ ↦ h.ne (hl.symm.trans hk)]

/-- For `i < j`, the coordinate basis vector at `(i, j)` is `Eᵢⱼ + Eⱼᵢ`. -/
theorem coe_hermitianBasis_of_lt {i j : Fin p} (hij : i < j) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l; rw [hermitianBasis_apply]
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩; simp [hij, hij.ne, hij.ne']
  by_cases h2 : k = j ∧ l = i
  · rcases h2 with ⟨rfl, rfl⟩; simp [hij, hij.ne, hij.ne']
  have h1' : ¬(i = k ∧ j = l) := fun ⟨a, b⟩ ↦ h1 ⟨a.symm, b.symm⟩
  have h2' : ¬(j = k ∧ i = l) := fun ⟨a, b⟩ ↦ h2 ⟨a.symm, b.symm⟩
  have hlk : ¬(l = i ∧ k = j) := fun ⟨a, b⟩ ↦ h2 ⟨b, a⟩
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, h1, h1', h2', hlk]
  · simp [h1, h1', h2']
  · simp [h, h1, h1', h2', hlk]

/-- For `j < i`, the coordinate basis vector at `(i, j)` (representing `(A j i).im`) is
`I • Eⱼᵢ - I • Eᵢⱼ`. -/
theorem coe_hermitianBasis_of_gt {i j : Fin p} (hji : j < i) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) =
      Matrix.single j i Complex.I - Matrix.single i j Complex.I := by
  ext k l; rw [hermitianBasis_apply]
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩; simp [hji, hji.ne, hji.ne']
  by_cases h2 : k = j ∧ l = i
  · rcases h2 with ⟨rfl, rfl⟩; simp [hji, hji.ne, hji.ne']
  have h1' : ¬(i = k ∧ j = l) := fun ⟨a, b⟩ ↦ h1 ⟨a.symm, b.symm⟩
  have h2' : ¬(j = k ∧ i = l) := fun ⟨a, b⟩ ↦ h2 ⟨a.symm, b.symm⟩
  have hlk : ¬(l = i ∧ k = j) := fun ⟨a, b⟩ ↦ h2 ⟨b, a⟩
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, h1, h1', h2', hlk]
  · simp [h1, h1', h2']
  · simp [h, h1, h1', h2', hlk]

end coordinates

/-! ### The one-dimensional carrier -/

/-- A `1 × 1` complex Hermitian matrix is determined by the real part of its single entry. -/
def hermitianFinOneEquiv : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A := ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re
      map_add' _ _ := rfl
      map_smul' _ _ := by simp
      invFun x := (hermitianCoordinates 1).symm fun _ ↦ x
      left_inv A := (hermitianCoordinates 1).injective <| funext fun ⟨i, j⟩ ↦ by
        simp [Subsingleton.elim i 0, Subsingleton.elim j 0]
      right_inv x := by simp }

/-- `TauCeti.hermitianFinOneEquiv` reads the real part of the `(0, 0)` entry. -/
@[simp]
theorem hermitianFinOneEquiv_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
    hermitianFinOneEquiv A = ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re := (rfl)

/-- `TauCeti.hermitianFinOneEquiv.symm` embeds a real scalar as a `1 × 1` Hermitian matrix. -/
@[simp]
theorem coe_hermitianFinOneEquiv_symm_apply (x : ℝ) (i j : Fin 1) :
    ((hermitianFinOneEquiv.symm x : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
        Matrix (Fin 1) (Fin 1) ℂ) i j = x := by
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact coe_hermitianCoordinates_symm_apply_self 1 (fun _ ↦ x) 0

end TauCeti

/-! ### Unitary conjugation on the Hermitian subspace -/

namespace Matrix.unitaryGroup

/-- Unitary conjugation `A ↦ U * A * Uᴴ` as a real linear isometry equivalence of the space of
`p × p` complex Hermitian matrices. -/
def hermitianConj {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) where
  toFun A := ⟨(U : Matrix (Fin p) (Fin p) ℂ) * A * (U : Matrix (Fin p) (Fin p) ℂ)ᴴ,
    Matrix.isHermitian_iff_isSelfAdjoint.mp <|
      Matrix.isHermitian_mul_mul_conjTranspose _ (selfAdjoint.isHermitian_coe_complex A)⟩
  map_add' A B := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' c A := Subtype.ext (by simp)
  invFun A := ⟨(U : Matrix (Fin p) (Fin p) ℂ)ᴴ * A * (U : Matrix (Fin p) (Fin p) ℂ),
    Matrix.isHermitian_iff_isSelfAdjoint.mp <| by
      simpa using Matrix.isHermitian_mul_mul_conjTranspose
        (U : Matrix (Fin p) (Fin p) ℂ)ᴴ (selfAdjoint.isHermitian_coe_complex A)⟩
  left_inv A := Subtype.ext <| by
    have hU : (U : Matrix (Fin p) (Fin p) ℂ)ᴴ * (U : Matrix (Fin p) (Fin p) ℂ) = 1 := by
      simpa only [star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.2
    simp only [Matrix.mul_assoc, hU, mul_one]; rw [← Matrix.mul_assoc, hU, one_mul]
  right_inv A := Subtype.ext <| by
    have hU : (U : Matrix (Fin p) (Fin p) ℂ) * (U : Matrix (Fin p) (Fin p) ℂ)ᴴ = 1 := by
      simpa only [star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp U.2
    simp only [Matrix.mul_assoc, hU, mul_one]; rw [← Matrix.mul_assoc, hU, one_mul]
  norm_map' A := by
    let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
    have hsq : ‖((U : Matrix (Fin p) (Fin p) ℂ) * A * (U : Matrix (Fin p) (Fin p) ℂ)ᴴ)‖ ^ 2 =
        ‖(A : Matrix (Fin p) (Fin p) ℂ)‖ ^ 2 := by
      simpa [star_eq_conjTranspose] using Matrix.frobenius_norm_sq_conj_unitary
        (star U : Matrix (Fin p) (Fin p) ℂ) (A : Matrix (Fin p) (Fin p) ℂ) (star U).2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Ambient matrix coercion of `Matrix.unitaryGroup.hermitianConj`. -/
@[simp]
theorem coe_hermitianConj_apply {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (hermitianConj U A : Matrix (Fin p) (Fin p) ℂ) =
      (U : Matrix (Fin p) (Fin p) ℂ) * A * (U : Matrix (Fin p) (Fin p) ℂ)ᴴ := (rfl)

/-- Ambient matrix coercion of the inverse of `Matrix.unitaryGroup.hermitianConj`. -/
@[simp]
theorem coe_hermitianConj_symm_apply {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ((hermitianConj U).symm A : Matrix (Fin p) (Fin p) ℂ) =
      (U : Matrix (Fin p) (Fin p) ℂ)ᴴ * A * (U : Matrix (Fin p) (Fin p) ℂ) := (rfl)

/-- Conjugating by the identity unitary matrix is the identity isometry. -/
@[simp]
theorem hermitianConj_one {p : ℕ} :
    hermitianConj (1 : Matrix.unitaryGroup (Fin p) ℂ) = LinearIsometryEquiv.refl ℝ _ :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext (by simp)

/-- Unitary conjugation is a left action of `Matrix.unitaryGroup`. -/
theorem hermitianConj_mul {p : ℕ} (U V : Matrix.unitaryGroup (Fin p) ℂ) :
    hermitianConj (U * V) = (hermitianConj V).trans (hermitianConj U) :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext (by simp [Matrix.mul_assoc])

/-- Conjugating by `U⁻¹` is the inverse linear isometry equivalence. -/
@[simp]
theorem hermitianConj_inv {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    hermitianConj U⁻¹ = (hermitianConj U).symm := by
  refine LinearIsometryEquiv.ext fun _ ↦ Subtype.ext ?_
  have hinv : ((U⁻¹ : Matrix.unitaryGroup (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) =
      (U : Matrix (Fin p) (Fin p) ℂ)ᴴ := rfl
  simp [hinv]

end Matrix.unitaryGroup
