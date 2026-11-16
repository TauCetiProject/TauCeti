/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
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
# The carrier of complex Hermitian matrix distributions

Complex Hermitian matrix distributions such as the GUE live on Mathlib's real self-adjoint
subspace `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`. By
`Matrix.isHermitian_iff_isSelfAdjoint`, its elements are precisely the Hermitian `n × n` complex
matrices.

This file equips that real vector space with the real Frobenius norm and inner product
`⟪A, B⟫_ℝ = Re tr(A * B)` while preserving the subtype uniformity and topology definitionally:
the norm is induced from `Matrix.frobeniusNormedAddCommGroup`, whose uniformity and topology are
definitionally the product ones, and `volume` is supplied by `measureSpaceOfInnerProductSpace`.

It fixes the real coordinate system `TauCeti.hermitianCoordinates n`, reading off the `n` real
diagonal entries, the `n(n - 1)/2` real parts of strictly upper-triangular entries, and the
`n(n - 1)/2` imaginary parts of strictly upper-triangular entries (indexed uniformly by
`Fin n × Fin n`), builds the corresponding coordinate basis `TauCeti.hermitianBasis n`, and
packages unitary conjugation `A ↦ U * A * Uᴴ` as a real linear isometry equivalence
`Matrix.unitaryGroup.hermitianConj`.

## Main declarations

* `TauCeti.hermitianMatrixNormedAddCommGroup`, `TauCeti.hermitianMatrixInnerProductSpace` — the
  real Frobenius structure on the complex Hermitian subspace.
* `selfAdjoint.inner_eq_re_trace_mul` and `selfAdjoint.norm_sq_eq_re_trace_sq` — the Frobenius
  pairing is `Re tr(A * B)` and the squared norm is `Re tr(A ^ 2)`.
* `TauCeti.hermitianCoordinates` — continuous linear equivalence with `Fin n × Fin n → ℝ`,
  reading diagonal real parts and strictly upper-triangular real and imaginary parts.
* `TauCeti.hermitianCoordinatesMeasurableEquiv` — its measurable-equivalence form.
* `TauCeti.finrank_hermitianMatrix` — the real dimension is `n ^ 2`.
* `TauCeti.hermitianBasis` — basis dual to `TauCeti.hermitianCoordinates`.
* `TauCeti.hermitianFinOneEquiv` — identification of `1 × 1` Hermitian matrices with `ℝ`.
* `Matrix.unitaryGroup.hermitianConj` — unitary conjugation `A ↦ U * A * Uᴴ` as a real linear
  isometry equivalence of the Hermitian subspace.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped RealInnerProductSpace Matrix

namespace TauCeti

/-! ### The real Frobenius structure on the complex Hermitian subspace -/

section instances

variable (n : ℕ)

/-- The complex Hermitian subspace carries the Frobenius norm induced from the ambient complex
matrices, with its metric rebuilt on the subtype uniformity so that the uniform and topological
structures agree definitionally with the subtype instances. -/
instance hermitianMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
    Submodule.normedAddCommGroup _
  -- Forces the uniformity field of the metric to be the subtype uniformity itself, so that
  -- downstream instance search unifies the two syntactically rather than only up to `rfl`.
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

/-- The complex Hermitian subspace carries the real Frobenius inner product
`⟪A, B⟫_ℝ = ∑ i, ∑ j, ⟪A i j, B i j⟫_ℝ`, which equals `Re tr(A * B)`
(`selfAdjoint.inner_eq_re_trace_mul`). -/
instance hermitianMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusInnerProductSpace
  { __ := (inferInstance : Module ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)))
    norm_smul_le r A := norm_smul_le r (A : Matrix (Fin n) (Fin n) ℂ)
    inner A B := ⟪(A : Matrix (Fin n) (Fin n) ℂ), (B : Matrix (Fin n) (Fin n) ℂ)⟫
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜 := ℝ) (A : Matrix (Fin n) (Fin n) ℂ) ↑B
    add_left A B C := by
      rw [Submodule.coe_add]
      exact InnerProductSpace.add_left (𝕜 := ℝ) (A : Matrix (Fin n) (Fin n) ℂ) ↑B ↑C
    smul_left A B r := Matrix.frobenius_inner_smul_left r (A : Matrix (Fin n) (Fin n) ℂ) ↑B }

instance hermitianMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance hermitianMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  secondCountable_of_proper

instance hermitianMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  FiniteDimensional.completeSpace ℝ _

instance hermitianMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  ESeminormedAddMonoid.toContinuousENorm

/-- The measurable structure is the Borel structure of the subtype topology. -/
instance hermitianMatrixBorelSpace :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  Subtype.borelSpace _

/-- The uniformity of the Frobenius structure is definitionally the subtype uniformity. -/
example :
    (hermitianMatrixNormedAddCommGroup n).toMetricSpace.toUniformSpace =
      (instUniformSpaceSubtype :
        UniformSpace (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) := by
  with_reducible_and_instances rfl

/-- The uniformity of the Frobenius structure induces the subtype topology definitionally. -/
example :
    (hermitianMatrixNormedAddCommGroup n).toMetricSpace.toUniformSpace.toTopologicalSpace =
      (instTopologicalSpaceSubtype :
        TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) := by
  with_reducible_and_instances rfl

/-- The selected topology is the subtype topology. -/
example :
    (inferInstance :
        TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) =
      @instTopologicalSpaceSubtype _ _ inferInstance := by
  with_reducible_and_instances rfl

/-- `volume` is supplied by `measureSpaceOfInnerProductSpace`. -/
example :
    (inferInstance : MeasureSpace (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) =
      measureSpaceOfInnerProductSpace :=
  rfl

end instances

end TauCeti

/-! ### Entry symmetries and the trace pairing -/

namespace selfAdjoint

variable {n : ℕ}

/-- An element of the complex Hermitian subspace is a Hermitian matrix. -/
theorem isHermitian_coe_complex (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    (A : Matrix (Fin n) (Fin n) ℂ).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.2 A.2

/-- An element of the complex Hermitian subspace is fixed by conjugate transposition. -/
@[simp]
theorem conjTranspose_coe (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    (A : Matrix (Fin n) (Fin n) ℂ)ᴴ = (A : Matrix (Fin n) (Fin n) ℂ) :=
  (isHermitian_coe_complex A).eq

/-- Swapping indices of a Hermitian matrix conjugates the entry. -/
theorem coe_apply_conj (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (i j : Fin n) :
    (A : Matrix (Fin n) (Fin n) ℂ) j i = starRingEnd ℂ ((A : Matrix (Fin n) (Fin n) ℂ) i j) :=
  ((isHermitian_coe_complex A).apply j i).symm

/-- Diagonal entries of a complex Hermitian matrix have zero imaginary part. -/
@[simp]
theorem coe_apply_self_im (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (i : Fin n) :
    ((A : Matrix (Fin n) (Fin n) ℂ) i i).im = 0 := by
  have h := congrArg Complex.im (coe_apply_conj A i i)
  simp only [Complex.conj_im] at h
  linarith

/-- The real parts of entries of a Hermitian matrix are symmetric. -/
theorem coe_apply_re_comm (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (i j : Fin n) :
    ((A : Matrix (Fin n) (Fin n) ℂ) j i).re = ((A : Matrix (Fin n) (Fin n) ℂ) i j).re := by
  rw [coe_apply_conj, Complex.conj_re]

/-- The imaginary parts of entries of a Hermitian matrix are skew-symmetric. -/
theorem coe_apply_im_comm (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (i j : Fin n) :
    ((A : Matrix (Fin n) (Fin n) ℂ) j i).im = -((A : Matrix (Fin n) (Fin n) ℂ) i j).im := by
  rw [coe_apply_conj, Complex.conj_im]

open scoped Matrix.Norms.Frobenius in
/-- The real inner product on the Hermitian subspace is the ambient real Frobenius inner product
of the underlying complex matrices. -/
@[simp]
theorem coe_inner_hermitian (A B : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ⟪A, B⟫ = ⟪(A : Matrix (Fin n) (Fin n) ℂ), (B : Matrix (Fin n) (Fin n) ℂ)⟫ :=
  (rfl)

/-- On the complex Hermitian subspace, the real Frobenius inner product is `Re tr(A * B)`. -/
theorem inner_eq_re_trace_mul (A B : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ⟪A, B⟫ = ((A : Matrix (Fin n) (Fin n) ℂ) * (B : Matrix (Fin n) (Fin n) ℂ)).trace.re := by
  let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusInnerProductSpace
  rw [coe_inner_hermitian, Matrix.frobenius_inner_def, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    coe_apply_re_comm B i j, coe_apply_im_comm B i j]
  ring

/-- The squared Frobenius norm of a complex Hermitian matrix is `Re tr(A ^ 2)`. -/
theorem norm_sq_eq_re_trace_sq (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ‖A‖ ^ 2 = ((A : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_re_trace_mul, sq]

end selfAdjoint

namespace TauCeti

/-! ### Diagonal-real and upper-triangular real/imaginary coordinates -/

section coordinates

variable (n : ℕ)

/-- The continuous linear equivalence reading off the real coordinates of a complex Hermitian
matrix: `(A i i).re` at `(i, i)`, `(A i j).re` at `(i, j)` for `i < j`, and `(A j i).im` at
`(i, j)` for `j < i`. Its inverse reconstructs the Hermitian matrix from these `n ^ 2` real
coordinates. -/
def hermitianCoordinates :
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) ≃L[ℝ] (Fin n × Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A p := if p.1 ≤ p.2 then ((A : Matrix (Fin n) (Fin n) ℂ) p.1 p.2).re
        else ((A : Matrix (Fin n) (Fin n) ℂ) p.2 p.1).im
      map_add' A B := by
        funext p
        by_cases h : p.1 ≤ p.2 <;> simp [h]
      map_smul' c A := by
        funext p
        by_cases h : p.1 ≤ p.2 <;> simp [h, Complex.real_smul]
      invFun x :=
        ⟨Matrix.of fun i j =>
            if i = j then (x (i, i) : ℂ)
            else if i < j then (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ)
            else (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ), by
          refine Matrix.isHermitian_iff_isSelfAdjoint.1 (Matrix.IsHermitian.ext fun i j => ?_)
          simp only [Matrix.of_apply, Complex.star_def]
          rcases lt_trichotomy i j with h | rfl | h
          · simp [h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]
          · simp
          · simp [h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]⟩
      left_inv A := by
        refine Subtype.ext ?_
        ext i j
        simp only [Matrix.of_apply]
        rcases lt_trichotomy i j with h | rfl | h
        · simp only [h.ne, ↓reduceIte, h, h.le, h.not_ge]
          rw [mul_comm, Complex.re_add_im]
        · simp only [↓reduceIte, le_rfl]
          exact Complex.ext rfl (by simp)
        · simp only [h.ne', ↓reduceIte, h.not_gt, h.le, h.not_ge]
          apply Complex.ext
          · simp [selfAdjoint.coe_apply_re_comm A j i]
          · simp [selfAdjoint.coe_apply_im_comm A j i]
      right_inv x := by
        funext ⟨i, j⟩
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.le, h.ne]
        · simp
        · simp [h, h.not_ge, h.ne] }

@[simp]
theorem hermitianCoordinates_apply_of_le (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    {i j : Fin n} (h : i ≤ j) :
    hermitianCoordinates n A (i, j) = ((A : Matrix (Fin n) (Fin n) ℂ) i j).re :=
  ite_eq_left h

@[simp]
theorem hermitianCoordinates_apply_of_gt (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    {i j : Fin n} (h : j < i) :
    hermitianCoordinates n A (i, j) = ((A : Matrix (Fin n) (Fin n) ℂ) j i).im :=
  ite_eq_right (not_le.2 h)

@[simp]
theorem coe_hermitianCoordinates_symm_apply_self (x : Fin n × Fin n → ℝ) (i : Fin n) :
    ((hermitianCoordinates n).symm x : Matrix (Fin n) (Fin n) ℂ) i i = (x (i, i) : ℂ) := by
  simp [hermitianCoordinates]

@[simp]
theorem coe_hermitianCoordinates_symm_apply_of_lt (x : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : i < j) :
    ((hermitianCoordinates n).symm x : Matrix (Fin n) (Fin n) ℂ) i j =
      (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ) := by
  simp [hermitianCoordinates, h, h.ne]

@[simp]
theorem coe_hermitianCoordinates_symm_apply_of_gt (x : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : j < i) :
    ((hermitianCoordinates n).symm x : Matrix (Fin n) (Fin n) ℂ) i j =
      (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ) := by
  simp [hermitianCoordinates, h.not_gt, h.ne']

/-- The measurable equivalence induced by `TauCeti.hermitianCoordinates`. -/
def hermitianCoordinatesMeasurableEquiv :
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) ≃ᵐ (Fin n × Fin n → ℝ) :=
  (hermitianCoordinates n).toHomeomorph.toMeasurableEquiv

@[simp]
theorem hermitianCoordinatesMeasurableEquiv_coe :
    (hermitianCoordinatesMeasurableEquiv n : _ → Fin n × Fin n → ℝ) =
      hermitianCoordinates n :=
  (rfl)

@[simp]
theorem hermitianCoordinatesMeasurableEquiv_symm_coe :
    ((hermitianCoordinatesMeasurableEquiv n).symm : (Fin n × Fin n → ℝ) → _) =
      (hermitianCoordinates n).symm :=
  (rfl)

/-- The real vector space of `n × n` complex Hermitian matrices has dimension `n ^ 2`. -/
theorem finrank_hermitianMatrix :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) = n ^ 2 := by
  rw [(hermitianCoordinates n).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin, sq]

/-- The real basis of the complex Hermitian subspace dual to `TauCeti.hermitianCoordinates`:
`Eᵢᵢ` on the diagonal, `Eᵢⱼ + Eⱼᵢ` for `i < j`, and `I • Eⱼᵢ - I • Eᵢⱼ` for `j < i`. -/
def hermitianBasis :
    Basis (Fin n × Fin n) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (Pi.basisFun ℝ (Fin n × Fin n)).map (hermitianCoordinates n).symm.toLinearEquiv

theorem hermitianBasis_apply (p : Fin n × Fin n) :
    hermitianBasis n p = (hermitianCoordinates n).symm (Pi.single p 1) := by
  simp [hermitianBasis]

/-- The coordinates of a Hermitian matrix in `TauCeti.hermitianBasis` are
`TauCeti.hermitianCoordinates`. -/
@[simp]
theorem hermitianBasis_repr (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (p : Fin n × Fin n) :
    (hermitianBasis n).repr A p = hermitianCoordinates n A p := by
  simp [hermitianBasis]

/-- On the diagonal, the coordinate basis vector is a single matrix unit. -/
theorem coe_hermitianBasis_diag (i : Fin n) :
    ((hermitianBasis n (i, i) : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) = Matrix.single i i 1 := by
  ext k l
  rw [hermitianBasis_apply, Matrix.single_apply]
  rcases lt_trichotomy k l with h | rfl | h
  · rw [coe_hermitianCoordinates_symm_apply_of_lt n _ h]
    simp only [Pi.single_apply, Prod.mk.injEq]
    have h1 : ¬(k = i ∧ l = i) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    have h2 : ¬(l = i ∧ k = i) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    have h3 : ¬(i = k ∧ i = l) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    simp [h1, h2, h3]
  · rw [coe_hermitianCoordinates_symm_apply_self]
    simp only [Pi.single_apply, Prod.mk.injEq, and_self]
    rcases eq_or_ne k i with rfl | hki <;> simp [*, Ne.symm]
  · rw [coe_hermitianCoordinates_symm_apply_of_gt n _ h]
    simp only [Pi.single_apply, Prod.mk.injEq]
    have h1 : ¬(l = i ∧ k = i) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    have h2 : ¬(k = i ∧ l = i) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    have h3 : ¬(i = k ∧ i = l) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    simp [h1, h2, h3]

/-- Above the diagonal (`i < j`), the coordinate basis vector is `Eᵢⱼ + Eⱼᵢ`. -/
theorem coe_hermitianBasis_offDiag_lt {i j : Fin n} (h : i < j) :
    ((hermitianBasis n (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  rw [hermitianBasis_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [coe_hermitianCoordinates_symm_apply_of_lt n _ hkl]
    have hne1 : ¬(j = k ∧ i = l) := by rintro ⟨rfl, rfl⟩; exact h.not_gt hkl
    have hne2 : (l, k) ≠ (i, j) := by
      intro heq; rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h.not_gt hkl
    simp only [Pi.single_apply, hne1, hne2, ↓reduceIte, Complex.ofReal_zero, mul_zero, add_zero,
      Prod.mk.injEq]
    rcases eq_or_ne k i with rfl | hki <;> rcases eq_or_ne l j with rfl | hlj <;>
      simp [*, Ne.symm]
  · rw [coe_hermitianCoordinates_symm_apply_self]
    have hne1 : (k, k) ≠ (i, j) := by
      intro heq; rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h.ne rfl
    have hne2 : ¬(i = k ∧ j = k) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    have hne3 : ¬(j = k ∧ i = k) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    simp [hne1, hne2, hne3]
  · rw [coe_hermitianCoordinates_symm_apply_of_gt n _ hkl]
    have hne1 : ¬(i = k ∧ j = l) := by rintro ⟨rfl, rfl⟩; exact h.not_gt hkl
    have hne2 : (k, l) ≠ (i, j) := by
      intro heq; rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h.not_gt hkl
    simp only [Pi.single_apply, hne1, hne2, ↓reduceIte, Complex.ofReal_zero, mul_zero, sub_zero,
      zero_add, Prod.mk.injEq]
    rcases eq_or_ne l i with rfl | hli <;> rcases eq_or_ne k j with rfl | hkj <;>
      simp [*, Ne.symm]

/-- Below the diagonal (`j < i`), the coordinate basis vector is `I • Eⱼᵢ - I • Eᵢⱼ`. -/
theorem coe_hermitianBasis_offDiag_gt {i j : Fin n} (h : j < i) :
    ((hermitianBasis n (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) =
      Matrix.single j i Complex.I - Matrix.single i j Complex.I := by
  ext k l
  rw [hermitianBasis_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply]
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [coe_hermitianCoordinates_symm_apply_of_lt n _ hkl]
    have hne1 : ¬(i = k ∧ j = l) := by rintro ⟨rfl, rfl⟩; exact h.not_gt hkl
    have hne2 : (k, l) ≠ (i, j) := by
      intro heq; rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h.not_gt hkl
    simp only [Pi.single_apply, hne1, hne2, ↓reduceIte, Complex.ofReal_zero, zero_add, sub_zero,
      Prod.mk.injEq]
    rcases eq_or_ne l i with rfl | hli <;> rcases eq_or_ne k j with rfl | hkj <;>
      simp [*, Ne.symm]
  · rw [coe_hermitianCoordinates_symm_apply_self]
    have hne1 : (k, k) ≠ (i, j) := by
      intro heq; rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h.ne' rfl
    have hne2 : ¬(j = k ∧ i = k) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    have hne3 : ¬(i = k ∧ j = k) := by rintro ⟨rfl, rfl⟩; exact h.ne rfl
    simp [hne1, hne2, hne3]
  · rw [coe_hermitianCoordinates_symm_apply_of_gt n _ hkl]
    have hne1 : ¬(j = k ∧ i = l) := by rintro ⟨rfl, rfl⟩; exact h.not_gt hkl
    have hne2 : (l, k) ≠ (i, j) := by
      intro heq; rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h.not_gt hkl
    simp only [Pi.single_apply, hne1, hne2, ↓reduceIte, Complex.ofReal_zero, zero_sub,
      Prod.mk.injEq]
    rcases eq_or_ne k i with rfl | hki <;> rcases eq_or_ne l j with rfl | hlj <;>
      simp [*, Ne.symm]

end coordinates

/-! ### The one-dimensional carrier -/

/-- A `1 × 1` complex Hermitian matrix is its single real diagonal entry. -/
def hermitianFinOneEquiv : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) ≃L[ℝ] ℝ :=
  letI : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ => Subsingleton.elim _ _⟩
  (hermitianCoordinates 1).trans (ContinuousLinearEquiv.funUnique (Fin 1 × Fin 1) ℝ ℝ)

@[simp]
theorem hermitianFinOneEquiv_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
    hermitianFinOneEquiv A = ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ => Subsingleton.elim _ _⟩
  have hdefault : (default : Fin 1 × Fin 1) = (0, 0) := Subsingleton.elim _ _
  rw [hermitianFinOneEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_funUnique, Function.eval, hdefault,
    hermitianCoordinates_apply_of_le 1 A le_rfl]

@[simp]
theorem coe_hermitianFinOneEquiv_symm_apply (x : ℝ) (i j : Fin 1) :
    ((hermitianFinOneEquiv.symm x : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
        Matrix (Fin 1) (Fin 1) ℂ) i j = (x : ℂ) := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ => Subsingleton.elim _ _⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [hermitianFinOneEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.coe_funUnique_symm, coe_hermitianCoordinates_symm_apply_self,
    Function.const_apply]

end TauCeti

/-! ### Unitary conjugation on the complex Hermitian subspace -/

namespace Matrix.unitaryGroup

variable {n : ℕ}

/-- Unitary conjugation `A ↦ U * A * Uᴴ` as a real linear isometry equivalence of the complex
Hermitian subspace. -/
def hermitianConj (U : Matrix.unitaryGroup (Fin n) ℂ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  toFun A :=
    ⟨(U : Matrix (Fin n) (Fin n) ℂ) * (A : Matrix (Fin n) (Fin n) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ)ᴴ,
      Matrix.isHermitian_iff_isSelfAdjoint.1
        (Matrix.isHermitian_mul_mul_conjTranspose _ (selfAdjoint.isHermitian_coe_complex A))⟩
  invFun A :=
    ⟨(U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (A : Matrix (Fin n) (Fin n) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ),
      Matrix.isHermitian_iff_isSelfAdjoint.1
        (Matrix.isHermitian_conjTranspose_mul_mul _ (selfAdjoint.isHermitian_coe_complex A))⟩
  map_add' A B := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' r A := Subtype.ext (by simp)
  left_inv A := Subtype.ext (by
    have hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.1 U.2
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℂ)ᴴ,
      hU, one_mul, mul_one])
  right_inv A := Subtype.ext (by
    have hU : (U : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.1 U.2
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℂ),
      hU, one_mul, mul_one])
  norm_map' A := by
    let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
    have hU' : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      simpa [Matrix.star_eq_conjTranspose] using U⁻¹.2
    have hsq := Matrix.frobenius_norm_sq_conj_unitary
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ (A : Matrix (Fin n) (Fin n) ℂ) hU'
    rw [Matrix.conjTranspose_conjTranspose] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

@[simp]
theorem coe_hermitianConj_apply (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    (hermitianConj U A : Matrix (Fin n) (Fin n) ℂ) =
      (U : Matrix (Fin n) (Fin n) ℂ) * (A : Matrix (Fin n) (Fin n) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ)ᴴ :=
  (rfl)

theorem coe_hermitianConj_symm_apply (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ((hermitianConj U).symm A : Matrix (Fin n) (Fin n) ℂ) =
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (A : Matrix (Fin n) (Fin n) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ) :=
  (rfl)

@[simp]
theorem hermitianConj_one :
    hermitianConj (1 : Matrix.unitaryGroup (Fin n) ℂ) = LinearIsometryEquiv.refl ℝ _ := by
  refine LinearIsometryEquiv.ext fun A => Subtype.ext ?_
  simp

theorem hermitianConj_mul (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    hermitianConj (U * V) = (hermitianConj V).trans (hermitianConj U) := by
  refine LinearIsometryEquiv.ext fun A => Subtype.ext ?_
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp]
theorem hermitianConj_symm (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (hermitianConj U).symm = hermitianConj U⁻¹ := by
  refine LinearIsometryEquiv.ext fun A => Subtype.ext ?_
  simp [coe_hermitianConj_symm_apply, Matrix.star_eq_conjTranspose]

end Matrix.unitaryGroup
