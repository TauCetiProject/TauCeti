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
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# The carrier of complex Hermitian-matrix distributions

Complex Hermitian random-matrix distributions such as the Gaussian unitary ensemble live on
Mathlib's real self-adjoint subspace `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)`. Over
`ℂ`, `star` is conjugate transpose, so this real vector space consists of the `p × p` Hermitian
matrices, and `Matrix.isHermitian_iff_isSelfAdjoint` connects membership to the spectral API.

Parallel to `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic`, this file equips that subspace
with the real Frobenius norm and inner product
`⟪A, B⟫_ℝ = ((B : Matrix (Fin p) (Fin p) ℂ) * A).trace.re` while keeping the subtype topology and
uniformity definitionally unchanged. It also fixes the `p²` real coordinates
`TauCeti.hermitianCoordinates` — diagonal real entries `(A i i).re` at `(i, i)`, strictly
upper-triangular real parts `(A i j).re` at `(i, j)` (`i < j`), and strictly upper-triangular
imaginary parts `(A i j).im` at `(j, i)` (`i < j`) — together with unitary conjugation
`Matrix.UnitaryGroup.hermitianConj` as a real linear isometry equivalence.

## Main declarations

* `TauCeti.hermitianMatrixNormedAddCommGroup`, `TauCeti.hermitianMatrixInnerProductSpace` —
  the real Frobenius structure on the complex Hermitian subspace.
* `selfAdjoint.coe_inner_complex` and `selfAdjoint.inner_eq_re_trace_mul` — the real Frobenius
  pairing on the Hermitian subspace is `Re tr (B A)`.
* `TauCeti.hermitianCoordinates` — the continuous linear equivalence with `Fin p × Fin p → ℝ`
  reading diagonal real parts and strictly upper-triangular real and imaginary parts.
* `TauCeti.hermitianCoordinatesMeasurableEquiv` — its measurable-equivalence form.
* `TauCeti.hermitianBasis` — the basis dual to `TauCeti.hermitianCoordinates`.
* `TauCeti.finrank_hermitianMatrix` — the real dimension is `p ^ 2`.
* `TauCeti.hermitianFinOneEquiv` — the identification of `1 × 1` Hermitian matrices with `ℝ`.
* `Matrix.UnitaryGroup.hermitianConj` — unitary conjugation `A ↦ U * A * Uᴴ` as a real linear
  isometry equivalence of the Hermitian subspace.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate InnerProductSpace Matrix RealInnerProductSpace

namespace TauCeti

/-! ### The real Frobenius structure on the complex Hermitian subspace -/

section instances

variable (p : ℕ)

/-- The complex Hermitian subspace carries the Frobenius norm induced from ambient complex
matrices, with its metric rebuilt on the subtype uniformity so that the uniform and topological
structures agree definitionally with the subtype ones. -/
instance hermitianMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
    Submodule.normedAddCommGroup _
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

/-- The complex Hermitian subspace carries the real Frobenius inner product
`⟪A, B⟫ = ∑ i, ∑ j, ⟪A i j, B i j⟫_ℝ = Re tr (B * A)` of the underlying complex matrices. -/
instance hermitianMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusInnerProductSpace
  { __ := (inferInstance : Module ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)))
    norm_smul_le r A := norm_smul_le r (A : Matrix (Fin p) (Fin p) ℂ)
    inner A B := ⟪(A : Matrix (Fin p) (Fin p) ℂ), (B : Matrix (Fin p) (Fin p) ℂ)⟫_ℝ
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℂ)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℂ) ↑B
    add_left A B C := by
      rw [Submodule.coe_add]
      exact InnerProductSpace.add_left (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℂ) ↑B ↑C
    smul_left A B r := by
      rw [Submodule.coe_smul]
      exact Matrix.frobenius_inner_smul_left r (A : Matrix (Fin p) (Fin p) ℂ) ↑B }

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

example :
    (hermitianMatrixNormedAddCommGroup p).toMetricSpace.toUniformSpace =
      (instUniformSpaceSubtype :
        UniformSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  with_reducible_and_instances rfl

example :
    (hermitianMatrixNormedAddCommGroup p).toMetricSpace.toUniformSpace.toTopologicalSpace =
      (instTopologicalSpaceSubtype :
        TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  with_reducible_and_instances rfl

example :
    (inferInstance : MeasureSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
      measureSpaceOfInnerProductSpace :=
  rfl

end instances

end TauCeti

/-! ### Hermitian entries and the real trace pairing -/

namespace selfAdjoint

open scoped Matrix.Norms.Frobenius in
/-- The real inner product on the complex Hermitian subspace is the ambient real Frobenius inner
product of the underlying matrices. -/
@[simp]
theorem coe_inner_complex {p : ℕ}
    (A B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ⟪A, B⟫ = ⟪(A : Matrix (Fin p) (Fin p) ℂ), (B : Matrix (Fin p) (Fin p) ℂ)⟫_ℝ :=
  (rfl)

/-- An element of the complex Hermitian subspace is fixed by conjugate transposition. -/
@[simp]
theorem conjTranspose_coe {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (A : Matrix (Fin p) (Fin p) ℂ)ᴴ = (A : Matrix (Fin p) (Fin p) ℂ) :=
  A.2.isHermitian.eq

/-- Conjugate-reflecting an entry of a Hermitian matrix swaps its indices. -/
theorem coe_apply_conj {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (i j : Fin p) :
    conj ((A : Matrix (Fin p) (Fin p) ℂ) i j) = (A : Matrix (Fin p) (Fin p) ℂ) j i := by
  simpa using A.2.isHermitian.apply j i

/-- Diagonal entries of a Hermitian matrix have vanishing imaginary part. -/
@[simp]
theorem im_coe_apply_self {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (i : Fin p) :
    ((A : Matrix (Fin p) (Fin p) ℂ) i i).im = 0 := by
  have h := congrArg Complex.im (coe_apply_conj A i i)
  simp only [Complex.conj_im, neg_eq_self] at h
  exact h

/-- On the complex Hermitian subspace, the real Frobenius inner product is `Re tr (Θ * A)`. -/
theorem inner_eq_re_trace_mul {p : ℕ}
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ⟪A, Θ⟫ = ((Θ : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ)).trace.re := by
  let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusInnerProductSpace
  rw [coe_inner_complex, Matrix.frobenius_inner_def]
  simp only [Complex.inner, coe_apply_conj A, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Complex.re_sum]

/-- The squared Frobenius norm of a Hermitian matrix is `Re tr (A * A)`. -/
theorem norm_sq_eq_re_trace_mul_self {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ‖A‖ ^ 2 = ((A : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ)).trace.re := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_re_trace_mul]

/-- The real trace pairing against a fixed Hermitian matrix is continuous. -/
theorem continuous_re_trace_mul_coe {p : ℕ}
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      ((Θ : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ)).trace.re := by
  simp only [← inner_eq_re_trace_mul]
  exact continuous_id.inner continuous_const

/-- Reading off an entry of a complex Hermitian matrix is continuous. -/
@[fun_prop]
theorem continuous_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j :=
  continuous_subtype_val.matrix_elem i j

/-- Reading off an entry of a complex Hermitian matrix is measurable. -/
@[fun_prop]
theorem measurable_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j :=
  (continuous_coe_apply_complex i j).measurable

end selfAdjoint

namespace TauCeti

/-! ### Real coordinates on the complex Hermitian subspace -/

section coordinates

variable (p : ℕ)

/-- The continuous `ℝ`-linear equivalence identifying a `p × p` complex Hermitian matrix with its
`p²` real coordinates indexed by `Fin p × Fin p`:
* `(A i i).re` at `(i, i)` on the diagonal,
* `(A i j).re` at `(i, j)` strictly above the diagonal (`i < j`),
* `(A i j).im` at `(j, i)` strictly below the diagonal (`i < j`).

This coordinate system fixes the normalization of `TauCeti.hermitianLebesgue` and aligns entry
by entry with `TauCeti.Probability.gaussianEnsemble 2 p`. -/
def hermitianCoordinates :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃L[ℝ] (Fin p × Fin p → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A ab :=
        if ab.1 ≤ ab.2 then ((A : Matrix (Fin p) (Fin p) ℂ) ab.1 ab.2).re
        else ((A : Matrix (Fin p) (Fin p) ℂ) ab.2 ab.1).im
      map_add' A B := by
        funext ab
        simp only [Submodule.coe_add, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> simp
      map_smul' c A := by
        funext ab
        simp only [Submodule.coe_smul, Matrix.smul_apply, Complex.real_smul, RingHom.id_apply,
          Pi.smul_apply, smul_eq_mul]
        split_ifs <;> simp
      invFun x :=
        ⟨Matrix.of fun i j ↦
            if i = j then (x (i, i) : ℂ)
            else if i < j then (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ)
            else (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ), by
          refine (Matrix.IsHermitian.ext fun i j ↦ ?_).isSelfAdjoint
          simp only [Matrix.of_apply]
          rcases lt_trichotomy i j with h | rfl | h
          · simp [h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]
          · simp
          · simp [h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]⟩
      left_inv A := by
        refine Subtype.ext (Matrix.ext fun i j ↦ ?_)
        simp only [Matrix.of_apply]
        rcases lt_trichotomy i j with h | rfl | h
        · simp only [h.ne, ↓reduceIte, h, h.le, not_le.2 h]
          exact Complex.ext (by simp) (by simp)
        · simp only [↓reduceIte, le_rfl]
          exact Complex.ext rfl (selfAdjoint.im_coe_apply_self A i).symm
        · simp only [h.ne', ↓reduceIte, h.not_gt, h.le, not_le.2 h]
          rw [← selfAdjoint.coe_apply_conj A j i]
          exact Complex.ext (by simp) (by simp)
      right_inv x := by
        funext ⟨i, j⟩
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.le, h.ne]
        · simp
        · simp [not_le.2 h, h, h.ne] }

theorem hermitianCoordinates_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (ab : Fin p × Fin p) :
    hermitianCoordinates p A ab =
      if ab.1 ≤ ab.2 then ((A : Matrix (Fin p) (Fin p) ℂ) ab.1 ab.2).re
      else ((A : Matrix (Fin p) (Fin p) ℂ) ab.2 ab.1).im :=
  (rfl)

@[simp]
theorem hermitianCoordinates_apply_of_le (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    {i j : Fin p} (h : i ≤ j) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) i j).re :=
  ite_eq_left h

theorem hermitianCoordinates_apply_self (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (i : Fin p) :
    hermitianCoordinates p A (i, i) = ((A : Matrix (Fin p) (Fin p) ℂ) i i).re :=
  ite_eq_left le_rfl

@[simp]
theorem hermitianCoordinates_apply_of_gt (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    {i j : Fin p} (h : j < i) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) j i).im :=
  ite_eq_right (not_le.2 h)

private theorem coe_hermitianCoordinates_symm_apply (x : Fin p × Fin p → ℝ) (k l : Fin p) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) k l =
      if k = l then (x (k, k) : ℂ)
      else if k < l then (x (k, l) : ℂ) + Complex.I * (x (l, k) : ℂ)
      else (x (l, k) : ℂ) - Complex.I * (x (k, l) : ℂ) :=
  rfl

@[simp]
theorem coe_hermitianCoordinates_symm_apply_self (x : Fin p × Fin p → ℝ) (i : Fin p) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i i = (x (i, i) : ℂ) := by
  simp [coe_hermitianCoordinates_symm_apply]

@[simp]
theorem coe_hermitianCoordinates_symm_apply_of_lt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : i < j) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ) := by
  simp [coe_hermitianCoordinates_symm_apply, h, h.ne]

@[simp]
theorem coe_hermitianCoordinates_symm_apply_of_gt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : j < i) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ) := by
  simp [coe_hermitianCoordinates_symm_apply, h.ne', h.not_gt]

/-- The measurable equivalence induced by `TauCeti.hermitianCoordinates`. -/
def hermitianCoordinatesMeasurableEquiv :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ᵐ (Fin p × Fin p → ℝ) :=
  (hermitianCoordinates p).toHomeomorph.toMeasurableEquiv

@[simp]
theorem hermitianCoordinatesMeasurableEquiv_coe :
    (hermitianCoordinatesMeasurableEquiv p : _ → Fin p × Fin p → ℝ) =
      hermitianCoordinates p :=
  (rfl)

@[simp]
theorem hermitianCoordinatesMeasurableEquiv_symm_coe :
    ((hermitianCoordinatesMeasurableEquiv p).symm : (Fin p × Fin p → ℝ) → _) =
      (hermitianCoordinates p).symm :=
  (rfl)

/-- The complex Hermitian subspace has real dimension `p ^ 2`. -/
theorem finrank_hermitianMatrix :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) = p ^ 2 := by
  rw [(hermitianCoordinates p).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin, sq]

/-- The real basis of the complex Hermitian subspace dual to `TauCeti.hermitianCoordinates`. -/
def hermitianBasis :
    Basis (Fin p × Fin p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (Pi.basisFun ℝ (Fin p × Fin p)).map (hermitianCoordinates p).symm.toLinearEquiv

theorem hermitianBasis_apply (ab : Fin p × Fin p) :
    hermitianBasis p ab = (hermitianCoordinates p).symm (Pi.single ab 1) := by
  simp [hermitianBasis]

@[simp]
theorem hermitianBasis_repr (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (ab : Fin p × Fin p) :
    (hermitianBasis p).repr A ab = hermitianCoordinates p A ab := by
  simp [hermitianBasis]

private theorem ofReal_single_one (a b c d : Fin p) :
    ((Pi.single (M := fun _ ↦ ℝ) (a, b) 1 (c, d) : ℝ) : ℂ) =
      if c = a ∧ d = b then 1 else 0 := by
  simp only [Pi.single_apply, Prod.mk.injEq]; split_ifs <;> simp

/-- On the diagonal `(i, i)`, the coordinate basis vector is `Eᵢᵢ`. -/
theorem coe_hermitianBasis_diag (i : Fin p) :
    ((hermitianBasis p (i, i) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i i 1 := by
  obtain ⟨i, hi⟩ := i
  ext ⟨k, hk⟩ ⟨l, hl⟩
  rw [hermitianBasis_apply, coe_hermitianCoordinates_symm_apply, Matrix.single_apply]
  simp only [ofReal_single_one, Fin.mk.injEq, Fin.mk_lt_mk]
  split_ifs <;> first | (simp; done) | omega

/-- Strictly above the diagonal (`i < j`), the coordinate basis vector at `(i, j)` is
`Eᵢⱼ + Eⱼᵢ`. -/
theorem coe_hermitianBasis_of_lt {i j : Fin p} (h : i < j) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j; rw [Fin.mk_lt_mk] at h
  ext ⟨k, hk⟩ ⟨l, hl⟩
  rw [hermitianBasis_apply, coe_hermitianCoordinates_symm_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.single_apply]
  simp only [ofReal_single_one, Fin.mk.injEq, Fin.mk_lt_mk]
  split_ifs <;> first | (simp; done) | omega

/-- Strictly below the diagonal (`j < i`), the coordinate basis vector at `(i, j)` is
`I • Eⱼᵢ - I • Eᵢⱼ`. -/
theorem coe_hermitianBasis_of_gt {i j : Fin p} (h : j < i) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) =
      Matrix.single j i Complex.I - Matrix.single i j Complex.I := by
  obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j; rw [Fin.mk_lt_mk] at h
  ext ⟨k, hk⟩ ⟨l, hl⟩
  rw [hermitianBasis_apply, coe_hermitianCoordinates_symm_apply, Matrix.sub_apply,
    Matrix.single_apply, Matrix.single_apply]
  simp only [ofReal_single_one, Fin.mk.injEq, Fin.mk_lt_mk]
  split_ifs <;> first | (simp; done) | omega

end coordinates

/-! ### The one-dimensional carrier -/

/-- A `1 × 1` complex Hermitian matrix is determined by the real part of its single entry. -/
def hermitianFinOneEquiv : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) ≃L[ℝ] ℝ :=
  letI : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  (hermitianCoordinates 1).trans (ContinuousLinearEquiv.funUnique (Fin 1 × Fin 1) ℝ ℝ)

@[simp]
theorem hermitianFinOneEquiv_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
    hermitianFinOneEquiv A = ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  rw [hermitianFinOneEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_funUnique, Function.eval,
    Subsingleton.elim (default : Fin 1 × Fin 1) (0, 0), hermitianCoordinates_apply_self]

@[simp]
theorem coe_hermitianFinOneEquiv_symm_apply (x : ℝ) (i j : Fin 1) :
    ((hermitianFinOneEquiv.symm x : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
        Matrix (Fin 1) (Fin 1) ℂ) i j = (x : ℂ) := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [hermitianFinOneEquiv, ContinuousLinearEquiv.coe_funUnique_symm]

end TauCeti

/-! ### Unitary conjugation on the complex Hermitian subspace -/

namespace Matrix.UnitaryGroup

variable {p : ℕ}

private def hermitianConjLinearMap (M : Matrix (Fin p) (Fin p) ℂ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) →ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) where
  toFun A := ⟨M * (A : Matrix (Fin p) (Fin p) ℂ) * Mᴴ,
    (Matrix.isHermitian_mul_mul_conjTranspose M A.2.isHermitian).isSelfAdjoint⟩
  map_add' _ _ := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' _ _ := Subtype.ext (by simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc])

private theorem hermitianConjLinearMap_mul (M N : Matrix (Fin p) (Fin p) ℂ) :
    hermitianConjLinearMap (M * N) =
      (hermitianConjLinearMap M).comp (hermitianConjLinearMap N) :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp [hermitianConjLinearMap, Matrix.mul_assoc])

private theorem hermitianConjLinearMap_one :
    hermitianConjLinearMap (1 : Matrix (Fin p) (Fin p) ℂ) = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp [hermitianConjLinearMap])

private def hermitianConjLinearEquiv (U : Matrix.unitaryGroup (Fin p) ℂ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) :=
  LinearEquiv.ofLinearMap
    (hermitianConjLinearMap U.1)
    (hermitianConjLinearMap (U⁻¹ : Matrix.unitaryGroup (Fin p) ℂ).1)
    (by rw [← hermitianConjLinearMap_mul, ← mul_val, mul_inv_cancel, one_val,
          hermitianConjLinearMap_one])
    (by rw [← hermitianConjLinearMap_mul, ← mul_val, inv_mul_cancel, one_val,
          hermitianConjLinearMap_one])

/-- Unitary conjugation `A ↦ U * A * Uᴴ` on the complex Hermitian subspace, as a real linear
isometry equivalence for the Frobenius norm. -/
def hermitianConj (U : Matrix.unitaryGroup (Fin p) ℂ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) where
  toLinearEquiv := hermitianConjLinearEquiv U
  norm_map' A := by
    let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℂ) := Matrix.frobeniusNormedAddCommGroup
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    change ‖(U : Matrix (Fin p) (Fin p) ℂ) * A.1 * (U : Matrix (Fin p) (Fin p) ℂ)ᴴ‖ ^ 2 =
      ‖(A : Matrix (Fin p) (Fin p) ℂ)‖ ^ 2
    simpa [star_eq_conjTranspose] using
      Matrix.frobenius_norm_sq_conj_unitary
        ((U⁻¹ : Matrix.unitaryGroup (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) A.1 (U⁻¹).2

@[simp]
theorem coe_hermitianConj_apply (U : Matrix.unitaryGroup (Fin p) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (hermitianConj U A : Matrix (Fin p) (Fin p) ℂ) =
      (U : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ) *
        (U : Matrix (Fin p) (Fin p) ℂ)ᴴ :=
  (rfl)

/-- Conjugation by the identity unitary matrix is the identity. -/
@[simp]
theorem hermitianConj_one :
    hermitianConj (1 : Matrix.unitaryGroup (Fin p) ℂ) =
      LinearIsometryEquiv.refl ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext (by simp)

/-- Conjugation by a product of unitary matrices composes the two conjugations in reverse
order. -/
@[simp]
theorem hermitianConj_mul (U₁ U₂ : Matrix.unitaryGroup (Fin p) ℂ) :
    hermitianConj (U₁ * U₂) = (hermitianConj U₂).trans (hermitianConj U₁) :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext (by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc])

/-- The inverse of unitary conjugation by `U` is unitary conjugation by `U⁻¹ = Uᴴ`. -/
@[simp]
theorem hermitianConj_symm (U : Matrix.unitaryGroup (Fin p) ℂ) :
    (hermitianConj U).symm = hermitianConj U⁻¹ := by
  refine LinearIsometryEquiv.ext fun A ↦ (hermitianConj U).symm_apply_eq.2 ?_
  rw [← LinearIsometryEquiv.trans_apply, ← hermitianConj_mul, mul_inv_cancel, hermitianConj_one]
  rfl

/-- Unitary conjugation preserves `Re tr (A * A)`. -/
theorem re_trace_mul_self_hermitianConj_apply (U : Matrix.unitaryGroup (Fin p) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (((hermitianConj U A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
        Matrix (Fin p) (Fin p) ℂ) *
      (hermitianConj U A : Matrix (Fin p) (Fin p) ℂ)).trace.re =
      ((A : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ)).trace.re := by
  simp only [← selfAdjoint.norm_sq_eq_re_trace_mul_self, LinearIsometryEquiv.norm_map]

end Matrix.UnitaryGroup
