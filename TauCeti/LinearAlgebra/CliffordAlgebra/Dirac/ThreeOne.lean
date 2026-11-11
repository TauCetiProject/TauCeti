/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.ThreeOne

/-!
# The Dirac representation of the Lorentzian Clifford algebra

This file builds the Weyl (chiral) Dirac representation of `Cl(3,1)` on `ℂ⁴ = ℂ² ⊕ ℂ²`, with
four-by-four complex matrices indexed by the two Weyl summands, from the native Hermitian-matrix
model of Lorentz four-space and the equivalence `Spin(3,1) ≃ SL₂(ℂ)`.

Native coordinates `v` are time-last, with `Q(v) = v₀² + v₁² + v₂² - v₃²`. Physical coordinates
`x` are time-first, with Minkowski form `g(x) = x₀² - x₁² - x₂² - x₃²`, the real Clifford form of
signature `(1,3)`. The fixed coordinate change `P x = (x₃, -x₂, x₁, x₀)` satisfies
`Q(P x) = -g(x)` and has determinant `-1`.

Writing `X(v)` for the Hermitian matrix of `v`, the vector Clifford map is
`C(v) = [[0, X(v)], [adj X(v), 0]]`, so `C(v)² = -Q(v)`. The real algebra homomorphism
`diracClifford` sends a vector `v` to `-i C(v)`. On the even subalgebra it is block diagonal,
`x ↦ diag(M x, (adj M x)ᴴ)` for the native matrix model `M` of `Cl⁺(3,1)`, and on Spin it is
the Weyl action `diag(A, (adj A)ᴴ) = diag(A, (Aᴴ)⁻¹)` of `A ∈ SL₂(ℂ)`. Consequently Clifford
multiplication is Spin-covariant and the Weyl action preserves the indefinite Hermitian pairing
`H₀ = [[0, 1], [1, 0]] = C(P e₀)`.

The dual-frame Dirac matrices `Γ^μ = η^{μμ} C(P e_μ)` satisfy `{Γ^μ, Γ^ν} = 2 η^{μν}`. The
chirality matrix `Γ⁵ = i Γ⁰ Γ¹ Γ² Γ³` is `diag(1, -1)`, and `Γ⁰ Γ¹ Γ² Γ³` is the image of the
ordered native volume element `ι b₀ ι b₁ ι b₂ ι b₃`.

## Main definitions and results

* `TauCeti.timeFirstToNative`: the coordinate change `P`, with
  `TauCeti.realCliffordForm_three_one_timeFirstToNative` and `TauCeti.det_timeFirstToNative`.
* `TauCeti.diracVector`: the vector Clifford map `C`, with `TauCeti.diracVector_mul_self`.
* `TauCeti.diracClifford`: the real Clifford representation, with `TauCeti.diracClifford_ι`,
  `TauCeti.diracClifford_even` and `TauCeti.diracClifford_spinGroup`.
* `TauCeti.diracWeyl`: the Weyl action of `Spin(3,1)`.
* `TauCeti.diracVector_smul_mul_diracWeyl`: Spin covariance of Clifford multiplication.
* `TauCeti.conjTranspose_diracWeyl_mul_mul`: invariance of the Hermitian pairing `H₀`.
* `TauCeti.diracGamma`, `TauCeti.diracGamma_mul_add_mul_swap`: the dual-frame Dirac matrices and
  their anticommutation relations.
* `TauCeti.diracChirality`, `TauCeti.diracChirality_eq`: the chirality matrix.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory* (1995), §3.2, for
  the Weyl representation; the conventions here are fixed by the coordinate change `P`.
-/

public section

open Matrix
open scoped Matrix

namespace TauCeti

/-! ## Time-first coordinates -/

/-- The linear change `P x = (x₃, -x₂, x₁, x₀)` from time-first physical coordinates to the
time-last native coordinates of `realCliffordForm 3 1`. -/
def timeFirstToNative : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := ![x 3, -x 2, x 1, x 0]
  invFun v := ![v 3, v 2, -v 1, v 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [add_comm]
  map_smul' r x := by
    funext i
    fin_cases i <;> simp
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv v := by
    funext i
    fin_cases i <;> simp

@[simp]
theorem timeFirstToNative_apply (x : Fin 4 → ℝ) :
    timeFirstToNative x = ![x 3, -x 2, x 1, x 0] := (rfl)

@[simp]
theorem timeFirstToNative_symm_apply (v : Fin 4 → ℝ) :
    timeFirstToNative.symm v = ![v 3, v 2, -v 1, v 0] := (rfl)

/-- The native form of `P x` is minus the time-first Minkowski form: `Q(P x) = -g(x)`. -/
theorem realCliffordForm_three_one_timeFirstToNative (x : Fin 4 → ℝ) :
    realCliffordForm 3 1 (timeFirstToNative x) = -realCliffordForm 1 3 x := by
  simp only [realCliffordForm_three_one_apply, realCliffordForm_one_three_apply,
    timeFirstToNative_apply, Matrix.cons_val, neg_sq]
  ring

/-- The polar form of the native form at `P x, P y` is minus the polar Minkowski form. -/
theorem polar_realCliffordForm_three_one_timeFirstToNative (x y : Fin 4 → ℝ) :
    QuadraticMap.polar (realCliffordForm 3 1) (timeFirstToNative x) (timeFirstToNative y) =
      -QuadraticMap.polar (realCliffordForm 1 3) x y := by
  simp only [QuadraticMap.polar, ← map_add, realCliffordForm_three_one_timeFirstToNative]
  ring

/-- The coordinate change `P` reverses orientation. -/
theorem det_timeFirstToNative :
    LinearMap.det (timeFirstToNative : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) = -1 := by
  have h : LinearMap.toMatrix' (timeFirstToNative : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) =
      !![0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply]
  rw [← LinearMap.det_toMatrix', h]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-! ## Vector Clifford multiplication -/

/-- Physical vector Clifford multiplication `C(v) = [[0, X(v)], [adj X(v), 0]]` in Weyl blocks,
where `X(v)` is the native Hermitian matrix of `v`. Its square is `-Q(v)`; at `v = P x` this is
the time-first Minkowski form `g(x)`. -/
noncomputable def diracVector :
    (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ where
  toFun v := fromBlocks 0 (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ)
    (adjugate (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ)) 0
  map_add' v w := by
    simp only [map_add, Submodule.coe_add, ← adjugateFinTwoLinearMap_apply, fromBlocks_add,
      add_zero]
  map_smul' r v := by
    simp only [map_smul, Submodule.coe_smul, ← adjugateFinTwoLinearMap_apply,
      LinearMap.map_smul_of_tower, fromBlocks_smul, smul_zero, RingHom.id_apply]

/-- The defining block formula of the vector Clifford map. -/
theorem diracVector_apply (v : Fin 4 → ℝ) :
    diracVector v =
      fromBlocks 0 (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ)
        (adjugate (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ)) 0 :=
  (rfl)

/-- The Clifford square of the vector Clifford map: `C(v)² = -Q(v)`. -/
@[simp]
theorem diracVector_mul_self (v : Fin 4 → ℝ) :
    diracVector v * diracVector v = (-(realCliffordForm 3 1 v : ℂ)) • 1 := by
  rw [diracVector_apply, fromBlocks_multiply, mul_adjugate, adjugate_mul,
    realCliffordThreeOneVectorEquivHermitian_det, ← fromBlocks_one, fromBlocks_smul]
  simp

/-- In time-first coordinates the Clifford square is the Minkowski form: `C(P x)² = g(x)`. -/
theorem diracVector_timeFirstToNative_mul_self (x : Fin 4 → ℝ) :
    diracVector (timeFirstToNative x) * diracVector (timeFirstToNative x) =
      (realCliffordForm 1 3 x : ℂ) • 1 := by
  rw [diracVector_mul_self, realCliffordForm_three_one_timeFirstToNative, Complex.ofReal_neg,
    neg_neg]

/-! ## The Clifford representation -/

/-- The real Clifford representation of `Cl(3,1)` on `ℂ⁴`, sending a vector `v` to `-i C(v)`.
Its restriction to `Spin(3,1)` is the Weyl action `diracWeyl`. -/
noncomputable def diracClifford :
    CliffordAlgebra (realCliffordForm 3 1) →ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  CliffordAlgebra.lift _ ⟨(-Complex.I) • diracVector, fun v => by
    rw [LinearMap.smul_apply, smul_mul_smul_comm, diracVector_mul_self, smul_smul,
      Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    congr 1
    simp⟩

/-- The Clifford representation sends a vector `v` to `-i C(v)`. -/
@[simp]
theorem diracClifford_ι (v : Fin 4 → ℝ) :
    diracClifford (CliffordAlgebra.ι _ v) = (-Complex.I) • diracVector v := by
  simp [diracClifford]

/-- The product of two vector Clifford matrices is block diagonal. -/
theorem diracVector_mul_diracVector (v w : Fin 4 → ℝ) :
    diracVector v * diracVector w =
      fromBlocks
        ((realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ) *
          adjugate (realCliffordThreeOneVectorEquivHermitian w : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
        (adjugate (realCliffordThreeOneVectorEquivHermitian v : Matrix (Fin 2) (Fin 2) ℂ) *
          (realCliffordThreeOneVectorEquivHermitian w : Matrix (Fin 2) (Fin 2) ℂ)) := by
  simp [diracVector_apply, fromBlocks_multiply]

/-- On a product of two generators, the Clifford representation is the block-diagonal matrix of
the native even matrix model and its conjugate-transposed adjugate. -/
theorem diracClifford_ι_mul_ι (m n : Fin 4 → ℝ) :
    diracClifford (CliffordAlgebra.ι _ m * CliffordAlgebra.ι _ n) =
      fromBlocks (realCliffordThreeOneEvenEquivComplexMatrix
          ((CliffordAlgebra.even.ι (realCliffordForm 3 1)).bilin m n)) 0 0
        (adjugate (realCliffordThreeOneEvenEquivComplexMatrix
          ((CliffordAlgebra.even.ι (realCliffordForm 3 1)).bilin m n)))ᴴ := by
  rw [map_mul, diracClifford_ι, diracClifford_ι, smul_mul_smul_comm, diracVector_mul_diracVector,
    realCliffordThreeOneEvenEquivComplexMatrix_ι_eq_neg_mul_adjugate]
  set X := (realCliffordThreeOneVectorEquivHermitian m : Matrix (Fin 2) (Fin 2) ℂ)
  set Y := (realCliffordThreeOneVectorEquivHermitian n : Matrix (Fin 2) (Fin 2) ℂ)
  have hX : Xᴴ = X :=
    (isHermitian_iff_isSelfAdjoint.mpr (realCliffordThreeOneVectorEquivHermitian m).2).eq
  have hY : Yᴴ = Y :=
    (isHermitian_iff_isSelfAdjoint.mpr (realCliffordThreeOneVectorEquivHermitian n).2).eq
  have hneg : adjugate (-(X * adjugate Y)) = -(Y * adjugate X) := by
    rw [← adjugateFinTwoLinearMap_apply, map_neg, adjugateFinTwoLinearMap_apply,
      adjugate_mul_distrib, adjugate_adjugate _ (by norm_num)]
    simp
  simp only [hneg, neg_mul_neg, Complex.I_mul_I, neg_one_smul, fromBlocks_neg, neg_zero,
    conjTranspose_neg, conjTranspose_mul, adjugate_conjTranspose, hX, hY]

/-- On the even subalgebra, the Clifford representation is block diagonal:
`x ↦ diag(M x, (adj M x)ᴴ)` for the native complex matrix model `M` of `Cl⁺(3,1)`. -/
theorem diracClifford_even (x : CliffordAlgebra.even (realCliffordForm 3 1)) :
    diracClifford (x : CliffordAlgebra (realCliffordForm 3 1)) =
      fromBlocks (realCliffordThreeOneEvenEquivComplexMatrix x) 0 0
        (adjugate (realCliffordThreeOneEvenEquivComplexMatrix x))ᴴ := by
  obtain ⟨x, hx⟩ := x
  induction x, hx using CliffordAlgebra.even_induction with
  -- In each case, name the even element through the subalgebra operations, which are computed
  -- in the ambient Clifford algebra.
  | algebraMap r =>
    have h : (⟨algebraMap ℝ _ r, SetLike.algebraMap_mem_graded _ _⟩ :
        CliffordAlgebra.even (realCliffordForm 3 1)) = algebraMap ℝ _ r := rfl
    rw [h, Subalgebra.coe_algebraMap, AlgHom.commutes, AlgEquiv.commutes]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one] <;> ring
  | add x y hx hy ihx ihy =>
    have h : (⟨x + y, Submodule.add_mem _ hx hy⟩ : CliffordAlgebra.even (realCliffordForm 3 1)) =
        ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [h, Subalgebra.coe_add, map_add, ihx, ihy, map_add]
    simp only [← adjugateFinTwoLinearMap_apply, map_add, conjTranspose_add, fromBlocks_add,
      add_zero]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h : (⟨_, zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded
          (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ m₁ m₂) hx⟩ :
          CliffordAlgebra.even (realCliffordForm 3 1)) =
        (CliffordAlgebra.even.ι _).bilin m₁ m₂ * ⟨x, hx⟩ := rfl
    rw [h, Subalgebra.coe_mul, map_mul, ih, CliffordAlgebra.coe_even_ι_bilin, diracClifford_ι_mul_ι,
      fromBlocks_multiply, map_mul, adjugate_mul_distrib, conjTranspose_mul]
    simp

/-! ## The Weyl action of Spin -/

/-- The Weyl action of `Spin(3,1)` on `ℂ⁴`: the element corresponding to `A ∈ SL₂(ℂ)` acts by
`diag(A, (adj A)ᴴ)`, which is `diag(A, (Aᴴ)⁻¹)` since `det A = 1`. -/
noncomputable def diracWeyl :
    spinGroup (realCliffordForm 3 1) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ where
  toFun s := fromBlocks (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    (adjugate (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
  map_one' := by simp
  map_mul' s t := by
    simp [fromBlocks_multiply, adjugate_mul_distrib, conjTranspose_mul]

/-- The defining block formula of the Weyl action. -/
theorem diracWeyl_apply (s : spinGroup (realCliffordForm 3 1)) :
    diracWeyl s =
      fromBlocks (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        (adjugate (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ))ᴴ :=
  (rfl)

/-- The Clifford representation restricts on `Spin(3,1)` to the Weyl action. -/
@[simp]
theorem diracClifford_spinGroup (s : spinGroup (realCliffordForm 3 1)) :
    diracClifford (s : CliffordAlgebra (realCliffordForm 3 1)) = diracWeyl s := by
  rw [diracWeyl_apply, coe_realSpinThreeOneEquivSpecialLinear_apply,
    CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, ← diracClifford_even,
    CliffordAlgebra.coe_spinGroupToEven_apply]

/-- Clifford multiplication is Spin-covariant: `C(s • v) ρ_W(s) = ρ_W(s) C(v)`. -/
theorem diracVector_smul_mul_diracWeyl (s : spinGroup (realCliffordForm 3 1)) (v : Fin 4 → ℝ) :
    diracVector (s • v) * diracWeyl s = diracWeyl s * diracVector v := by
  have h := congrArg diracClifford (CliffordAlgebra.ι_spinVectorAction_apply_mul _ s v)
  rw [map_mul, map_mul, diracClifford_ι, diracClifford_ι, diracClifford_spinGroup,
    ← CliffordAlgebra.spinGroup_smul_apply, smul_mul_assoc, mul_smul_comm] at h
  exact smul_right_injective _ (neg_ne_zero.mpr Complex.I_ne_zero) h

/-- The vector Clifford matrix of the physical time direction is the Hermitian pairing
`H₀ = [[0, 1], [1, 0]]`. -/
theorem diracVector_timeFirstToNative_single_zero :
    diracVector (timeFirstToNative (Pi.single 0 1)) = fromBlocks 0 1 1 0 := by
  have h : (realCliffordThreeOneVectorEquivHermitian (timeFirstToNative (Pi.single 0 1)) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [coe_realCliffordThreeOneVectorEquivHermitian_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [diracVector_apply, h, adjugate_one]

/-- The Weyl action preserves the indefinite Hermitian pairing `H₀ = [[0, 1], [1, 0]]`:
`ρ_W(s)ᴴ H₀ ρ_W(s) = H₀`. -/
theorem conjTranspose_diracWeyl_mul_mul (s : spinGroup (realCliffordForm 3 1)) :
    (diracWeyl s)ᴴ * fromBlocks 0 1 1 0 * diracWeyl s = fromBlocks 0 1 1 0 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe (realSpinThreeOneEquivSpecialLinear s)
  rw [diracWeyl_apply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_conjTranspose, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.mul_one, zero_add, add_zero]
  rw [← conjTranspose_mul, adjugate_mul, hdet, one_smul, conjTranspose_one]

/-! ## Polarization, dual-frame Dirac matrices and chirality -/

/-- The polarized Clifford relation: `C(v) C(w) + C(w) C(v)` is minus the polar form of `Q`. -/
theorem diracVector_mul_add_mul_swap (v w : Fin 4 → ℝ) :
    diracVector v * diracVector w + diracVector w * diracVector v =
      (-((QuadraticMap.polar (realCliffordForm 3 1) v w : ℝ) : ℂ)) • 1 := by
  have h := congrArg diracClifford
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := realCliffordForm 3 1) v w)
  simp only [map_add, map_mul, diracClifford_ι, smul_mul_smul_comm, neg_mul_neg, Complex.I_mul_I,
    neg_one_smul, AlgHom.commutes] at h
  rw [neg_smul, Complex.coe_smul, ← Algebra.algebraMap_eq_smul_one, ← h]
  abel

/-- In time-first coordinates, `C(P x) C(P y) + C(P y) C(P x)` is the polar Minkowski form,
that is, `2 g(x, y)`. -/
theorem diracVector_timeFirstToNative_mul_add_mul_swap (x y : Fin 4 → ℝ) :
    diracVector (timeFirstToNative x) * diracVector (timeFirstToNative y) +
        diracVector (timeFirstToNative y) * diracVector (timeFirstToNative x) =
      ((QuadraticMap.polar (realCliffordForm 1 3) x y : ℝ) : ℂ) • 1 := by
  rw [diracVector_mul_add_mul_swap, polar_realCliffordForm_three_one_timeFirstToNative]
  simp

/-- The dual-frame Dirac matrices `Γ^μ = Σ_ν η^{μν} C(P e_ν)`, that is, `Γ⁰ = C(P e₀)` and
`Γⁱ = -C(P eᵢ)`. These are the coefficients of `∂_μ` in the Dirac operator. -/
noncomputable def diracGamma (μ : Fin 4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  realCliffordWeight 1 3 μ • diracVector (timeFirstToNative (Pi.single μ 1))

/-- `Γ⁰` is the Hermitian pairing `H₀`. -/
theorem diracGamma_zero : diracGamma 0 = fromBlocks 0 1 1 0 := by
  rw [diracGamma, realCliffordWeight_of_lt (by decide), one_smul,
    diracVector_timeFirstToNative_single_zero]

/-- `Γ¹ = [[0, -σ₃], [σ₃, 0]]`. -/
theorem diracGamma_one :
    diracGamma 1 = fromBlocks 0 !![-1, 0; 0, 1] !![1, 0; 0, -1] 0 := by
  rw [diracGamma, realCliffordWeight_of_le (by decide), diracVector_apply,
    coe_realCliffordThreeOneVectorEquivHermitian_apply, adjugate_fin_two]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

/-- `Γ² = [[0, -σ₁], [σ₁, 0]]`. -/
theorem diracGamma_two :
    diracGamma 2 = fromBlocks 0 !![0, -1; -1, 0] !![0, 1; 1, 0] 0 := by
  rw [diracGamma, realCliffordWeight_of_le (by decide), diracVector_apply,
    coe_realCliffordThreeOneVectorEquivHermitian_apply, adjugate_fin_two]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

/-- `Γ³ = [[0, -σ₂], [σ₂, 0]]`. -/
theorem diracGamma_three :
    diracGamma 3 =
      fromBlocks 0 !![0, Complex.I; -Complex.I, 0] !![0, -Complex.I; Complex.I, 0] 0 := by
  rw [diracGamma, realCliffordWeight_of_le (by decide), diracVector_apply,
    coe_realCliffordThreeOneVectorEquivHermitian_apply, adjugate_fin_two]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

/-- The Dirac anticommutation relations `{Γ^μ, Γ^ν} = 2 η^{μν}` for `η = diag(1, -1, -1, -1)`. -/
theorem diracGamma_mul_add_mul_swap (μ ν : Fin 4) :
    diracGamma μ * diracGamma ν + diracGamma ν * diracGamma μ =
      (if μ = ν then 2 * (realCliffordWeight 1 3 μ : ℂ) else 0) • 1 := by
  rw [diracGamma, diracGamma, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm (realCliffordWeight 1 3 ν), ← smul_add,
    diracVector_timeFirstToNative_mul_add_mul_swap, ← Complex.coe_smul, smul_smul]
  split_ifs with h
  · subst h
    rw [QuadraticMap.polar_self, realCliffordForm_apply_single, realCliffordWeight_mul_self]
    simp
  · rw [(isOrtho_realCliffordForm_single h 1 1).polar_eq_zero]
    simp

/-- The chirality matrix `Γ⁵ = i Γ⁰ Γ¹ Γ² Γ³`. -/
noncomputable def diracChirality : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Complex.I • (diracGamma 0 * diracGamma 1 * diracGamma 2 * diracGamma 3)

/-- In the Weyl blocks, the chirality matrix is `diag(1, -1)`. -/
theorem diracChirality_eq : diracChirality = fromBlocks 1 0 0 (-1) := by
  rw [diracChirality, diracGamma_zero, diracGamma_one, diracGamma_two, diracGamma_three]
  simp only [fromBlocks_multiply, fromBlocks_smul]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

/-- The chirality matrix is an involution. -/
@[simp]
theorem diracChirality_mul_self : diracChirality * diracChirality = 1 := by
  rw [diracChirality_eq, fromBlocks_multiply, ← fromBlocks_one]
  simp

/-- The chirality matrix anticommutes with every vector Clifford matrix. -/
theorem diracChirality_mul_diracVector (v : Fin 4 → ℝ) :
    diracChirality * diracVector v = -(diracVector v * diracChirality) := by
  rw [diracChirality_eq, diracVector_apply, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_neg]
  simp [-coe_realCliffordThreeOneVectorEquivHermitian_apply]

/-- The chirality matrix anticommutes with every Dirac matrix. -/
theorem diracChirality_mul_diracGamma (μ : Fin 4) :
    diracChirality * diracGamma μ = -(diracGamma μ * diracChirality) := by
  rw [diracGamma, mul_smul_comm, diracChirality_mul_diracVector, smul_mul_assoc, smul_neg]

/-- The ordered native volume element `ι b₀ ι b₁ ι b₂ ι b₃` acts by `Γ⁰ Γ¹ Γ² Γ³`, so that
`Γ⁵` is `i` times its image. -/
theorem diracClifford_ι_mul_ι_mul_ι_mul_ι :
    diracClifford (CliffordAlgebra.ι _ (Pi.single 0 1) * CliffordAlgebra.ι _ (Pi.single 1 1) *
        CliffordAlgebra.ι _ (Pi.single 2 1) * CliffordAlgebra.ι _ (Pi.single 3 1)) =
      diracGamma 0 * diracGamma 1 * diracGamma 2 * diracGamma 3 := by
  rw [diracGamma_zero, diracGamma_one, diracGamma_two, diracGamma_three]
  simp only [map_mul, diracClifford_ι, smul_mul_smul_comm, diracVector_apply,
    coe_realCliffordThreeOneVectorEquivHermitian_apply, adjugate_fin_two, fromBlocks_multiply,
    fromBlocks_smul]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

end TauCeti
