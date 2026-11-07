/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.ThreeOne

/-!
# The Dirac representation of the Lorentzian Clifford algebra

This file builds the four-dimensional complex Dirac representation of the real Clifford algebra
of signature `(3,1)` in Weyl (chiral) coordinates, and compares its restriction to `Spin(3,1)`
with the action of `SL₂(ℂ)` on the two Weyl summands.

The native quadratic form `realCliffordForm 3 1` is time-last,
`Q v = v₀² + v₁² + v₂² - v₃²`, while physical coordinates are time-first with metric
`g = diag(+1,-1,-1,-1)`. The coordinate change `timeFirstToNative`,
`(x₀,x₁,x₂,x₃) ↦ (x₃,-x₂,x₁,x₀)`, satisfies `Q (P x) = -g x` and has determinant `-1`.

Write `X v` for the Hermitian matrix `realCliffordThreeOneVectorEquivHermitian v`; on time-first
coordinates it is `X (P x) = [[x₀+x₁, x₂-ix₃], [x₂+ix₃, x₀-x₁]]`. The physical Clifford
multiplication of a vector on `S_L ⊕ S_R = ℂ² ⊕ ℂ²` is the off-diagonal block matrix
`C v = [[0, X v], [adj (X v), 0]]`, which squares to `-Q v`. The dual-frame Dirac matrices are
`Γ⁰ = C (P e₀)` and `Γ^i = -C (P e_i)`, with `{Γ^μ, Γ^ν} = 2 η^{μν}`, and the chirality matrix
`Γ⁵ = i Γ⁰ Γ¹ Γ² Γ³` is `diag(1,-1)`. The Weyl action of
`A ∈ SL₂(ℂ)` is `diag(A, (adj A)ᴴ) = diag(A, (Aᴴ)⁻¹)`; it preserves the indefinite Hermitian
pairing `H₀ = [[0,1],[1,0]] = C (P e₀)` and intertwines `C` with the Hermitian-congruence vector
action. Finally `v ↦ -i C v` satisfies the Clifford relation of `Q`, so it lifts to a real
algebra homomorphism on `Cl(3,1)` whose restriction to `Spin(3,1)` is the Weyl action, through
the native equivalence `realSpinThreeOneEquivSpecialLinear`.

## Main definitions

* `TauCeti.timeFirstToNative`: time-first Minkowski coordinates to native coordinates.
* `TauCeti.diracVector`: physical Clifford multiplication `C` in Weyl coordinates.
* `TauCeti.diracGamma`, `TauCeti.diracChirality`: the dual-frame matrices `Γ^μ` and `Γ⁵`.
* `TauCeti.diracWeylAlgHom`: the real algebra map `A ↦ diag(A, (adj A)ᴴ)`.
* `TauCeti.diracWeyl`: the Weyl action of `Spin(3,1)`, as a monoid homomorphism.
* `TauCeti.diracClifford`: the real Clifford representation with `ι v ↦ -i C v`.

## Main results

* `TauCeti.realCliffordForm_timeFirstToNative`: `Q (P x) = -(x₀² - x₁² - x₂² - x₃²)`.
* `TauCeti.diracVector_mul_self`: `C v * C v = -Q v`; on time-first coordinates
  `TauCeti.diracVector_timeFirstToNative_mul_self` gives `C (P x) * C (P x) = g x`.
* `TauCeti.diracGamma_mul_add_mul_swap`: `{Γ^μ, Γ^ν} = 2 η^{μν}`.
* `TauCeti.diracChirality_eq_fromBlocks`: `Γ⁵ = diag(1,-1)`; it squares to one and anticommutes
  with every `Γ^μ`.
* `TauCeti.conjTranspose_diracWeyl_mul_mul_self`: the Weyl action preserves `H₀`.
* `TauCeti.diracVector_smul_mul_diracWeyl`: `C (s • v) ρ(s) = ρ(s) C v`.
* `TauCeti.diracClifford_even`: on the even subalgebra, `diracClifford` is `diracWeylAlgHom`
  composed with the native matrix model `Cl⁺(3,1) ≃ M₂(ℂ)`.
* `TauCeti.diracClifford_spinGroup`: `diracClifford s = diracWeyl s` for `s ∈ Spin(3,1)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory* (1995), §3.2.
-/

public section

open Matrix

namespace TauCeti

/-! ## Time-first coordinates -/

/-- The change from time-first Minkowski coordinates `(x₀,x₁,x₂,x₃)`, with metric
`diag(+1,-1,-1,-1)`, to the native time-last coordinates of `realCliffordForm 3 1`:
`(x₀,x₁,x₂,x₃) ↦ (x₃,-x₂,x₁,x₀)`. -/
noncomputable def timeFirstToNative : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
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

/-- The native coordinates of a time-first vector. -/
@[simp]
theorem timeFirstToNative_apply (x : Fin 4 → ℝ) :
    timeFirstToNative x = ![x 3, -x 2, x 1, x 0] := (rfl)

/-- The time-first coordinates of a native vector. -/
@[simp]
theorem timeFirstToNative_symm_apply (v : Fin 4 → ℝ) :
    timeFirstToNative.symm v = ![v 3, v 2, -v 1, v 0] := (rfl)

/-- The native quadratic form on time-first coordinates is minus the Minkowski form
`x₀² - x₁² - x₂² - x₃²`. -/
theorem realCliffordForm_timeFirstToNative (x : Fin 4 → ℝ) :
    realCliffordForm 3 1 (timeFirstToNative x) = -(x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2) := by
  simp only [realCliffordForm_three_one_apply, timeFirstToNative_apply]
  simp
  ring

/-- The time-first timelike basis vector is the native timelike basis vector. -/
theorem timeFirstToNative_single_zero :
    timeFirstToNative (Pi.single 0 1) = Pi.single 3 1 := by
  funext i
  fin_cases i <;> simp

/-- The first time-first spatial basis vector is the third native basis vector. -/
theorem timeFirstToNative_single_one :
    timeFirstToNative (Pi.single 1 1) = Pi.single 2 1 := by
  funext i
  fin_cases i <;> simp

/-- The second time-first spatial basis vector is minus the second native basis vector. -/
theorem timeFirstToNative_single_two :
    timeFirstToNative (Pi.single 2 1) = -Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp

/-- The third time-first spatial basis vector is the first native basis vector. -/
theorem timeFirstToNative_single_three :
    timeFirstToNative (Pi.single 3 1) = Pi.single 0 1 := by
  funext i
  fin_cases i <;> simp

/-- The coordinate change `timeFirstToNative` reverses orientation. -/
theorem det_timeFirstToNative :
    LinearMap.det (timeFirstToNative : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) = -1 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 4)), Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Pi.single_apply]
  norm_num [Fin.succAbove, Fin.lt_def]

/-! ## Physical Clifford multiplication -/

/-- Physical Clifford multiplication by a native vector `v` on the Weyl carrier `ℂ² ⊕ ℂ²`: the
off-diagonal block matrix whose upper block is the Hermitian matrix of `v` and whose lower block
is its adjugate. -/
noncomputable def diracVector :
    (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ where
  toFun v :=
    fromBlocks 0 (realCliffordThreeOneVectorEquivHermitian v).1
      (adjugate (realCliffordThreeOneVectorEquivHermitian v).1) 0
  map_add' v w := by
    simp only [map_add, Submodule.coe_add, ← adjugateFinTwoLinearMap_apply, fromBlocks_add,
      add_zero]
  map_smul' r v := by
    simp only [map_smul, Submodule.coe_smul, ← adjugateFinTwoLinearMap_apply,
      LinearMap.map_smul_of_tower, fromBlocks_smul, smul_zero, RingHom.id_apply]

/-- Physical Clifford multiplication in Weyl block form. -/
theorem diracVector_apply (v : Fin 4 → ℝ) :
    diracVector v =
      fromBlocks 0 (realCliffordThreeOneVectorEquivHermitian v).1
        (adjugate (realCliffordThreeOneVectorEquivHermitian v).1) 0 :=
  (rfl)

/-- Physical Clifford multiplication squares to minus the native quadratic form. -/
@[simp]
theorem diracVector_mul_self (v : Fin 4 → ℝ) :
    diracVector v * diracVector v = (-realCliffordForm 3 1 v) • 1 := by
  set X : Matrix (Fin 2) (Fin 2) ℂ := (realCliffordThreeOneVectorEquivHermitian v).1 with hX
  have hdet : X.det = ((-realCliffordForm 3 1 v : ℝ) : ℂ) := by
    rw [hX, realCliffordThreeOneVectorEquivHermitian_det, Complex.ofReal_neg]
  rw [diracVector_apply, ← hX, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, mul_adjugate, adjugate_mul,
    hdet, Complex.coe_smul, ← fromBlocks_one, fromBlocks_smul, smul_zero]

/-- Physical Clifford multiplication satisfies the polarized Clifford relation. -/
theorem diracVector_mul_add_mul_swap (v w : Fin 4 → ℝ) :
    diracVector v * diracVector w + diracVector w * diracVector v =
      (-QuadraticMap.polar (realCliffordForm 3 1) v w) • 1 := by
  rw [← QuadraticMap.polar_neg, ← FunLike.coe_neg, ← Algebra.algebraMap_eq_smul_one]
  exact CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq (Q := -realCliffordForm 3 1)
    diracVector (fun x => by
      rw [diracVector_mul_self, neg_apply, Algebra.algebraMap_eq_smul_one]) v w

/-- On time-first coordinates, physical Clifford multiplication squares to the Minkowski form
`x₀² - x₁² - x₂² - x₃²`. -/
theorem diracVector_timeFirstToNative_mul_self (x : Fin 4 → ℝ) :
    diracVector (timeFirstToNative x) * diracVector (timeFirstToNative x) =
      (x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2) • 1 := by
  rw [diracVector_mul_self, realCliffordForm_timeFirstToNative, neg_neg]

/-- The native timelike basis vector acts by the Weyl swap `H₀ = [[0,1],[1,0]]`. -/
theorem diracVector_single_three :
    diracVector (Pi.single 3 1) = fromBlocks 0 1 1 0 := by
  have hX : (realCliffordThreeOneVectorEquivHermitian (Pi.single 3 1) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [coe_realCliffordThreeOneVectorEquivHermitian_apply, one_fin_two]
    simp
  rw [diracVector_apply, hX, adjugate_one]

/-- The time-first timelike basis vector acts by the Weyl swap `H₀ = [[0,1],[1,0]]`. -/
theorem diracVector_timeFirstToNative_single_zero :
    diracVector (timeFirstToNative (Pi.single 0 1)) = fromBlocks 0 1 1 0 := by
  rw [timeFirstToNative_single_zero, diracVector_single_three]

/-! ## Dual-frame Dirac matrices and chirality -/

/-- The dual-frame Dirac matrices `Γ^μ = Σ_ν η^{μν} C (P e_ν)` for the time-first Minkowski
metric `η = diag(+1,-1,-1,-1)`: `Γ⁰ = C (P e₀)` and `Γ^i = -C (P e_i)`. These are the
coefficients of `∂_μ` in the Dirac operator. -/
noncomputable def diracGamma (μ : Fin 4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  (![1, -1, -1, -1] μ : ℝ) • diracVector (timeFirstToNative (Pi.single μ 1))

/-- The defining formula of the dual-frame Dirac matrices: `Γ^μ = η^{μμ} C (P e_μ)`. -/
theorem diracGamma_def (μ : Fin 4) :
    diracGamma μ = (![1, -1, -1, -1] μ : ℝ) • diracVector (timeFirstToNative (Pi.single μ 1)) :=
  (rfl)

/-- The dual-frame Dirac matrices satisfy `{Γ^μ, Γ^ν} = 2 η^{μν}`. -/
theorem diracGamma_mul_add_mul_swap (μ ν : Fin 4) :
    diracGamma μ * diracGamma ν + diracGamma ν * diracGamma μ =
      (2 * diagonal ![1, -1, -1, -1] μ ν : ℝ) • 1 := by
  rw [diracGamma, diracGamma, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm (![1, -1, -1, -1] ν : ℝ), ← smul_add, diracVector_mul_add_mul_swap, smul_smul]
  congr 1
  fin_cases μ <;> fin_cases ν <;>
    simp [QuadraticMap.polar, realCliffordForm_three_one_apply] <;> norm_num

/-- The chirality matrix `Γ⁵ = i Γ⁰ Γ¹ Γ² Γ³`. -/
noncomputable def diracChirality : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Complex.I • (diracGamma 0 * diracGamma 1 * diracGamma 2 * diracGamma 3)

/-- In Weyl coordinates the chirality matrix is `diag(1,-1)`. -/
theorem diracChirality_eq_fromBlocks : diracChirality = fromBlocks 1 0 0 (-1) := by
  simp only [diracChirality, diracGamma, timeFirstToNative_single_zero, diracVector_single_three]
  simp [diracVector_apply, fromBlocks_multiply, fromBlocks_smul, fromBlocks_neg, one_fin_two]

/-- The chirality matrix is an involution. -/
@[simp]
theorem diracChirality_mul_self : diracChirality * diracChirality = 1 := by
  rw [diracChirality_eq_fromBlocks, fromBlocks_multiply]
  simp

/-- The chirality matrix anticommutes with every dual-frame Dirac matrix. -/
theorem diracChirality_mul_diracGamma (μ : Fin 4) :
    diracChirality * diracGamma μ = -(diracGamma μ * diracChirality) := by
  rw [diracChirality_eq_fromBlocks, diracGamma, diracVector_apply, fromBlocks_smul,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
  simp only [smul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.neg_mul, Matrix.mul_neg, add_zero, zero_add, neg_zero, neg_neg]

/-! ## The Weyl action -/

/-- The real algebra homomorphism `A ↦ diag(A, (adj A)ᴴ)` from complex `2 × 2` matrices to the
Weyl carrier. On `SL₂(ℂ)` the lower block is `(Aᴴ)⁻¹`. -/
noncomputable def diracWeylAlgHom :
    Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ where
  toFun A := fromBlocks A 0 0 (starAdjugateFinTwoAlgHom A)
  map_one' := by rw [map_one, fromBlocks_one]
  map_mul' A B := by
    rw [map_mul, fromBlocks_multiply]
    simp
  map_zero' := by rw [map_zero, fromBlocks_zero]
  map_add' A B := by rw [map_add, fromBlocks_add, add_zero]
  commutes' r := by
    rw [AlgHom.commutes]
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero]

/-- The Weyl block map in coordinates. -/
@[simp]
theorem diracWeylAlgHom_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    diracWeylAlgHom A = fromBlocks A 0 0 (adjugate A)ᴴ := by
  rw [← star_eq_conjTranspose, ← starAdjugateFinTwoAlgHom_apply]
  rfl

/-- The Weyl action `s ↦ diag(A, (adj A)ᴴ)` of `Spin(3,1)`, where `A ∈ SL₂(ℂ)` is the image of `s`
under the native equivalence `realSpinThreeOneEquivSpecialLinear`. -/
noncomputable def diracWeyl :
    spinGroup (realCliffordForm 3 1) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  (diracWeylAlgHom.toMonoidHom.comp Matrix.SpecialLinearGroup.coeMonoidHom).comp
    realSpinThreeOneEquivSpecialLinear.toMonoidHom

/-- The Weyl action in block form. -/
theorem diracWeyl_apply (s : spinGroup (realCliffordForm 3 1)) :
    diracWeyl s =
      fromBlocks (realSpinThreeOneEquivSpecialLinear s).1 0 0
        (adjugate (realSpinThreeOneEquivSpecialLinear s).1)ᴴ :=
  diracWeylAlgHom_apply _

/-- The Weyl action preserves the indefinite Hermitian pairing `H₀ = [[0,1],[1,0]]`. -/
theorem conjTranspose_diracWeyl_mul_mul_self (s : spinGroup (realCliffordForm 3 1)) :
    (diracWeyl s)ᴴ * fromBlocks 0 1 1 0 * diracWeyl s = fromBlocks 0 1 1 0 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (realSpinThreeOneEquivSpecialLinear s).1 with hA
  have hadj : adjugate A * A = 1 :=
    (adjugate_mul_self_eq_one_iff_det_eq_one A).mpr (Matrix.SpecialLinearGroup.det_coe _)
  have hadj' : Aᴴ * (adjugate A)ᴴ = 1 := by
    rw [← conjTranspose_mul, hadj, conjTranspose_one]
  rw [diracWeyl_apply, ← hA, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, conjTranspose_conjTranspose, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, zero_add, add_zero, hadj, hadj']

/-- Physical Clifford multiplication is equivariant for the Spin vector action and the Weyl
action: `C (s • v) ρ(s) = ρ(s) C v`. -/
theorem diracVector_smul_mul_diracWeyl (s : spinGroup (realCliffordForm 3 1))
    (v : Fin 4 → ℝ) :
    diracVector (s • v) * diracWeyl s = diracWeyl s * diracVector v := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (realSpinThreeOneEquivSpecialLinear s).1 with hA
  set X : Matrix (Fin 2) (Fin 2) ℂ := (realCliffordThreeOneVectorEquivHermitian v).1 with hX
  have hadj : adjugate A * A = 1 :=
    (adjugate_mul_self_eq_one_iff_det_eq_one A).mpr (Matrix.SpecialLinearGroup.det_coe _)
  have hadj' : Aᴴ * (adjugate A)ᴴ = 1 := by
    rw [← conjTranspose_mul, hadj, conjTranspose_one]
  have haction : (realCliffordThreeOneVectorEquivHermitian (s • v) :
      Matrix (Fin 2) (Fin 2) ℂ) = A * X * Aᴴ :=
    realSpinThreeOneEquivSpecialLinear_action s v
  rw [diracVector_apply, diracVector_apply, diracWeyl_apply, ← hA, ← hX, haction,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  congr 1
  · rw [Matrix.mul_assoc, hadj', Matrix.mul_one]
  · rw [adjugate_mul_distrib, adjugate_mul_distrib, ← adjugate_conjTranspose, Matrix.mul_assoc,
      Matrix.mul_assoc, hadj, Matrix.mul_one]

/-! ## The real Clifford representation -/

private theorem neg_I_smul_diracVector_mul_self (v : Fin 4 → ℝ) :
    ((-Complex.I) • diracVector) v * ((-Complex.I) • diracVector) v =
      algebraMap ℝ _ (realCliffordForm 3 1 v) := by
  rw [LinearMap.smul_apply, smul_mul_smul_comm, diracVector_mul_self, neg_mul_neg,
    Complex.I_mul_I, neg_one_smul, neg_smul, neg_neg, Algebra.algebraMap_eq_smul_one]

/-- The real Dirac representation of `Cl(3,1)` on the Weyl carrier: the lift of the Clifford map
`v ↦ -i C v`. -/
noncomputable def diracClifford :
    CliffordAlgebra (realCliffordForm 3 1) →ₐ[ℝ] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  CliffordAlgebra.lift _ ⟨(-Complex.I) • diracVector, neg_I_smul_diracVector_mul_self⟩

/-- The Dirac representation sends a native vector `v` to `-i C v`. -/
@[simp]
theorem diracClifford_ι (v : Fin 4 → ℝ) :
    diracClifford (CliffordAlgebra.ι _ v) = (-Complex.I) • diracVector v := by
  rw [diracClifford, CliffordAlgebra.lift_ι_apply, LinearMap.smul_apply]

/-- The Dirac representation of a product of two native vectors in the Weyl block form. -/
private theorem diracClifford_ι_mul_ι (m n : Fin 4 → ℝ) :
    diracClifford (CliffordAlgebra.ι _ m * CliffordAlgebra.ι _ n) =
      diracWeylAlgHom (realCliffordThreeOneEvenEquivComplexMatrix
        ((CliffordAlgebra.even.ι (realCliffordForm 3 1)).bilin m n)) := by
  rw [map_mul, diracClifford_ι, diracClifford_ι, smul_mul_smul_comm,
    realCliffordThreeOneEvenEquivComplexMatrix_ι, diracWeylAlgHom_apply, diracVector_apply,
    diracVector_apply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, neg_mul_neg, Complex.I_mul_I,
    neg_one_smul, coe_realCliffordThreeOneVectorEquivHermitian_apply]
  rw [fromBlocks_neg, neg_zero]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [adjugate_fin_two, -adjugate_fin_two_eq_trace_smul_one_sub] <;> ring

/-- On the even subalgebra, the Dirac representation is the Weyl block map composed with the
native matrix model `Cl⁺(3,1) ≃ M₂(ℂ)`. -/
theorem diracClifford_even (x : CliffordAlgebra.even (realCliffordForm 3 1)) :
    diracClifford x = diracWeylAlgHom (realCliffordThreeOneEvenEquivComplexMatrix x) := by
  have h : diracClifford.comp (CliffordAlgebra.even (realCliffordForm 3 1)).val =
      diracWeylAlgHom.comp realCliffordThreeOneEvenEquivComplexMatrix.toAlgHom := by
    apply CliffordAlgebra.even.algHom_ext
    rw [CliffordAlgebra.EvenHom.ext_iff]
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply, Subalgebra.coe_val,
      CliffordAlgebra.coe_even_ι_bilin]
    exact diracClifford_ι_mul_ι m n
  exact DFunLike.congr_fun h x

/-- The Dirac representation restricts on `Spin(3,1)` to the Weyl action. -/
theorem diracClifford_spinGroup (s : spinGroup (realCliffordForm 3 1)) :
    diracClifford (s : CliffordAlgebra (realCliffordForm 3 1)) = diracWeyl s := by
  rw [← CliffordAlgebra.coe_spinGroupToEven_apply, diracClifford_even, diracWeyl_apply,
    coe_realSpinThreeOneEquivSpecialLinear_apply,
    CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, diracWeylAlgHom_apply]

end TauCeti

end
