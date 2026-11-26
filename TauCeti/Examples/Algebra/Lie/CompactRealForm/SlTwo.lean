/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CompactRealForm.CartanInvolution
public import TauCeti.Algebra.Lie.RestrictScalars
public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.Matrix.NegConjTranspose
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
public import TauCeti.Examples.Algebra.Lie.CartanInvolution.Complex
import Mathlib.Analysis.Complex.Basic
import TauCeti.Algebra.Lie.Sl2.Killing
import TauCeti.LinearAlgebra.Matrix.Trace.Positive

/-!
# The compact real form of `𝔰𝔩₂(ℂ)` and the Cartan involution of `𝔰𝔩₂(ℝ)`

Worked examples for compact conjugations (`TauCeti.IsCompactConjugation`) and the Cartan
involution of a real form built from a commuting compact conjugation
(`TauCeti.IsCompactConjugation.isCartanInvolution_restrictRealForm`).

* The conjugation `τ X = -X*` of `𝔰𝔩₂(ℂ)` is compact: with `e`, `f`, `h` the standard basis,
  `τ h = -h`, `τ e = -f`, `τ f = -e`, and `H_τ(X, X) = -B(X, τ X) = 4 tr(X X*) > 0` for `X ≠ 0`;
  in particular `H_τ(e, e) = B(e, f) = 4` and `H_τ(h, h) = B(h, h) = 8`. Its real form is `𝔰𝔲(2)`,
  the skew-Hermitian trace-zero matrices, containing `i h`, `e - f` and `i (e + f)`.
* The entrywise conjugation `σ` of `𝔰𝔩₂(ℂ)` is a conjugation commuting with `τ`, with real form the
  real trace-zero matrices, identified with `𝔰𝔩₂(ℝ)`. The Cartan involution `θ = στ` on `Fix σ` is
  `X ↦ -Xᵀ`, matching `X ↦ -Xᵀ` on `𝔰𝔩₂(ℝ)` under this identification, so `𝔨 = 𝔰𝔬(2)` and `𝔭` is
  the symmetric trace-zero matrices.
* Non-example: the complex-linear Chevalley involution `ω X = -Xᵀ` (`h ↦ -h`, `e ↦ -f`, `f ↦ -e`)
  is a Lie automorphism, but its fixed set is a complex subalgebra, containing `e - f` and
  `i (e - f)`, and `-B(x, ω x)` takes the values `8` at `h` and `-8` at `i h`.
-/

public section

open LieAlgebra LieAlgebra.SpecialLinear Matrix Complex
open scoped ComplexOrder

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The compact conjugation `X ↦ -X*` of `𝔰𝔩₂(ℂ)`: `slFinTwoNegConjTranspose` as a
conjugate-linear map. -/
noncomputable def slFinTwoCompactConj : sl (Fin 2) ℂ →ₛₗ[starRingEnd ℂ] sl (Fin 2) ℂ where
  toFun := slFinTwoNegConjTranspose
  map_add' := map_add _
  map_smul' := slFinTwoNegConjTranspose_smul

/-- `slFinTwoCompactConj` sends `X` to `-X*`. -/
@[simp]
theorem coe_slFinTwoCompactConj_apply (X : sl (Fin 2) ℂ) :
    (slFinTwoCompactConj X : Matrix (Fin 2) (Fin 2) ℂ) = -(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
  coe_slFinTwoNegConjTranspose_apply X

/-- The entrywise conjugation of `𝔰𝔩₂(ℂ)`, `X ↦ X*ᵀ`, a conjugate-linear map. -/
noncomputable def slFinTwoEntrywiseConj : sl (Fin 2) ℂ →ₛₗ[starRingEnd ℂ] sl (Fin 2) ℂ where
  toFun X := ⟨(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴᵀ, transpose_mem_sl (conjTranspose_mem_sl X.property)⟩
  map_add' X Y := Subtype.ext (by simp)
  map_smul' c X := Subtype.ext (by simp [conjTranspose_smul])

/-- `slFinTwoEntrywiseConj` sends `X` to `X*ᵀ`, the entrywise conjugate. -/
@[simp]
theorem coe_slFinTwoEntrywiseConj_apply (X : sl (Fin 2) ℂ) :
    (slFinTwoEntrywiseConj X : Matrix (Fin 2) (Fin 2) ℂ) = (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴᵀ :=
  (rfl)

/-- The entries of `slFinTwoEntrywiseConj X` are the conjugates of the entries of `X`. -/
theorem slFinTwoEntrywiseConj_apply_apply (X : sl (Fin 2) ℂ) (i j : Fin 2) :
    (slFinTwoEntrywiseConj X : Matrix (Fin 2) (Fin 2) ℂ) i j =
      starRingEnd ℂ ((X : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (rfl)

/-- `X ↦ -X*` is a conjugation of `𝔰𝔩₂(ℂ)`. -/
theorem isLieConjugation_slFinTwoCompactConj : IsLieConjugation slFinTwoCompactConj where
  map_lie := slFinTwoNegConjTranspose.map_lie
  involutive X := Subtype.ext (by simp)

/-- The entrywise conjugation is a conjugation of `𝔰𝔩₂(ℂ)`. -/
theorem isLieConjugation_slFinTwoEntrywiseConj : IsLieConjugation slFinTwoEntrywiseConj where
  map_lie X Y := Subtype.ext (by simp [Ring.lie_def, conjTranspose_mul, transpose_mul])
  involutive X := Subtype.ext (by ext i j; simp)

/-- The Hermitian Killing form of `X ↦ -X*` is `H_τ(X, X) = 4 tr(X X*)`. -/
theorem killingHermitianForm_slFinTwoCompactConj_apply_self (X : sl (Fin 2) ℂ) :
    slFinTwoCompactConj.killingHermitianForm X X =
      4 * ((X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace := by
  rw [LinearMap.killingHermitianForm_def, killingForm_slFinTwo_apply,
    coe_slFinTwoCompactConj_apply]
  simp

/-- **`X ↦ -X*` is a compact conjugation of `𝔰𝔩₂(ℂ)`**:
`H_τ(X, X) = -B(X, -X*) = 4 tr(X X*) > 0` for `X ≠ 0`. -/
theorem isCompactConjugation_slFinTwoCompactConj : IsCompactConjugation slFinTwoCompactConj where
  toIsLieConjugation := isLieConjugation_slFinTwoCompactConj
  pos X hX := by
    rw [killingHermitianForm_slFinTwoCompactConj_apply_self]
    exact mul_pos (by norm_num) (trace_mul_conjTranspose_self_pos fun h ↦ hX (Subtype.ext h))

/-- `τ h = -h`. -/
theorem slFinTwoCompactConj_slFinTwoBasis_two :
    slFinTwoCompactConj (slFinTwoBasis ℂ 2) = -slFinTwoBasis ℂ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_two]

/-- `τ e = -f`. -/
theorem slFinTwoCompactConj_slFinTwoBasis_zero :
    slFinTwoCompactConj (slFinTwoBasis ℂ 0) = -slFinTwoBasis ℂ 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_zero, slFinTwoBasis_one]

/-- `τ f = -e`. -/
theorem slFinTwoCompactConj_slFinTwoBasis_one :
    slFinTwoCompactConj (slFinTwoBasis ℂ 1) = -slFinTwoBasis ℂ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_zero, slFinTwoBasis_one]

/-- `H_τ(e, e) = -B(e, τ e) = B(e, f) = 4`. -/
example : slFinTwoCompactConj.killingHermitianForm (slFinTwoBasis ℂ 0) (slFinTwoBasis ℂ 0) = 4 := by
  rw [LinearMap.killingHermitianForm_def, slFinTwoCompactConj_slFinTwoBasis_zero, map_neg, neg_neg,
    killingForm_slFinTwoBasis]
  simp

/-- `H_τ(h, h) = -B(h, τ h) = B(h, h) = 8`. -/
example : slFinTwoCompactConj.killingHermitianForm (slFinTwoBasis ℂ 2) (slFinTwoBasis ℂ 2) = 8 := by
  rw [LinearMap.killingHermitianForm_def, slFinTwoCompactConj_slFinTwoBasis_two, map_neg, neg_neg,
    killingForm_slFinTwoBasis]
  simp

/-- **The compact real form is `𝔰𝔲(2)`**: the skew-Hermitian trace-zero matrices. -/
theorem mem_realForm_slFinTwoCompactConj_iff {X : sl (Fin 2) ℂ} :
    X ∈ isLieConjugation_slFinTwoCompactConj.realForm ↔
      (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = -(X : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [IsLieConjugation.mem_realForm, ← mem_fixedSubalgebra_slFinTwoNegConjTranspose_iff,
    LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom]
  -- `τ` is `slFinTwoNegConjTranspose` as a conjugate-linear map, so the two sides agree.
  exact Iff.rfl

/-- `i h`, `e - f` and `i (e + f)` lie in the compact real form `𝔰𝔲(2)`. -/
example :
    I • slFinTwoBasis ℂ 2 ∈ isLieConjugation_slFinTwoCompactConj.realForm ∧
      slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ∈ isLieConjugation_slFinTwoCompactConj.realForm ∧
      I • (slFinTwoBasis ℂ 0 + slFinTwoBasis ℂ 1) ∈
        isLieConjugation_slFinTwoCompactConj.realForm := by
  simp only [IsLieConjugation.mem_realForm, map_smulₛₗ, map_sub, map_add,
    slFinTwoCompactConj_slFinTwoBasis_two, slFinTwoCompactConj_slFinTwoBasis_zero,
    slFinTwoCompactConj_slFinTwoBasis_one, conj_I]
  refine ⟨?_, ?_, ?_⟩ <;> module

/-- The entrywise conjugation commutes with `X ↦ -X*`. -/
theorem slFinTwoEntrywiseConj_slFinTwoCompactConj_comm (X : sl (Fin 2) ℂ) :
    slFinTwoEntrywiseConj (slFinTwoCompactConj X) =
      slFinTwoCompactConj (slFinTwoEntrywiseConj X) :=
  Subtype.ext (by ext i j; simp)

/-- **The real form of the entrywise conjugation** is the real trace-zero matrices. -/
theorem mem_realForm_slFinTwoEntrywiseConj_iff {X : sl (Fin 2) ℂ} :
    X ∈ isLieConjugation_slFinTwoEntrywiseConj.realForm ↔
      ∀ i j, starRingEnd ℂ ((X : Matrix (Fin 2) (Fin 2) ℂ) i j) =
        (X : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  rw [IsLieConjugation.mem_realForm, ← Subtype.coe_inj]
  exact ⟨fun h i j ↦ congrFun (congrFun h i) j, fun h ↦ funext₂ h⟩

/-- The Cartan involution `θ = στ` of the real form `Fix σ` of `𝔰𝔩₂(ℂ)`. -/
local notation "θ" =>
  isLieConjugation_slFinTwoEntrywiseConj.restrictRealForm isLieConjugation_slFinTwoCompactConj
    slFinTwoEntrywiseConj_slFinTwoCompactConj_comm

/-- **`θ = στ` is a Cartan involution of `Fix σ`.** -/
example : (θ).IsCartanInvolution :=
  isCompactConjugation_slFinTwoCompactConj.isCartanInvolution_restrictRealForm
    isLieConjugation_slFinTwoEntrywiseConj slFinTwoEntrywiseConj_slFinTwoCompactConj_comm

/-- **On `Fix σ` the Cartan involution `θ = στ` is `X ↦ -Xᵀ`.** -/
theorem coe_restrictRealForm_slFinTwo_apply
    (X : isLieConjugation_slFinTwoEntrywiseConj.realForm) :
    ((θ X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      -((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
  rw [IsLieConjugation.coe_restrictRealForm_apply_eq_apply_apply]
  simp

/-- **`𝔨 = 𝔰𝔬(2)`**: the fixed subalgebra of `θ` on `Fix σ` is the skew-symmetric matrices. -/
theorem mem_fixedSubalgebra_restrictRealForm_slFinTwo_iff
    {X : isLieConjugation_slFinTwoEntrywiseConj.realForm} :
    X ∈ (θ).toLieHom.fixedSubalgebra ↔
      ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ =
        -((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, ← Subtype.coe_inj, ← Subtype.coe_inj,
    coe_restrictRealForm_slFinTwo_apply, neg_eq_iff_eq_neg]

/-- **`𝔭` is the symmetric trace-zero matrices**: the `-1`-eigenspace of `θ` on `Fix σ`. -/
theorem mem_cartanP_restrictRealForm_slFinTwo_iff
    {X : isLieConjugation_slFinTwoEntrywiseConj.realForm} :
    X ∈ (θ).cartanP ↔
      ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ =
        ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [LieEquiv.mem_cartanP, ← Subtype.coe_inj, ← Subtype.coe_inj,
    coe_restrictRealForm_slFinTwo_apply, NegMemClass.coe_neg, NegMemClass.coe_neg, neg_inj]

/-- **`B_θ(X, X) = -B(X, θ X) = 4 tr(X Xᵀ)`** for the twisted Killing form of `θ` on `Fix σ`,
whose Killing form is the restriction of the Killing form of `𝔰𝔩₂(ℂ)`. -/
theorem twistedKillingForm_restrictRealForm_slFinTwo_apply_self
    (X : isLieConjugation_slFinTwoEntrywiseConj.realForm) :
    ((θ).twistedKillingForm X X : ℂ) =
      4 * (((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ).trace := by
  rw [LieEquiv.twistedKillingForm_apply, ofReal_neg, IsLieConjugation.killingForm_realForm,
    killingForm_slFinTwo_apply, coe_restrictRealForm_slFinTwo_apply]
  simp

/-- **`Fix σ` is `𝔰𝔩₂(ℝ)`**: the real form of the entrywise conjugation of `𝔰𝔩₂(ℂ)` is isomorphic to
`𝔰𝔩₂(ℝ)`, by viewing real matrices as complex, with inverse taking real parts of entries. -/
noncomputable def slFinTwoRealFormEquiv :
    sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆ isLieConjugation_slFinTwoEntrywiseConj.realForm where
  toFun Y := ⟨⟨Complex.ofRealHom.mapMatrix (Y : Matrix (Fin 2) (Fin 2) ℝ), by
    simp [mem_sl_iff, ← AddMonoidHom.map_trace, mem_sl_iff.mp Y.property]⟩,
    by
      rw [IsLieConjugation.mem_realForm, ← Subtype.coe_inj]
      ext i j
      simp⟩
  map_add' X Y := by ext i j; simp
  map_smul' r X := by ext i j; simp
  map_lie' {X Y} := by ext i j; simp [Ring.lie_def, Matrix.mul_apply]
  invFun X := ⟨((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map Complex.re, by
    have h := congrArg Complex.re (mem_sl_iff.mp (X : sl (Fin 2) ℂ).property)
    rw [trace_fin_two, add_re, zero_re] at h
    rwa [mem_sl_iff, trace_fin_two, map_apply, map_apply]⟩
  left_inv Y := by ext i j; simp
  right_inv X := by
    ext i j
    simpa [eq_comm] using
      Complex.conj_eq_iff_re.mp (mem_realForm_slFinTwoEntrywiseConj_iff.mp X.property i j)

/-- `slFinTwoRealFormEquiv` views a real matrix as a complex matrix. -/
@[simp]
theorem coe_slFinTwoRealFormEquiv_apply (Y : sl (Fin 2) ℝ) :
    ((slFinTwoRealFormEquiv Y : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (Y : Matrix (Fin 2) (Fin 2) ℝ).map (↑) :=
  (rfl)

/-- `slFinTwoRealFormEquiv.symm` takes the real parts of the entries. -/
@[simp]
theorem coe_slFinTwoRealFormEquiv_symm_apply (X : isLieConjugation_slFinTwoEntrywiseConj.realForm) :
    ((slFinTwoRealFormEquiv.symm X : sl (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map Complex.re :=
  (rfl)

/-- **Under `Fix σ ≃ 𝔰𝔩₂(ℝ)`, `θ = στ` is the Cartan involution `X ↦ -Xᵀ` of `𝔰𝔩₂(ℝ)`.** -/
theorem restrictRealForm_slFinTwoRealFormEquiv (Y : sl (Fin 2) ℝ) :
    θ (slFinTwoRealFormEquiv Y) =
      slFinTwoRealFormEquiv
        (LieSubalgebra.restrictNegConjTranspose (sl (Fin 2) ℝ)
          (fun _ ↦ conjTranspose_mem_sl) Y) := by
  ext i j
  simp [conjTranspose_eq_transpose_of_trivial]

/-! ### The complex-linear Chevalley involution -/

/-- The complex-linear Chevalley involution `X ↦ -Xᵀ` of `𝔰𝔩₂(ℂ)`: `h ↦ -h`, `e ↦ -f`, `f ↦ -e`,
with no conjugation of scalars. -/
def slFinTwoChevalleyInvolution : sl (Fin 2) ℂ ≃ₗ⁅ℂ⁆ sl (Fin 2) ℂ :=
  (sl (Fin 2) ℂ).restrictNegTranspose fun _ ↦ transpose_mem_sl

/-- `slFinTwoChevalleyInvolution` sends `X` to `-Xᵀ`. -/
@[simp]
theorem coe_slFinTwoChevalleyInvolution_apply (X : sl (Fin 2) ℂ) :
    (slFinTwoChevalleyInvolution X : Matrix (Fin 2) (Fin 2) ℂ) =
      -(X : Matrix (Fin 2) (Fin 2) ℂ)ᵀ :=
  LieSubalgebra.coe_restrictNegTranspose_apply _ _ X

/-- The Chevalley involution sends `h ↦ -h`. -/
theorem slFinTwoChevalleyInvolution_slFinTwoBasis_two :
    slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 2) = -slFinTwoBasis ℂ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_two]

/-- The Chevalley involution sends `e ↦ -f`. -/
theorem slFinTwoChevalleyInvolution_slFinTwoBasis_zero :
    slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 0) = -slFinTwoBasis ℂ 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_zero, slFinTwoBasis_one]

/-- The Chevalley involution sends `f ↦ -e`. -/
theorem slFinTwoChevalleyInvolution_slFinTwoBasis_one :
    slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 1) = -slFinTwoBasis ℂ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_zero, slFinTwoBasis_one]

/-- **The fixed set of the complex-linear Chevalley involution is not a real form**: it contains
both `e - f` and `i (e - f)`, so it meets its image under multiplication by `i`. -/
example :
    slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ∈ slFinTwoChevalleyInvolution.toLieHom.fixedSubalgebra ∧
      I • (slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1) ∈
        slFinTwoChevalleyInvolution.toLieHom.fixedSubalgebra ∧
      slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ≠ 0 := by
  have hfix : slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ∈
      slFinTwoChevalleyInvolution.toLieHom.fixedSubalgebra := by
    rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, map_sub,
      slFinTwoChevalleyInvolution_slFinTwoBasis_zero, slFinTwoChevalleyInvolution_slFinTwoBasis_one]
    abel
  refine ⟨hfix, LieSubalgebra.smul_mem _ I hfix, sub_ne_zero.mpr ?_⟩
  exact (slFinTwoBasis ℂ).injective.ne (by decide)

/-- **`-B(x, ω x)` is not positive for the complex-linear Chevalley involution `ω`**: it is `8` at
`h` but `-8` at `i h`, since `x ↦ -B(x, ω x)` is quadratic rather than Hermitian. -/
example :
    -killingForm ℂ (sl (Fin 2) ℂ) (slFinTwoBasis ℂ 2)
        (slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 2)) = 8 ∧
      -killingForm ℂ (sl (Fin 2) ℂ) (I • slFinTwoBasis ℂ 2)
        (slFinTwoChevalleyInvolution (I • slFinTwoBasis ℂ 2)) = -8 := by
  have h8 : killingForm ℂ (sl (Fin 2) ℂ) (slFinTwoBasis ℂ 2) (slFinTwoBasis ℂ 2) = 8 := by
    rw [killingForm_slFinTwoBasis]
    simp
  constructor
  · rw [slFinTwoChevalleyInvolution_slFinTwoBasis_two, map_neg, neg_neg, h8]
  · simp only [map_smul, slFinTwoChevalleyInvolution_slFinTwoBasis_two, map_neg,
      LinearMap.smul_apply, smul_neg, neg_neg, h8, smul_eq_mul]
    rw [← mul_assoc, I_mul_I]
    ring

end TauCeti
