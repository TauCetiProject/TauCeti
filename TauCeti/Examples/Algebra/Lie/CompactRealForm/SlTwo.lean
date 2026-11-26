/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CompactRealForm.CartanInvolution
public import TauCeti.Algebra.Lie.RestrictScalars
public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Algebra.Lie.Sl2.Killing

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

/-- The compact conjugation `X ↦ -X*` of `𝔰𝔩₂(ℂ)`, a conjugate-linear map. -/
noncomputable def slFinTwoCompactConj : sl (Fin 2) ℂ →ₛₗ[starRingEnd ℂ] sl (Fin 2) ℂ where
  toFun X := ⟨-(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ, neg_mem (conjTranspose_mem_sl X.property)⟩
  map_add' X Y := Subtype.ext (by simp [add_comm])
  map_smul' c X := Subtype.ext (by simp [conjTranspose_smul])

/-- `slFinTwoCompactConj` sends `X` to `-X*`. -/
@[simp]
theorem coe_slFinTwoCompactConj_apply (X : sl (Fin 2) ℂ) :
    (slFinTwoCompactConj X : Matrix (Fin 2) (Fin 2) ℂ) = -(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
  (rfl)

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
  map_lie X Y := Subtype.ext (by simp [Ring.lie_def, conjTranspose_mul])
  involutive X := Subtype.ext (by simp)

/-- The entrywise conjugation is a conjugation of `𝔰𝔩₂(ℂ)`. -/
theorem isLieConjugation_slFinTwoEntrywiseConj : IsLieConjugation slFinTwoEntrywiseConj where
  map_lie X Y := Subtype.ext (by simp [Ring.lie_def, conjTranspose_mul, transpose_mul])
  involutive X := Subtype.ext (by ext i j; simp)

/-- **`X ↦ -X*` is a compact conjugation of `𝔰𝔩₂(ℂ)`**:
`H_τ(X, X) = -B(X, -X*) = 4 tr(X X*) > 0` for `X ≠ 0`. -/
theorem isCompactConjugation_slFinTwoCompactConj : IsCompactConjugation slFinTwoCompactConj where
  toIsLieConjugation := isLieConjugation_slFinTwoCompactConj
  pos X hX := by
    have hX' : (X : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := fun h ↦ hX (Subtype.ext h)
    have hpos : 0 < ((X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace :=
      (posSemidef_self_mul_conjTranspose _).trace_nonneg.lt_of_ne
        (Ne.symm (trace_mul_conjTranspose_self_eq_zero_iff.not.2 hX'))
    rw [LinearMap.killingHermitianForm_def, killingForm_slFinTwo_apply,
      coe_slFinTwoCompactConj_apply, mul_neg, trace_neg, mul_neg, neg_neg]
    exact mul_pos (by norm_num) hpos

/-- The Hermitian Killing form of `X ↦ -X*` is `H_τ(X, X) = 4 tr(X X*)`. -/
theorem killingHermitianForm_slFinTwoCompactConj_apply_self (X : sl (Fin 2) ℂ) :
    slFinTwoCompactConj.killingHermitianForm X X =
      4 * ((X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace := by
  rw [LinearMap.killingHermitianForm_def, killingForm_slFinTwo_apply,
    coe_slFinTwoCompactConj_apply, mul_neg, trace_neg, mul_neg, neg_neg]

/-- `τ h = -h`. -/
theorem slFinTwoCompactConj_h :
    slFinTwoCompactConj (slFinTwoBasis ℂ 2) = -slFinTwoBasis ℂ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_two]

/-- `τ e = -f`. -/
theorem slFinTwoCompactConj_e :
    slFinTwoCompactConj (slFinTwoBasis ℂ 0) = -slFinTwoBasis ℂ 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_zero, slFinTwoBasis_one]

/-- `τ f = -e`. -/
theorem slFinTwoCompactConj_f :
    slFinTwoCompactConj (slFinTwoBasis ℂ 1) = -slFinTwoBasis ℂ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoBasis_zero, slFinTwoBasis_one]

/-- `H_τ(e, e) = -B(e, τ e) = B(e, f) = 4`. -/
example : slFinTwoCompactConj.killingHermitianForm (slFinTwoBasis ℂ 0) (slFinTwoBasis ℂ 0) = 4 := by
  rw [LinearMap.killingHermitianForm_def, slFinTwoCompactConj_e, map_neg, neg_neg,
    killingForm_slFinTwoBasis]
  rfl

/-- `H_τ(h, h) = -B(h, τ h) = B(h, h) = 8`. -/
example : slFinTwoCompactConj.killingHermitianForm (slFinTwoBasis ℂ 2) (slFinTwoBasis ℂ 2) = 8 := by
  rw [LinearMap.killingHermitianForm_def, slFinTwoCompactConj_h, map_neg, neg_neg,
    killingForm_slFinTwoBasis]
  rfl

/-- **The compact real form is `𝔰𝔲(2)`**: the skew-Hermitian trace-zero matrices. -/
theorem mem_realForm_slFinTwoCompactConj_iff {X : sl (Fin 2) ℂ} :
    X ∈ isLieConjugation_slFinTwoCompactConj.realForm ↔
      (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = -(X : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [IsLieConjugation.mem_realForm, ← Subtype.coe_inj, coe_slFinTwoCompactConj_apply,
    neg_eq_iff_eq_neg]

/-- `i h`, `e - f` and `i (e + f)` lie in the compact real form `𝔰𝔲(2)`. -/
example :
    I • slFinTwoBasis ℂ 2 ∈ isLieConjugation_slFinTwoCompactConj.realForm ∧
      slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ∈ isLieConjugation_slFinTwoCompactConj.realForm ∧
      I • (slFinTwoBasis ℂ 0 + slFinTwoBasis ℂ 1) ∈
        isLieConjugation_slFinTwoCompactConj.realForm := by
  simp only [IsLieConjugation.mem_realForm, map_smulₛₗ, map_sub, map_add, slFinTwoCompactConj_h,
    slFinTwoCompactConj_e, slFinTwoCompactConj_f, conj_I]
  refine ⟨?_, ?_, ?_⟩ <;> module

/-- The entrywise conjugation commutes with `X ↦ -X*`. -/
theorem slFinTwoEntrywiseConj_comm (X : sl (Fin 2) ℂ) :
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
    slFinTwoEntrywiseConj_comm

/-- **`θ = στ` is a Cartan involution of `Fix σ`.** -/
example : (θ).IsCartanInvolution :=
  isCompactConjugation_slFinTwoCompactConj.isCartanInvolution_restrictRealForm
    isLieConjugation_slFinTwoEntrywiseConj slFinTwoEntrywiseConj_comm

/-- **On `Fix σ` the Cartan involution `θ = στ` is `X ↦ -Xᵀ`.** -/
theorem coe_restrictRealForm_slFinTwo_apply
    (X : isLieConjugation_slFinTwoEntrywiseConj.realForm) :
    ((θ X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      -((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
  have hX := congrArg Subtype.val (IsLieConjugation.apply_coe_realForm _ X)
  rw [coe_slFinTwoEntrywiseConj_apply] at hX
  rw [IsLieConjugation.coe_restrictRealForm_apply, coe_slFinTwoCompactConj_apply,
    ← transpose_transpose ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ, hX]

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

/-- **`-B(X, θ X) = 4 tr(X Xᵀ)`** for the real Killing form of `Fix σ`, which is the restriction of
the Killing form of `𝔰𝔩₂(ℂ)`. -/
theorem killingForm_restrictRealForm_slFinTwo_apply_self
    (X : isLieConjugation_slFinTwoEntrywiseConj.realForm) :
    (-killingForm ℝ _ X (θ X) : ℂ) =
      4 * (((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ).trace := by
  rw [IsLieConjugation.killingForm_realForm, killingForm_slFinTwo_apply,
    coe_restrictRealForm_slFinTwo_apply, mul_neg, trace_neg, mul_neg, neg_neg]

/-- The inclusion of `𝔰𝔩₂(ℝ)` into the real form `Fix σ` of `𝔰𝔩₂(ℂ)`, a morphism of real Lie
algebras. -/
noncomputable def slFinTwoRealToRealForm :
    sl (Fin 2) ℝ →ₗ⁅ℝ⁆ isLieConjugation_slFinTwoEntrywiseConj.realForm where
  toFun Y := ⟨⟨Complex.ofRealHom.mapMatrix (Y : Matrix (Fin 2) (Fin 2) ℝ), by
    rw [mem_sl_iff, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, mem_sl_iff.mp Y.property,
      map_zero]⟩,
    by
      rw [IsLieConjugation.mem_realForm, ← Subtype.coe_inj]
      ext i j
      simp⟩
  map_add' X Y := by ext i j; simp
  map_smul' r X := by ext i j; simp
  map_lie' {X Y} := by ext i j; simp [Ring.lie_def, Matrix.mul_apply]

/-- `slFinTwoRealToRealForm` views a real matrix as a complex matrix. -/
@[simp]
theorem coe_slFinTwoRealToRealForm_apply (Y : sl (Fin 2) ℝ) :
    ((slFinTwoRealToRealForm Y : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (Y : Matrix (Fin 2) (Fin 2) ℝ).map (↑) :=
  (rfl)

/-- **`Fix σ` is `𝔰𝔩₂(ℝ)`**: the real form of the entrywise conjugation of `𝔰𝔩₂(ℂ)` is isomorphic to
`𝔰𝔩₂(ℝ)`, by viewing real matrices as complex. -/
noncomputable def slFinTwoRealFormEquiv :
    sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆ isLieConjugation_slFinTwoEntrywiseConj.realForm :=
  LieEquiv.ofBijective slFinTwoRealToRealForm
    ⟨fun X Y h ↦ by
      ext i j
      simpa using congrArg (fun Z : isLieConjugation_slFinTwoEntrywiseConj.realForm ↦
        ((Z : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j) h,
    fun X ↦ by
      have hX := mem_realForm_slFinTwoEntrywiseConj_iff.mp X.property
      refine ⟨⟨((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map Complex.re, ?_⟩, ?_⟩
      · change (((X : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map Complex.reAddGroupHom).trace = 0
        rw [← AddMonoidHom.map_trace Complex.reAddGroupHom,
          mem_sl_iff.mp (X : sl (Fin 2) ℂ).property, map_zero]
      · ext i j
        simpa [eq_comm] using (Complex.conj_eq_iff_re.mp (hX i j))⟩

/-- `slFinTwoRealFormEquiv` views a real matrix as a complex matrix. -/
@[simp]
theorem coe_slFinTwoRealFormEquiv_apply (Y : sl (Fin 2) ℝ) :
    ((slFinTwoRealFormEquiv Y : sl (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (Y : Matrix (Fin 2) (Fin 2) ℝ).map (↑) :=
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
noncomputable def slFinTwoChevalleyInvolution : sl (Fin 2) ℂ ≃ₗ⁅ℂ⁆ sl (Fin 2) ℂ where
  toFun X := ⟨-(X : Matrix (Fin 2) (Fin 2) ℂ)ᵀ, neg_transpose_mem_sl X.property⟩
  invFun X := ⟨-(X : Matrix (Fin 2) (Fin 2) ℂ)ᵀ, neg_transpose_mem_sl X.property⟩
  map_add' X Y := Subtype.ext (by simp [add_comm])
  map_smul' c X := Subtype.ext (by simp)
  map_lie' {X Y} := Subtype.ext (by simp [Ring.lie_def, transpose_mul])
  left_inv X := Subtype.ext (by simp)
  right_inv X := Subtype.ext (by simp)

/-- `slFinTwoChevalleyInvolution` sends `X` to `-Xᵀ`. -/
@[simp]
theorem coe_slFinTwoChevalleyInvolution_apply (X : sl (Fin 2) ℂ) :
    (slFinTwoChevalleyInvolution X : Matrix (Fin 2) (Fin 2) ℂ) =
      -(X : Matrix (Fin 2) (Fin 2) ℂ)ᵀ :=
  (rfl)

/-- The Chevalley involution sends `h ↦ -h`, `e ↦ -f` and `f ↦ -e`. -/
theorem slFinTwoChevalleyInvolution_basis :
    slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 2) = -slFinTwoBasis ℂ 2 ∧
      slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 0) = -slFinTwoBasis ℂ 1 ∧
      slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 1) = -slFinTwoBasis ℂ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [slFinTwoBasis_zero, slFinTwoBasis_one, slFinTwoBasis_two]

/-- **The fixed set of the complex-linear Chevalley involution is not a real form**: it contains
both `e - f` and `i (e - f)`, so it meets its image under multiplication by `i`. -/
theorem sub_mem_fixedSubalgebra_slFinTwoChevalleyInvolution :
    slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ∈ slFinTwoChevalleyInvolution.toLieHom.fixedSubalgebra ∧
      I • (slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1) ∈
        slFinTwoChevalleyInvolution.toLieHom.fixedSubalgebra ∧
      slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ≠ 0 := by
  obtain ⟨-, he, hf⟩ := slFinTwoChevalleyInvolution_basis
  have hfix : slFinTwoBasis ℂ 0 - slFinTwoBasis ℂ 1 ∈
      slFinTwoChevalleyInvolution.toLieHom.fixedSubalgebra := by
    rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, map_sub, he, hf]
    abel
  refine ⟨hfix, LieSubalgebra.smul_mem _ I hfix, sub_ne_zero.mpr ?_⟩
  exact (slFinTwoBasis ℂ).injective.ne (by decide)

/-- **`-B(x, ω x)` is not positive for the complex-linear Chevalley involution `ω`**: it is `8` at
`h` but `-8` at `i h`, since `x ↦ -B(x, ω x)` is quadratic rather than Hermitian. -/
theorem killingForm_slFinTwoChevalleyInvolution_h :
    -killingForm ℂ (sl (Fin 2) ℂ) (slFinTwoBasis ℂ 2)
        (slFinTwoChevalleyInvolution (slFinTwoBasis ℂ 2)) = 8 ∧
      -killingForm ℂ (sl (Fin 2) ℂ) (I • slFinTwoBasis ℂ 2)
        (slFinTwoChevalleyInvolution (I • slFinTwoBasis ℂ 2)) = -8 := by
  obtain ⟨hh, -, -⟩ := slFinTwoChevalleyInvolution_basis
  have h8 : killingForm ℂ (sl (Fin 2) ℂ) (slFinTwoBasis ℂ 2) (slFinTwoBasis ℂ 2) = 8 := by
    rw [killingForm_slFinTwoBasis]
    rfl
  simp only [map_smul, hh, map_neg, LinearMap.smul_apply, smul_neg, neg_neg, h8, smul_eq_mul]
  refine ⟨trivial, ?_⟩
  rw [← mul_assoc, I_mul_I]
  ring

end TauCeti
