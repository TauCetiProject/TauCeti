/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.Cartan
public import TauCeti.Algebra.Lie.Orthogonal.SlTwo
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# The Cartan decomposition of `𝔰𝔬(2, 1)`

On `𝔰𝔬(2, 1) = LieAlgebra.Orthogonal.so' (Fin 2) (Fin 1) ℝ`, the matrix Cartan involution
`θ X = -Xᵀ` (`LieAlgebra.Orthogonal.isCartanInvolution_restrictNegConjTranspose_so'`) has:

* Killing form `B(X, Y) = tr(XY)`, the case `p + q - 2 = 1` of `TauCeti.killingForm_so'_apply`;
* fixed subalgebra `𝔨 = 𝔰𝔬(2)`, the block matrices `[[A, 0], [0, 0]]` with `A` skew-symmetric of
  size two, of dimension one;
* `-1`-eigenspace `𝔭` the block matrices `[[0, b], [bᵀ, 0]]`, of dimension two.

In the coordinates `TauCeti.soTwoOneMatrix x y z` of `𝔰𝔬(2, 1)` (the image of
`[[x, y], [z, -x]] ∈ 𝔰𝔩₂(ℝ)` under `TauCeti.slTwoLieEquivSoTwoOne`), `𝔨` is `x = 0, z = -y` and
`𝔭` is `y = z`, the images of the skew-symmetric and of the symmetric trace-zero matrices; the
isomorphism intertwines the two Cartan involutions by `TauCeti.slTwoLieEquivSoTwoOne_neg_transpose`.
-/

public section

open LieAlgebra LieAlgebra.Orthogonal Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- The Killing form of `𝔰𝔬(2, 1)` is `B(X, Y) = tr(XY)`. -/
theorem killingForm_soTwoOne_apply (X Y : so' (Fin 2) (Fin 1) ℝ) :
    killingForm ℝ (so' (Fin 2) (Fin 1) ℝ) X Y =
      ((X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) * Y).trace := by
  rw [killingForm_so'_apply]
  norm_num

/-- The coordinates `(x, y, z)` are determined by `TauCeti.soTwoOneMatrix x y z`. -/
theorem soTwoOneMatrix_injective {x y z x' y' z' : ℝ}
    (h : soTwoOneMatrix x y z = soTwoOneMatrix x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  have h₁ := congrFun (congrFun h (.inl 0)) (.inr 0)
  have h₂ := congrFun (congrFun h (.inl 0)) (.inl 1)
  have h₃ := congrFun (congrFun h (.inl 1)) (.inr 0)
  simp only [Fin.isValue, soTwoOneMatrix_def, fromBlocks_apply₁₂, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
    fromBlocks_apply₁₁, cons_val_one] at h₁ h₂ h₃
  refine ⟨h₁, ?_, ?_⟩ <;> linarith

/-- Every element of `𝔰𝔬(2, 1)` is `TauCeti.soTwoOneMatrix x y z` for some `x`, `y`, `z`. -/
theorem exists_eq_soTwoOneMatrix (X : so' (Fin 2) (Fin 1) ℝ) :
    ∃ x y z, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix x y z :=
  ⟨_, _, _, by rw [← slTwoLieEquivSoTwoOne.apply_symm_apply X, coe_slTwoLieEquivSoTwoOne_apply]⟩

/-- The Cartan involution `X ↦ -Xᵀ` of `𝔰𝔬(2, 1)`. -/
noncomputable abbrev soTwoOneCartanInvolution : so' (Fin 2) (Fin 1) ℝ ≃ₗ⁅ℝ⁆ so' (Fin 2) (Fin 1) ℝ :=
  (so' (Fin 2) (Fin 1) ℝ).restrictNegConjTranspose fun _ ↦ conjTranspose_mem_so'

/-- `X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔬(2, 1)`. -/
theorem isCartanInvolution_soTwoOneCartanInvolution :
    soTwoOneCartanInvolution.IsCartanInvolution :=
  isCartanInvolution_restrictNegConjTranspose_so' (by simp)

/-- `X ↦ -Xᵀ` sends `TauCeti.soTwoOneMatrix x y z` to `TauCeti.soTwoOneMatrix (-x) (-z) (-y)`. -/
theorem coe_soTwoOneCartanInvolution_apply {X : so' (Fin 2) (Fin 1) ℝ} {x y z : ℝ}
    (hX : (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix x y z) :
    (soTwoOneCartanInvolution X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) =
      soTwoOneMatrix (-x) (-z) (-y) := by
  rw [LieSubalgebra.coe_restrictNegConjTranspose_apply, hX, conjTranspose_eq_transpose_of_trivial,
    soTwoOneMatrix_transpose, soTwoOneMatrix_neg]

/-- The fixed subalgebra `𝔨` of `X ↦ -Xᵀ` on `𝔰𝔬(2, 1)` in coordinates: `x = 0` and `z = -y`. -/
theorem mem_fixedSubalgebra_soTwoOne_iff {X : so' (Fin 2) (Fin 1) ℝ} :
    X ∈ soTwoOneCartanInvolution.toLieHom.fixedSubalgebra ↔
      ∃ y, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix 0 y (-y) := by
  obtain ⟨x, y, z, hX⟩ := exists_eq_soTwoOneMatrix X
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, ← Subtype.coe_inj,
    coe_soTwoOneCartanInvolution_apply hX, hX]
  constructor
  · intro h
    obtain ⟨h₁, h₂, -⟩ := soTwoOneMatrix_injective h
    exact ⟨y, by rw [show x = 0 by linarith, show z = -y by linarith]⟩
  · rintro ⟨y', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := soTwoOneMatrix_injective h
    simp

/-- The `-1`-eigenspace `𝔭` of `X ↦ -Xᵀ` on `𝔰𝔬(2, 1)` in coordinates: `y = z`. -/
theorem mem_cartanP_soTwoOne_iff {X : so' (Fin 2) (Fin 1) ℝ} :
    X ∈ soTwoOneCartanInvolution.cartanP ↔
      ∃ x y, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix x y y := by
  obtain ⟨x, y, z, hX⟩ := exists_eq_soTwoOneMatrix X
  rw [LieEquiv.mem_cartanP, ← Subtype.coe_inj, coe_soTwoOneCartanInvolution_apply hX,
    NegMemClass.coe_neg, hX, ← soTwoOneMatrix_neg]
  constructor
  · intro h
    obtain ⟨-, h₂, -⟩ := soTwoOneMatrix_injective h
    exact ⟨x, y, by rw [show z = y by linarith]⟩
  · rintro ⟨x', y', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := soTwoOneMatrix_injective h
    rfl

/-- `𝔨 = 𝔰𝔬(2)`: the fixed subalgebra of `X ↦ -Xᵀ` on `𝔰𝔬(2, 1)` consists of the block matrices
`[[A, 0], [0, 0]]` with `A` skew-symmetric of size two. -/
theorem mem_fixedSubalgebra_soTwoOne_iff_fromBlocks {X : so' (Fin 2) (Fin 1) ℝ} :
    X ∈ soTwoOneCartanInvolution.toLieHom.fixedSubalgebra ↔
      ∃ A ∈ so (Fin 2) ℝ, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = fromBlocks A 0 0 0 := by
  rw [mem_fixedSubalgebra_soTwoOne_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨!![0, 2 * y; -(2 * y), 0], ?_, ?_⟩
    · rw [mem_so]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · rw [hy, soTwoOneMatrix_def]
      congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
  · rintro ⟨A, hA, h⟩
    have hA' := congrFun (congrFun ((mem_so _ _ A).mp hA) 0) 1
    have hA₀ := congrFun (congrFun ((mem_so _ _ A).mp hA) 0) 0
    have hA₁ := congrFun (congrFun ((mem_so _ _ A).mp hA) 1) 1
    simp only [transpose_apply, Matrix.neg_apply] at hA' hA₀ hA₁
    refine ⟨A 0 1 / 2, h.trans ?_⟩
    rw [soTwoOneMatrix_def]
    congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The linear map `y ↦ TauCeti.soTwoOneMatrix 0 y (-y)` onto `𝔨`. -/
private noncomputable def soTwoOneK : ℝ →ₗ[ℝ] so' (Fin 2) (Fin 1) ℝ where
  toFun y := ⟨soTwoOneMatrix 0 y (-y), soTwoOneMatrix_mem_so' _ _ _⟩
  map_add' y y' := Subtype.ext <| by
    change soTwoOneMatrix 0 (y + y') (-(y + y')) =
      soTwoOneMatrix 0 y (-y) + soTwoOneMatrix 0 y' (-y')
    rw [← soTwoOneMatrix_add, add_zero, neg_add]
  map_smul' r y := Subtype.ext <| by
    change soTwoOneMatrix 0 (r • y) (-(r • y)) = r • soTwoOneMatrix 0 y (-y)
    rw [← soTwoOneMatrix_smul, mul_zero, smul_eq_mul, mul_neg]

/-- The linear map `(x, y) ↦ TauCeti.soTwoOneMatrix x y y` onto `𝔭`. -/
private noncomputable def soTwoOneP : ℝ × ℝ →ₗ[ℝ] so' (Fin 2) (Fin 1) ℝ where
  toFun v := ⟨soTwoOneMatrix v.1 v.2 v.2, soTwoOneMatrix_mem_so' _ _ _⟩
  map_add' v w := Subtype.ext <| by
    change soTwoOneMatrix (v + w).1 (v + w).2 (v + w).2 =
      soTwoOneMatrix v.1 v.2 v.2 + soTwoOneMatrix w.1 w.2 w.2
    rw [← soTwoOneMatrix_add, Prod.fst_add, Prod.snd_add]
  map_smul' r v := Subtype.ext <| by
    change soTwoOneMatrix (r • v).1 (r • v).2 (r • v).2 = r • soTwoOneMatrix v.1 v.2 v.2
    rw [← soTwoOneMatrix_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul]

/-- `𝔨 = 𝔰𝔬(2)` is one-dimensional. -/
theorem finrank_fixedSubalgebra_soTwoOne :
    finrank ℝ soTwoOneCartanInvolution.toLieHom.fixedSubalgebra = 1 := by
  have hinj : Function.Injective soTwoOneK := fun y y' h ↦
    (soTwoOneMatrix_injective (congrArg Subtype.val h)).2.1
  have hrange : LinearMap.range soTwoOneK =
      soTwoOneCartanInvolution.toLieHom.fixedSubalgebra.toSubmodule := by
    ext X
    rw [LinearMap.mem_range, LieSubalgebra.mem_toSubmodule, mem_fixedSubalgebra_soTwoOne_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy.symm⟩
  have := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_self] at this
  exact this

/-- `𝔭` is two-dimensional. -/
theorem finrank_cartanP_soTwoOne : finrank ℝ soTwoOneCartanInvolution.cartanP = 2 := by
  have hinj : Function.Injective soTwoOneP := fun v w h ↦ by
    obtain ⟨h₁, h₂, -⟩ := soTwoOneMatrix_injective (congrArg Subtype.val h)
    exact Prod.ext h₁ h₂
  have hrange : LinearMap.range soTwoOneP = soTwoOneCartanInvolution.cartanP := by
    ext X
    rw [LinearMap.mem_range, mem_cartanP_soTwoOne_iff]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, v.2, rfl⟩
    · rintro ⟨x, y, hxy⟩
      exact ⟨(x, y), Subtype.ext hxy.symm⟩
  have := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_prod, finrank_self] at this
  exact this

end TauCeti
