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
* `-1`-eigenspace `𝔭` of dimension two.

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

/-- The Cartan involution `X ↦ -Xᵀ` of `𝔰𝔬(2, 1)`. -/
noncomputable def soTwoOneCartanInvolution : so' (Fin 2) (Fin 1) ℝ ≃ₗ⁅ℝ⁆ so' (Fin 2) (Fin 1) ℝ :=
  (so' (Fin 2) (Fin 1) ℝ).restrictNegConjTranspose fun _ ↦ conjTranspose_mem_so'

/-- `soTwoOneCartanInvolution` sends `X` to `-Xᵀ`. -/
@[simp]
theorem coe_soTwoOneCartanInvolution_apply (X : so' (Fin 2) (Fin 1) ℝ) :
    (soTwoOneCartanInvolution X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) =
      -(X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ)ᵀ := by
  rw [soTwoOneCartanInvolution, LieSubalgebra.coe_restrictNegConjTranspose_apply,
    conjTranspose_eq_transpose_of_trivial]

/-- `X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔬(2, 1)`. -/
theorem isCartanInvolution_soTwoOneCartanInvolution :
    soTwoOneCartanInvolution.IsCartanInvolution :=
  isCartanInvolution_restrictNegConjTranspose_so' (by simp)

/-- `X ↦ -Xᵀ` sends `TauCeti.soTwoOneMatrix x y z` to `TauCeti.soTwoOneMatrix (-x) (-z) (-y)`. -/
theorem coe_soTwoOneCartanInvolution_apply_of_coe_eq {X : so' (Fin 2) (Fin 1) ℝ} {x y z : ℝ}
    (hX : (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix x y z) :
    (soTwoOneCartanInvolution X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) =
      soTwoOneMatrix (-x) (-z) (-y) := by
  rw [coe_soTwoOneCartanInvolution_apply, hX, soTwoOneMatrix_transpose, soTwoOneMatrix_neg]

/-- The fixed subalgebra `𝔨` of `X ↦ -Xᵀ` on `𝔰𝔬(2, 1)` in coordinates: `x = 0` and `z = -y`. -/
theorem mem_fixedSubalgebra_soTwoOneCartanInvolution_iff {X : so' (Fin 2) (Fin 1) ℝ} :
    X ∈ soTwoOneCartanInvolution.toLieHom.fixedSubalgebra ↔
      ∃ y, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix 0 y (-y) := by
  obtain ⟨x, y, z, hX⟩ := exists_eq_soTwoOneMatrix X
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, ← Subtype.coe_inj,
    coe_soTwoOneCartanInvolution_apply_of_coe_eq hX, hX]
  constructor
  · intro h
    obtain ⟨h₁, h₂, -⟩ := soTwoOneMatrix_inj.mp h
    exact ⟨y, by rw [show x = 0 by linarith, show z = -y by linarith]⟩
  · rintro ⟨y', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := soTwoOneMatrix_inj.mp h
    simp

/-- The `-1`-eigenspace `𝔭` of `X ↦ -Xᵀ` on `𝔰𝔬(2, 1)` in coordinates: `y = z`. -/
theorem mem_cartanP_soTwoOneCartanInvolution_iff {X : so' (Fin 2) (Fin 1) ℝ} :
    X ∈ soTwoOneCartanInvolution.cartanP ↔
      ∃ x y, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix x y y := by
  obtain ⟨x, y, z, hX⟩ := exists_eq_soTwoOneMatrix X
  rw [LieEquiv.mem_cartanP, ← Subtype.coe_inj, coe_soTwoOneCartanInvolution_apply_of_coe_eq hX,
    NegMemClass.coe_neg, hX, ← soTwoOneMatrix_neg]
  constructor
  · intro h
    obtain ⟨-, h₂, -⟩ := soTwoOneMatrix_inj.mp h
    exact ⟨x, y, by rw [show z = y by linarith]⟩
  · rintro ⟨x', y', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := soTwoOneMatrix_inj.mp h
    rfl

/-- The coordinates `x = 0`, `z = -y` give the block matrix `[[A, 0], [0, 0]]` with
`A = [[0, 2y], [-2y, 0]]`. -/
private theorem soTwoOneMatrix_zero_neg (y : ℝ) :
    soTwoOneMatrix 0 y (-y) = fromBlocks !![0, 2 * y; -(2 * y), 0] 0 0 0 := by
  rw [soTwoOneMatrix_def]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring

/-- `𝔨 = 𝔰𝔬(2)`: the fixed subalgebra of `X ↦ -Xᵀ` on `𝔰𝔬(2, 1)` consists of the block matrices
`[[A, 0], [0, 0]]` with `A` skew-symmetric of size two. -/
theorem mem_fixedSubalgebra_soTwoOneCartanInvolution_iff_fromBlocks
    {X : so' (Fin 2) (Fin 1) ℝ} :
    X ∈ soTwoOneCartanInvolution.toLieHom.fixedSubalgebra ↔
      ∃ A ∈ so (Fin 2) ℝ, (X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = fromBlocks A 0 0 0 := by
  rw [mem_fixedSubalgebra_soTwoOneCartanInvolution_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨!![0, 2 * y; -(2 * y), 0], ?_, hy.trans (soTwoOneMatrix_zero_neg y)⟩
    rw [mem_so]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rintro ⟨A, hA, h⟩
    have hA' := (mem_so _ _ A).mp hA
    refine ⟨A 0 1 / 2, h.trans ?_⟩
    rw [soTwoOneMatrix_zero_neg]
    congr 1
    ext i j
    have hij := congrFun (congrFun hA' i) j
    have hji := congrFun (congrFun hA' j) i
    fin_cases i <;> fin_cases j <;> simp at hij hji ⊢ <;> linarith

/-- The linear map `y ↦ TauCeti.soTwoOneMatrix 0 y (-y)` onto `𝔨`. -/
private noncomputable def soTwoOneK : ℝ →ₗ[ℝ] so' (Fin 2) (Fin 1) ℝ where
  toFun y := ⟨soTwoOneMatrix 0 y (-y), soTwoOneMatrix_mem_so' _ _ _⟩
  map_add' y y' := Subtype.ext <| by
    simp [← soTwoOneMatrix_add, add_comm]
  map_smul' r y := Subtype.ext <| by
    simp [← soTwoOneMatrix_smul]

/-- The coercion of `soTwoOneK y` is `TauCeti.soTwoOneMatrix 0 y (-y)`. -/
private theorem coe_soTwoOneK_apply (y : ℝ) :
    (soTwoOneK y : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix 0 y (-y) :=
  rfl

/-- The linear map `(x, y) ↦ TauCeti.soTwoOneMatrix x y y` onto `𝔭`. -/
private noncomputable def soTwoOneP : ℝ × ℝ →ₗ[ℝ] so' (Fin 2) (Fin 1) ℝ where
  toFun v := ⟨soTwoOneMatrix v.1 v.2 v.2, soTwoOneMatrix_mem_so' _ _ _⟩
  map_add' v w := Subtype.ext <| by
    simp [soTwoOneMatrix_add]
  map_smul' r v := Subtype.ext <| by
    simp [soTwoOneMatrix_smul]

/-- The coercion of `soTwoOneP v` is `TauCeti.soTwoOneMatrix v.1 v.2 v.2`. -/
private theorem coe_soTwoOneP_apply (v : ℝ × ℝ) :
    (soTwoOneP v : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = soTwoOneMatrix v.1 v.2 v.2 :=
  rfl

/-- `𝔨 = 𝔰𝔬(2)` is one-dimensional. -/
theorem finrank_fixedSubalgebra_soTwoOneCartanInvolution :
    finrank ℝ soTwoOneCartanInvolution.toLieHom.fixedSubalgebra = 1 := by
  have hinj : Function.Injective soTwoOneK := fun y y' h ↦ by
    rw [← Subtype.coe_inj, coe_soTwoOneK_apply, coe_soTwoOneK_apply, soTwoOneMatrix_inj] at h
    exact h.2.1
  have hrange : LinearMap.range soTwoOneK =
      soTwoOneCartanInvolution.toLieHom.fixedSubalgebra.toSubmodule := by
    ext X
    rw [LinearMap.mem_range, LieSubalgebra.mem_toSubmodule,
      mem_fixedSubalgebra_soTwoOneCartanInvolution_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, coe_soTwoOneK_apply y⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext ((coe_soTwoOneK_apply y).trans hy.symm)⟩
  have := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_self] at this
  exact this

/-- `𝔭` is two-dimensional. -/
theorem finrank_cartanP_soTwoOneCartanInvolution :
    finrank ℝ soTwoOneCartanInvolution.cartanP = 2 := by
  have hinj : Function.Injective soTwoOneP := fun v w h ↦ by
    rw [← Subtype.coe_inj, coe_soTwoOneP_apply, coe_soTwoOneP_apply, soTwoOneMatrix_inj] at h
    exact Prod.ext h.1 h.2.1
  have hrange : LinearMap.range soTwoOneP = soTwoOneCartanInvolution.cartanP := by
    ext X
    rw [LinearMap.mem_range, mem_cartanP_soTwoOneCartanInvolution_iff]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, v.2, coe_soTwoOneP_apply v⟩
    · rintro ⟨x, y, hxy⟩
      exact ⟨(x, y), Subtype.ext ((coe_soTwoOneP_apply (x, y)).trans hxy.symm)⟩
  have := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_prod, finrank_self] at this
  exact this

end TauCeti
