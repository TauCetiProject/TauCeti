/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.Algebra.Lie.Symplectic.Basic

/-!
# The quaternionic unitary Lie algebra `𝔰𝔭(p, q)`

Let `n = p + q` and let `D = LieAlgebra.Orthogonal.indefiniteDiagonal p q ℂ` be the diagonal
matrix of signature `(p, q)`. On `ℂ^{2n}`, indexed by `(p ⊕ q) ⊕ (p ⊕ q)`, put
`K = fromBlocks D 0 0 D` (`TauCeti.quaternionicUnitaryGram p q`), the Gram matrix of a Hermitian
form of signature `(2p, 2q)`. The real Lie algebra `𝔰𝔭(p, q)`
(`TauCeti.quaternionicUnitaryLieAlgebra p q`) is the set of complex matrices `X` in the complex
symplectic Lie algebra `𝔰𝔭_{2n}(ℂ) = LieAlgebra.Symplectic.sp (p ⊕ q) ℂ` with `Xᴴ K = -(K X)`. It
is a real, not a complex, Lie subalgebra of `𝔤𝔩_{2n}(ℂ)`; for `q` empty it is the compact
symplectic Lie algebra `𝔰𝔭(n)`.

`𝔰𝔭(p, q)` is closed under conjugate transpose
(`TauCeti.conjTranspose_mem_quaternionicUnitaryLieAlgebra`), and its centre is trivial
(`TauCeti.center_quaternionicUnitaryLieAlgebra_eq_bot`). For the latter, conjugation by `K`
preserves `𝔰𝔭_{2n}(ℂ)` because `K` commutes with the symplectic matrix `J` and is symmetric. So
each `Y ∈ 𝔰𝔭_{2n}(ℂ)` is `2 Y = A - i B` with `A = Y - K Yᴴ K` and `B = i (Y + K Yᴴ K)` in
`𝔰𝔭(p, q)`. A central element of `𝔰𝔭(p, q)` therefore commutes with all of `𝔰𝔭_{2n}(ℂ)`, so it is
scalar (`Matrix.mem_range_scalar_of_commute_sp`), and a scalar symplectic matrix is zero
(`Matrix.scalar_mem_sp_iff`).

## Main definitions

* `TauCeti.quaternionicUnitaryGram p q`: the Hermitian Gram matrix `K = fromBlocks D 0 0 D`.
* `TauCeti.quaternionicUnitaryLieAlgebra p q`: the real Lie algebra `𝔰𝔭(p, q)`.

## Main results

* `TauCeti.conjTranspose_mem_quaternionicUnitaryLieAlgebra`: `𝔰𝔭(p, q)` is closed under conjugate
  transpose.
* `TauCeti.center_quaternionicUnitaryLieAlgebra_eq_bot`: the centre of `𝔰𝔭(p, q)` is trivial.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Chapter I
  (the real form `𝔰𝔭(p, q)` among the examples of semisimple Lie algebras, realized inside
  `𝔰𝔭(n, ℂ)` through the Hermitian form of `diag(I_{p,q}, I_{p,q})`).
-/

public section

open LieAlgebra LieAlgebra.Orthogonal LieAlgebra.Symplectic Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (p q : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The Gram matrix `K = fromBlocks D 0 0 D` of the Hermitian form of signature `(2p, 2q)` on
`ℂ^{2(p + q)}` preserved by `𝔰𝔭(p, q)`, for `D = diag(1, …, 1, -1, …, -1)` the indefinite
diagonal matrix of signature `(p, q)`. -/
def quaternionicUnitaryGram : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ :=
  fromBlocks (indefiniteDiagonal p q ℂ) 0 0 (indefiniteDiagonal p q ℂ)

omit [Fintype p] [Fintype q] in
/-- `K = fromBlocks D 0 0 D` for `D` the indefinite diagonal matrix of signature `(p, q)`. -/
theorem quaternionicUnitaryGram_def :
    quaternionicUnitaryGram p q =
      fromBlocks (indefiniteDiagonal p q ℂ) 0 0 (indefiniteDiagonal p q ℂ) :=
  (rfl)

variable {p q}

/-- `K * K = 1`. -/
@[simp]
theorem quaternionicUnitaryGram_mul_quaternionicUnitaryGram :
    quaternionicUnitaryGram p q * quaternionicUnitaryGram p q = 1 := by
  simp [quaternionicUnitaryGram, fromBlocks_multiply, indefiniteDiagonal_mul_indefiniteDiagonal,
    ← fromBlocks_one]

/-- `K * (K * M) = M`. -/
@[simp]
theorem quaternionicUnitaryGram_mul_quaternionicUnitaryGram_mul
    (M : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ) :
    quaternionicUnitaryGram p q * (quaternionicUnitaryGram p q * M) = M := by
  rw [← Matrix.mul_assoc, quaternionicUnitaryGram_mul_quaternionicUnitaryGram, Matrix.one_mul]

/-- `M * K * K = M`. -/
@[simp]
theorem mul_quaternionicUnitaryGram_mul_quaternionicUnitaryGram
    (M : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ) :
    M * quaternionicUnitaryGram p q * quaternionicUnitaryGram p q = M := by
  rw [Matrix.mul_assoc, quaternionicUnitaryGram_mul_quaternionicUnitaryGram, Matrix.mul_one]

omit [Fintype p] [Fintype q] in
/-- `K` is Hermitian. -/
@[simp]
theorem conjTranspose_quaternionicUnitaryGram :
    (quaternionicUnitaryGram p q)ᴴ = quaternionicUnitaryGram p q := by
  simp [quaternionicUnitaryGram, fromBlocks_conjTranspose,
    (isHermitian_indefiniteDiagonal (p := p) (q := q) (R := ℂ)).eq]

omit [Fintype p] [Fintype q] in
/-- `K` is symmetric. -/
@[simp]
theorem transpose_quaternionicUnitaryGram :
    (quaternionicUnitaryGram p q)ᵀ = quaternionicUnitaryGram p q := by
  simp [quaternionicUnitaryGram, indefiniteDiagonal]

/-- `K` commutes with the standard symplectic matrix `J`. -/
theorem commute_quaternionicUnitaryGram_J :
    Commute (quaternionicUnitaryGram p q) (J (p ⊕ q) ℂ) := by
  simp [Commute, SemiconjBy, quaternionicUnitaryGram, J, fromBlocks_multiply]

/-- Conjugation by `K` preserves the complex symplectic Lie algebra. -/
theorem quaternionicUnitaryGram_mul_mul_mem_sp
    {X : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ} (hX : X ∈ sp (p ⊕ q) ℂ) :
    quaternionicUnitaryGram p q * X * quaternionicUnitaryGram p q ∈ sp (p ⊕ q) ℂ := by
  rw [mem_sp] at hX ⊢
  rw [transpose_mul, transpose_mul, transpose_quaternionicUnitaryGram, Matrix.mul_assoc,
    Matrix.mul_assoc, commute_quaternionicUnitaryGram_J.eq, ← Matrix.mul_assoc Xᵀ, hX]
  simp only [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc,
    commute_quaternionicUnitaryGram_J.eq]

variable (p q)

/-- The **quaternionic unitary Lie algebra** `𝔰𝔭(p, q)`: the real Lie subalgebra of the complex
matrices `X` in the complex symplectic Lie algebra `𝔰𝔭_{2(p + q)}(ℂ)` with `Xᴴ K = -(K X)`, for
`K = TauCeti.quaternionicUnitaryGram p q` the Gram matrix of signature `(2p, 2q)`. -/
def quaternionicUnitaryLieAlgebra :
    LieSubalgebra ℝ (Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ) where
  carrier := {X | X ∈ sp (p ⊕ q) ℂ ∧
    Xᴴ * quaternionicUnitaryGram p q = -(quaternionicUnitaryGram p q * X)}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, hX.2, hY.2, neg_add]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' r X hX := ⟨by simpa [Complex.coe_smul] using (sp (p ⊕ q) ℂ).smul_mem (r : ℂ) hX.1, by
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, hX.2, smul_neg]⟩
  lie_mem' {X Y} hX hY := by
    refine ⟨(sp (p ⊕ q) ℂ).lie_mem hX.1 hY.1, ?_⟩
    obtain ⟨-, hX⟩ := hX
    obtain ⟨-, hY⟩ := hY
    have hX' (A : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ) :
        Xᴴ * (quaternionicUnitaryGram p q * A) = -(quaternionicUnitaryGram p q * (X * A)) := by
      rw [← Matrix.mul_assoc, hX, Matrix.neg_mul, Matrix.mul_assoc]
    have hY' (A : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ) :
        Yᴴ * (quaternionicUnitaryGram p q * A) = -(quaternionicUnitaryGram p q * (Y * A)) := by
      rw [← Matrix.mul_assoc, hY, Matrix.neg_mul, Matrix.mul_assoc]
    simp only [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hX, hY, hX', hY', Matrix.mul_neg, neg_neg]
    abel

variable {p q}

/-- Membership in `𝔰𝔭(p, q)`: `X ∈ 𝔰𝔭_{2(p + q)}(ℂ)` and `Xᴴ K = -(K X)`. -/
@[simp]
theorem mem_quaternionicUnitaryLieAlgebra_iff
    {X : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ} :
    X ∈ quaternionicUnitaryLieAlgebra p q ↔ X ∈ sp (p ⊕ q) ℂ ∧
      Xᴴ * quaternionicUnitaryGram p q = -(quaternionicUnitaryGram p q * X) :=
  Iff.rfl

/-- `𝔰𝔭(p, q)` is closed under conjugate transpose. -/
theorem conjTranspose_mem_quaternionicUnitaryLieAlgebra
    {X : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ}
    (hX : X ∈ quaternionicUnitaryLieAlgebra p q) : Xᴴ ∈ quaternionicUnitaryLieAlgebra p q := by
  obtain ⟨hsp, h⟩ := mem_quaternionicUnitaryLieAlgebra_iff.mp hX
  refine mem_quaternionicUnitaryLieAlgebra_iff.mpr ⟨conjTranspose_mem_sp hsp, ?_⟩
  rw [conjTranspose_conjTranspose]
  calc X * quaternionicUnitaryGram p q
      = -(quaternionicUnitaryGram p q * -(quaternionicUnitaryGram p q * X) *
          quaternionicUnitaryGram p q) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg,
          quaternionicUnitaryGram_mul_quaternionicUnitaryGram_mul]
    _ = -(quaternionicUnitaryGram p q * (Xᴴ * quaternionicUnitaryGram p q) *
          quaternionicUnitaryGram p q) := by rw [h]
    _ = -(quaternionicUnitaryGram p q * Xᴴ) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, quaternionicUnitaryGram_mul_quaternionicUnitaryGram,
          Matrix.mul_one]

/-- A matrix commuting with every element of `𝔰𝔭(p, q)` commutes with every element of the
complex symplectic Lie algebra `𝔰𝔭_{2(p+q)}(ℂ)`. -/
theorem commute_of_forall_mem_quaternionicUnitaryLieAlgebra
    {Z Y : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ}
    (hZ : ∀ X ∈ quaternionicUnitaryLieAlgebra p q, Commute Z X) (hY : Y ∈ sp (p ⊕ q) ℂ) :
    Commute Z Y := by
  set K := quaternionicUnitaryGram p q
  have hσ : K * Yᴴ * K ∈ sp (p ⊕ q) ℂ :=
    quaternionicUnitaryGram_mul_mul_mem_sp (conjTranspose_mem_sp hY)
  have hA : Y - K * Yᴴ * K ∈ quaternionicUnitaryLieAlgebra p q := by
    refine mem_quaternionicUnitaryLieAlgebra_iff.mpr ⟨sub_mem hY hσ, ?_⟩
    simp only [K, conjTranspose_sub, conjTranspose_mul, conjTranspose_quaternionicUnitaryGram,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      quaternionicUnitaryGram_mul_quaternionicUnitaryGram, Matrix.mul_one,
      quaternionicUnitaryGram_mul_quaternionicUnitaryGram_mul]
    abel
  have hB : Complex.I • (Y + K * Yᴴ * K) ∈ quaternionicUnitaryLieAlgebra p q := by
    refine mem_quaternionicUnitaryLieAlgebra_iff.mpr ⟨(sp (p ⊕ q) ℂ).smul_mem _ (add_mem hY hσ), ?_⟩
    simp only [K, conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
      conjTranspose_quaternionicUnitaryGram, conjTranspose_conjTranspose, Complex.star_def,
      Complex.conj_I, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
      quaternionicUnitaryGram_mul_quaternionicUnitaryGram_mul, neg_smul, smul_add]
    simp only [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc,
      quaternionicUnitaryGram_mul_quaternionicUnitaryGram, Matrix.mul_one]
    abel
  have h2 : (2 : ℂ) • Y = (Y - K * Yᴴ * K) - Complex.I • (Complex.I • (Y + K * Yᴴ * K)) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, two_smul]
    abel
  have hc : Commute Z ((2 : ℂ) • Y) := by
    rw [h2]
    exact ((hZ _ hA).sub_right ((hZ _ hB).smul_right _))
  have h := hc.eq
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  exact smul_right_injective _ two_ne_zero h

variable (p q)

/-- The **centre of `𝔰𝔭(p, q)` is trivial**. -/
theorem center_quaternionicUnitaryLieAlgebra_eq_bot :
    center ℝ (quaternionicUnitaryLieAlgebra p q) = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun ⟨Z, hZq⟩ hZ ↦ ?_
  rw [LieModule.mem_maxTrivSubmodule] at hZ
  have hcomm (X : Matrix ((p ⊕ q) ⊕ (p ⊕ q)) ((p ⊕ q) ⊕ (p ⊕ q)) ℂ)
      (hX : X ∈ quaternionicUnitaryLieAlgebra p q) : Commute Z X := by
    have := congrArg Subtype.val (hZ ⟨X, hX⟩)
    rw [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero, sub_eq_zero] at this
    exact this.symm
  obtain ⟨c, rfl⟩ := mem_range_scalar_of_commute_sp Z
    fun Y hY ↦ commute_of_forall_mem_quaternionicUnitaryLieAlgebra hcomm hY
  exact Subtype.ext ((scalar_mem_sp_iff c).mp (mem_quaternionicUnitaryLieAlgebra_iff.mp hZq).1)

end TauCeti
