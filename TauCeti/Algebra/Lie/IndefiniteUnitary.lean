/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import TauCeti.Algebra.Lie.Orthogonal.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.Complex
import TauCeti.Algebra.Lie.GeneralLinear.Killing
import TauCeti.Algebra.Lie.Killing.Subalgebra
import TauCeti.LinearAlgebra.Trace.Complex
import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# The indefinite unitary Lie algebras `𝔲(p, q)` and `𝔰𝔲(p, q)`

Let `J = LieAlgebra.Orthogonal.indefiniteDiagonal p q ℂ = diag(1, …, 1, -1, …, -1)`, the Gram
matrix of the Hermitian form of signature `(p, q)` preserved by the indefinite unitary group
`TauCeti.Matrix.indefiniteUnitaryGroup p q ℂ`. Its Lie algebra is the real Lie algebra
`𝔲(p, q)` of the complex matrices `X` with `Xᴴ J + J X = 0`
(`TauCeti.indefiniteUnitaryLieAlgebra p q`), and `𝔰𝔲(p, q)` is its subalgebra of trace-free
matrices (`TauCeti.specialIndefiniteUnitaryLieAlgebra p q`). Both are real, not complex, Lie
subalgebras of `𝔤𝔩_n(ℂ)`, `n = p + q`; for `q` empty, `𝔲(p, q)` is the unitary Lie algebra
`𝔲(n)` of skew-Hermitian matrices.

The Killing form of `𝔲(p, q)` is the real part of the Killing form of `𝔤𝔩_n(ℂ)`:

`κ(X, Y) = Re (2 n trace (X * Y) - 2 trace X * trace Y)`.

The map `σ Z = J Zᴴ J` is a conjugate-linear involution of `𝔤𝔩_n(ℂ)` acting as `-1` on
`𝔲(p, q)`, so `P Z = Z - σ Z` maps `𝔤𝔩_n(ℂ)` onto `𝔲(p, q)` and acts on it as multiplication by
two. For `X, Y ∈ 𝔲(p, q)` the operator `L = ad X ∘ ad Y` of `𝔤𝔩_n(ℂ)` preserves `𝔲(p, q)`, so
cycling the trace, twice the real trace of `ad X ∘ ad Y` on `𝔲(p, q)` is the real trace of `L`
minus that of `σ ∘ L`. The first is twice the real part of the complex trace of the
complex-linear map `L` (`LinearMap.trace_restrictScalars`), which is the Killing form of
`𝔤𝔩_n(ℂ)` (`Matrix.killingForm_apply`). The second vanishes, since `σ ∘ L` anticommutes with
multiplication by `i` (`LinearMap.trace_eq_zero_of_map_I_smul_eq_neg`). This follows the
computation of `LieAlgebra.Symplectic.killingForm_apply` in
`TauCeti/Algebra/Lie/Symplectic/Killing.lean`.

Brackets in `𝔲(p, q)` are trace-free (`TauCeti.lie_mem_specialIndefiniteUnitaryLieAlgebra`), so
the Killing form of `𝔰𝔲(p, q)` is the restriction of that of `𝔲(p, q)`
(`LieSubalgebra.killingForm_inclusion_eq`):

`κ(X, Y) = 2 n Re trace (X * Y)`.

`𝔲(p, q)` and `𝔰𝔲(p, q)` are closed under conjugate transpose, and `Re trace (Xᴴ * X)` is the sum
of the squares of the absolute values of the entries of `X`. So the Killing form of `𝔰𝔲(p, q)`
is nondegenerate, and `𝔰𝔲(p, q)` is semisimple.

## Main definitions

* `TauCeti.indefiniteUnitaryLieAlgebra p q`: the real Lie algebra `𝔲(p, q)`.
* `TauCeti.specialIndefiniteUnitaryLieAlgebra p q`: the real Lie algebra `𝔰𝔲(p, q)`.

## Main results

* `TauCeti.killingForm_indefiniteUnitaryLieAlgebra_apply`: the Killing form of `𝔲(p, q)`.
* `TauCeti.killingForm_specialIndefiniteUnitaryLieAlgebra_apply`: the Killing form of
  `𝔰𝔲(p, q)`.
* `TauCeti.isKilling_specialIndefiniteUnitaryLieAlgebra`: the Killing form of `𝔰𝔲(p, q)` is
  nondegenerate; in particular `𝔰𝔲(p, q)` is semisimple
  (`TauCeti.isSemisimple_specialIndefiniteUnitaryLieAlgebra`).

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the real forms `𝔲(p, q)` and `𝔰𝔲(p, q)` and the Killing
  forms of the classical Lie algebras).
-/

public section

open LieAlgebra LieAlgebra.Orthogonal Matrix
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (p q : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The **indefinite unitary Lie algebra** `𝔲(p, q)`: the real Lie subalgebra of the complex
matrices `X` with `Xᴴ J = -(J X)`, for `J = diag(1, …, 1, -1, …, -1)` the Gram matrix of the
Hermitian form of signature `(p, q)`. It is the Lie algebra of the indefinite unitary group
`TauCeti.Matrix.indefiniteUnitaryGroup p q ℂ`. -/
def indefiniteUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix (p ⊕ q) (p ⊕ q) ℂ) where
  carrier := {X | Xᴴ * indefiniteDiagonal p q ℂ = -(indefiniteDiagonal p q ℂ * X)}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, neg_add] at *
    rw [hX, hY]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul] at *
    rw [hX, smul_neg]
  lie_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    -- `hX` and `hY` with a right factor, to rewrite right-associated products.
    have hX' (A : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
        Xᴴ * (indefiniteDiagonal p q ℂ * A) = -(indefiniteDiagonal p q ℂ * (X * A)) := by
      rw [← Matrix.mul_assoc, hX, Matrix.neg_mul, Matrix.mul_assoc]
    have hY' (A : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
        Yᴴ * (indefiniteDiagonal p q ℂ * A) = -(indefiniteDiagonal p q ℂ * (Y * A)) := by
      rw [← Matrix.mul_assoc, hY, Matrix.neg_mul, Matrix.mul_assoc]
    simp only [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hX, hY, hX', hY', Matrix.mul_neg, neg_neg]
    abel

variable {p q}

/-- Membership in `𝔲(p, q)` as the equation `Xᴴ J = -(J X)`. -/
@[simp]
theorem mem_indefiniteUnitaryLieAlgebra_iff {X : Matrix (p ⊕ q) (p ⊕ q) ℂ} :
    X ∈ indefiniteUnitaryLieAlgebra p q ↔
      Xᴴ * indefiniteDiagonal p q ℂ = -(indefiniteDiagonal p q ℂ * X) :=
  Iff.rfl

/-- Membership in `𝔲(p, q)` as the equation `J Xᴴ J = -X`. -/
theorem mem_indefiniteUnitaryLieAlgebra_iff' {X : Matrix (p ⊕ q) (p ⊕ q) ℂ} :
    X ∈ indefiniteUnitaryLieAlgebra p q ↔
      indefiniteDiagonal p q ℂ * Xᴴ * indefiniteDiagonal p q ℂ = -X := by
  rw [mem_indefiniteUnitaryLieAlgebra_iff]
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_neg, indefiniteDiagonal_mul_indefiniteDiagonal_mul]
  · intro h
    calc Xᴴ * indefiniteDiagonal p q ℂ = indefiniteDiagonal p q ℂ *
          (indefiniteDiagonal p q ℂ * Xᴴ * indefiniteDiagonal p q ℂ) := by
          rw [Matrix.mul_assoc, indefiniteDiagonal_mul_indefiniteDiagonal_mul]
      _ = -(indefiniteDiagonal p q ℂ * X) := by rw [h, Matrix.mul_neg]

/-- `𝔲(p, q)` is closed under conjugate transpose. -/
theorem conjTranspose_mem_indefiniteUnitaryLieAlgebra {X : Matrix (p ⊕ q) (p ⊕ q) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra p q) : Xᴴ ∈ indefiniteUnitaryLieAlgebra p q := by
  have h := congrArg (· * indefiniteDiagonal p q ℂ) (mem_indefiniteUnitaryLieAlgebra_iff.mp hX)
  simp only [Matrix.mul_assoc, indefiniteDiagonal_mul_indefiniteDiagonal, Matrix.mul_one,
    Matrix.neg_mul] at h
  rw [mem_indefiniteUnitaryLieAlgebra_iff', conjTranspose_conjTranspose, h, neg_neg,
    Matrix.mul_assoc]

variable (p q) in
/-- The **special indefinite unitary Lie algebra** `𝔰𝔲(p, q)`: the trace-free matrices of
`𝔲(p, q)`. -/
def specialIndefiniteUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix (p ⊕ q) (p ⊕ q) ℂ) where
  carrier := {X | X ∈ indefiniteUnitaryLieAlgebra p q ∧ X.trace = 0}
  add_mem' hX hY := ⟨add_mem hX.1 hY.1, by rw [trace_add, hX.2, hY.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, trace_zero _ _⟩
  smul_mem' r _ hX := ⟨SMulMemClass.smul_mem r hX.1, by rw [trace_smul, hX.2, smul_zero]⟩
  lie_mem' hX hY := ⟨LieSubalgebra.lie_mem _ hX.1 hY.1, matrix_trace_commutator_zero _ _ _ _⟩

/-- Membership in `𝔰𝔲(p, q)`: membership in `𝔲(p, q)` and trace zero. -/
@[simp]
theorem mem_specialIndefiniteUnitaryLieAlgebra_iff {X : Matrix (p ⊕ q) (p ⊕ q) ℂ} :
    X ∈ specialIndefiniteUnitaryLieAlgebra p q ↔
      X ∈ indefiniteUnitaryLieAlgebra p q ∧ X.trace = 0 :=
  Iff.rfl

/-- Brackets in `𝔲(p, q)` lie in `𝔰𝔲(p, q)`. -/
theorem lie_mem_specialIndefiniteUnitaryLieAlgebra {X Y : Matrix (p ⊕ q) (p ⊕ q) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra p q) (hY : Y ∈ indefiniteUnitaryLieAlgebra p q) :
    ⁅X, Y⁆ ∈ specialIndefiniteUnitaryLieAlgebra p q :=
  ⟨LieSubalgebra.lie_mem _ hX hY, matrix_trace_commutator_zero _ _ X Y⟩

/-- `𝔰𝔲(p, q)` is contained in `𝔲(p, q)`. -/
theorem specialIndefiniteUnitaryLieAlgebra_le :
    specialIndefiniteUnitaryLieAlgebra p q ≤ indefiniteUnitaryLieAlgebra p q :=
  fun _ hX ↦ hX.1

/-- `𝔰𝔲(p, q)` is closed under conjugate transpose. -/
theorem conjTranspose_mem_specialIndefiniteUnitaryLieAlgebra {X : Matrix (p ⊕ q) (p ⊕ q) ℂ}
    (hX : X ∈ specialIndefiniteUnitaryLieAlgebra p q) :
    Xᴴ ∈ specialIndefiniteUnitaryLieAlgebra p q :=
  ⟨conjTranspose_mem_indefiniteUnitaryLieAlgebra hX.1, by rw [trace_conjTranspose, hX.2, star_zero]⟩

/-! ### The Killing forms -/

/-- `𝔲(p, q)` is finite-dimensional over `ℝ`. -/
instance instModuleFiniteIndefiniteUnitaryLieAlgebra :
    Module.Finite ℝ (indefiniteUnitaryLieAlgebra p q) :=
  Module.Finite.of_injective (indefiniteUnitaryLieAlgebra p q).toSubmodule.subtype
    Subtype.val_injective

/-- `𝔰𝔲(p, q)` is finite-dimensional over `ℝ`. -/
instance instModuleFiniteSpecialIndefiniteUnitaryLieAlgebra :
    Module.Finite ℝ (specialIndefiniteUnitaryLieAlgebra p q) :=
  Module.Finite.of_injective (specialIndefiniteUnitaryLieAlgebra p q).toSubmodule.subtype
    Subtype.val_injective

/-- The conjugate-linear map `Z ↦ J Zᴴ J` of the complex matrices, as a real-linear map. -/
private def sigma : Matrix (p ⊕ q) (p ⊕ q) ℂ →ₗ[ℝ] Matrix (p ⊕ q) (p ⊕ q) ℂ where
  toFun Z := indefiniteDiagonal p q ℂ * Zᴴ * indefiniteDiagonal p q ℂ
  map_add' Z W := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r Z := by
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

private theorem sigma_apply (Z : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    sigma Z = indefiniteDiagonal p q ℂ * Zᴴ * indefiniteDiagonal p q ℂ :=
  rfl

private theorem sub_sigma_mem (Z : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    Z - sigma Z ∈ indefiniteUnitaryLieAlgebra p q := by
  simp only [mem_indefiniteUnitaryLieAlgebra_iff, sigma_apply, conjTranspose_sub,
    conjTranspose_mul, conjTranspose_conjTranspose, isHermitian_indefiniteDiagonal.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, indefiniteDiagonal_mul_indefiniteDiagonal,
    indefiniteDiagonal_mul_indefiniteDiagonal_mul, Matrix.mul_one, neg_sub]

private theorem sigma_I_smul (Z : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    sigma (Complex.I • Z) = -(Complex.I • sigma Z) := by
  rw [sigma_apply, sigma_apply, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.mul_smul, Matrix.smul_mul, neg_smul]

/-- The projection `Z ↦ Z - J Zᴴ J` of the complex matrices onto `𝔲(p, q)`, which is
multiplication by two on `𝔲(p, q)`. -/
private def project : Matrix (p ⊕ q) (p ⊕ q) ℂ →ₗ[ℝ] indefiniteUnitaryLieAlgebra p q where
  toFun Z := ⟨Z - sigma Z, sub_sigma_mem Z⟩
  map_add' Z W := by ext1; simp only [map_add, AddMemClass.coe_add]; abel
  map_smul' r Z := by ext1; simp [smul_sub]

private theorem coe_project_apply (Z : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    (project Z : Matrix (p ⊕ q) (p ⊕ q) ℂ) = Z - sigma Z :=
  rfl

/-- Twice the Killing form of `𝔲(p, q)` is twice the real part of that of `𝔤𝔩_n(ℂ)`. -/
private theorem two_mul_killingForm_indefiniteUnitaryLieAlgebra_apply
    (X Y : indefiniteUnitaryLieAlgebra p q) :
    2 * killingForm ℝ (indefiniteUnitaryLieAlgebra p q) X Y =
      2 * (killingForm ℂ (Matrix (p ⊕ q) (p ⊕ q) ℂ) X Y).re := by
  let ι := (indefiniteUnitaryLieAlgebra p q).incl.toLinearMap
  -- `ad X ∘ ad Y` on `𝔤𝔩_n(ℂ)`, a complex-linear map viewed as a real-linear one.
  let L := (ad ℂ (Matrix (p ⊕ q) (p ⊕ q) ℂ) X ∘ₗ ad ℂ _ Y).restrictScalars ℝ
  have h1 : project ∘ₗ L ∘ₗ ι =
      (2 : ℝ) • (ad ℝ (indefiniteUnitaryLieAlgebra p q) X ∘ₗ ad ℝ _ Y) := by
    ext1 W
    have hW : L W ∈ indefiniteUnitaryLieAlgebra p q :=
      LieSubalgebra.lie_mem _ X.property (LieSubalgebra.lie_mem _ Y.property W.property)
    have hσ : sigma (L W) = -L W := mem_indefiniteUnitaryLieAlgebra_iff'.mp hW
    apply Subtype.ext
    simp only [ι, LinearMap.comp_apply, coe_project_apply, LieHom.coe_toLinearMap,
      LieSubalgebra.coe_incl, hσ, sub_neg_eq_add]
    simp [L, two_smul]
  have h2 : ι ∘ₗ project = LinearMap.id - sigma := by
    ext1 Z
    simp [ι, coe_project_apply]
  -- `σ ∘ L` anticommutes with multiplication by `i`, so its real trace vanishes.
  have h3 : LinearMap.trace ℝ _ (sigma ∘ₗ L) = 0 :=
    LinearMap.trace_eq_zero_of_map_I_smul_eq_neg _ fun Z ↦ by
      simp only [L, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul,
        sigma_I_smul]
  have htrace : LinearMap.trace ℝ _ (project ∘ₗ L ∘ₗ ι) =
      LinearMap.trace ℝ _ L - LinearMap.trace ℝ _ (sigma ∘ₗ L) := by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, h2,
      LinearMap.sub_comp, map_sub, LinearMap.id_comp]
  rw [h1, map_smul, smul_eq_mul, h3, sub_zero, LinearMap.trace_restrictScalars,
    Algebra.trace_complex_apply] at htrace
  rw [killingForm_apply_apply, killingForm_apply_apply]
  exact htrace

/-- **The Killing form of `𝔲(p, q)`** is the real part of that of `𝔤𝔩_n(ℂ)`:
`κ(X, Y) = Re (2 n trace (X * Y) - 2 trace X * trace Y)` for `n = p + q`. -/
theorem killingForm_indefiniteUnitaryLieAlgebra_apply (X Y : indefiniteUnitaryLieAlgebra p q) :
    killingForm ℝ (indefiniteUnitaryLieAlgebra p q) X Y =
      (2 * Fintype.card (p ⊕ q) * ((X : Matrix (p ⊕ q) (p ⊕ q) ℂ) * Y).trace -
        2 * (X : Matrix (p ⊕ q) (p ⊕ q) ℂ).trace * (Y : Matrix (p ⊕ q) (p ⊕ q) ℂ).trace).re := by
  rw [← Matrix.killingForm_apply]
  exact mul_left_cancel₀ two_ne_zero (two_mul_killingForm_indefiniteUnitaryLieAlgebra_apply X Y)

/-- **The Killing form of `𝔰𝔲(p, q)`**: `κ(X, Y) = 2 n Re trace (X * Y)` for `n = p + q`. -/
theorem killingForm_specialIndefiniteUnitaryLieAlgebra_apply
    (X Y : specialIndefiniteUnitaryLieAlgebra p q) :
    killingForm ℝ (specialIndefiniteUnitaryLieAlgebra p q) X Y =
      2 * Fintype.card (p ⊕ q) * ((X : Matrix (p ⊕ q) (p ⊕ q) ℂ) * Y).trace.re := by
  rw [LieSubalgebra.killingForm_inclusion_eq specialIndefiniteUnitaryLieAlgebra_le
      (fun _ hx _ hy ↦ lie_mem_specialIndefiniteUnitaryLieAlgebra hx.1 hy),
    killingForm_indefiniteUnitaryLieAlgebra_apply]
  simp only [LieSubalgebra.coe_inclusion, X.property.2, mul_zero, zero_mul, sub_zero]
  norm_cast
  simp [Complex.mul_re]

/-- **The Killing form of `𝔰𝔲(p, q)` is nondegenerate.** For nonzero `X`, the element `Xᴴ` pairs
with it to `2 n` times the sum of the squares of the absolute values of its entries. -/
instance isKilling_specialIndefiniteUnitaryLieAlgebra :
    IsKilling ℝ (specialIndefiniteUnitaryLieAlgebra p q) := by
  refine ⟨(LieSubmodule.eq_bot_iff _).mpr fun X hX ↦ ?_⟩
  rw [LieIdeal.mem_killingCompl] at hX
  have h := hX ⟨_, conjTranspose_mem_specialIndefiniteUnitaryLieAlgebra X.property⟩
    (LieSubmodule.mem_top _)
  rw [killingForm_specialIndefiniteUnitaryLieAlgebra_apply] at h
  rcases mul_eq_zero.mp h with h | h
  · have : IsEmpty (p ⊕ q) := by
      rw [← Fintype.card_eq_zero_iff]
      exact_mod_cast (mul_eq_zero.mp h).resolve_left two_ne_zero
    exact Subtype.ext (Subsingleton.elim _ _)
  · have hre : ((X : Matrix (p ⊕ q) (p ⊕ q) ℂ)ᴴ * X).trace = 0 := by
      have h0 := Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self
        (X : Matrix (p ⊕ q) (p ⊕ q) ℂ)).trace_nonneg
      exact Complex.ext (by simpa using h) (by simpa using h0.2.symm)
    exact Subtype.ext (trace_conjTranspose_mul_self_eq_zero_iff.mp hre)

/-- **`𝔰𝔲(p, q)` is semisimple.** -/
instance isSemisimple_specialIndefiniteUnitaryLieAlgebra :
    IsSemisimple ℝ (specialIndefiniteUnitaryLieAlgebra p q) :=
  inferInstance

end TauCeti
