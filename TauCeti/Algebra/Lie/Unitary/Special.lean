/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import TauCeti.Algebra.Lie.Unitary
import Mathlib.Algebra.Lie.Classical
import TauCeti.Algebra.Lie.Unitary.Killing

/-!
# The special unitary Lie algebra `𝔰𝔲(n)`

The Lie algebra of the special unitary group `SU(n) = Matrix.specialUnitaryGroup ι ℂ` is the real
Lie algebra `𝔰𝔲(n)` of trace-free skew-Hermitian matrices, `Xᴴ = -X` and `tr X = 0`
(`TauCeti.specialUnitaryLieAlgebra ι`). Like `𝔲(n) = TauCeti.unitaryLieAlgebra ι` it is a real,
not a complex, Lie subalgebra of `Matrix ι ι ℂ`, so Mathlib's complex `LieAlgebra.SpecialLinear.sl`
does not describe it.

Inside `𝔲(n)` it is the derived algebra `[𝔲(n), 𝔲(n)]`
(`TauCeti.coe_mem_specialUnitaryLieAlgebra_iff`), the complement of the centre `iℝ · 1`. Its real
dimension is `n² - 1` (`TauCeti.finrank_specialUnitaryLieAlgebra`): the imaginary part of the
trace is a surjection `𝔲(n) → ℝ` with kernel `𝔰𝔲(n)` (for `n ≥ 1`), and `𝔲(n)` has dimension
`n²`.

The unitary group acts on `𝔰𝔲(n)` by conjugation, `Ad_U X = U X Uᴴ`, by Lie algebra automorphisms
(`TauCeti.specialUnitaryAdjointRepresentation`). This is the adjoint representation of `SU(n)`
extended to `U(n)`; its invariant metric, orientation and kernel are computed in
`TauCeti.Algebra.Lie.Unitary.Adjoint`.

## Main definitions

* `TauCeti.specialUnitaryLieAlgebra ι`: the real Lie algebra `𝔰𝔲(n)`.
* `TauCeti.specialUnitaryAdjointRepresentation ι`: the action of `U(n)` on `𝔰𝔲(n)` by
  conjugation.

## Main results

* `TauCeti.mem_specialUnitaryLieAlgebra_iff`: `X ∈ 𝔰𝔲(n)` exactly when `Xᴴ = -X` and `tr X = 0`.
* `TauCeti.coe_mem_specialUnitaryLieAlgebra_iff`: `𝔰𝔲(n)` is the derived algebra of `𝔲(n)`.
* `TauCeti.mem_range_scalar_of_forall_mem_specialUnitaryLieAlgebra_commute`: a matrix commuting
  with every element of `𝔰𝔲(n)` is scalar.
* `TauCeti.finrank_specialUnitaryLieAlgebra`: `𝔰𝔲(n)` has real dimension `n² - 1`.
* `TauCeti.specialUnitaryAdjointRepresentation_lie`: the adjoint action is by Lie algebra
  automorphisms.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer GTM 222, 2015, Chapter 3 (the Lie algebras of the classical groups).
-/

public section

noncomputable section

open Matrix Module Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-! ### The special unitary Lie algebra -/

/-- The **special unitary Lie algebra** `𝔰𝔲(n)`: the real Lie subalgebra of `Matrix ι ι ℂ`
consisting of the trace-free skew-Hermitian matrices, `Xᴴ = -X` and `tr X = 0`. It is the Lie
algebra of the special unitary group `Matrix.specialUnitaryGroup ι ℂ`. -/
def specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix ι ι ℂ) where
  carrier := {X | X ∈ unitaryLieAlgebra ι ∧ X.trace = 0}
  add_mem' hX hY := ⟨add_mem hX.1 hY.1, by rw [trace_add, hX.2, hY.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, trace_zero _ _⟩
  smul_mem' r _ hX := ⟨SMulMemClass.smul_mem r hX.1, by rw [trace_smul, hX.2, smul_zero]⟩
  lie_mem' hX hY :=
    ⟨LieSubalgebra.lie_mem _ hX.1 hY.1, LieAlgebra.matrix_trace_commutator_zero _ _ _ _⟩

variable {ι}

/-- Membership in `𝔰𝔲(n)`: skew-Hermitian and trace-free. -/
@[simp]
theorem mem_specialUnitaryLieAlgebra_iff {X : Matrix ι ι ℂ} :
    X ∈ specialUnitaryLieAlgebra ι ↔ Xᴴ = -X ∧ X.trace = 0 := by
  rw [← mem_unitaryLieAlgebra_iff]
  exact Iff.rfl

/-- `𝔰𝔲(n)` is contained in `𝔲(n)`. -/
theorem specialUnitaryLieAlgebra_le : specialUnitaryLieAlgebra ι ≤ unitaryLieAlgebra ι :=
  fun _ hX ↦ hX.1

/-- An element of `𝔰𝔲(n)` is skew-Hermitian. -/
@[simp]
theorem conjTranspose_coe_specialUnitaryLieAlgebra (X : specialUnitaryLieAlgebra ι) :
    (X : Matrix ι ι ℂ)ᴴ = -X :=
  (mem_specialUnitaryLieAlgebra_iff.mp X.property).1

/-- An element of `𝔰𝔲(n)` is trace-free. -/
@[simp]
theorem trace_coe_specialUnitaryLieAlgebra (X : specialUnitaryLieAlgebra ι) :
    (X : Matrix ι ι ℂ).trace = 0 :=
  (mem_specialUnitaryLieAlgebra_iff.mp X.property).2

/-- **`𝔰𝔲(n)` is the derived algebra of `𝔲(n)`**: an element of `𝔲(n)` lies in `𝔰𝔲(n)` exactly
when it lies in `[𝔲(n), 𝔲(n)]`. -/
theorem coe_mem_specialUnitaryLieAlgebra_iff {X : unitaryLieAlgebra ι} :
    (X : Matrix ι ι ℂ) ∈ specialUnitaryLieAlgebra ι ↔
      X ∈ LieAlgebra.derivedSeries ℝ (unitaryLieAlgebra ι) 1 := by
  rw [mem_derivedSeries_one_unitaryLieAlgebra_iff]
  exact and_iff_right X.property

/-- **A matrix commuting with `𝔰𝔲(n)` is scalar.** For `i ≠ j` the matrix unit `E_ij` is
`(A - I • B) / 2` with `A = E_ij - E_ji` and `B = I • (E_ij + E_ji)` in `𝔰𝔲(n)`. -/
theorem mem_range_scalar_of_forall_mem_specialUnitaryLieAlgebra_commute {M : Matrix ι ι ℂ}
    (h : ∀ X ∈ specialUnitaryLieAlgebra ι, Commute X M) : M ∈ Set.range (scalar ι) := by
  refine mem_range_scalar_of_commute_single fun i j hij ↦ ?_
  have hA : single i j (1 : ℂ) - single j i 1 ∈ specialUnitaryLieAlgebra ι := by
    simp [conjTranspose_sub, trace_single_eq_of_ne _ _ _ hij, trace_single_eq_of_ne _ _ _ hij.symm]
  have hB : I • (single i j (1 : ℂ) + single j i 1) ∈ specialUnitaryLieAlgebra ι := by
    rw [mem_specialUnitaryLieAlgebra_iff, conjTranspose_smul, conjTranspose_add,
      conjTranspose_single, conjTranspose_single, trace_smul, trace_add,
      trace_single_eq_of_ne _ _ _ hij, trace_single_eq_of_ne _ _ _ hij.symm]
    simp [add_comm]
  have hE : single i j (1 : ℂ) =
      (2⁻¹ : ℂ) • ((single i j 1 - single j i 1) - I • I • (single i j 1 + single j i 1)) := by
    rw [smul_smul, I_mul_I]
    module
  dsimp only
  rw [hE]
  exact ((h _ hA).sub_left ((h _ hB).smul_left I)).smul_left _

instance : FiniteDimensional ℝ (specialUnitaryLieAlgebra ι) :=
  Module.Finite.of_injective (specialUnitaryLieAlgebra ι).toSubmodule.subtype
    Subtype.val_injective

/-- The imaginary part of the trace on `𝔲(n)`; its kernel is `𝔰𝔲(n)`. -/
private def imTrace : unitaryLieAlgebra ι →ₗ[ℝ] ℝ where
  toFun X := (X : Matrix ι ι ℂ).trace.im
  map_add' X Y := by simp
  map_smul' c X := by simp

private theorem imTrace_apply (X : unitaryLieAlgebra ι) :
    imTrace X = (X : Matrix ι ι ℂ).trace.im :=
  (rfl)

/-- `𝔰𝔲(n)` is the kernel of the imaginary part of the trace on `𝔲(n)`. -/
private def specialUnitaryLieAlgebraEquivKer :
    specialUnitaryLieAlgebra ι ≃ₗ[ℝ] LinearMap.ker (imTrace (ι := ι)) where
  toFun X := ⟨⟨X, specialUnitaryLieAlgebra_le X.property⟩, by simp [imTrace_apply]⟩
  invFun X := ⟨X.val, X.val.property, Complex.ext (re_trace_coe_unitaryLieAlgebra X.val)
    (by rw [← imTrace_apply]; exact LinearMap.mem_ker.mp X.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (ι) in
/-- **`𝔰𝔲(n)` has real dimension `n² - 1`.** For `n = 0` both sides vanish. -/
theorem finrank_specialUnitaryLieAlgebra :
    finrank ℝ (specialUnitaryLieAlgebra ι) = Fintype.card ι * Fintype.card ι - 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · rw [Fintype.card_eq_zero, finrank_zero_iff.mpr inferInstance]
  have hsurj : Function.Surjective (imTrace (ι := ι)) := fun t ↦ by
    refine ⟨⟨single i i ((t : ℂ) * I), ?_⟩, ?_⟩
    · have h : star ((t : ℂ) * I) = -((t : ℂ) * I) := by simp
      rw [mem_unitaryLieAlgebra_iff, conjTranspose_single, h]
      exact map_neg (singleAddMonoidHom i i) _
    · simp [imTrace_apply]
  have h := LinearMap.finrank_range_add_finrank_ker (imTrace (ι := ι))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self, finrank_unitaryLieAlgebra,
    ← specialUnitaryLieAlgebraEquivKer.finrank_eq] at h
  omega

/-! ### The adjoint representation -/

variable (ι) in
/-- The **adjoint representation** of `U(n)` on `𝔰𝔲(n)`, by conjugation `Ad_U X = U X Uᴴ`.
Restricted to `SU(n)` it is the adjoint representation of `SU(n)`. -/
def specialUnitaryAdjointRepresentation :
    Representation ℝ (unitaryGroup ι ℂ) (specialUnitaryLieAlgebra ι) where
  toFun U :=
    { toFun X := ⟨U * X * star (U : Matrix ι ι ℂ),
        ⟨by simpa only [coe_unitaryAdjointRepresentation_apply] using
            (unitaryAdjointRepresentation ι U ⟨X, specialUnitaryLieAlgebra_le X.property⟩).property,
          by rw [trace_mul_cycle, Unitary.star_mul_self_of_mem U.property, Matrix.one_mul,
            trace_coe_specialUnitaryLieAlgebra]⟩⟩
      map_add' X Y := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
      map_smul' c X := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun X ↦ Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun X ↦ Subtype.ext (by simp [Matrix.mul_assoc])

@[simp]
theorem coe_specialUnitaryAdjointRepresentation_apply (U : unitaryGroup ι ℂ)
    (X : specialUnitaryLieAlgebra ι) :
    (specialUnitaryAdjointRepresentation ι U X : Matrix ι ι ℂ) = U * X * star (U : Matrix ι ι ℂ) :=
  (rfl)

/-- **The adjoint action on `𝔰𝔲(n)` is by Lie algebra automorphisms.** -/
theorem specialUnitaryAdjointRepresentation_lie (U : unitaryGroup ι ℂ)
    (X Y : specialUnitaryLieAlgebra ι) :
    specialUnitaryAdjointRepresentation ι U ⁅X, Y⁆ =
      ⁅specialUnitaryAdjointRepresentation ι U X, specialUnitaryAdjointRepresentation ι U Y⁆ := by
  have h := congrArg Subtype.val <| unitaryAdjointRepresentation_lie U
    ⟨X, specialUnitaryLieAlgebra_le X.property⟩ ⟨Y, specialUnitaryLieAlgebra_le Y.property⟩
  ext1
  simpa only [coe_specialUnitaryAdjointRepresentation_apply, LieSubalgebra.coe_bracket,
    coe_unitaryAdjointRepresentation_apply] using h

end TauCeti
