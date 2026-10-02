/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Conductor
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Localization.NormTrace

/-!
# The index and discriminant of a number-field order

An order `O` of a number field `K` is a full-rank sublattice of the maximal order `𝓞 K`, so it has
a finite index `[𝓞 K : O]`. Its discriminant is the discriminant of any `ℤ`-basis of `O`. The
two are tied to the field discriminant by the classical formula

  `disc O = [𝓞 K : O] ^ 2 * disc K`,

which follows by expressing a basis of `O` in a basis of `𝓞 K`: the change of basis matrix has
determinant `± [𝓞 K : O]`. This is the argument of
`TauCeti.NumberField.IntegralPrimitiveElement.discr_minpoly_eq_index_sq_mul_discr` for a monogenic
order `ℤ[θ]`, run with an arbitrary `ℤ`-basis of `O` in place of a power basis.

The index annihilates `𝓞 K / O`, so it lies in the conductor of `O`. Consequently the conductor
is a nonzero ideal, and a prime of `𝓞 K` containing the conductor lies above a prime number whose
square divides `disc O`. In particular an order with squarefree discriminant is maximal.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.toRingOfIntegers`: an order as a subalgebra of the
  maximal order.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.index`: the index `[𝓞 K : O]`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.discr`: the discriminant of an order.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.discr_eq_index_sq_mul`:
  `disc O = [𝓞 K : O] ^ 2 * disc K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.natCast_index_mem_conductor`: the index lies in
  the conductor.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.conductor_ne_bot`: the conductor is nonzero.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.sq_ringChar_dvd_discr_of_conductor_le`: the
  residue characteristic of a prime containing the conductor has square dividing `disc O`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.eq_maximal_of_squarefree_discr`: an order with
  squarefree discriminant is the maximal order.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2 and §12.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- An order `O`, viewed as a `ℤ`-subalgebra of the maximal order `𝓞 K`. -/
def toRingOfIntegers : Subalgebra ℤ (𝓞 K) :=
  O.toSubalgebra.comap (IsScalarTower.toAlgHom ℤ (𝓞 K) K)

/-- An algebraic integer lies in the copy of `O` inside `𝓞 K` exactly when it lies in `O`. -/
@[simp]
theorem mem_toRingOfIntegers {x : 𝓞 K} : x ∈ O.toRingOfIntegers ↔ (x : K) ∈ O.toSubalgebra :=
  Iff.rfl

/-- The index `[𝓞 K : O]` of an order in the maximal order. -/
def index : ℕ :=
  (Subalgebra.toSubmodule O.toRingOfIntegers).cardQuot

/-- The index of an order is the cardinality of the additive quotient `𝓞 K / O`. -/
theorem index_def : O.index = Nat.card (𝓞 K ⧸ Subalgebra.toSubmodule O.toRingOfIntegers) :=
  Submodule.cardQuot_apply _

/-- The discriminant of an order: the discriminant of a `ℤ`-basis of it. By
`NumberFieldOrder.discr_eq_discr` it does not depend on the basis. -/
def discr : ℤ :=
  Algebra.discr ℤ (Module.Free.chooseBasis ℤ O.toSubalgebra)

/-- Any `ℤ`-basis of an order computes its discriminant. -/
theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ O.toSubalgebra) : Algebra.discr ℤ b = O.discr := by
  classical
  let b₀ := (Module.Free.chooseBasis ℤ O.toSubalgebra).reindex
    ((Module.Free.chooseBasis ℤ O.toSubalgebra).indexEquiv b)
  rw [Algebra.discr_eq_discr O.toSubalgebra b b₀, Module.Basis.coe_reindex,
    Algebra.discr_reindex, discr]

/-- The discriminant of an order is nonzero. -/
theorem discr_ne_zero : O.discr ≠ 0 := by
  rw [← Int.cast_ne_zero (α := ℚ), discr, ← eq_intCast (algebraMap ℤ ℚ),
    ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  exact Algebra.discr_not_zero_of_basis ℚ _

/-- An order is `ℤ`-linearly equivalent to its copy inside the maximal order. -/
private def equivToRingOfIntegers :
    O.toSubalgebra ≃ₗ[ℤ] Subalgebra.toSubmodule O.toRingOfIntegers where
  toFun x := ⟨⟨x, O.le_ringOfIntegers x.2⟩, x.2⟩
  invFun y := ⟨((y : 𝓞 K) : K), y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The index formula for discriminants.** The discriminant of an order is the square of its
index in the maximal order times the discriminant of the number field. -/
theorem discr_eq_index_sq_mul : O.discr = O.index ^ 2 * NumberField.discr K := by
  classical
  set bK := RingOfIntegers.basis K
  set bO := Module.Free.chooseBasis ℤ O.toSubalgebra
  let bO' := bO.localizationLocalization ℚ ℤ⁰ K
  -- Transport a basis of `O` into `𝓞 K`, indexed like the basis `bK` of `𝓞 K`.
  let σ := bO'.indexEquiv (integralBasis K)
  let bN := (bO.map O.equivToRingOfIntegers).reindex σ
  let v : _ → 𝓞 K := (↑) ∘ bN
  -- The change of basis determinant from `bK` to `v` is the index up to sign.
  have hidx : (bK.det v).natAbs = O.index := by
    rw [index_def]
    exact Submodule.natAbs_det_basis_change bK _ bN
  have hv : Algebra.discr ℤ v = (bK.det v) ^ 2 * NumberField.discr K := by
    have := Algebra.discr_of_matrix_vecMul bK (bK.toMatrix v)
    rwa [bK.toMatrix_map_vecMul, ← Module.Basis.det_apply] at this
  -- The discriminant of `v`, computed with traces of `𝓞 K`, is that of `O`: compare in `K`.
  have hO : O.discr = Algebra.discr ℤ v := by
    apply Int.cast_injective (α := ℚ)
    -- Traces over `ℤ` in `𝓞 K` are traces over `ℚ` in `K`.
    have htr : Algebra.discr ℚ (algebraMap (𝓞 K) K ∘ v) = Algebra.discr ℤ v := by
      rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
      congr 1
      ext i j
      simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, Function.comp_apply, ← map_mul]
      exact Algebra.trace_localization ℤ ℤ⁰ _
    rw [← htr]
    have : algebraMap (𝓞 K) K ∘ v = bO' ∘ σ.symm := by
      ext i
      simp only [v, bN, bO', Function.comp_apply, Module.Basis.reindex_apply,
        Module.Basis.map_apply, Module.Basis.localizationLocalization_apply]
      -- `equivToRingOfIntegers` keeps the underlying element of `K`, and both sides are that
      -- element.
      rfl
    rw [this, Algebra.discr_reindex, Algebra.discr_localizationLocalization, eq_intCast, discr]
  rw [hO, hv, ← hidx, Int.natCast_natAbs, sq_abs]

/-- The square of the index of an order divides its discriminant. -/
theorem sq_index_dvd_discr : (O.index : ℤ) ^ 2 ∣ O.discr :=
  O.discr_eq_index_sq_mul ▸ dvd_mul_right _ _

/-- The index of an order in the maximal order is nonzero. -/
theorem index_ne_zero : O.index ≠ 0 := by
  intro h
  apply O.discr_ne_zero
  rw [discr_eq_index_sq_mul, h]
  simp

/-- The index annihilates `𝓞 K / O`, so it lies in the conductor of `O`. -/
theorem natCast_index_mem_conductor : (O.index : 𝓞 K) ∈ O.conductor := by
  rw [mem_conductor_iff]
  intro y
  have h := (Subalgebra.toSubmodule O.toRingOfIntegers).toAddSubgroup.nsmul_index_mem y
  simpa [index, Submodule.cardQuot, nsmul_eq_mul] using h

/-- The conductor of an order is a nonzero ideal of the maximal order. -/
theorem conductor_ne_bot : O.conductor ≠ ⊥ := by
  intro h
  have hmem := O.natCast_index_mem_conductor
  rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hmem
  exact O.index_ne_zero hmem

/-- The residue characteristic of an ideal of `𝓞 K` containing the conductor divides the
index. -/
theorem ringChar_dvd_index_of_conductor_le {P : Ideal (𝓞 K)} (h : O.conductor ≤ P) :
    ringChar (𝓞 K ⧸ P) ∣ O.index :=
  ringChar.dvd <| by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact h O.natCast_index_mem_conductor

/-- The square of the residue characteristic of an ideal of `𝓞 K` containing the conductor
divides the discriminant of the order. -/
theorem sq_ringChar_dvd_discr_of_conductor_le {P : Ideal (𝓞 K)} (h : O.conductor ≤ P) :
    (ringChar (𝓞 K ⧸ P) : ℤ) ^ 2 ∣ O.discr :=
  (pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr (O.ringChar_dvd_index_of_conductor_le h))
    2).trans O.sq_index_dvd_discr

/-- An order has index one exactly when it is the maximal order. -/
theorem index_eq_one_iff : O.index = 1 ↔ O = maximalNumberFieldOrder K := by
  constructor
  · intro h
    rw [← conductor_eq_top_iff, Ideal.eq_top_iff_one]
    simpa [h] using O.natCast_index_mem_conductor
  · rintro rfl
    rw [index, Submodule.cardQuot_eq_one_iff, Algebra.toSubmodule_eq_top, eq_top_iff]
    intro x _
    rw [mem_toRingOfIntegers, maximalNumberFieldOrder_toSubalgebra]
    exact x.isIntegral_coe

/-- The maximal order has index one. -/
@[simp]
theorem index_maximal : (maximalNumberFieldOrder K).index = 1 :=
  (index_eq_one_iff _).mpr rfl

/-- The discriminant of the maximal order is the discriminant of the number field. -/
@[simp]
theorem discr_maximal : (maximalNumberFieldOrder K).discr = NumberField.discr K := by
  rw [discr_eq_index_sq_mul, index_maximal]
  simp

/-- An order has the discriminant of its number field exactly when it is the maximal order. -/
theorem discr_eq_discr_iff : O.discr = NumberField.discr K ↔ O = maximalNumberFieldOrder K := by
  rw [← index_eq_one_iff, discr_eq_index_sq_mul, mul_eq_right₀ (NumberField.discr_ne_zero K)]
  norm_cast
  simp

/-- An order whose discriminant is squarefree is the maximal order. -/
theorem eq_maximal_of_squarefree_discr (h : Squarefree O.discr) :
    O = maximalNumberFieldOrder K := by
  rw [← index_eq_one_iff]
  have hunit := h (O.index : ℤ) (by rw [← sq]; exact O.sq_index_dvd_discr)
  rwa [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit

end NumberFieldOrder

end TauCeti.GlobalNumberFields
