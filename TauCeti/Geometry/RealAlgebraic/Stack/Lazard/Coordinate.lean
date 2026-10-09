/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic

/-!
# Lazard delineation of the distinguished coordinate

Every nonzero constant multiple of the last coordinate polynomial has one constant root section,
at zero, over every nonempty base. Its Lazard evaluation in the base variables is the corresponding
constant multiple of the univariate polynomial `X`: no base power is removed, and its root has
multiplicity one. This supplies the exceptional coordinate factor in Lazard lifting, for which the
usual nonzero-trailing-coefficient preparation does not apply.

## Main result

* `TauCeti.lazardDelineationCMulLastCoordinate`: the one-section Lazard delineation of a
  nonzero constant multiple of the last coordinate polynomial.
* `TauCeti.nonempty_lazardDelineation_lastCoordinate`: the specialization to the monic coordinate.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 5.
-/

public section

open MvPolynomial Polynomial Set

namespace TauCeti

variable {n : ℕ} {S : Set (Fin n → ℝ)}

private theorem optionEquivRight_C_mul_lastCoordinate (a : ℝ) :
    optionEquivRight ℝ (Fin n)
        (rename finSuccEquivLast (MvPolynomial.C a * X (Fin.last n))) =
      MvPolynomial.C (Polynomial.C a * Polynomial.X) := by
  simp

/-- A nonzero constant multiple of the distinguished (last) coordinate polynomial has the
constant root section zero as its Lazard delineation over every nonempty base. No base-variable
powers are removed, and the root has multiplicity one. This includes every associate of the
coordinate polynomial over `ℝ`. -/
noncomputable def lazardDelineationCMulLastCoordinate (hS : S.Nonempty) {a : ℝ} (ha : a ≠ 0) :
    LazardDelineation (fun _ : Unit ↦ MvPolynomial.C a * X (Fin.last n)) S :=
    { nonempty := hS
      count := 1
      root := fun _ _ ↦ 0
      continuous_root := fun _ ↦ continuous_const
      strictMono_root := fun _ ↦ Fin.strictMono_iff_lt_succ.mpr fun i ↦ Fin.elim0 i
      exponent := fun _ ↦ 0
      lazardExponent_eq := by
        intro _ x
        rw [optionEquivRight_C_mul_lastCoordinate]
        exact lazardExponent_eq_zero_of_eval_ne_zero (by simp [ha])
      multiplicity := fun _ _ ↦ 1
      rootMultiplicity_root := by
        intro _ _ x
        rw [optionEquivRight_C_mul_lastCoordinate]
        rw [MvPolynomial.lazardEval_C]
        rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr ha)
          Polynomial.X_ne_zero), Polynomial.rootMultiplicity_C, zero_add]
        simpa only [map_zero, sub_zero] using
          (Polynomial.rootMultiplicity_X_sub_C_self (R := ℝ) (x := 0))
      exists_root_eq := by
        intro _ x _ t ht
        rw [optionEquivRight_C_mul_lastCoordinate] at ht
        rw [MvPolynomial.lazardEval_C] at ht
        refine ⟨0, ?_⟩
        have hat : a * t = 0 := by
          simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using ht.eq_zero
        exact ((mul_eq_zero.mp hat).resolve_left ha).symm
      exists_multiplicity_pos := by
        intro _
        exact ⟨(), by simp⟩ }

@[simp]
theorem lazardDelineationCMulLastCoordinate_count (hS : S.Nonempty) {a : ℝ} (ha : a ≠ 0) :
    (lazardDelineationCMulLastCoordinate hS ha).count = 1 := (rfl)

@[simp]
theorem lazardDelineationCMulLastCoordinate_root (hS : S.Nonempty) {a : ℝ} (ha : a ≠ 0)
    (i : Fin (lazardDelineationCMulLastCoordinate hS ha).count) (x : S) :
    (lazardDelineationCMulLastCoordinate hS ha).root i x = 0 := (rfl)

@[simp]
theorem lazardDelineationCMulLastCoordinate_exponent (hS : S.Nonempty) {a : ℝ}
    (ha : a ≠ 0) (k : Unit) :
    (lazardDelineationCMulLastCoordinate hS ha).exponent k = 0 := (rfl)

@[simp]
theorem lazardDelineationCMulLastCoordinate_multiplicity (hS : S.Nonempty) {a : ℝ}
    (ha : a ≠ 0) (k : Unit) (i : Fin (lazardDelineationCMulLastCoordinate hS ha).count) :
    (lazardDelineationCMulLastCoordinate hS ha).multiplicity k i = 1 := (rfl)

/-- The distinguished coordinate itself has the constant root section zero over every nonempty
base. -/
theorem nonempty_lazardDelineation_lastCoordinate (hS : S.Nonempty) :
    Nonempty (LazardDelineation (fun _ : Unit ↦ X (Fin.last n)) S) := by
  simpa only [map_one, one_mul] using
    Nonempty.intro (lazardDelineationCMulLastCoordinate hS one_ne_zero)

end TauCeti
