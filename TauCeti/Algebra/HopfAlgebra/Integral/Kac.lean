/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral.ModularAutomorphism
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Schur
import TauCeti.Algebra.Coalgebra.Comodule.Unitary.SchurOrthogonality
import TauCeti.Algebra.HopfAlgebra.Integral.CompactType
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# The Kac equivalence for algebraic Haar functionals

Let `h` be an algebraic Haar functional (`TauCeti.AlgebraicHaar`) on a complex Hopf star algebra
`A`. Then `h` is a trace, `h (a * b) = h (b * a)`, exactly when the antipode `S` is involutive,
`S (S a) = a` (`TauCeti.haar_trace_iff_antipode_involutive`). Compact quantum groups with these
properties are said to be of Kac type; the classical example is the algebra of representative
functions on a compact group, where `h` is the Haar integral and `S f (g) = f (g⁻¹)`.

Both conditions are detected on the coefficient matrix `u` of a simple comodule, in a basis where
`u` is unitary, by the normalized unitarizing matrix `Ft` of weighted Schur orthogonality:

* `Ft` transposed intertwines `u` with `S² u`, so by Schur's lemma `S² u = u` exactly when `Ft` is a
  scalar matrix, and the normalization `Tr Ft = Tr Ft⁻¹` makes this scalar one
  (`TauCeti.AlgebraicHaar.unitarizingMatrix_eq_one_iff`);
* if `h` is a trace then comparing the two Schur orthogonality relations forces `Ft = 1`
  (`TauCeti.AlgebraicHaar.unitarizingMatrix_eq_one_of_apply_mul_comm`), and conversely `Ft = 1`
  makes the modular automorphism `θ(u) = Ftᵀ u Ftᵀ` trivial on `u`.

Since the coefficient spaces of simple comodules span `A`, these block statements give the
equivalence.

## Main declarations

* `TauCeti.AlgebraicHaar.unitarizingMatrix_eq_one_iff`: on a unitary coefficient matrix `u` of a
  simple comodule, `Ft = 1` if and only if `S² u = u`.
* `TauCeti.AlgebraicHaar.unitarizingMatrix_eq_one_of_apply_mul_comm`: if `h` is a trace, then
  `Ft = 1` on every unitary coefficient matrix of a simple comodule.
* `TauCeti.haar_trace_iff_antipode_involutive`: the Kac equivalence.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Proposition 1.7.7.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
-/

public section

open Module Matrix TauCeti.Comodule
open scoped ComplexOrder

namespace TauCeti

universe u

variable {A : Type u} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A] [StarCoalgebra ℂ A]

namespace AlgebraicHaar

variable (h : AlgebraicHaar A)

section CoefficientMatrix

variable {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]

omit [StarCoalgebra ℂ A] in
/-- A normalized unitarizing matrix which is a scalar matrix is the identity. -/
private theorem unitarizingMatrix_eq_one_of_eq_smul (b : Basis ι ℂ M) {c : ℂ}
    (hc : unitarizingMatrix h.toLinearMap b = c • 1) : unitarizingMatrix h.toLinearMap b = 1 :=
  Matrix.PosDef.eq_of_eq_smul_of_trace_eq_trace_inv (h.posDef_unitarizingMatrix b)
    Matrix.PosDef.one hc (h.trace_unitarizingMatrix_eq_trace_inv b) (by simp)

variable [IsSimpleOrder (Subcomodule ℂ A M)]

/-- On the unitary coefficient matrix `u` of a simple comodule, the normalized unitarizing matrix
`Ft` is the identity if and only if the square of the antipode fixes `u`. -/
theorem unitarizingMatrix_eq_one_iff (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    unitarizingMatrix h.toLinearMap b = 1 ↔
      ((coefficientMatrix (C := A) b).map (HopfAlgebra.antipode ℂ)).map
        (HopfAlgebra.antipode ℂ) = coefficientMatrix (C := A) b := by
  -- `S² u * Ftᵀ = Ftᵀ * u`.
  have hint := b.map_antipode_map_antipode_mul_transpose_of_conjTranspose_map_star_mul_mul_eq hu
    (conjTranspose_map_star_mul_unitarizingMatrix_mul h.isRightInvariantIntegral b hu)
  refine ⟨fun hF ↦ by simpa [hF] using hint, fun hS ↦ ?_⟩
  rw [hS] at hint
  obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_commute_coefficientMatrix _ hint
  exact h.unitarizingMatrix_eq_one_of_eq_smul b (c := c) <| by
    simpa using congrArg Matrix.transpose hc

/-- If an algebraic Haar functional is a trace, then the normalized unitarizing matrix of every
unitary coefficient matrix of a simple comodule is the identity. -/
theorem unitarizingMatrix_eq_one_of_apply_mul_comm (H : ∀ a b : A, h (a * b) = h (b * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    unitarizingMatrix h.toLinearMap b = 1 := by
  have : Nontrivial M := (Subcomodule.nontrivial_iff (R := ℂ) (C := A)).mp inferInstance
  have : Nonempty ι := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set Ft := unitarizingMatrix h.toLinearMap b with hFt_def
  have htr : Ft⁻¹.trace = Ft.trace := (h.trace_unitarizingMatrix_eq_trace_inv b).symm
  have htr0 : Ft.trace ≠ 0 := (h.posDef_unitarizingMatrix b).trace_pos.ne'
  refine h.unitarizingMatrix_eq_one_of_eq_smul b (c := Ft⁻¹ i₀ i₀) (Matrix.ext fun j l ↦ ?_)
  -- Compare `h (u i₀ j * star (u i₀ l))` and `h (star (u i₀ l) * u i₀ j)` by Schur orthogonality.
  have hjl := H (coefficientMatrix (C := A) b i₀ j) (star (coefficientMatrix (C := A) b i₀ l))
  simp only [h.apply_coefficientMatrix_mul_star b hu, h.apply_star_mul_coefficientMatrix b hu,
    ← hFt_def, htr, ite_true] at hjl
  have hjl' : Ft j l = if l = j then Ft⁻¹ i₀ i₀ else 0 := by
    rw [← div_left_inj₀ htr0, hjl, ite_div, zero_div]
  rw [← hFt_def, hjl', Matrix.smul_apply, Matrix.one_apply]
  rcases eq_or_ne j l with rfl | hne
  · simp
  · simp [hne, hne.symm]

end CoefficientMatrix

end AlgebraicHaar

open AlgebraicHaar in
/-- **The Kac equivalence.** An algebraic Haar functional `h` on a complex Hopf star algebra is a
trace, `h (a * b) = h (b * a)`, if and only if the antipode is involutive. -/
theorem haar_trace_iff_antipode_involutive (h : AlgebraicHaar A) :
    (∀ a b : A, h (a * b) = h (b * a)) ↔
      Function.Involutive (HopfAlgebra.antipode ℂ : A → A) := by
  refine ⟨fun H a ↦ ?_, fun HS ↦ h.modularAut_eq_refl_iff.mp ?_⟩
  · -- A trace has `Ft = 1` on every block, so `S²` fixes every unitary coefficient.
    refine LinearMap.congr_fun (h.linearMap_ext
      (f := HopfAlgebra.antipode ℂ ∘ₗ HopfAlgebra.antipode ℂ) (g := LinearMap.id)
      fun M _ _ _ _ b hb i j ↦ ?_) a
    have := (h.unitarizingMatrix_eq_one_iff b hb).mp
      (h.unitarizingMatrix_eq_one_of_apply_mul_comm H b hb)
    simpa using congrFun (congrFun this i) j
  · -- An involutive antipode has `Ft = 1` on every block, so `θ(u) = Ftᵀ u Ftᵀ = u`.
    refine AlgEquiv.toLinearMap_injective (h.linearMap_ext fun M _ _ _ _ b hb i j ↦ ?_)
    have hF := (h.unitarizingMatrix_eq_one_iff b hb).mpr (Matrix.ext fun i j ↦ HS _)
    simpa [hF] using congrFun (congrFun (h.map_modularAut_coefficientMatrix b hb) i) j

end TauCeti
