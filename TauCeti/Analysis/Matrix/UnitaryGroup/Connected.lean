/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus

/-!
# Hermitian logarithms and connectedness of the complex unitary group

Every complex unitary matrix is `exp (I • H)` for a Hermitian matrix `H`.
Diagonalization reduces this to choosing a real phase for each eigenvalue on the circle.
This is an existence theorem for each matrix; it does not choose a globally continuous logarithm.

The existing map `selfAdjoint.expUnitary` is therefore surjective on complex matrices.
Its continuity and the path connectedness of the real vector space of Hermitian matrices give
`PathConnectedSpace (Matrix.unitaryGroup n ℂ)`, and hence connectedness. No nonemptiness
assumption on the finite index type is needed.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer GTM 222, 2015, Chapter 1 (the classical matrix groups).
-/

public section

noncomputable section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every complex unitary matrix is the exponential of `I` times a Hermitian matrix,
using Mathlib's exponential map from selfadjoint elements to unitary elements. -/
theorem exists_expUnitary_eq (g : unitaryGroup n ℂ) :
    ∃ H : selfAdjoint (Matrix n n ℂ), selfAdjoint.expUnitary H = g := by
  obtain ⟨z, hz⟩ := TauCeti.exists_isConj_unitaryTorusHom g
  obtain ⟨u, hu⟩ := isConj_iff.mp hz.symm
  choose θ hθ using fun i => Circle.exp_surjective (z i)
  let D : Matrix n n ℂ := diagonal fun i => (θ i : ℂ)
  have hD : D.IsHermitian := by
    exact isHermitian_diagonal_iff.mpr fun i => by
      simp [IsSelfAdjoint]
  let H : selfAdjoint (Matrix n n ℂ) :=
    ⟨(u : Matrix n n ℂ) * D * star (u : Matrix n n ℂ),
      (isHermitian_mul_mul_conjTranspose (u : Matrix n n ℂ) hD).isSelfAdjoint⟩
  refine ⟨H, Subtype.ext ?_⟩
  have hexp : exp (Complex.I • D) = (TauCeti.unitaryTorusHom n z : Matrix n n ℂ) := by
    rw [← diagonal_smul, exp_diagonal, TauCeti.coe_unitaryTorusHom]
    apply congrArg diagonal
    funext i
    simpa only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ, Circle.coe_exp,
      mul_comm] using congrArg (fun w : Circle => (w : ℂ)) (hθ i)
  have hconj : exp ((u : Matrix n n ℂ) * (Complex.I • D) * star (u : Matrix n n ℂ)) =
      (u : Matrix n n ℂ) * exp (Complex.I • D) * star (u : Matrix n n ℂ) := by
    simpa only [← map_inv, Unitary.val_toUnits_apply, ← Unitary.star_eq_inv,
      Unitary.coe_star] using Matrix.exp_units_conj (Unitary.toUnits u) (Complex.I • D)
  have hu' : (u : Matrix n n ℂ) * (TauCeti.unitaryTorusHom n z : Matrix n n ℂ) *
      star (u : Matrix n n ℂ) = (g : Matrix n n ℂ) := by
    simpa only [Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star] using
      congrArg Subtype.val hu
  rw [hexp, hu'] at hconj
  simpa only [selfAdjoint.expUnitary_coe, H, smul_mul_assoc, mul_smul_comm] using hconj

/-- The complex unitary matrix group is path connected, including in dimension zero. -/
instance instPathConnectedSpace : PathConnectedSpace (unitaryGroup n ℂ) :=
  Function.Surjective.pathConnectedSpace (fun g => exists_expUnitary_eq g)
    selfAdjoint.continuous_expUnitary

end Matrix.UnitaryGroup
