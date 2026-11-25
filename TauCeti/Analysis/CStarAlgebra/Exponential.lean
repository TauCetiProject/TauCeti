/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Star.StarProjection
import TauCeti.Algebra.Star.Projection.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Exponential unitaries and projections

Let `A` be a complete normed complex algebra with a continuous star structure and `h` a
self-adjoint element of `A`. The adjoint of the unitary `selfAdjoint.expUnitary h` is
`expUnitary (-h)`, `selfAdjoint.star_expUnitary`, whose underlying element is `exp (-(I • h))`.

Using `IsIdempotentElem.exp_smul` from `TauCeti.Analysis.Normed.Algebra.Exponential`, we evaluate
the exponential unitary of a real multiple of a star projection
(`IsStarProjection.coe_expUnitary_smul`, `.coe_expUnitary_pi_smul`), express every self-adjoint
unitary as an exponential unitary (`Unitary.expUnitary_pi_half_one_sub`), and connect every
self-adjoint unitary in a unital C⋆-algebra to `1` by an explicit exponential path
(`Unitary.expUnitaryPathOfIsSelfAdjoint`).

## Main declarations

* `selfAdjoint.star_expUnitary`: the adjoint of `expUnitary`.
* `IsStarProjection.coe_expUnitary_smul`, `IsStarProjection.coe_expUnitary_pi_smul`: evaluating
  `expUnitary` on a real multiple of a star projection.
* `Unitary.expUnitary_pi_half_one_sub`: expressing a self-adjoint unitary as `expUnitary`.
* `Unitary.expUnitaryPathOfIsSelfAdjoint`, `Unitary.coe_expUnitaryPathOfIsSelfAdjoint_apply`:
  explicit exponential path from `1` to a self-adjoint unitary in a unital C⋆-algebra.

## References

* Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
  Section 2.5.3, for the one-parameter group `t ↦ exp (ith)` of a self-adjoint element.
-/

public section

noncomputable section

open scoped Nat Real unitInterval

namespace selfAdjoint

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The adjoint of `expUnitary` is `expUnitary` of the negative. -/
@[simp]
theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

end selfAdjoint

/-- The exponential unitary `expUnitary ((t : ℂ) • r)` of a real multiple of a star projection `r`
evaluates to `1 + (Complex.exp (Complex.I * t) - 1) • r`. -/
theorem IsStarProjection.coe_expUnitary_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    {r : A} (hr : IsStarProjection r) (t : ℝ) :
    ((selfAdjoint.expUnitary ⟨(t : ℂ) • r,
        IsSelfAdjoint.smul (Complex.conj_ofReal t) hr.isSelfAdjoint⟩ : unitary A) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • r := by
  simp only [selfAdjoint.expUnitary_coe]
  rw [smul_smul, hr.isIdempotentElem.exp_smul, Complex.exp_eq_exp_ℂ]

/-- Evaluating `expUnitary ((π : ℂ) • r)` for a star projection `r` gives `1 - (2 : ℂ) • r`. -/
theorem IsStarProjection.coe_expUnitary_pi_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    {r : A} (hr : IsStarProjection r) :
    ((selfAdjoint.expUnitary ⟨(π : ℂ) • r,
        IsSelfAdjoint.smul (Complex.conj_ofReal π) hr.isSelfAdjoint⟩ : unitary A) :
        A) = 1 - (2 : ℂ) • r := by
  rw [hr.coe_expUnitary_smul π, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]
  norm_num [sub_eq_add_neg]

/-- Every self-adjoint unitary `u` equals `selfAdjoint.expUnitary ⟨(π : ℂ) • r, _⟩` for
`r = (2 : ℂ)⁻¹ • (1 - u)`. -/
theorem Unitary.expUnitary_pi_half_one_sub {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) :
    selfAdjoint.expUnitary ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))),
        IsSelfAdjoint.smul (Complex.conj_ofReal π)
          (IsSelfAdjoint.smul (by simp : IsSelfAdjoint ((2 : ℂ)⁻¹))
            ((IsSelfAdjoint.one A).sub hu))⟩ = u := by
  have hu2 : (u : A) * (u : A) = 1 := by
    simpa [hu.star_eq] using Unitary.star_mul_self_of_mem u.property
  apply Subtype.ext
  rw [(IsStarProjection.half_one_sub_of_mul_self_eq_one hu2 hu).coe_expUnitary_pi_smul, smul_smul]
  norm_num

/-- Explicit continuous exponential path in `unitary A` from `1` to a self-adjoint unitary `u`. -/
def Unitary.expUnitaryPathOfIsSelfAdjoint {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) :
    Path (1 : unitary A) u :=
  (selfAdjoint.expUnitaryPathToOne
    ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))),
      IsSelfAdjoint.smul (Complex.conj_ofReal π)
        (IsSelfAdjoint.smul (by simp : IsSelfAdjoint ((2 : ℂ)⁻¹))
          ((IsSelfAdjoint.one A).sub hu))⟩).cast rfl
    (Unitary.expUnitary_pi_half_one_sub u hu).symm

/-- Pointwise exponential formula for `Unitary.expUnitaryPathOfIsSelfAdjoint`. -/
@[simp]
theorem Unitary.expUnitaryPathOfIsSelfAdjoint_apply {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) (t : I) :
    Unitary.expUnitaryPathOfIsSelfAdjoint u hu t =
      selfAdjoint.expUnitary ((t : ℝ) •
        ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))),
          IsSelfAdjoint.smul (Complex.conj_ofReal π)
            (IsSelfAdjoint.smul (by simp : IsSelfAdjoint ((2 : ℂ)⁻¹))
              ((IsSelfAdjoint.one A).sub hu))⟩) :=
  (rfl)

/-- Closed-form formula for `Unitary.expUnitaryPathOfIsSelfAdjoint` at parameter `t : I`. -/
theorem Unitary.coe_expUnitaryPathOfIsSelfAdjoint_apply {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) (t : I) :
    ((Unitary.expUnitaryPathOfIsSelfAdjoint u hu t : unitary A) : A) =
      1 + (Complex.exp (Complex.I * (((t : ℝ) * π : ℝ) : ℂ)) - 1) •
        ((2 : ℂ)⁻¹ • (1 - (u : A))) := by
  have hu_sq : (u : A) * (u : A) = 1 := by
    simpa [hu.star_eq] using Unitary.coe_star_mul_self u
  let r : A := (2 : ℂ)⁻¹ • (1 - (u : A))
  have hr : IsStarProjection r := IsStarProjection.half_one_sub_of_mul_self_eq_one hu_sq hu
  let a : selfAdjoint A :=
    ⟨(π : ℂ) • r, IsSelfAdjoint.smul (Complex.conj_ofReal π) hr.isSelfAdjoint⟩
  rw [Unitary.expUnitaryPathOfIsSelfAdjoint_apply]
  have hsub : (t : ℝ) • a =
      ⟨(((t : ℝ) * π : ℝ) : ℂ) • r,
        IsSelfAdjoint.smul (Complex.conj_ofReal ((t : ℝ) * π)) hr.isSelfAdjoint⟩ := by
    refine Subtype.ext ?_
    rw [selfAdjoint.val_smul]
    simp only [a, ← smul_assoc, Complex.real_smul, Complex.ofReal_mul]
  have hexp := congrArg (fun x : selfAdjoint A => ((selfAdjoint.expUnitary x : unitary A) : A))
    hsub
  rw [hr.coe_expUnitary_smul ((t : ℝ) * π)] at hexp
  simpa only [r, a] using hexp
