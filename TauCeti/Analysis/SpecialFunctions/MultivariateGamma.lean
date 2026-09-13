/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The multivariate Gamma function

The multivariate Gamma function of dimension `p` is

`Γ_p(a) = π ^ (p * (p - 1) / 4) * ∏_{i < p} Γ(a - i / 2)`.

It is the normalizing constant of the Wishart density, because for `(p - 1) / 2 < a` it is the
integral of `(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the cone of positive-definite
symmetric `p × p` matrices, taken against `TauCeti.symmetricLebesgue p`. The normalization of
that reference measure is part of the identity, not a convention that can be changed afterwards.
`TauCeti.integral_posDef_multivariateGamma_zero` records the identity in dimension zero, where
the symmetric matrices form a single point and both sides are `1`.

The exponent of `π` is real, not the truncated natural-number quotient `p * (p - 1) / 4`, and so
is the shift `i / 2` in each Gamma factor; `Γ_p` interpolates the classical constants in half
steps. Outside the range `(p - 1) / 2 < a` the definition still makes sense and takes the value
`0` exactly when some factor sits at a pole of `Γ`
(`TauCeti.multivariateGamma_eq_zero_iff`), which is the behaviour the totalized Wishart laws
inherit.

## Main definitions

* `TauCeti.multivariateGamma` — the multivariate Gamma function.

## Main results

* `TauCeti.multivariateGamma_add` — the dimensions add,
  `Γ_{p + q}(a) = π ^ (p * q / 2) * Γ_p(a) * Γ_q(a - p / 2)`, with the classical one-step
  recursion `TauCeti.multivariateGamma_succ` as a special case;
* `TauCeti.multivariateGamma_one` — dimension one recovers `Real.Gamma`;
* `TauCeti.multivariateGamma_pos` — positivity on the classical range `(p - 1) / 2 < a`;
* `TauCeti.multivariateGamma_eq_zero_iff` — the vanishing locus outside that range;
* `TauCeti.measurable_multivariateGamma` — measurability in the parameter, as the parameter
  measurability of the Wishart laws needs;
* `TauCeti.integral_posDef_multivariateGamma_zero` — the cone integral in dimension zero.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Chapter 5.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Section 2.1.
-/

public section

noncomputable section

open MeasureTheory Real

namespace TauCeti

/-- The **multivariate Gamma function** of dimension `p`,
`Γ_p(a) = π ^ (p * (p - 1) / 4) * ∏_{i < p} Γ(a - i / 2)`. Both the exponent of `π` and the
shifts of the Gamma factors are real, so this is not the truncated natural-number quotient. -/
def multivariateGamma (p : ℕ) (a : ℝ) : ℝ :=
  π ^ (((p : ℝ) * ((p : ℝ) - 1)) / 4) * ∏ i : Fin p, Real.Gamma (a - (i.1 : ℝ) / 2)

/-- The defining formula of the multivariate Gamma function. -/
theorem multivariateGamma_def (p : ℕ) (a : ℝ) :
    multivariateGamma p a =
      π ^ (((p : ℝ) * ((p : ℝ) - 1)) / 4) * ∏ i : Fin p, Real.Gamma (a - (i.1 : ℝ) / 2) := (rfl)

/-- In dimension zero there are no Gamma factors and the constant is `1`. -/
@[simp]
theorem multivariateGamma_zero (a : ℝ) : multivariateGamma 0 a = 1 := by
  simp [multivariateGamma_def]

/-- In dimension one the multivariate Gamma function is Euler's. -/
@[simp]
theorem multivariateGamma_one (a : ℝ) : multivariateGamma 1 a = Real.Gamma a := by
  simp [multivariateGamma_def]

/-- Splitting the dimension: the first `p` Gamma factors assemble into `Γ_p(a)` and the last `q`
into `Γ_q(a - p / 2)`, at the cost of the cross term `π ^ (p * q / 2)` in the exponent. -/
theorem multivariateGamma_add (p q : ℕ) (a : ℝ) :
    multivariateGamma (p + q) a = π ^ ((p : ℝ) * (q : ℝ) / 2) *
      multivariateGamma p a * multivariateGamma q (a - (p : ℝ) / 2) := by
  have hprod : (∏ i : Fin (p + q), Real.Gamma (a - (i.1 : ℝ) / 2)) =
      (∏ i : Fin p, Real.Gamma (a - (i.1 : ℝ) / 2)) *
        ∏ j : Fin q, Real.Gamma (a - (p : ℝ) / 2 - (j.1 : ℝ) / 2) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring
  have hexp : ((p + q : ℕ) : ℝ) * (((p + q : ℕ) : ℝ) - 1) / 4 =
      (p : ℝ) * (q : ℝ) / 2 + ((p : ℝ) * ((p : ℝ) - 1) / 4 + (q : ℝ) * ((q : ℝ) - 1) / 4) := by
    push_cast
    ring
  rw [multivariateGamma_def, multivariateGamma_def, multivariateGamma_def, hprod, hexp,
    Real.rpow_add pi_pos, Real.rpow_add pi_pos]
  ring

/-- The classical one-step recursion of the multivariate Gamma function. -/
theorem multivariateGamma_succ (p : ℕ) (a : ℝ) :
    multivariateGamma (p + 1) a =
      π ^ ((p : ℝ) / 2) * multivariateGamma p a * Real.Gamma (a - (p : ℝ) / 2) := by
  rw [multivariateGamma_add, multivariateGamma_one]
  norm_num

/-- On the classical range of the shape parameter every Gamma factor is evaluated to the right of
its rightmost pole, so `Γ_p(a)` is positive. This is the range on which it normalizes a Wishart
density. -/
theorem multivariateGamma_pos {p : ℕ} {a : ℝ} (ha : ((p : ℝ) - 1) / 2 < a) :
    0 < multivariateGamma p a := by
  rw [multivariateGamma_def]
  refine mul_pos (rpow_pos_of_pos pi_pos _) (Finset.prod_pos fun i _ => Gamma_pos_of_pos ?_)
  have hi : (i.1 : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast i.2
  linarith

/-- `Γ_p` does not vanish on the classical range of its shape parameter. -/
theorem multivariateGamma_ne_zero {p : ℕ} {a : ℝ} (ha : ((p : ℝ) - 1) / 2 < a) :
    multivariateGamma p a ≠ 0 :=
  (multivariateGamma_pos ha).ne'

/-- Off the classical range, `Γ_p(a)` vanishes exactly when one of its Gamma factors sits at a
pole, that is, when `a - i / 2` is a nonpositive integer for some `i < p`. -/
theorem multivariateGamma_eq_zero_iff (p : ℕ) (a : ℝ) :
    multivariateGamma p a = 0 ↔ ∃ i : Fin p, ∃ m : ℕ, a - (i.1 : ℝ) / 2 = -m := by
  rw [multivariateGamma_def, mul_eq_zero,
    or_iff_right (rpow_pos_of_pos pi_pos _).ne', Finset.prod_eq_zero_iff]
  simp [Real.Gamma_eq_zero_iff]

/-- `Γ_p` is Borel measurable in its shape parameter, including at the poles of its factors. The
Wishart laws need this to be measurable in their degree parameter. -/
@[fun_prop]
theorem measurable_multivariateGamma (p : ℕ) : Measurable (multivariateGamma p) := by
  have hfun : multivariateGamma p = fun a => π ^ (((p : ℝ) * ((p : ℝ) - 1)) / 4) *
      ∏ i : Fin p, Real.Gamma (a - (i.1 : ℝ) / 2) := funext (multivariateGamma_def p)
  rw [hfun]
  exact measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    Real.measurable_Gamma.comp (measurable_id.sub_const _))

/-- The cone integral that characterizes `Γ_p`, in dimension zero: the symmetric `0 × 0` matrices
form a single point, which is positive definite and has determinant `1` and trace `0`, and
`symmetricLebesgue 0` is the Dirac measure there. Both sides are `1`, so unlike the
positive-dimensional identity this one needs no hypothesis on the shape parameter. -/
theorem integral_posDef_multivariateGamma_zero (a : ℝ) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
        (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef},
      (A : Matrix (Fin 0) (Fin 0) ℝ).det ^ (a - 1 / 2) *
        exp (-(A : Matrix (Fin 0) (Fin 0) ℝ).trace) ∂symmetricLebesgue 0 =
      multivariateGamma 0 a := by
  have hset : {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
      (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef} = Set.univ :=
    Set.eq_univ_of_forall fun A =>
      ⟨selfAdjoint.isHermitian_coe A, fun x hx => absurd (by ext i; exact i.elim0) hx⟩
  rw [hset, Measure.restrict_univ, symmetricLebesgue_zero, integral_dirac]
  simp [Matrix.det_fin_zero]

end TauCeti
