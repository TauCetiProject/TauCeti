/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Partial derivatives of entire functions on `ℂⁿ`

This file defines the partial derivative `∂ᵢ f (z) = Df(z) eᵢ` (`TauCeti.partialDeriv`) of a
function `f : ℂⁿ → ℂ` in the direction of the `i`-th coordinate vector, and develops its calculus
on entire functions.

## Main results

* `TauCeti.partialDeriv_eq_deriv_update`: `∂ᵢ f (z)` is the derivative of `f` along the line
  through `z` parallel to the `i`-th coordinate axis.
* `TauCeti.differentiable_partialDeriv`: a partial derivative of an entire function is entire.
* `TauCeti.partialDeriv_comm`: partial derivatives of an entire function commute.
* `TauCeti.partialDeriv_add`, `TauCeti.partialDeriv_const_mul`: `∂ᵢ` is linear.
-/

public section

open Function

namespace TauCeti

variable {n : ℕ}

/-- The partial derivative `∂ᵢ f (z) = Df(z) eᵢ` of a function `f : ℂⁿ → ℂ` in the direction of
the `i`-th coordinate vector. -/
noncomputable def partialDeriv (i : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z ↦ fderiv ℂ f z (Pi.single i 1)

theorem partialDeriv_def (i : Fin n) (f : (Fin n → ℂ) → ℂ) :
    partialDeriv i f = fun z ↦ fderiv ℂ f z (Pi.single i 1) := (rfl)

theorem partialDeriv_apply (i : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    partialDeriv i f z = fderiv ℂ f z (Pi.single i 1) := (rfl)

/-- The partial derivative `∂ᵢ f (z)` is the derivative of `f` restricted to the line through `z`
parallel to the `i`-th coordinate axis. -/
theorem partialDeriv_eq_deriv_update {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : Fin n) :
    partialDeriv i f z = deriv (fun s ↦ f (update z i s)) (z i) := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) (update z i (z i)) := by
    rw [update_eq_self]
    exact hf.hasFDerivAt
  have hline := (hf'.comp (z i) (hasFDerivAt_update z (i := i) (z i))).hasDerivAt
  refine (hline.deriv.trans ?_).symm
  simp only [partialDeriv_apply, ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- A partial derivative of the zero function is zero. -/
@[simp]
theorem partialDeriv_zero_fun (i : Fin n) : partialDeriv i (0 : (Fin n → ℂ) → ℂ) = 0 := by
  ext z
  simp [partialDeriv_apply, fderiv_zero]

variable {f g : (Fin n → ℂ) → ℂ}

/-- An entire function on `ℂⁿ` is `C^k` for every `k`. -/
private theorem contDiff_of_differentiable (hf : Differentiable ℂ f) {k : WithTop ℕ∞} :
    ContDiff ℂ k f :=
  contDiffOn_univ.mp (hf.differentiableOn.contDiffOn_of_finiteDimensional isOpen_univ)

/-- The derivative of an entire function on `ℂⁿ` is entire. -/
private theorem differentiable_fderiv (hf : Differentiable ℂ f) :
    Differentiable ℂ (fderiv ℂ f) :=
  ((contDiff_of_differentiable hf (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
    one_ne_zero

/-- A partial derivative of an entire function is entire. -/
theorem differentiable_partialDeriv (hf : Differentiable ℂ f) (i : Fin n) :
    Differentiable ℂ (partialDeriv i f) :=
  (differentiable_fderiv hf).clm_apply (differentiable_const _)

/-- **Partial derivatives of an entire function commute.** -/
theorem partialDeriv_comm (hf : Differentiable ℂ f) (i j : Fin n) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  have key (k l : Fin n) (z : Fin n → ℂ) : partialDeriv k (partialDeriv l f) z =
      fderiv ℂ (fderiv ℂ f) z (Pi.single k 1) (Pi.single l 1) := by
    rw [partialDeriv_apply, partialDeriv_def l f,
      fderiv_clm_apply (differentiable_fderiv hf z) (differentiableAt_const _)]
    simp
  ext z
  rw [key, key]
  exact (contDiff_of_differentiable hf (k := 2)).contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-- `∂ᵢ` is additive on entire functions. -/
theorem partialDeriv_add (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (i : Fin n) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  ext z
  simp [partialDeriv_apply, fderiv_add (hf z) (hg z)]

/-- `∂ᵢ` commutes with multiplication by a constant. -/
theorem partialDeriv_const_mul (c : ℂ) (i : Fin n) :
    partialDeriv i (fun z ↦ c * f z) = fun z ↦ c * partialDeriv i f z := by
  ext z
  rw [partialDeriv_apply, show (fun z ↦ c * f z) = c • f from rfl, fderiv_const_smul_field]
  rfl

/-! ### Iterated partial derivatives in one direction -/

/-- An iterated partial derivative of an entire function is entire. -/
theorem differentiable_iterate_partialDeriv (hf : Differentiable ℂ f) (i : Fin n) (k : ℕ) :
    Differentiable ℂ ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iterate_succ_apply']; exact differentiable_partialDeriv ih i

/-- `∂ᵢ^k` commutes with `∂ⱼ` on entire functions. -/
theorem iterate_partialDeriv_comm (hf : Differentiable ℂ f) (i j : Fin n) (k : ℕ) :
    (partialDeriv i)^[k] (partialDeriv j f) = partialDeriv j ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_comm (differentiable_iterate_partialDeriv hf i k)]

/-- `∂ᵢ^k` is additive on entire functions. -/
theorem iterate_partialDeriv_add (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (i : Fin n)
    (k : ℕ) : (partialDeriv i)^[k] (f + g) = (partialDeriv i)^[k] f + (partialDeriv i)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_add (differentiable_iterate_partialDeriv hf i k)
        (differentiable_iterate_partialDeriv hg i k)]

/-- `∂ᵢ^k` commutes with multiplication by a constant. -/
theorem iterate_partialDeriv_const_mul (c : ℂ) (i : Fin n) (k : ℕ) :
    (partialDeriv i)^[k] (fun z ↦ c * f z) = fun z ↦ c * (partialDeriv i)^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', ih, partialDeriv_const_mul]

end TauCeti
