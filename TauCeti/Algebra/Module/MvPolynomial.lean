/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Modules over a polynomial ring on which the variables act by zero

Elementary facts about modules over a polynomial ring `A[X_σ]` on which every variable acts by
zero: a polynomial then acts through its constant coefficient, so a finitely generated module over
`A[X_σ]` is finitely generated over `A`. Such modules are the base case of inductions on the
number of variables, as in the proof of the Hilbert–Serre theorem.

## Main results

* `TauCeti.MvPolynomial.smul_eq_constantCoeff_smul`: a polynomial acts through its constant
  coefficient.
* `TauCeti.MvPolynomial.finite_of_forall_X_smul_eq_zero`: a finitely generated module on which
  all variables act by zero is finitely generated over the coefficients.
-/

public section

open MvPolynomial

namespace TauCeti.MvPolynomial

variable {σ A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
  [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]

/-- A polynomial acts through its constant coefficient on a module on which every variable acts
by zero. -/
theorem smul_eq_constantCoeff_smul
    (h : ∀ (i : σ) (m : M), (X i : MvPolynomial σ A) • m = 0) (p : MvPolynomial σ A) (m : M) :
    p • m = constantCoeff p • m := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [constantCoeff_C, ← algebraMap_eq, algebraMap_smul]
  | add p q hp hq => rw [add_smul, hp, hq, map_add, add_smul]
  | mul_X p i _ => rw [mul_smul, h, smul_zero, map_mul, constantCoeff_X, mul_zero, zero_smul]

/-- A finitely generated module over a polynomial ring on which every variable acts by zero is
finitely generated over the coefficients. -/
theorem finite_of_forall_X_smul_eq_zero [Module.Finite (MvPolynomial σ A) M]
    (h : ∀ (i : σ) (m : M), (X i : MvPolynomial σ A) • m = 0) : Module.Finite A M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := MvPolynomial σ A) (M := M)
  refine ⟨⟨s, Submodule.eq_top_iff'.mpr fun m ↦ ?_⟩⟩
  have hm : m ∈ Submodule.span (MvPolynomial σ A) (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul p x _ hx =>
    rw [smul_eq_constantCoeff_smul h]
    exact Submodule.smul_mem _ _ hx

end TauCeti.MvPolynomial
