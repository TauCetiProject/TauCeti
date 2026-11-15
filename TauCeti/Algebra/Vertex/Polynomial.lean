/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Commutative
public import TauCeti.Algebra.Vertex.Reconstruction
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# The polynomial formal vertex algebra via reconstruction

On a polynomial ring `R[X]`, left multiplication by `X + z` defines a vertex operator
`Polynomial.shiftedXField R` whose `(-1)`-mode is multiplication by `X`, whose `(-2)`-mode is the
identity, and whose remaining modes vanish. It is translation-covariant with `d/dX`
(`Polynomial.derivative'`), mutually local with itself of order `0`, and its modes generate `R[X]`
from the vacuum `1`.

Over a `ℚ`-algebra `R`, applying `TauCeti.FormalVertexAxioms.ofGeneratingFields` to `(1, d/dX)` and
the single generating field `Polynomial.shiftedXField R` recovers the commutative differential
vertex algebra `(Polynomial.derivative').formalVertexAxioms`
(`Polynomial.ofGeneratingFields_shiftedXField`).

## Main definitions

* `Polynomial.shiftedXField`: the field `p ↦ (X + z) p` on `R[X]`.

## Main results

* `Polynomial.formalVertexAxioms_derivative'_field_X`: in
  `(Polynomial.derivative').formalVertexAxioms`, the field of `X` is `Polynomial.shiftedXField R`.
* `Polynomial.ofGeneratingFields_shiftedXField`: reconstructing a formal vertex algebra on `R[X]`
  from `Polynomial.shiftedXField R` recovers `(Polynomial.derivative').formalVertexAxioms`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §1.4 and §4.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.4 and §2.3.3.
-/

public section

noncomputable section

open scoped VertexOperator Polynomial

namespace Polynomial

section CommRing

variable (R : Type*) [CommRing R]

private theorem bddBelow_shiftedXField (p : R[X]) :
    BddBelow (Function.support fun k : ℤ ↦
      (if k = 0 then LinearMap.mulLeft R X else if k = 1 then 1 else 0) p) :=
  ⟨0, fun k hk ↦ by
    by_contra! hlt
    exact hk (by
      have h₀ : k ≠ 0 := by omega
      have h₁ : k ≠ 1 := by omega
      simp [h₀, h₁])⟩

/-- The shifted multiplication field `F(z) p = (X + z) p` on `R[X]`: its `z^0`-coefficient
(mode `-1`) is multiplication by `X`, its `z^1`-coefficient (mode `-2`) is the identity, and all
other coefficients vanish. -/
def shiftedXField : VertexOperator R R[X] :=
  VertexOperator.of_coeff
    (fun k ↦ if k = 0 then LinearMap.mulLeft R X else if k = 1 then 1 else 0)
    (bddBelow_shiftedXField R)

/-- The `(-1)`-mode (`z^0`-coefficient) of `shiftedXField R` is left multiplication by `X`. -/
@[simp]
theorem ncoeff_neg_one_shiftedXField :
    (shiftedXField R)[[-1]] = LinearMap.mulLeft R X := by
  simp [shiftedXField]

/-- The `(-2)`-mode (`z^1`-coefficient) of `shiftedXField R` is the identity on `R[X]`. -/
@[simp]
theorem ncoeff_neg_two_shiftedXField :
    (shiftedXField R)[[-2]] = 1 := by
  simp [shiftedXField]

/-- All modes of `shiftedXField R` other than `-1` and `-2` vanish. -/
theorem ncoeff_shiftedXField_of_ne {n : ℤ} (h₁ : n ≠ -1) (h₂ : n ≠ -2) :
    (shiftedXField R)[[n]] = 0 := by
  rw [shiftedXField, VertexOperator.ncoeff_of_coeff]
  have hk₀ : -n - 1 ≠ 0 := by omega
  have hk₁ : -n - 1 ≠ 1 := by omega
  simp [hk₀, hk₁]

/-- Translation covariance of `shiftedXField R` with `d/dX`. -/
theorem lie_derivative_ncoeff_shiftedXField (n : ℤ) :
    ⁅((derivative' : Derivation R R[X] R[X]) : Module.End R R[X]), (shiftedXField R)[[n]]⁆ =
      (VertexOperator.derivative (shiftedXField R))[[n]] := by
  by_cases h₁ : n = -1
  · subst h₁
    refine LinearMap.ext fun p ↦ ?_
    simp [Ring.lie_def, mul_comm X]
  · by_cases h₂ : n = -2
    · subst h₂
      have h₃ : (-2 : ℤ) - 1 ≠ -1 := by omega
      have h₄ : (-2 : ℤ) - 1 ≠ -2 := by omega
      rw [ncoeff_neg_two_shiftedXField, VertexOperator.ncoeff_derivative,
        ncoeff_shiftedXField_of_ne R h₃ h₄, smul_zero]
      simp [Ring.lie_def]
    · rw [ncoeff_shiftedXField_of_ne R h₁ h₂, VertexOperator.ncoeff_derivative]
      by_cases h₀ : n = 0
      · subst h₀
        simp [Ring.lie_def]
      · have hm₁ : n - 1 ≠ -1 := by omega
        have hm₂ : n - 1 ≠ -2 := by omega
        rw [ncoeff_shiftedXField_of_ne R hm₁ hm₂, smul_zero]
        simp [Ring.lie_def]

/-- `shiftedXField R` is mutually local with itself of order `0`. -/
theorem isLocalOfOrder_shiftedXField :
    (shiftedXField R).IsLocalOfOrder (shiftedXField R) 0 :=
  VertexOperator.IsLocalOfOrder.of_commute fun m n ↦ LinearMap.ext fun p ↦ by
    rw [shiftedXField, VertexOperator.ncoeff_of_coeff, VertexOperator.ncoeff_of_coeff]
    split_ifs <;> simp

/-- Any `R`-submodule of `R[X]` containing `1` and stable under the modes of `shiftedXField R` is
all of `R[X]`. -/
theorem submodule_eq_top_of_shiftedXField (W : Submodule R R[X]) (h1 : (1 : R[X]) ∈ W)
    (hF : ∀ (n : ℤ), ∀ p ∈ W, ((shiftedXField R)[[n]]) p ∈ W) :
    W = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro p
  refine Polynomial.induction_on p (fun a ↦ ?_) (fun f g hf hg ↦ W.add_mem hf hg) fun n a ih ↦ ?_
  · have ha : C a = a • (1 : R[X]) := by rw [Algebra.smul_def, algebraMap_eq, mul_one]
    exact ha ▸ W.smul_mem a h1
  · have hmul := hF (-1) (C a * X ^ n) ih
    rw [ncoeff_neg_one_shiftedXField, LinearMap.mulLeft_apply, mul_left_comm, ← pow_succ'] at hmul
    exact hmul

end CommRing

section RatAlgebra

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- In the commutative differential vertex algebra on `R[X]` with `T = d/dX`, the field attached to
`X` is `shiftedXField R`, i.e., `Y(X, z) p = (X + z) p`. -/
@[simp]
theorem formalVertexAxioms_derivative'_field_X :
    (derivative' : Derivation R R[X] R[X]).formalVertexAxioms.field X = shiftedXField R := by
  refine VertexOperator.ext_ncoeff fun n ↦ ?_
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [Derivation.ncoeff_formalVertexAxioms_field_neg]
    rcases k with _ | _ | k
    · simp
    · have h2 : -((0 + 1 : ℕ) : ℤ) - 1 = -2 := rfl
      rw [h2, ncoeff_neg_two_shiftedXField]
      simp only [Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, inv_one, pow_one,
        Derivation.coeFn_coe, derivative'_apply, derivative_X, one_smul]
      exact LinearMap.ext fun _ ↦ one_mul _
    · have h₁ : -((k + 2 : ℕ) : ℤ) - 1 ≠ -1 := by omega
      have h₂ : -((k + 2 : ℕ) : ℤ) - 1 ≠ -2 := by omega
      rw [ncoeff_shiftedXField_of_ne R h₁ h₂]
      have hd : (((derivative' : Derivation R R[X] R[X]) : Module.End R R[X]) ^ (k + 2)) X = 0 := by
        rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
        simp
      simp [hd]
  · have h₁ : n ≠ -1 := by omega
    have h₂ : n ≠ -2 := by omega
    rw [Derivation.ncoeff_formalVertexAxioms_field_of_nonneg _ _ hn,
      ncoeff_shiftedXField_of_ne R h₁ h₂]

/-- Reconstructing a formal vertex algebra on `R[X]` from vacuum `1`, translation `d/dX`, and the
single generator `shiftedXField R` recovers `(Polynomial.derivative').formalVertexAxioms`. -/
theorem ofGeneratingFields_shiftedXField :
    TauCeti.FormalVertexAxioms.ofGeneratingFields
      (1 : R[X]) ((derivative' : Derivation R R[X] R[X]) : Module.End R R[X])
      (fun _ : Unit ↦ shiftedXField R)
      derivative_one
      (fun _ ↦ lie_derivative_ncoeff_shiftedXField R)
      (fun _ _ ↦ ⟨0, isLocalOfOrder_shiftedXField R⟩)
      (fun W h1 hF ↦ submodule_eq_top_of_shiftedXField R W h1 (hF ())) =
    (derivative' : Derivation R R[X] R[X]).formalVertexAxioms :=
  (TauCeti.FormalVertexAxioms.eq_of_generatingFields _ _ _ _ _ _ _
    (Derivation.formalVertexAxioms_vacuum (derivative' : Derivation R R[X] R[X])) fun _ ↦ by
      simp [formalVertexAxioms_derivative'_field_X]).symm

end RatAlgebra

end Polynomial
