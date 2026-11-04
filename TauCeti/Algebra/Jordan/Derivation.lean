/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic

/-!
# Inner derivations of a commutative Jordan algebra

In a commutative Jordan algebra `A` over a ring in which `2` is invertible, the commutator
`⁅L_a, L_b⁆ = L_a L_b - L_b L_a` of two multiplication operators is a derivation. These are the
**inner derivations** of `A`. For the split Albert algebra they supply the derivations that
`TauCeti/Algebra/AlbertAlgebra/Derivation/Finrank.lean` uses to show that its derivation algebra has
dimension `52`.

## Main definitions

* `TauCeti.jordanInnerDerivation R a b`: the inner derivation `⁅L_a, L_b⁆`, bundled as an element
  of `TauCeti.derivationLieAlgebra R A`.

## Main results

* `TauCeti.lie_mulLeft_mulLeft_mem_derivationLieAlgebra`: `⁅L_a, L_b⁆` is a derivation.

## The argument

Mathlib's fully linearized Jordan identity `two_nsmul_lie_lmul_lmul_add_add_eq_zero` says that
`⁅L_a, L_{bc}⁆ + ⁅L_b, L_{ca}⁆ + ⁅L_c, L_{ab}⁆` is killed by `2`, so vanishes once `2` is
invertible. Evaluated at a fourth element and read as an identity of operators in a different
variable it becomes

`L_{(bc)d} = L_{bc} L_d + L_{bd} L_c + L_{cd} L_b - L_b L_d L_c - L_c L_d L_b`,

and the difference of two instances of this is `⁅⁅L_a, L_b⁆, L_c⁆ = L_{a(bc) - b(ac)}`. That is the
Leibniz rule for `⁅L_a, L_b⁆` applied to a product `c x`.

## References

* N. Jacobson, *Structure and Representations of Jordan Algebras*, AMS Colloquium Publications 39
  (1968), Chapter I.
* R. D. Schafer, *An Introduction to Nonassociative Algebras*, Academic Press (1966), Chapter IV.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocCommRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [IsCommJordan A] [Invertible (2 : R)]

omit [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] in
/-- The fully linearized Jordan identity evaluated at a fourth element `d`, up to the factor `2`. -/
private theorem two_nsmul_linearized_jordan (a b c d : A) :
    (2 : ℕ) • (a * (b * c * d) - b * c * (a * d) + (b * (c * a * d) - c * a * (b * d))
      + (c * (a * b * d) - a * b * (c * d))) = 0 := by
  have h := DFunLike.congr_fun (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c) d
  simp only [Ring.lie_def] at h
  -- Evaluating an additive endomorphism at `d` commutes definitionally with the ring operations
  -- of `AddMonoid.End A`, which carry no `simp` lemmas of their own for `nsmul` and `sub`.
  exact h

variable (R) in
/-- **The commutator of two multiplication operators of a commutative Jordan algebra is a
derivation**: `⁅L_a, L_b⁆ = L_a L_b - L_b L_a`, the inner derivation of `a` and `b`. -/
theorem lie_mulLeft_mulLeft_mem_derivationLieAlgebra (a b : A) :
    ⁅(LinearMap.mulLeft R a : Module.End R A), LinearMap.mulLeft R b⁆ ∈
      derivationLieAlgebra R A := by
  have cancel : ∀ x : A, (2 : ℕ) • x = 0 → x = 0 := fun x hx => by
    simpa [← Nat.cast_smul_eq_nsmul R, smul_smul] using congrArg (⅟(2 : R) • ·) hx
  rw [mem_derivationLieAlgebra]
  intro x y
  have h₁ := cancel _ (two_nsmul_linearized_jordan y b x a)
  have h₂ := cancel _ (two_nsmul_linearized_jordan y a x b)
  simp only [Ring.lie_def, LinearMap.sub_apply, _root_.mul_apply_eq_comp, LinearMap.mulLeft_apply]
  rw [← sub_eq_zero]
  have key : a * (b * (x * y)) - b * (a * (x * y)) -
      ((a * (b * x) - b * (a * x)) * y + x * (a * (b * y) - b * (a * y))) =
      -(y * (b * x * a) - b * x * (y * a) + (b * (x * y * a) - x * y * (b * a))
          + (x * (y * b * a) - y * b * (x * a))) +
        (y * (a * x * b) - a * x * (y * b) + (a * (x * y * b) - x * y * (a * b))
          + (x * (y * a * b) - y * a * (x * b))) := by
    -- Both sides agree after reordering the factors of nine products.
    have e₁ : y * (b * x * a) = a * (b * x) * y := by rw [mul_comm y, mul_comm (b * x) a]
    have e₂ : y * a * (x * b) = b * x * (y * a) := by rw [mul_comm (y * a), mul_comm x b]
    have e₃ : b * (x * y * a) = b * (a * (x * y)) := by rw [mul_comm (x * y) a]
    have e₄ : x * y * (b * a) = x * y * (a * b) := by rw [mul_comm b a]
    have e₅ : x * (y * b * a) = x * (a * (b * y)) := by rw [mul_comm (y * b) a, mul_comm y b]
    have e₆ : y * b * (x * a) = a * x * (y * b) := by rw [mul_comm (y * b), mul_comm x a]
    have e₇ : y * (a * x * b) = b * (a * x) * y := by rw [mul_comm y, mul_comm (a * x) b]
    have e₈ : a * (x * y * b) = a * (b * (x * y)) := by rw [mul_comm (x * y) b]
    have e₉ : x * (y * a * b) = x * (b * (a * y)) := by rw [mul_comm (y * a) b, mul_comm y a]
    rw [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, sub_mul, mul_sub]
    abel
  rw [key, h₁, h₂, neg_zero, add_zero]

variable (R) in
/-- **The inner derivation** `⁅L_a, L_b⁆ = L_a L_b - L_b L_a` of two elements `a` and `b` of a
commutative Jordan algebra, as an element of the derivation algebra. -/
def jordanInnerDerivation (a b : A) : derivationLieAlgebra R A :=
  ⟨⁅(LinearMap.mulLeft R a : Module.End R A), LinearMap.mulLeft R b⁆,
    lie_mulLeft_mulLeft_mem_derivationLieAlgebra R a b⟩

@[simp]
theorem jordanInnerDerivation_apply (a b x : A) :
    (jordanInnerDerivation R a b : Module.End R A) x = a * (b * x) - b * (a * x) := by
  simp [jordanInnerDerivation, Ring.lie_def]

end TauCeti
