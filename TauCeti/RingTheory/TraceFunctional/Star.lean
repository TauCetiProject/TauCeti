/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TraceFunctional.Radical
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Sesquilinear trace forms

A linear functional on a star algebra defines the sesquilinear form
`(x, y) ↦ τ (star x * y)`, conjugate-linear in the first variable. If the functional preserves
star, this form is Hermitian. If it is also tracial, its multiplication-pairing radical is
star-stable and equals the kernel of the sesquilinear form. No positivity is assumed: these
facts apply before deciding whether a trace gives a Hilbert space after quotient and completion.

Over `ℂ`, traciality reduces to self-adjoint elements
(`LinearMap.forall_map_mul_comm_iff_forall_isSelfAdjoint`) and can be tested on the pairs
`(star a, a)`: `LinearMap.forall_map_mul_comm_iff_forall_map_star_mul_self` says that a complex
linear map `f` on a possibly nonunital star algebra satisfies `f (a * b) = f (b * a)` for all `a, b`
as soon as `f (star a * a) = f (a * star a)` for all `a`. This is polarization: the sesquilinear
forms `(a, b) ↦ f (star a * b)` and `(a, b) ↦ f (b * star a)` agree on the diagonal, hence
everywhere.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, for sesquilinear trace forms and
  trace radicals of Temperley–Lieb algebras.
-/

public section

namespace LinearMap

section Semiring

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [Algebra R A] [StarModule R A]

/-- The sesquilinear form of a linear functional on a star algebra, conjugate-linear in the
first argument. Hermitian symmetry requires that the functional preserve star. -/
def traceSesqForm (τ : A →ₗ[R] R) : A →ₗ⋆[R] A →ₗ[R] R :=
  ((LinearMap.mul R A).compr₂ τ).comp (starLinearEquiv R).toLinearMap

/-- Evaluation of the sesquilinear trace form. -/
@[simp]
theorem traceSesqForm_apply (τ : A →ₗ[R] R) (x y : A) :
    τ.traceSesqForm x y = τ (star x * y) := (rfl)

/-- A star-preserving functional has a Hermitian sesquilinear trace form. Traciality is not
needed for this symmetry. -/
theorem traceSesqForm_isSymm (τ : A →ₗ[R] R) (hstar : ∀ x, τ (star x) = star (τ x)) :
    τ.traceSesqForm.IsSymm := by
  constructor
  intro x y
  simp only [traceSesqForm_apply, starRingEnd_apply, ← hstar, star_mul, star_star]

end Semiring

variable {R A : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]

/-- The multiplication-pairing radical of a star-preserving trace is stable under star. -/
theorem star_mem_traceRadical_iff (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) {x : A} :
    star x ∈ τ.traceRadical hτ ↔ x ∈ τ.traceRadical hτ := by
  have hmem {a : A} (ha : a ∈ τ.traceRadical hτ) : star a ∈ τ.traceRadical hτ := by
    rw [mem_traceRadical] at ha ⊢
    intro y
    rw [hτ, ← star_star y, ← star_mul, hstar, ha, star_zero]
  exact ⟨fun hx ↦ by simpa only [star_star] using hmem hx, hmem⟩

/-- For a star-preserving trace, the left kernel of its sesquilinear form is the underlying
coefficient submodule of its multiplication-pairing radical. -/
theorem ker_traceSesqForm [StarModule R A] (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) :
    ker τ.traceSesqForm = (τ.traceRadical hτ).restrictScalars R := by
  ext x
  rw [mem_ker, LinearMap.ext_iff, Submodule.restrictScalars_mem,
    ← τ.star_mem_traceRadical_iff hτ hstar, mem_traceRadical]
  simp [traceSesqForm_apply]

section Polarization

variable {A M : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [AddCommGroup M] [Module ℂ M]

/-- **Cartesian reduction of traciality.** A complex linear map `f` on a possibly nonunital star
algebra vanishes on all commutators if and only if it vanishes on commutators of self-adjoint
elements. -/
theorem forall_map_mul_comm_iff_forall_isSelfAdjoint (f : A →ₗ[ℂ] M) :
    (∀ a b, f (a * b) = f (b * a)) ↔
      ∀ a b, IsSelfAdjoint a → IsSelfAdjoint b → f (a * b) = f (b * a) :=
  ⟨fun h a b _ _ => h a b, fun h x y => by
    have key : (LinearMap.mul ℂ A).compr₂ f = ((LinearMap.mul ℂ A).compr₂ f).flip :=
      LinearMap.ext_on span_selfAdjoint fun a ha =>
        LinearMap.ext_on span_selfAdjoint fun b hb => by
          simpa using h a b (selfAdjoint.mem_iff.mp ha) (selfAdjoint.mem_iff.mp hb)
    simpa using LinearMap.congr_fun₂ key x y⟩

/-- **Polarization criterion for traciality.** A complex linear map `f` on a possibly nonunital
star algebra satisfies `f (a * b) = f (b * a)` for all `a, b` exactly when
`f (star a * a) = f (a * star a)` for all `a`. Over `ℝ` the criterion fails: on `2 × 2` real
matrices, `x ↦ x₀₁ - x₁₀` vanishes on the symmetric matrices `aᵀa` and `aaᵀ`, but takes the value
`1` at `e₀₀e₀₁ = e₀₁` and `0` at `e₀₁e₀₀ = 0`. -/
theorem forall_map_mul_comm_iff_forall_map_star_mul_self (f : A →ₗ[ℂ] M) :
    (∀ a b, f (a * b) = f (b * a)) ↔ ∀ a, f (star a * a) = f (a * star a) := by
  refine ⟨fun h a => h _ _, fun h x b => ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a, star a = x := ⟨star x, star_star x⟩
  -- expand the diagonal identity at `a + b` and at `a + I • b`
  have h₁ := h (a + b)
  have h₂ := h (a + Complex.I • b)
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_I, neg_smul, add_mul, mul_add,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, map_add, map_neg, map_smul] at h₁ h₂
  apply smul_right_injective M Complex.I_ne_zero
  linear_combination (norm := module) (Complex.I / 2) • (h₁ - h a - h b) +
    (1 / 2 : ℂ) • (h₂ - h a) + (Complex.I ^ 2 / 2) • h b

end Polarization

end LinearMap
