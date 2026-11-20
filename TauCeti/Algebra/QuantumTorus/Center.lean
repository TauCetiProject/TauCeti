/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# The center of a based quantum torus

Commutation with a normalized monomial is a coefficientwise condition. Over a domain,
the nonzero coefficients can be cancelled, so central elements are exactly the finite
linear combinations of monomials whose commutation factors are one. The coefficientwise
criterion also applies over rings with zero divisors, where this cancellation can fail.

For alternating forms the central exponent condition is `u ^ (2 * Λ a b) = 1` for every `b`.
No infinite-order assumption on the parameter is imposed.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), Proposition 11.2.
-/

public section

namespace TauCeti.QuantumTorus

section CentralExponents

variable {R L : Type*} [Monoid R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- Exponents whose normalized monomials commute with every normalized monomial.
The definition retains all finite-order phenomena of the parameter. -/
def centralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) : AddSubgroup L where
  carrier := {a | ∀ b, u ^ (Λ a b) = u ^ (Λ b a)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb c
    simp only [map_add, LinearMap.add_apply, zpow_add, ha c, hb c]
  neg_mem' := by
    intro a ha b
    simp only [map_neg, LinearMap.neg_apply, zpow_neg, ha b]

/-- Membership in the central exponent subgroup is equality of the opposite twist factors. -/
@[simp]
theorem mem_centralExponents (a : L) :
    a ∈ centralExponents u Λ ↔ ∀ b, u ^ (Λ a b) = u ^ (Λ b a) :=
  Iff.rfl

/-- For an alternating form, central exponents are detected by the commutation factor
`u ^ (2 * Λ a b)`, without an infinite-order hypothesis. -/
theorem mem_centralExponents_iff_of_isAlt (hΛ : Λ.IsAlt) (a : L) :
    a ∈ centralExponents u Λ ↔ ∀ b, u ^ (2 * Λ a b) = 1 := by
  rw [mem_centralExponents]
  apply forall_congr'
  intro b
  have he : Λ a b - Λ b a = 2 * Λ a b := by
    have := hΛ.neg_eq a b
    omega
  rw [← he, zpow_sub, mul_inv_eq_one]

end CentralExponents

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- Right multiplication by a monomial shifts the exponent and twists its coefficient. -/
theorem repr_mul_monomial_apply (f : QuantumTorus R L u Λ) (a b : L) :
    (basis u Λ).repr (f * monomial u Λ b) (a + b) =
      (basis u Λ).repr f a * (u ^ (Λ a b) : Rˣ) := by
  classical
  have h : (Finsupp.lapply (a + b)).comp
      ((basis u Λ).repr.toLinearMap.comp (LinearMap.mulRight R (monomial u Λ b))) =
      ((u ^ (Λ a b) : Rˣ) : R) • (Finsupp.lapply a).comp (basis u Λ).repr.toLinearMap := by
    apply (basis u Λ).ext
    intro c
    by_cases hc : c = a
    · subst c
      simp [monomial_mul_monomial]
    · simp [monomial_mul_monomial, hc]
  simpa [mul_comm] using LinearMap.congr_fun h f

/-- Left multiplication by a monomial shifts the exponent with the opposite twist factor. -/
theorem repr_monomial_mul_apply (f : QuantumTorus R L u Λ) (a b : L) :
    (basis u Λ).repr (monomial u Λ b * f) (a + b) =
      (basis u Λ).repr f a * (u ^ (Λ b a) : Rˣ) := by
  classical
  have h : (Finsupp.lapply (a + b)).comp
      ((basis u Λ).repr.toLinearMap.comp (LinearMap.mulLeft R (monomial u Λ b))) =
      ((u ^ (Λ b a) : Rˣ) : R) • (Finsupp.lapply a).comp (basis u Λ).repr.toLinearMap := by
    apply (basis u Λ).ext
    intro c
    by_cases hc : c = a
    · subst c
      simp [monomial_mul_monomial, add_comm]
    · simp [monomial_mul_monomial, hc, add_comm b]
  simpa [mul_comm] using LinearMap.congr_fun h f

/-- Commutation with a monomial is equality of the two twisted coefficient families. -/
theorem commute_monomial_iff (f : QuantumTorus R L u Λ) (b : L) :
    Commute f (monomial u Λ b) ↔ ∀ a,
      (basis u Λ).repr f a * (u ^ (Λ a b) : Rˣ) =
        (basis u Λ).repr f a * (u ^ (Λ b a) : Rˣ) := by
  constructor
  · intro h a
    simpa only [repr_mul_monomial_apply, repr_monomial_mul_apply] using
      congrArg (fun z ↦ (basis u Λ).repr z (a + b)) h.eq
  · intro h
    apply (basis u Λ).repr.injective
    ext c
    rw [← sub_add_cancel c b, repr_mul_monomial_apply, repr_monomial_mul_apply]
    exact h (c - b)

/-- A based quantum-torus element is central exactly when it commutes with every monomial. -/
theorem mem_center_iff_commute_monomial (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ b, Commute f (monomial u Λ b) := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h b
    exact (h _).symm
  · intro h g
    have heq : LinearMap.mulLeft R f = LinearMap.mulRight R f :=
      (basis u Λ).ext fun b ↦ by simpa using (h b).eq
    exact (LinearMap.congr_fun heq g).symm

/-- Centrality is the coefficientwise equality of opposite twist factors, without cancellation
or a domain hypothesis on the coefficients. -/
theorem mem_center_iff_coeff (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔ ∀ a b,
      (basis u Λ).repr f a * (u ^ (Λ a b) : Rˣ) =
        (basis u Λ).repr f a * (u ^ (Λ b a) : Rˣ) := by
  rw [mem_center_iff_commute_monomial]
  simp_rw [commute_monomial_iff]
  exact forall_comm

/-- A normalized monomial is central exactly when its exponent is central. No scalar
cancellation assumption is needed because its basis coefficient is one. -/
theorem monomial_mem_center_iff (a : L) :
    monomial u Λ a ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      a ∈ centralExponents u Λ := by
  classical
  rw [mem_center_iff_coeff]
  constructor
  · intro h b
    apply Units.ext
    simpa only [basis_repr_monomial, Finsupp.single_eq_same, one_mul] using h a b
  · intro h c b
    by_cases hc : a = c
    · subst c
      simpa only [basis_repr_monomial, Finsupp.single_eq_same, one_mul] using
        congrArg Units.val (h b)
    · simp [basis_repr_monomial, hc]

/-- With cancellation away from zero in the coefficient semiring, centrality is precisely
support on the central exponent subgroup. In particular this applies over every domain. -/
theorem mem_center_iff_support [IsCancelMulZero R] (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ a ∈ ((basis u Λ).repr f).support, a ∈ centralExponents u Λ := by
  rw [mem_center_iff_coeff]
  constructor
  · intro h a ha b
    apply Units.ext
    exact mul_left_cancel₀ (Finsupp.mem_support_iff.mp ha) (h a b)
  · intro h a b
    by_cases ha : (basis u Λ).repr f a = 0
    · simp [ha]
    · rw [h a (Finsupp.mem_support_iff.mpr ha) b]

/-- The center is the span of the normalized monomials with central exponents, assuming
cancellation of nonzero scalar coefficients. -/
theorem center_toSubmodule_eq_span [IsCancelMulZero R] :
    (Subalgebra.center R (QuantumTorus R L u Λ)).toSubmodule =
      Submodule.span R (monomial u Λ '' (centralExponents u Λ : Set L)) := by
  have hb : (basis u Λ : L → QuantumTorus R L u Λ) = monomial u Λ :=
    funext fun a ↦ basis_apply a
  have hi : (basis u Λ) '' (centralExponents u Λ : Set L) =
      monomial u Λ '' (centralExponents u Λ : Set L) :=
    congrArg (fun v : L → QuantumTorus R L u Λ ↦ v '' (centralExponents u Λ : Set L)) hb
  rw [← hi]
  ext f
  exact (mem_center_iff_support f).trans
    ((basis u Λ).mem_span_image (m := f) (s := (centralExponents u Λ : Set L))).symm


end TauCeti.QuantumTorus
