/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.Kronecker
import Mathlib.Data.ZMod.Basic

/-!
# Polynomial graphs with bounded-base coefficient preservation

The substitution `Xᵢ ↦ T^(B^i)` parametrizes a graph through the origin when `B > 0`.
The first coordinate is `T`, so the substitution is surjective in positive dimension.
Choosing `B` larger than every exponent of a nonzero polynomial makes its pullback nonzero,
even over a finite field, where every rational straight line may lie in its zero locus.

The coefficient and injectivity results specialize
`MvPolynomial.coeff_aeval_X_pow_weight` and `MvPolynomial.injOn_aeval_X_pow` using uniqueness
of base-`B` digits (`Finsupp.injOn_weight_pow`).
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial

variable (R : Type*) [CommSemiring R] (m B : ℕ)

/-- The ring map parametrizing the graph `T ↦ (T, T^B, T^(B²), …)` in `m` variables.
It is defined also for zero variables and for bases zero and one. -/
def polynomialGraph : MvPolynomial (Fin m) R →+* Polynomial R :=
  eval₂Hom Polynomial.C (fun i ↦ Polynomial.X ^ (B ^ i.val))

@[simp]
theorem polynomialGraph_C (a : R) :
    polynomialGraph R m B (C a) = Polynomial.C a := by
  simp [polynomialGraph]

@[simp]
theorem polynomialGraph_X (i : Fin m) :
    polynomialGraph R m B (X i) = Polynomial.X ^ (B ^ i.val) := by
  simp [polynomialGraph]

/-- The graph map is the underlying ring map of the Kronecker algebra substitution. -/
theorem polynomialGraph_eq_aeval :
    polynomialGraph R m B =
      (aeval (fun i : Fin m ↦ (Polynomial.X : Polynomial R) ^ (B ^ i.val))).toRingHom := by
  rfl

/-- A monomial maps to the monomial at its base-`B` weight. -/
@[simp]
theorem polynomialGraph_monomial (d : Fin m →₀ ℕ) (a : R) :
    polynomialGraph R m B (monomial d a) =
      Polynomial.monomial (Finsupp.weight (fun i : Fin m ↦ B ^ i.val) d) a := by
  rw [polynomialGraph_eq_aeval]
  exact aeval_X_pow_left_monomial _ _ _

/-- The graph is a morphism over the coefficient semiring. -/
@[simp]
theorem polynomialGraph_comp_C :
    (polynomialGraph R m B).comp C = Polynomial.C := by
  ext a
  simp

/-- A positive base makes the graph pass through the origin. Base zero is excluded because
then the variable indexed by one maps to the constant polynomial one. -/
@[simp]
theorem constantCoeff_comp_polynomialGraph (hB : 0 < B) :
    Polynomial.constantCoeff.comp (polynomialGraph R m B) = constantCoeff := by
  ext <;> simp [RingHom.comp_apply, ne_of_lt (pow_pos hB _)]

/-- Substitution commutes with changing the coefficients. -/
@[simp]
theorem polynomialGraph_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (h : MvPolynomial (Fin m) R) :
    polynomialGraph S m B (map f h) = Polynomial.map f (polynomialGraph R m B h) := by
  have he : (polynomialGraph S m B).comp (map f) =
      (Polynomial.mapRingHom f).comp (polynomialGraph R m B) := by
    ext <;> simp
  exact DFunLike.congr_fun he h

variable {R m B}

/-- All coefficients survive substitution when both the support exponents and the query
exponent have entries strictly below the base. No positivity assumption on the base is needed. -/
theorem polynomialGraph_coeff {h : MvPolynomial (Fin m) R}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) {e : Fin m →₀ ℕ} (he : ∀ i, e i < B) :
    (polynomialGraph R m B h).coeff (Finsupp.weight (fun i : Fin m ↦ B ^ i.val) e) =
      h.coeff e := by
  rw [polynomialGraph_eq_aeval]
  exact coeff_aeval_X_pow_weight (Finsupp.injOn_weight_pow m B) hh he

/-- The graph substitution is injective on polynomials with all exponents below the base. -/
theorem polynomialGraph_injOn (R : Type*) [CommSemiring R] (m B : ℕ) :
    Set.InjOn (polynomialGraph R m B)
      {h | ∀ d ∈ h.support, ∀ i, d i < B} := by
  rw [polynomialGraph_eq_aeval]
  exact (injOn_aeval_X_pow (Finsupp.injOn_weight_pow m B)).mono fun h hh ↦
    (mem_restrictSupport_iff (R := R)).mpr hh

/-- A polynomial supported in the bounded box vanishes after substitution exactly when it
was zero. -/
@[simp]
theorem polynomialGraph_eq_zero_iff {h : MvPolynomial (Fin m) R}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    polynomialGraph R m B h = 0 ↔ h = 0 := by
  exact ⟨fun hz ↦ polynomialGraph_injOn R m B hh (by simp) (hz.trans (map_zero _).symm),
    fun hz ↦ by simp [hz]⟩

/-- The first coordinate is `T`, so every univariate polynomial is a pullback, even at base
zero. The positive-dimension hypothesis is essential over a nontrivial semiring. -/
theorem polynomialGraph_surjective (R : Type*) [CommSemiring R] {m : ℕ} (hm : 0 < m) (B : ℕ) :
    Function.Surjective (polynomialGraph R m B) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨f, rfl⟩ := hp
    obtain ⟨g, rfl⟩ := hq
    exact ⟨f + g, map_add _ _ _⟩
  | monomial n a =>
    refine ⟨C a * X (⟨0, hm⟩ : Fin m) ^ n, ?_⟩
    simp [Polynomial.C_mul_X_pow_eq_monomial]

/-- A computable base at least two separates all monomials of a nonzero polynomial.
The construction works over any commutative semiring, not only over a field. -/
theorem exists_polynomialGraph_ne_zero {h : MvPolynomial (Fin m) R} (hh : h ≠ 0) :
    ∃ B, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph R m B h ≠ 0 := by
  let B := 2 + h.totalDegree
  have hbound : ∀ d ∈ h.support, ∀ i, d i < B := by
    intro d hd i
    exact lt_of_le_of_lt ((le_degreeOf_of_mem_support i hd).trans (degreeOf_le_totalDegree h i))
      (by omega)
  exact ⟨B, by omega, hbound, (polynomialGraph_eq_zero_iff hbound).not.mpr hh⟩

-- The first coordinate stays T, even at base zero.
example : polynomialGraph ℤ 1 0 (X 0) = Polynomial.X := by simp

-- At base zero the second coordinate misses the origin.
example : polynomialGraph ℤ 2 0 (X 1) = 1 := by simp

-- A non-strict exponent bound would allow this collision.
example : polynomialGraph (ZMod 2) 2 2 (X 1 - X 0 ^ 2) = 0 := by simp

-- The nonlinear graph succeeds over F₂ even where all rational lines fail.
example : polynomialGraph (ZMod 2) 2 3 (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) ↦ p.coeff 5) h
  norm_num [map_sub, map_mul, map_pow, polynomialGraph_X, ← pow_mul, ← pow_add] at hc

end TauCeti
