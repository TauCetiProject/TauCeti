/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Detection
public import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Uniqueness from the HOMFLY specializations

The substitutions `a = q ^ N` and `z = q - q⁻¹`, for positive integers `N`, jointly
detect two-variable Laurent polynomials over any field. These are the substitutions
relating HOMFLY to its `sl_N` specializations, as obtained from enhanced Jimbo traces.
Thus, if a two-variable Laurent polynomial realizing the specializations exists, it
is unique. This file proves uniqueness, without asserting the existence of that polynomial.

We represent `K[a, a⁻¹, z, z⁻¹]` by `LaurentPolynomial (LaurentPolynomial K)`,
with `z` the inner variable and `a` the outer variable. Values lie in `RatFunc K`,
where `q` is `RatFunc.X`. Using rational functions permits negative powers of `z`;
`q - q⁻¹` is transcendental and hence nonzero. No characteristic restriction is needed.
In fact, any infinite set of ranks suffices for uniqueness.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388 (the HOMFLY specialization of braid traces).
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (enhanced representations).
-/

public section

noncomputable section

namespace TauCeti.KnotTheory

open LaurentPolynomial
open scoped Polynomial

variable (K : Type*) [Field K]

/-- The HOMFLY substitution `a ↦ q ^ N`, `z ↦ q - q⁻¹` into `K(q)`.
The inner Laurent variable is `z` and the outer one is `a`. -/
def homflySpecialization (N : ℕ) :
    LaurentPolynomial (LaurentPolynomial K) →+* RatFunc K :=
  eval₂
    (eval₂ (algebraMap K (RatFunc K))
      (Units.mk0 (RatFunc.X - RatFunc.X⁻¹)
        (transcendental_ratFunc_X_sub_inv K).ne_zero))
    (Units.mk0 RatFunc.X RatFunc.X_ne_zero ^ N)

/-- The defining equation of the two-variable HOMFLY substitution. -/
theorem homflySpecialization_def (N : ℕ) (p : LaurentPolynomial (LaurentPolynomial K)) :
    homflySpecialization K N p =
      eval₂
        (eval₂ (algebraMap K (RatFunc K))
          (Units.mk0 (RatFunc.X - RatFunc.X⁻¹)
            (transcendental_ratFunc_X_sub_inv K).ne_zero))
        (Units.mk0 RatFunc.X RatFunc.X_ne_zero ^ N) p := (rfl)

/-- The constant coefficient polynomial is evaluated at `z = q - q⁻¹`. -/
@[simp]
theorem homflySpecialization_C (N : ℕ) (p : LaurentPolynomial K) :
    homflySpecialization K N (C p) =
      eval₂ (algebraMap K (RatFunc K))
        (Units.mk0 (RatFunc.X - RatFunc.X⁻¹)
          (transcendental_ratFunc_X_sub_inv K).ne_zero) p := by
  simp [homflySpecialization_def]

/-- The outer Laurent variable is evaluated at `a = q ^ N`. -/
@[simp]
theorem homflySpecialization_T (N : ℕ) (i : ℤ) :
    homflySpecialization K N (T i) = RatFunc.X ^ ((N : ℤ) * i) := by
  simp [homflySpecialization_def, ← zpow_natCast, ← zpow_mul]

/-- An infinite set of HOMFLY ranks detects two-variable Laurent polynomials. -/
theorem homflySpecialization_injective_of_infinite {s : Set ℕ} (hs : s.Infinite) :
    Function.Injective (fun p : LaurentPolynomial (LaurentPolynomial K) ↦
      fun N : s ↦ homflySpecialization K N p) := by
  simp only [homflySpecialization_def]
  apply RingHom.laurent_eval₂_family_injective _
    (Units.laurent_eval₂_injective_of_transcendental _ (transcendental_ratFunc_X_sub_inv K))
  have hinj : Function.Injective
      (fun N : ℕ ↦ (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) ^ N) := by
    intro m n h
    have hp : (Polynomial.X : K[X]) ^ m = Polynomial.X ^ n :=
      RatFunc.algebraMap_injective K (by simpa using congrArg Units.val h)
    simpa using congrArg Polynomial.natDegree hp
  simpa only [Set.image_eq_range] using hs.image hinj.injOn

/-- All positive-rank specializations jointly detect two-variable Laurent polynomials.
Rank zero is not needed. -/
theorem homflySpecialization_jointly_injective :
    Function.Injective (fun p : LaurentPolynomial (LaurentPolynomial K) ↦
      fun N : ℕ ↦ homflySpecialization K (N + 1) p) := by
  intro p q hpq
  apply homflySpecialization_injective_of_infinite K
    (s := Set.range Nat.succ) (Set.infinite_range_of_injective Nat.succ_injective)
  funext N
  obtain ⟨n, hn⟩ := N.property
  simpa only [← hn] using congrFun hpq n

end TauCeti.KnotTheory
