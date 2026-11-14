/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Connected
public import TauCeti.Algebra.Polynomial.Grading

/-!
# Betti Poincaré series of graded monomial quotients `k[X] / (X^m)`

Give `A = k[X]` its standard nonnegative monomial grading (`deg X = 1`) from
`TauCeti.Polynomial.degreeGrade`. Note that `k[X]` is infinite-dimensional over `k`, so this example
uses the connected-algebra projective basis `TauCeti.connectedRegularProjectiveBasis` (`[k[X]]`)
developed without finite-dimensionality hypotheses.

For any `m ≥ 1`, multiplication by `X^m` defines an injective graded morphism
`k[X]{m} ⟶ k[X]` whose cokernel `k[X] / (X^m)` has the minimal two-term graded free resolution

```text
0 ⟶ k[X]{m} ⟶ k[X] ⟶ k[X] / (X^m) ⟶ 0.
```

In the regular basis `[k[X]]`, its Betti Poincaré series is the polynomial `1 + q^m t`. For `m = 2`
(`M = k[X] / (X²)`), the series `1 + q² t` is a genuine polynomial in `t` with a nonzero
off-diagonal Betti number at `(n, d) = (1, 2)`, witnessing that a minimal finite-length resolution
over a Koszul algebra (`k[X]`) need not be linear when the module has relations in higher internal
degree. Specializing `q = 1` yields `1 + t`.

## Main definitions

* `TauCeti.polynomialPowMulHom`: the graded monomorphism `k[X]{m} ⟶ k[X]` given by multiplication
  by `X^m`.
* `TauCeti.polynomialMonomialQuotient`: the graded quotient module `k[X] / (X^m)`.
* `TauCeti.polynomialMonomialQuotientResolution`: the two-term graded free resolution of
  `k[X] / (X^m)`.
* `TauCeti.polynomialRegularProjectiveBasis`: the regular basis `[k[X]]` of `K₀^gr(proj k[X])`.

## Main results

* `TauCeti.isMinimal_polynomialMonomialQuotientResolution`: for `0 < m`, the resolution is minimal.
* `TauCeti.bettiPoincarePowerSeries_polynomialMonomialQuotientResolution`: the Betti Poincaré
  series of `k[X] / (X^m)` is `1 + q^m t`.
* `TauCeti.isLinear_polynomialMonomialQuotientResolution_iff`: for `0 < m`, the resolution is
  linear if and only if `m = 1`; in particular `¬ IsLinear` for `k[X] / (X²)`.
* `TauCeti.map_laurentEval_one_bettiPoincarePowerSeries_polynomialMonomialQuotient_two`: setting
  `q = 1` on `k[X] / (X²)` gives `1 + t`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial _root_.Polynomial

universe u

section CommRing

variable (k : Type u) [CommRing k]

/-- Multiplication by `X ^ m` as a degree-zero morphism `k[X]{m} ⟶ k[X]` of graded
`k[X]`-modules. -/
def polynomialPowMulHom (m : ℕ) :
    (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m ⟶
      GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k) :=
  GradedModuleCat.ofHom (LinearMap.toSpanSingleton k[X] k[X] (X ^ m)) <|
    LinearMap.isHomogeneous_def.2 fun p f hf ↦ by
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hf
      rw [add_zero, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
      change (X ^ m : k[X]) • f ∈ _
      let _ : SetLike.GradedSMul (Polynomial.degreeGrade k)
        (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).grading.piece :=
        (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).gradedSMul
      have hsmul := SetLike.GradedSMul.smul_mem
        (B := (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).grading.piece)
        (Polynomial.X_pow_mem_degreeGrade k m) hf
      simpa [vadd_eq_add] using hsmul

instance mono_polynomialPowMulHom (m : ℕ) : Mono (polynomialPowMulHom k m) := by
  refine (GradedModuleCat.mono_iff_injective _).2 <|
    (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  change f * X ^ m = 0 at hf
  ext n
  rw [coeff_zero, ← coeff_mul_X_pow f m n, hf, coeff_zero]

/-- The graded monomial quotient `k[X] / (X ^ m)` in `GradedModuleCat (Polynomial.degreeGrade k)`,
constructed as the cokernel of multiplication by `X ^ m : k[X]{m} ⟶ k[X]`. -/
abbrev polynomialMonomialQuotient (m : ℕ) : GradedModuleCat.{u} (Polynomial.degreeGrade k) :=
  GradedModuleCat.cokernelObj (polynomialPowMulHom k m)

private instance moduleProjective_regular_polynomial :
    Module.Projective k[X] (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)) :=
  inferInstanceAs (Module.Projective k[X] k[X])

private instance moduleFinite_regular_polynomial :
    Module.Finite k[X] (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)) :=
  inferInstanceAs (Module.Finite k[X] k[X])

private instance moduleProjective_shiftObj_regular_polynomial (m : ℕ) :
    Module.Projective k[X]
      ((GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m) :=
  inferInstanceAs (Module.Projective k[X] k[X])

private instance moduleFinite_shiftObj_regular_polynomial (m : ℕ) :
    Module.Finite k[X]
      ((GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m) :=
  inferInstanceAs (Module.Finite k[X] k[X])

/-- **The two-term graded free resolution** `0 ⟶ k[X]{m} ⟶ k[X] ⟶ k[X] / (X ^ m) ⟶ 0` of the
graded monomial quotient `k[X] / (X ^ m)`. -/
def polynomialMonomialQuotientResolution (m : ℕ) :
    GradedProjectiveResolution.{u, u, u, u} (Polynomial.degreeGrade k)
      (polynomialMonomialQuotient k m).grading :=
  GradedProjectiveResolution.ofShortExact
    (GradedModuleCat.shortExact_cokernelπ (polynomialPowMulHom k m))

instance moduleFinite_polynomialMonomialQuotientResolution_X (m n : ℕ) :
    Module.Finite k[X] ((polynomialMonomialQuotientResolution k m).X n) := by
  unfold polynomialMonomialQuotientResolution
  exact inferInstance

/-- **For `0 < m`, the two-term resolution of `k[X] / (X ^ m)` is minimal**: multiplication by
`X ^ m` lands in the positive-degree ideal `k[X]₊`. -/
theorem isMinimal_polynomialMonomialQuotientResolution {m : ℕ} (hm : 0 < m) :
    (polynomialMonomialQuotientResolution k m).IsMinimal := by
  unfold polynomialMonomialQuotientResolution
  rw [GradedProjectiveResolution.isMinimal_ofShortExact_iff]
  intro f
  change f * X ^ m ∈ _
  rw [mul_comm]
  change (X ^ m : k[X]) • f ∈ _
  exact Submodule.smul_mem_smul
    (Submodule.mem_iSup_of_mem (m : ℤ)
      (Submodule.mem_iSup_of_mem (Int.natCast_pos.2 hm)
        (Polynomial.X_pow_mem_degreeGrade k m)))
    Submodule.mem_top

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The `Unit`-indexed basis `[k[X]]` of `K₀^gr(proj k[X])` over `ℤ[q,q⁻¹]`. -/
def polynomialRegularProjectiveBasis :
    Module.Basis Unit (LaurentPolynomial ℤ)
      (LaurentK0.{u} (gradedFiniteProjectiveModulesExactStructure (Polynomial.degreeGrade k))) :=
  connectedRegularProjectiveBasis
    (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg k)
    (Polynomial.degreeGrade_zero_eq_span_one k).le

/-- **Betti Poincaré series of `k[X] / (X ^ m)`.** In the regular basis `[k[X]]`, the Betti Poincaré
power series of `k[X] / (X ^ m)` is `1 + q^m t`. -/
theorem bettiPoincarePowerSeries_polynomialMonomialQuotientResolution (m : ℕ) (u : Unit) :
    (polynomialMonomialQuotientResolution k m).bettiPoincarePowerSeries
        (polynomialRegularProjectiveBasis k) u =
      1 + PowerSeries.C (T (m : ℤ)) * PowerSeries.X := by
  cases u
  unfold polynomialMonomialQuotientResolution polynomialRegularProjectiveBasis
  rw [GradedProjectiveResolution.bettiPoincarePowerSeries_ofShortExact]
  have h0 : (⟨GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k),
      gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :
        (gradedFiniteProjectiveModules (Polynomial.degreeGrade k)).FullSubcategory) =
      gradedRegularProjective (Polynomial.degreeGrade k) :=
    rfl
  have h1 : (⟨(GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj (m : ℤ),
      gradedFiniteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :
        (gradedFiniteProjectiveModules (Polynomial.degreeGrade k)).FullSubcategory) =
      ⟨(GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj (m : ℤ),
        gradedFiniteProjectiveModules_shiftObj
          (gradedRegularProjective (Polynomial.degreeGrade k)).property (m : ℤ)⟩ :=
    rfl
  rw [h0, h1, ← connectedRegularProjectiveBasis_apply
      (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg k)
      (Polynomial.degreeGrade_zero_eq_span_one k).le (),
    Module.Basis.repr_self, Finsupp.single_eq_same, map_one,
    connectedRegularProjectiveBasis_repr_of_shiftObj]

/-- **Betti Poincaré series of `k[X] / (X²)`**: `B(q, t) = 1 + q² t`. -/
theorem bettiPoincarePowerSeries_polynomialMonomialQuotient_two (u : Unit) :
    (polynomialMonomialQuotientResolution k 2).bettiPoincarePowerSeries
        (polynomialRegularProjectiveBasis k) u =
      1 + PowerSeries.C (T 2) * PowerSeries.X :=
  bettiPoincarePowerSeries_polynomialMonomialQuotientResolution k 2 u

/-- The resolution of `k[X] / (X²)` has a nonzero off-diagonal graded Betti number `1` at
homological degree `n = 1` and internal degree `d = 2`. -/
theorem coeff_one_two_bettiPoincarePowerSeries_polynomialMonomialQuotient_two :
    (PowerSeries.coeff 1
      ((polynomialMonomialQuotientResolution k 2).bettiPoincarePowerSeries
        (polynomialRegularProjectiveBasis k) ())).coeff 2 = 1 := by
  rw [bettiPoincarePowerSeries_polynomialMonomialQuotient_two]
  simp only [map_add, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte, zero_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one]
  rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

/-- **Linearity criterion for `k[X] / (X ^ m)` (`0 < m`).** The minimal two-term resolution of
`k[X] / (X ^ m)` is linear if and only if `m = 1`. -/
theorem isLinear_polynomialMonomialQuotientResolution_iff {m : ℕ} (hm : 0 < m) :
    (polynomialMonomialQuotientResolution k m).IsLinear ↔ m = 1 := by
  rw [GradedProjectiveResolution.isLinear_iff_diagonal_bettiPoincarePowerSeries_connected
    (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg k)
    (Polynomial.degreeGrade_zero_eq_span_one k).le
    (polynomialMonomialQuotientResolution k m)]
  constructor
  · intro hdiag
    by_contra hm1
    have hne : (1 : ℤ) ≠ (m : ℤ) := by omega
    have hz := hdiag 1 (m : ℤ) hne
    rw [← polynomialRegularProjectiveBasis,
      bettiPoincarePowerSeries_polynomialMonomialQuotientResolution] at hz
    simp only [map_add, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte, zero_add,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one] at hz
    rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hz
    exact one_ne_zero hz
  · rintro rfl n d hnd
    rw [← polynomialRegularProjectiveBasis,
      bettiPoincarePowerSeries_polynomialMonomialQuotientResolution, Nat.cast_one]
    match n with
    | 0 =>
      simp only [map_add, PowerSeries.coeff_zero_eq_constantCoeff, map_one, PowerSeries.coeff_C_mul,
        PowerSeries.constantCoeff_X, mul_zero, add_zero, LaurentPolynomial.coeff_one,
        ite_eq_right_iff]
      exact fun hd ↦ absurd hd.symm hnd
    | 1 =>
      simp only [map_add, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte, zero_add,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one]
      rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right_iff]
      exact fun hd ↦ absurd hd hnd
    | n + 2 =>
      simp [PowerSeries.coeff_one]

/-- **The minimal resolution of `k[X] / (X²)` is not linear**: its relation `X²` sits in internal
degree `2 > 1`. -/
theorem not_isLinear_polynomialMonomialQuotientResolution_two :
    ¬ (polynomialMonomialQuotientResolution k 2).IsLinear := by
  rw [isLinear_polynomialMonomialQuotientResolution_iff k two_pos]
  omega

/-- Specializing `q = 1` in the Betti Poincaré series of `k[X] / (X²)` yields `1 + t`. -/
@[simp]
theorem map_laurentEval_one_bettiPoincarePowerSeries_polynomialMonomialQuotient_two (u : Unit) :
    PowerSeries.map (laurentEval (R := ℤ) (1 : ℤˣ) : LaurentPolynomial ℤ →+* ℤ)
        ((polynomialMonomialQuotientResolution k 2).bettiPoincarePowerSeries
          (polynomialRegularProjectiveBasis k) u) =
      1 + PowerSeries.X := by
  rw [bettiPoincarePowerSeries_polynomialMonomialQuotient_two]
  simp

end Field

end TauCeti
