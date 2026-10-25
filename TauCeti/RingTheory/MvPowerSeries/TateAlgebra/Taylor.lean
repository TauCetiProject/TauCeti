/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor
public import TauCeti.RingTheory.MvPowerSeries.HasseDeriv.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst

/-!
# Taylor expansion of restricted power series

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`, let `r` be positive
radii for the variables `X₁, …, X_k`, and let `a ∈ Rᵏ` lie in the closed polydisc of radii `r`.
The translation `f(X) ↦ f(X + a)` is an isometric automorphism of `R{X/r}`
(`TauCeti.MvPowerSeries.restrictedTranslate`). Its coefficients are the values at `a` of the Hasse
derivatives of `f`:

```text
f(X + a) = ∑_ν (∂^ν f)(a) Xᵛ,    (∂^ν f)(a) = ∑_m (∏ⱼ (mⱼ + νⱼ choose νⱼ)) f_{m+ν} aᵐ.
```

Evaluating at a point `y` of the closed polydisc gives the Taylor expansion of `f` around `a`,
which converges on the whole closed polydisc of radii `r`:

```text
f(a + y) = ∑_ν (∂^ν f)(a) yᵛ.
```

The point `y` may lie in any complete ultrametric ring receiving `R` by a norm-nonincreasing
homomorphism, for instance a complete normed field extension. Hasse derivatives need no division
by factorials, so these formulas hold in every characteristic. On polynomials, translation is the
Taylor shift `MvPolynomial.taylor`, and the coefficient formula is
`MvPolynomial.coeff_taylor`; the general case follows by continuity, since polynomials are dense.

## Main results

* `TauCeti.MvPowerSeries.restrictedTranslate_polynomial`: on polynomials, translation is the
  Taylor shift `MvPolynomial.taylor`.
* `TauCeti.MvPowerSeries.coeff_restrictedTranslate`: the coefficient of `Xᵛ` in `f(X + a)` is
  `(∂^ν f)(a)`.
* `TauCeti.MvPowerSeries.hasSum_coeff_restrictedTranslate`: the binomial coefficient formula for
  translation.
* `TauCeti.MvPowerSeries.hasSum_restrictedEval₂_add`: the Taylor expansion
  `f(a + y) = ∑_ν (∂^ν f)(a) yᵛ` on the closed polydisc.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R] {r : Fin k → ℝ} [∀ i, Fact (0 < r i)] (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i)

/-- **Translation of a polynomial is its Taylor shift**: for a polynomial `p`, the translate
`p(X + a)` is `MvPolynomial.taylor a p`. -/
@[simp]
theorem restrictedTranslate_polynomial (p : MvPolynomial (Fin k) R) :
    restrictedTranslate a ha ⟨(p : MvPowerSeries (Fin k) R), p.isRestricted r⟩ =
      ⟨(MvPolynomial.taylor a p : MvPowerSeries (Fin k) R),
        (MvPolynomial.taylor a p).isRestricted r⟩ := by
  induction p using MvPolynomial.induction_on with
  | C b =>
    have h : (⟨((MvPolynomial.C b : MvPolynomial (Fin k) R) : MvPowerSeries (Fin k) R),
        (MvPolynomial.C b).isRestricted r⟩ : IsRestricted.subring (R := R) r) =
          algebraMap R _ b := Subtype.ext (by simp [coe_algebraMap_isRestrictedSubring])
    rw [h, AlgHom.commutes, ← h, MvPolynomial.taylor_C]
  | add p q hp hq =>
    have h : (⟨((p + q : MvPolynomial (Fin k) R) : MvPowerSeries (Fin k) R),
        (p + q).isRestricted r⟩ : IsRestricted.subring (R := R) r) =
          ⟨(p : MvPowerSeries (Fin k) R), p.isRestricted r⟩ +
            ⟨(q : MvPowerSeries (Fin k) R), q.isRestricted r⟩ := Subtype.ext (by simp)
    rw [h, map_add, hp, hq]
    exact Subtype.ext (by simp)
  | mul_X p i hp =>
    have h : (⟨((p * MvPolynomial.X i : MvPolynomial (Fin k) R) : MvPowerSeries (Fin k) R),
        (p * MvPolynomial.X i).isRestricted r⟩ : IsRestricted.subring (R := R) r) =
          ⟨(p : MvPowerSeries (Fin k) R), p.isRestricted r⟩ *
            ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ := Subtype.ext (by simp)
    rw [h, map_mul, hp, restrictedTranslate_X]
    exact Subtype.ext (by simp [coe_algebraMap_isRestrictedSubring])

/-- **The coefficients of a translate are Hasse derivatives**: the coefficient of `Xᵛ` in
`f(X + a)` is the value `(∂^ν f)(a)` of the `ν`-th Hasse derivative of `f` at `a`. -/
theorem coeff_restrictedTranslate (f : IsRestricted.subring (R := R) r) (ν : Fin k →₀ ℕ) :
    coeff ν (restrictedTranslate a ha f : MvPowerSeries (Fin k) R) =
      restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha (restrictedHasseDeriv ν f) := by
  -- both sides are continuous and additive in `f`, so it suffices to compare them on monomials
  have hL : Continuous fun f : IsRestricted.subring (R := R) r ↦
      coeff ν (restrictedTranslate a ha f : MvPowerSeries (Fin k) R) :=
    (continuous_coeff_isRestrictedSubring ν).comp (continuous_restrictedTranslate a ha)
  have hR : Continuous fun f : IsRestricted.subring (R := R) r ↦
      restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha (restrictedHasseDeriv ν f) :=
    (continuous_restrictedEval₂ _ _ _ _).comp (continuous_restrictedHasseDeriv ν)
  refine congrFun (hL.ext_on (dense_closure_monomial dense_univ) hR fun f hf ↦ ?_) f
  induction hf using AddSubgroup.closure_induction with
  | mem _ h =>
    obtain ⟨⟨t, b⟩, -, rfl⟩ := h
    have hp : (⟨monomial t b, isRestricted_monomial r t b⟩ : IsRestricted.subring (R := R) r) =
        ⟨((MvPolynomial.monomial t b : MvPolynomial (Fin k) R) : MvPowerSeries (Fin k) R),
          (MvPolynomial.monomial t b).isRestricted r⟩ :=
      Subtype.ext (MvPolynomial.coe_monomial t b).symm
    simp only [hp, restrictedTranslate_polynomial, restrictedHasseDeriv_polynomial,
      restrictedEval₂_polynomial, MvPolynomial.coeff_coe, MvPolynomial.coeff_taylor,
      MvPolynomial.eval₂_id]
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
  | neg _ _ h => simp [h]

/-- **The binomial coefficient formula for translation**: the coefficient of `Xᵛ` in `f(X + a)`
is the convergent sum `∑_m (∏ⱼ (mⱼ + νⱼ choose νⱼ)) f_{m+ν} aᵐ`. -/
theorem hasSum_coeff_restrictedTranslate (f : IsRestricted.subring (R := R) r)
    (ν : Fin k →₀ ℕ) :
    HasSum (fun m : Fin k →₀ ℕ ↦ ((ν.prod fun j l ↦ (m j + l).choose l : ℕ) : R) *
        coeff (m + ν) (f : MvPowerSeries (Fin k) R) * ∏ i, a i ^ m i)
      (coeff ν (restrictedTranslate a ha f : MvPowerSeries (Fin k) R)) := by
  rw [coeff_restrictedTranslate]
  convert hasSum_restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha
    (restrictedHasseDeriv ν f) using 1
  ext m
  rw [Huber.weightedEvalTerm_def, coe_restrictedHasseDeriv, coeff_hasseDeriv, RingHom.id_apply]

/-- **Taylor expansion on the closed polydisc.** For `y` in a complete ultrametric ring `S`
receiving `R` by a norm-nonincreasing homomorphism `φ`, with `‖yᵢ‖ ≤ rᵢ`, the value
`f(a + y)` is the convergent sum `∑_ν φ((∂^ν f)(a)) yᵛ`. -/
theorem hasSum_restrictedEval₂_add {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (y : Fin k → S)
    (hy : ∀ i, ‖y i‖ ≤ r i) (f : IsRestricted.subring (R := R) r) :
    HasSum (fun ν : Fin k →₀ ℕ ↦
        φ (restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha (restrictedHasseDeriv ν f)) *
          ∏ i, y i ^ ν i)
      (restrictedEval₂ φ (fun i ↦ φ (a i) + y i) hφ
        (fun i ↦ (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le ((hφ _).trans (ha i)) (hy i))) f) := by
  have h := hasSum_restrictedEval₂ φ y hφ hy (restrictedTranslate a ha f)
  rw [restrictedTranslate_def, restrictedEval₂_restrictedAnalyticSubst] at h
  convert h using 1
  · ext ν
    rw [Huber.weightedEvalTerm_def, ← restrictedTranslate_def, coeff_restrictedTranslate]
  · congr 1
    ext i
    simp [add_comm]

end TauCeti.MvPowerSeries
