/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
public import TauCeti.AlgebraicGeometry.EllipticCurve.WorkedExamples

/-!
# Worked examples: reduced minimal equations of curves over `ℚ`

Every elliptic curve over `ℚ` has exactly one reduced minimal equation in its isomorphism class:
an equation that is minimal at every prime and satisfies `a₁, a₃ ∈ {0, 1}` and
`a₂ ∈ {-1, 0, 1}` (`WeierstrassCurve.existsUnique_reducedMinimal`). This is the equation by which
Cremona's tables and the LMFDB present a curve. Each database label identifies the curve's
isomorphism class; the displayed equation is its canonical reduced-minimal representative.
This file certifies the equations of two curves from those tables:

| LMFDB label | Cremona label | `[a₁, a₂, a₃, a₄, a₆]` | `Δ` | `c₄` |
|---|---|---|---|---|
| 11.a2 | 11a1 | `[0, -1, 1, -10, -20]` | `-11⁵` | `2⁴ · 31` |
| 37.a1 | 37a1 | `[0, 0, 1, -1, 0]` | `37` | `2⁴ · 3` |

The two labelling schemes differ on the conductor `11` isogeny class: the equation
`y² + y = x³ - x² - 10 x - 20` is Cremona's 11a1 and the LMFDB's 11.a2, in agreement with
`TauCeti.WorkedExamples.curve11a2`.

For each curve, the results below make the label name an equation: the displayed equation is the
reduced minimal model of every equation isomorphic to it, and no other reduced minimal equation is
isomorphic to it. They also compute the minimal discriminant ideal of each curve, an invariant of
its isomorphism class.

## Main results

* `TauCeti.WorkedExamples.isReducedMinimal_curve11a2` and
  `TauCeti.WorkedExamples.isReducedMinimal_curve37a1`: both equations are reduced minimal.
* `TauCeti.WorkedExamples.reducedMinimalModel_eq_curve11a2` and
  `TauCeti.WorkedExamples.reducedMinimalModel_eq_curve37a1`: each is the reduced minimal model of
  every curve isomorphic to it.
* `TauCeti.WorkedExamples.isReducedMinimal_and_exists_smul_eq_curve11a2_iff` and
  `TauCeti.WorkedExamples.isReducedMinimal_and_exists_smul_eq_curve37a1_iff`: each is the only
  reduced minimal equation in its isomorphism class.
* `TauCeti.WorkedExamples.minimalDiscriminantIdeal_curve11a2` and
  `TauCeti.WorkedExamples.minimalDiscriminantIdeal_curve37a1`: the minimal discriminant ideals are
  `(11⁵)` and `(37)`.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge University Press,
  1997: the tables, curves 11A1 and 37A1, and the normalisation of a minimal equation.
* The L-functions and modular forms database, elliptic curves 11.a2 and 37.a1.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-! ### The curve 11.a2 (Cremona 11a1) -/

-- The discriminant `-11⁵` and `c₄ = 496` are coprime, so the equation is minimal at every prime
-- (`isGlobalMinimal_baseChange_of_isCoprime`), and its coefficients are already normalised.
/-- **`y² + y = x³ - x² - 10 x - 20` is a reduced minimal equation**: it is the canonical
reduced-minimal representative of 11.a2. -/
theorem isReducedMinimal_curve11a2 : IsReducedMinimal (curve11a2.baseChange ℚ) := by
  refine isReducedMinimal_iff.2
    ⟨isGlobalMinimal_baseChange_of_isCoprime (O := ℤ) curve11a2 ?_, by simp [baseChange]⟩
  rw [Δ_curve11a2, c₄_curve11a2, Int.isCoprime_iff_gcd_eq_one]
  norm_num

/-- **The reduced minimal model of any curve isomorphic to 11.a2 is
`y² + y = x³ - x² - 10 x - 20`**, the canonical reduced-minimal representative of that class. -/
theorem reducedMinimalModel_eq_curve11a2 {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (C : VariableChange ℚ) (hC : C • E = curve11a2.baseChange ℚ) :
    reducedMinimalModel E = curve11a2.baseChange ℚ :=
  (eq_reducedMinimalModel isReducedMinimal_curve11a2 C hC).symm

/-- **`y² + y = x³ - x² - 10 x - 20` is the only reduced minimal equation of 11.a2**: an equation is
reduced minimal and isomorphic to it exactly when it is this equation. -/
theorem isReducedMinimal_and_exists_smul_eq_curve11a2_iff {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    (IsReducedMinimal W ∧ ∃ C : VariableChange ℚ, C • W = curve11a2.baseChange ℚ) ↔
      W = curve11a2.baseChange ℚ := by
  refine ⟨fun ⟨hW, C, hC⟩ ↦ hW.eq_of_smul_eq isReducedMinimal_curve11a2 C hC, ?_⟩
  rintro rfl
  exact ⟨isReducedMinimal_curve11a2, 1, one_smul _ _⟩

/-- **The minimal discriminant ideal of 11.a2 is `(11⁵)`.** -/
@[simp]
theorem minimalDiscriminantIdeal_curve11a2 :
    minimalDiscriminantIdeal ℤ (curve11a2.baseChange ℚ) = Ideal.span {11 ^ 5} := by
  rw [minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal
    isReducedMinimal_curve11a2.isGlobalMinimal (d := curve11a2.Δ) (by simp [baseChange]),
    Δ_curve11a2, Ideal.span_singleton_neg]

/-! ### The curve 37.a1 -/

-- The discriminant `37` and `c₄ = 48` are coprime, so the equation is minimal at every prime
-- (`isGlobalMinimal_baseChange_of_isCoprime`), and its coefficients are already normalised.
/-- **`y² + y = x³ - x` is a reduced minimal equation**: it is the canonical reduced-minimal
representative of 37.a1. -/
theorem isReducedMinimal_curve37a1 : IsReducedMinimal (curve37a1.baseChange ℚ) := by
  refine isReducedMinimal_iff.2
    ⟨isGlobalMinimal_baseChange_of_isCoprime (O := ℤ) curve37a1 ?_, by simp [baseChange]⟩
  rw [Δ_curve37a1, c₄_curve37a1, Int.isCoprime_iff_gcd_eq_one]
  norm_num

/-- **The reduced minimal model of any curve isomorphic to 37.a1 is `y² + y = x³ - x`**,
the canonical reduced-minimal representative of that class. -/
theorem reducedMinimalModel_eq_curve37a1 {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (C : VariableChange ℚ) (hC : C • E = curve37a1.baseChange ℚ) :
    reducedMinimalModel E = curve37a1.baseChange ℚ :=
  (eq_reducedMinimalModel isReducedMinimal_curve37a1 C hC).symm

/-- **`y² + y = x³ - x` is the only reduced minimal equation of 37.a1**: an equation is
reduced minimal and isomorphic to it exactly when it is this equation. -/
theorem isReducedMinimal_and_exists_smul_eq_curve37a1_iff {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    (IsReducedMinimal W ∧ ∃ C : VariableChange ℚ, C • W = curve37a1.baseChange ℚ) ↔
      W = curve37a1.baseChange ℚ := by
  refine ⟨fun ⟨hW, C, hC⟩ ↦ hW.eq_of_smul_eq isReducedMinimal_curve37a1 C hC, ?_⟩
  rintro rfl
  exact ⟨isReducedMinimal_curve37a1, 1, one_smul _ _⟩

/-- **The minimal discriminant ideal of 37.a1 is `(37)`.** -/
@[simp]
theorem minimalDiscriminantIdeal_curve37a1 :
    minimalDiscriminantIdeal ℤ (curve37a1.baseChange ℚ) = Ideal.span {37} := by
  rw [minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal
    isReducedMinimal_curve37a1.isGlobalMinimal (d := curve37a1.Δ) (by simp [baseChange]),
    Δ_curve37a1]

end TauCeti.WorkedExamples
