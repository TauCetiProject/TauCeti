/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.WorkedExamples.Reduced
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalPairModel
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.WorkedExamples
-- Proof-only: `norm_num` evaluates the integer `gcd`s.
import Mathlib.Tactic.NormNum.GCD

/-!
# Worked examples: the two canonical equations of 11.a1, 11.a2 and 37.a1

A table of elliptic curves over `ℚ` stores two equations for each curve, and both are canonical:
the **reduced minimal equation** (`WeierstrassCurve.IsReducedMinimal`), a long equation minimal at
every prime, and the **minimal-pair equation** (`WeierstrassCurve.MinimalPairModel`), a short
equation `y² = x³ + Ax + B` over `ℤ` from which the naïve height `max (4|A|³) (27B²)` of the curve
is computed. This file certifies both for three curves of conductors `11` and `37`.

| LMFDB label | Cremona label | reduced minimal equation | `Δ_min` | minimal-pair `(A, B)` |
|---|---|---|---|---|
| 11.a1 | 11a2 | `[0, -1, 1, -7820, -263580]` | `-11` | `(-10135152, -12419196912)` |
| 11.a2 | 11a1 | `[0, -1, 1, -10, -20]` | `-11⁵` | `(-13392, -1080432)` |
| 37.a1 | 37a1 | `[0, 0, 1, -1, 0]` | `37` | `(-16, 16)` |

**The reduced minimal equations.** Each of the three equations has `Δ` coprime to `c₄`, so it is
minimal at every prime (`WeierstrassCurve.isGlobalMinimal_baseChange_of_isCoprime`), and its
coefficients `a₁, a₃ ∈ {0, 1}`, `a₂ ∈ {-1, 0, 1}` are in reduced form. By uniqueness of the reduced
minimal equation (`WeierstrassCurve.existsUnique_reducedMinimal`), it is the only reduced minimal
equation in its `ℚ`-isomorphism class: every curve isomorphic to it has it as its
`WeierstrassCurve.reducedMinimalModel`. This is what lets a label name an equation. For 11.a2 and
37.a1 this is proved in
`TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/WorkedExamples/Reduced.lean`; this file adds
11.a1. The minimal discriminant `|Δ_min|` is then read off it.

**The minimal-pair equations.** Completing the square and the cube carries an equation with
invariants `c₄, c₆` to `y² = x³ - 27c₄x - 54c₆`. For 11.a1 and 11.a2 this pair is already a minimal
pair: the `gcd` of `A` and `B` is `432 = 2⁴ ⋅ 3³`, and `2⁶ ∤ B`. For 37.a1 the pair
`(-1296, 11664) = (-3⁴ ⋅ 16, 3⁶ ⋅ 16)` is divisible by `(3⁴, 3⁶)`, and dividing out leaves
`(-16, 16)`. By uniqueness of the minimal-pair equation (`WeierstrassCurve.minimalPairModel_unique`)
these are the equations of `WeierstrassCurve.minimalPairModel`, and their heights are the naïve
heights of the curves.

**The two canonical equations differ.** A minimal-pair equation need not be minimal at `2` and `3`.
For all three curves the change of variables from the minimal-pair equation to the reduced minimal
equation has `u = 2` or `u = 6`, which is not a unit of `ℤ`, so the minimal-pair equation is not
globally minimal (`WeierstrassCurve.not_isGlobalMinimal_of_smul_eq`). For 37.a1 its
discriminant is `2¹² ⋅ 37`.

The LMFDB and Cremona labels of the two curves of conductor `11` are swapped: the equation
`y² + y = x³ - x² - 10x - 20` is Cremona's 11a1 and the LMFDB's 11.a2. Both curves are certified,
with the LMFDB names `curve11a1` of
`TauCeti/AlgebraicGeometry/EllipticCurve/TateAlgorithm/WorkedExamples.lean` and `curve11a2` of
`TauCeti/AlgebraicGeometry/EllipticCurve/WorkedExamples.lean`.

## Main results

* `TauCeti.WorkedExamples.isReducedMinimal_curve11a1`: the equation of 11.a1 is reduced minimal.
* `TauCeti.WorkedExamples.reducedMinimalModel_eq_curve11a1`: it is the reduced minimal model of
  every curve isomorphic to it.
* `TauCeti.WorkedExamples.absNorm_minimalDiscriminantIdeal_curve11a1` and its two companions:
  `|Δ_min|` is `11`, `11⁵` and `37`.
* `TauCeti.WorkedExamples.minimalPairModel_model_curve11a1` and its two companions: the
  minimal-pair equations.
* `TauCeti.WorkedExamples.naiveHeight_curve11a1` and its two companions: the naïve heights.
* `TauCeti.WorkedExamples.not_isGlobalMinimal_minimalPairCurve11a1` and its two companions: the
  minimal-pair equations are not globally minimal.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge University Press,
  1997: reduced minimal equations, and the tables.
* J. S. Balakrishnan, W. Ho, N. Kaplan, S. Spicer, W. Stein, J. Weigandt, *Databases of elliptic
  curves ordered by height and distributions of Selmer groups and ranks*, LMS J. Comput. Math.
  **19** (2016), 351–370: the minimal-pair short equation and its height.
* The L-functions and modular forms database, elliptic curves 11.a1, 11.a2 and 37.a1.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-! ### The reduced minimal equation of 11.a1 -/

/-- **11.a1 is reduced minimal**: its discriminant `-11` is coprime to its `c₄`, and its
coefficients are in reduced form. -/
theorem isReducedMinimal_curve11a1 : IsReducedMinimal (curve11a1.baseChange ℚ) :=
  (isReducedMinimal_baseChange_iff _).2 ⟨isGlobalMinimal_baseChange_of_isCoprime _ <| by
    rw [Δ_curve11a1, c₄_curve11a1, Int.isCoprime_iff_gcd_eq_one]
    norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The label 11.a1 names an equation**: every elliptic curve over `ℚ` isomorphic to 11.a1 has
`y² + y = x³ - x² - 7820x - 263580` as its reduced minimal model. -/
theorem reducedMinimalModel_eq_curve11a1 {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (C : VariableChange ℚ) (hC : C • E = curve11a1.baseChange ℚ) :
    reducedMinimalModel E = curve11a1.baseChange ℚ :=
  (eq_reducedMinimalModel isReducedMinimal_curve11a1 C hC).symm

/-! ### Minimal discriminants -/

/-- **The minimal discriminant of 11.a1 is `-11`**, of absolute value `11`. -/
@[simp]
theorem absNorm_minimalDiscriminantIdeal_curve11a1 :
    Ideal.absNorm (minimalDiscriminantIdeal ℤ (curve11a1.baseChange ℚ)) = 11 := by
  rw [absNorm_minimalDiscriminantIdeal_baseChange _ isReducedMinimal_curve11a1.isGlobalMinimal,
    Δ_curve11a1]
  norm_num

/-- **The minimal discriminant of 11.a2 is `-11⁵`**, of absolute value `161051`. -/
theorem absNorm_minimalDiscriminantIdeal_curve11a2 :
    Ideal.absNorm (minimalDiscriminantIdeal ℤ (curve11a2.baseChange ℚ)) = 161051 := by
  rw [absNorm_minimalDiscriminantIdeal_baseChange _ isReducedMinimal_curve11a2.isGlobalMinimal,
    Δ_curve11a2]
  norm_num

/-- **The minimal discriminant of 37.a1 is `37`.** -/
theorem absNorm_minimalDiscriminantIdeal_curve37a1 :
    Ideal.absNorm (minimalDiscriminantIdeal ℤ (curve37a1.baseChange ℚ)) = 37 := by
  rw [absNorm_minimalDiscriminantIdeal_baseChange _ isReducedMinimal_curve37a1.isGlobalMinimal,
    Δ_curve37a1]
  norm_num

/-! ### Minimal-pair equations and naïve heights -/

/-- The minimal-pair equation `y² = x³ - 10135152x - 12419196912` of 11.a1. -/
abbrev minimalPairCurve11a1 : WeierstrassCurve ℤ := shortCurve (-10135152) (-12419196912)

/-- The minimal-pair equation `y² = x³ - 13392x - 1080432` of 11.a2. -/
abbrev minimalPairCurve11a2 : WeierstrassCurve ℤ := shortCurve (-13392) (-1080432)

/-- The minimal-pair equation `y² = x³ - 16x + 16` of 37.a1. -/
abbrev minimalPairCurve37a1 : WeierstrassCurve ℤ := shortCurve (-16) 16

/-- The changes of variables `(u, r, s, t) = (6, -12, 0, 108)`, carrying the minimal-pair
equations of 11.a1 and 11.a2 to their reduced minimal equations. -/
private def variableChangeElevenA : VariableChange ℚ :=
  ⟨Units.mk0 6 (by norm_num), -12, 0, 108⟩

/-- The change of variables `(u, r, s, t) = (2, 0, 0, 4)`, carrying the minimal-pair equation of
37.a1 to its reduced minimal equation. -/
private def variableChangeThirtySevenA : VariableChange ℚ :=
  ⟨Units.mk0 2 (by norm_num), 0, 0, 4⟩

private theorem variableChangeElevenA_smul_minimalPairCurve11a1 :
    variableChangeElevenA • minimalPairCurve11a1.baseChange ℚ = curve11a1.baseChange ℚ := by
  ext <;> norm_num [variableChangeElevenA, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, WeierstrassCurve.baseChange]

private theorem variableChangeElevenA_smul_minimalPairCurve11a2 :
    variableChangeElevenA • minimalPairCurve11a2.baseChange ℚ = curve11a2.baseChange ℚ := by
  ext <;> norm_num [variableChangeElevenA, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, WeierstrassCurve.baseChange]

private theorem variableChangeThirtySevenA_smul_minimalPairCurve37a1 :
    variableChangeThirtySevenA • minimalPairCurve37a1.baseChange ℚ = curve37a1.baseChange ℚ := by
  ext <;> norm_num [variableChangeThirtySevenA, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, WeierstrassCurve.baseChange]

/-- `y² = x³ - 10135152x - 12419196912` is a minimal pair: the `gcd` of its coefficients is
`432 = 2⁴ ⋅ 3³`, and `2⁶` does not divide `B`. -/
theorem isMinimalPairNF_minimalPairCurve11a1 : IsMinimalPairNF minimalPairCurve11a1 :=
  .of_forall_le 4 (by norm_num) (by norm_num) fun ℓ hℓ hp ↦ by
    interval_cases ℓ <;> first | exact absurd hp Nat.not_prime_one | norm_num at hp ⊢

/-- `y² = x³ - 13392x - 1080432` is a minimal pair: the `gcd` of its coefficients is
`432 = 2⁴ ⋅ 3³`, and `2⁶` does not divide `B`. -/
theorem isMinimalPairNF_minimalPairCurve11a2 : IsMinimalPairNF minimalPairCurve11a2 :=
  .of_forall_le 4 (by norm_num) (by norm_num) fun ℓ hℓ hp ↦ by
    interval_cases ℓ <;> first | exact absurd hp Nat.not_prime_one | norm_num at hp ⊢

/-- `y² = x³ - 16x + 16` is a minimal pair: the `gcd` of its coefficients is `2⁴`, and `2⁶` does
not divide `16`. -/
theorem isMinimalPairNF_minimalPairCurve37a1 : IsMinimalPairNF minimalPairCurve37a1 :=
  .of_forall_le 2 (by norm_num) (by norm_num) fun ℓ hℓ hp ↦ by
    interval_cases ℓ <;> first | exact absurd hp Nat.not_prime_one | norm_num at hp ⊢

/-- **The minimal-pair equation of 11.a1** is `y² = x³ - 10135152x - 12419196912`. -/
@[simp]
theorem minimalPairModel_model_curve11a1 :
    (minimalPairModel (curve11a1.baseChange ℚ)).model = minimalPairCurve11a1 :=
  minimalPairModel_unique _ _ ⟨_, isMinimalPairNF_minimalPairCurve11a1, _,
    variableChangeElevenA_smul_minimalPairCurve11a1⟩

/-- **The minimal-pair equation of 11.a2** is `y² = x³ - 13392x - 1080432`. -/
@[simp]
theorem minimalPairModel_model_curve11a2 :
    (minimalPairModel (curve11a2.baseChange ℚ)).model = minimalPairCurve11a2 :=
  minimalPairModel_unique _ _ ⟨_, isMinimalPairNF_minimalPairCurve11a2, _,
    variableChangeElevenA_smul_minimalPairCurve11a2⟩

/-- **The minimal-pair equation of 37.a1** is `y² = x³ - 16x + 16`. -/
@[simp]
theorem minimalPairModel_model_curve37a1 :
    (minimalPairModel (curve37a1.baseChange ℚ)).model = minimalPairCurve37a1 :=
  minimalPairModel_unique _ _ ⟨_, isMinimalPairNF_minimalPairCurve37a1, _,
    variableChangeThirtySevenA_smul_minimalPairCurve37a1⟩

/-- **The naïve height of 11.a1** is `27 ⋅ 12419196912²`. -/
@[simp]
theorem naiveHeight_curve11a1 :
    naiveHeight (curve11a1.baseChange ℚ) = 4164384202353819065088 := by
  rw [naiveHeight_eq ⟨_, isMinimalPairNF_minimalPairCurve11a1, _,
    variableChangeElevenA_smul_minimalPairCurve11a1⟩, MinimalPairModel.height_def]
  norm_num

/-- **The naïve height of 11.a2** is `27 ⋅ 1080432²`. -/
@[simp]
theorem naiveHeight_curve11a2 : naiveHeight (curve11a2.baseChange ℚ) = 31517999278848 := by
  rw [naiveHeight_eq ⟨_, isMinimalPairNF_minimalPairCurve11a2, _,
    variableChangeElevenA_smul_minimalPairCurve11a2⟩, MinimalPairModel.height_def]
  norm_num

/-- **The naïve height of 37.a1** is `4 ⋅ 16³ = 16384`. -/
@[simp]
theorem naiveHeight_curve37a1 : naiveHeight (curve37a1.baseChange ℚ) = 16384 := by
  rw [naiveHeight_eq ⟨_, isMinimalPairNF_minimalPairCurve37a1, _,
    variableChangeThirtySevenA_smul_minimalPairCurve37a1⟩, MinimalPairModel.height_def]
  norm_num

/-! ### The minimal-pair equations are not minimal -/

/-- The base change of the minimal-pair equation of 11.a1 is an elliptic curve, being isomorphic to
11.a1. -/
instance : (minimalPairCurve11a1.baseChange ℚ).IsElliptic := by
  rw [← inv_smul_smul variableChangeElevenA (minimalPairCurve11a1.baseChange ℚ),
    variableChangeElevenA_smul_minimalPairCurve11a1]
  infer_instance

/-- The base change of the minimal-pair equation of 11.a2 is an elliptic curve, being isomorphic to
11.a2. -/
instance : (minimalPairCurve11a2.baseChange ℚ).IsElliptic := by
  rw [← inv_smul_smul variableChangeElevenA (minimalPairCurve11a2.baseChange ℚ),
    variableChangeElevenA_smul_minimalPairCurve11a2]
  infer_instance

/-- The base change of the minimal-pair equation of 37.a1 is an elliptic curve, being isomorphic to
37.a1. -/
instance : (minimalPairCurve37a1.baseChange ℚ).IsElliptic := by
  rw [← inv_smul_smul variableChangeThirtySevenA (minimalPairCurve37a1.baseChange ℚ),
    variableChangeThirtySevenA_smul_minimalPairCurve37a1]
  infer_instance

/-- **The minimal-pair equation of 11.a1 is not globally minimal**: it is carried to the reduced
minimal equation with `u = 6`. -/
theorem not_isGlobalMinimal_minimalPairCurve11a1 :
    ¬ IsGlobalMinimal ℤ (minimalPairCurve11a1.baseChange ℚ) :=
  not_isGlobalMinimal_of_smul_eq isReducedMinimal_curve11a1.isGlobalMinimal _
    variableChangeElevenA_smul_minimalPairCurve11a1
    fun u ↦ by rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num [variableChangeElevenA]

/-- **The minimal-pair equation of 11.a2 is not globally minimal**: it is carried to the reduced
minimal equation with `u = 6`. -/
theorem not_isGlobalMinimal_minimalPairCurve11a2 :
    ¬ IsGlobalMinimal ℤ (minimalPairCurve11a2.baseChange ℚ) :=
  not_isGlobalMinimal_of_smul_eq isReducedMinimal_curve11a2.isGlobalMinimal _
    variableChangeElevenA_smul_minimalPairCurve11a2
    fun u ↦ by rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num [variableChangeElevenA]

/-- **The minimal-pair equation of 37.a1 is not globally minimal**: it is carried to the reduced
minimal equation with `u = 2`, and its discriminant is `2¹² ⋅ 37`. -/
theorem not_isGlobalMinimal_minimalPairCurve37a1 :
    ¬ IsGlobalMinimal ℤ (minimalPairCurve37a1.baseChange ℚ) :=
  not_isGlobalMinimal_of_smul_eq isReducedMinimal_curve37a1.isGlobalMinimal _
    variableChangeThirtySevenA_smul_minimalPairCurve37a1
    fun u ↦ by
      rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num [variableChangeThirtySevenA]

end TauCeti.WorkedExamples
