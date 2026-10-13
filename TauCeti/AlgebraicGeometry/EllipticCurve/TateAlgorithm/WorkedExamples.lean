/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Type
-- Proof-only: divisibility of integers by powers of `p` is read in `ℤ`.
import TauCeti.Data.Nat.Prime.IntCast
-- Proof-only: `norm_num` decides primality of the small primes.
import Mathlib.Tactic.NormNum.Prime

/-!
# Worked examples: Tate's algorithm on curves over `ℚ`, one for each reduction symbol

This file runs Tate's algorithm on integral Weierstrass equations of elliptic curves over `ℚ`, at
one prime each, and certifies the symbol at which it stops. Every kind of reduction symbol occurs:
`I₀`, `Iₙ` for `n = 1, 2, 5, 8`, `II`, `III`, `IV`, `Iₙ*` for `n = 0, 1, 2`, `IV*`, `III*` and
`II*`. The curves are taken from Cremona's tables, so each certificate can be compared with the
reduction data recorded there and in the LMFDB.

Each certificate is stated over an arbitrary discrete valuation ring `R`, with fraction field
`K`, in which the prime `p` is a uniformiser, for instance `ℤ_[p]` or the localisation of `ℤ` at
`p`. It has two parts:

* the equation, read over `K`, is minimal over `R`, because `p ^ 12` does not divide its
  discriminant (`WeierstrassCurve.isMinimal_baseChange_of_not_pow_twelve_dvd_Δ`);
* an explicit change of variables over `ℤ`, with `u = 1`, carries it to an equation on which
  Tate's algorithm stops with the stated symbol (`WeierstrassCurve.IsTateTerminal`).

Minimality matters: Tate's algorithm is run on a minimal equation, and only there does the symbol
describe the curve. The divisibility tests of the algorithm are decided over `ℤ`, and read over
`R` because the cast `ℤ → R` reflects divisibility by powers of `p`
(`Nat.Prime.pow_dvd_intCast_iff`, `WeierstrassCurve.isTateTerminal_map_iff`).

| LMFDB label | Cremona label | `[a₁, a₂, a₃, a₄, a₆]` | `Δ` | `p` | symbol | `(r, s, t)` |
|---|---|---|---|---|---|---|
| 11.a1 | 11a2 | `[0, -1, 1, -7820, -263580]` | `-11` | `11` | `I₁` | `(5, 0, 5)` |
| 11.a1 | 11a2 | `[0, -1, 1, -7820, -263580]` | `-11` | `2` | `I₀` | `(0, 0, 0)` |
| 11.a2 | 11a1 | `[0, -1, 1, -10, -20]` | `-11⁵` | `11` | `I₅` | `(5, 0, 5)` |
| 14.a4 | 14a6 | `[1, 0, 1, -11, 12]` | `2 · 7²` | `7` | `I₂` | `(0, 0, 3)` |
| 24.a5 | 24a4 | `[0, -1, 0, 1, 0]` | `-2⁴ · 3` | `3` | `I₁` | `(2, 0, 0)` |
| 45.a8 | 45a6 | `[1, -1, 0, 315, 1066]` | `-3⁸ · 5⁸` | `5` | `I₈` | `(3, 0, 1)` |
| 27.a4 | 27a3 | `[0, 0, 1, 0, 0]` | `-3³` | `3` | `II` | `(2, 0, 1)` |
| 24.a5 | 24a4 | `[0, -1, 0, 1, 0]` | `-2⁴ · 3` | `2` | `III` | `(1, 0, 1)` |
| 20.a3 | 20a2 | `[0, 1, 0, -1, 0]` | `2⁴ · 5` | `2` | `IV` | `(1, 0, 1)` |
| 32.a1 | 32a3 | `[0, 0, 0, -11, -14]` | `2⁹` | `2` | `I₀*` | `(1, 1, 0)` |
| 24.a4 | 24a1 | `[0, -1, 0, -4, 4]` | `2⁸ · 3²` | `2` | `I₁*` | `(0, 1, 2)` |
| 45.a8 | 45a6 | `[1, -1, 0, 315, 1066]` | `-3⁸ · 5⁸` | `3` | `I₂*` | `(2, 1, 26)` |
| 20.a2 | 20a3 | `[0, 1, 0, -36, -140]` | `-2⁸ · 5⁶` | `2` | `IV*` | `(0, 1, 2)` |
| 24.a3 | 24a2 | `[0, -1, 0, -24, -36]` | `2¹⁰ · 3⁴` | `2` | `III*` | `(2, 1, 4)` |
| 24.a1 | 24a5 | `[0, -1, 0, -384, -2772]` | `2¹¹ · 3²` | `2` | `II*` | `(2, 1, 4)` |

Of the multiplicative entries, 11.a1 and 11.a2 at `11` and 14.a4 at `7` are split, while 24.a5 at
`3` and 45.a8 at `5` are nonsplit. That distinction, and the Tamagawa numbers it determines, are
not certified here; neither is the independence of the symbol from the choices made in running the
algorithm.

The last section checks semistability over `ℤ` (`WeierstrassCurve.IsSemistable`) against these
symbols. At the primes not dividing the discriminant the reduction is good; at the others it is
the type the symbol names. So 11.a1, whose only bad prime is `11`, of symbol `I₁`, has
multiplicative reduction there, in agreement with its semistability, which the coprimality of its
discriminant and `c₄` gives directly; while 27.a4, of symbol `II` at `3`, has additive reduction
there and is not semistable.

## Main results

* `TauCeti.WorkedExamples.isMinimal_and_exists_isTateTerminal_curve11a1_11` and its fourteen
  companions, one for each row of the table.
* `TauCeti.WorkedExamples.hasGoodReduction_curve11a1_iff` and
  `TauCeti.WorkedExamples.hasMultiplicativeReduction_curve11a1`: 11.a1 has good reduction away
  from `11` and multiplicative reduction at `11`.
* `TauCeti.WorkedExamples.isSemistable_curve11a1`: 11.a1 is semistable.
* `TauCeti.WorkedExamples.hasGoodReduction_curve27a4_iff` and
  `TauCeti.WorkedExamples.hasAdditiveReduction_curve27a4`: 27.a4 has good reduction away from `3`
  and additive reduction at `3`.
* `TauCeti.WorkedExamples.not_isSemistable_curve27a4`: 27.a4 is not semistable.

## References

* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, GTM 106, VII.5.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., the tables; the equations
  above are those of Cremona's `ecdata` tables (`allcurves`, with the label correspondence of
  `alllabels`).
* The L-functions and modular forms database, the elliptic curves above, which record the same
  reduction symbols.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral equation over `ℤ` whose discriminant is not divisible by `p ^ 12`, and which a
change of variables over `ℤ` carries to an equation on which Tate's algorithm stops at `s`, is
minimal over any discrete valuation ring `R` with uniformiser `ϖ = p`, and Tate's algorithm run
over `R` stops at `s` after the image of that change of variables. -/
private theorem isMinimal_and_exists_isTateTerminal {p : ℕ} (hp : p.Prime) {ϖ : R}
    (hpϖ : (p : R) = ϖ) (hϖ : Irreducible ϖ) (W : WeierstrassCurve ℤ)
    (hΔ : ¬ (p : ℤ) ^ 12 ∣ W.Δ) (C : VariableChange ℤ) {s : ReductionSymbol}
    (h : (C • W).IsTateTerminal (p : ℤ) s) :
    IsMinimal R ((W.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • W.map (Int.castRingHom R)).IsTateTerminal ϖ s := by
  subst hpϖ
  have hdvd := hp.pow_dvd_intCast_iff hϖ.ne_zero hϖ.not_isUnit
  refine ⟨isMinimal_baseChange_of_not_pow_twelve_dvd_Δ R _ hϖ ?_, C.map (Int.castRingHom R), ?_⟩
  · rwa [map_Δ, eq_intCast, hdvd]
  · rw [map_variableChange, ← map_natCast (Int.castRingHom R) p,
      isTateTerminal_map_iff _ fun n x ↦ by simpa using hdvd n x]
    exact h

/-! ### Multiplicative and good reduction: the symbols `Iₙ` -/

/-- The curve 11.a1, `y² + y = x³ - x² - 7820 x - 263580`, of discriminant `-11`. -/
abbrev curve11a1 : WeierstrassCurve ℤ := ⟨0, -1, 1, -7820, -263580⟩

/-- **Tate's algorithm stops at `I₁` on 11.a1 at `11`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve11a1_11 (h : Irreducible (11 : R)) :
    IsMinimal R ((curve11a1.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve11a1.map (Int.castRingHom R)).IsTateTerminal 11 (.I 1) :=
  isMinimal_and_exists_isTateTerminal K (p := 11) (by norm_num) (by norm_num) h curve11a1
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 5, 0, 5⟩ (by simp [variableChange_def, Δ, b₂, b₄, b₆, b₈])

/-- **Tate's algorithm stops at `I₀` on 11.a1 at `2`**: the equation has good reduction there,
and is minimal. -/
theorem isMinimal_and_exists_isTateTerminal_curve11a1_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve11a1.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve11a1.map (Int.castRingHom R)).IsTateTerminal 2 (.I 0) :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve11a1
    (by simp [Δ, b₂, b₄, b₆, b₈]) 1 (by simp [Δ, b₂, b₄, b₆, b₈])

/-- The curve 11.a2, `y² + y = x³ - x² - 10 x - 20`, of discriminant `-11⁵`. -/
abbrev curve11a2 : WeierstrassCurve ℤ := ⟨0, -1, 1, -10, -20⟩

/-- **Tate's algorithm stops at `I₅` on 11.a2 at `11`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve11a2_11 (h : Irreducible (11 : R)) :
    IsMinimal R ((curve11a2.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve11a2.map (Int.castRingHom R)).IsTateTerminal 11 (.I 5) :=
  isMinimal_and_exists_isTateTerminal K (p := 11) (by norm_num) (by norm_num) h curve11a2
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 5, 0, 5⟩ (by simp [variableChange_def, Δ, b₂, b₄, b₆, b₈])

/-- The curve 14.a4, `y² + xy + y = x³ - 11 x + 12`, of discriminant `2 · 7²`. -/
abbrev curve14a4 : WeierstrassCurve ℤ := ⟨1, 0, 1, -11, 12⟩

/-- **Tate's algorithm stops at `I₂` on 14.a4 at `7`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve14a4_7 (h : Irreducible (7 : R)) :
    IsMinimal R ((curve14a4.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve14a4.map (Int.castRingHom R)).IsTateTerminal 7 (.I 2) :=
  isMinimal_and_exists_isTateTerminal K (p := 7) (by norm_num) (by norm_num) h curve14a4
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 0, 0, 3⟩ (by simp [variableChange_def, Δ, b₂, b₄, b₆, b₈])

/-- The curve 24.a5, `y² = x³ - x² + x`, of discriminant `-2⁴ · 3`. -/
abbrev curve24a5 : WeierstrassCurve ℤ := ⟨0, -1, 0, 1, 0⟩

/-- **Tate's algorithm stops at `I₁` on 24.a5 at `3`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve24a5_3 (h : Irreducible (3 : R)) :
    IsMinimal R ((curve24a5.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve24a5.map (Int.castRingHom R)).IsTateTerminal 3 (.I 1) :=
  isMinimal_and_exists_isTateTerminal K (p := 3) (by norm_num) (by norm_num) h curve24a5
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 2, 0, 0⟩ (by simp [variableChange_def, Δ, b₂, b₄, b₆, b₈])

/-- The curve 45.a8, `y² + xy = x³ - x² + 315 x + 1066`, of discriminant `-3⁸ · 5⁸`. -/
abbrev curve45a8 : WeierstrassCurve ℤ := ⟨1, -1, 0, 315, 1066⟩

/-- **Tate's algorithm stops at `I₈` on 45.a8 at `5`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve45a8_5 (h : Irreducible (5 : R)) :
    IsMinimal R ((curve45a8.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve45a8.map (Int.castRingHom R)).IsTateTerminal 5 (.I 8) :=
  isMinimal_and_exists_isTateTerminal K (p := 5) (by norm_num) (by norm_num) h curve45a8
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 3, 0, 1⟩ (by simp [variableChange_def, Δ, b₂, b₄, b₆, b₈])

/-! ### Additive reduction, Steps 3 to 5: the symbols `II`, `III` and `IV` -/

/-- The curve 27.a4, `y² + y = x³`, of discriminant `-3³`. -/
abbrev curve27a4 : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, 0⟩

/-- **Tate's algorithm stops at `II` on 27.a4 at `3`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve27a4_3 (h : Irreducible (3 : R)) :
    IsMinimal R ((curve27a4.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve27a4.map (Int.castRingHom R)).IsTateTerminal 3 .II :=
  isMinimal_and_exists_isTateTerminal K (p := 3) (by norm_num) (by norm_num) h curve27a4
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 2, 0, 1⟩ (by simp [variableChange_def, b₂])

/-- **Tate's algorithm stops at `III` on 24.a5 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve24a5_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve24a5.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve24a5.map (Int.castRingHom R)).IsTateTerminal 2 .III :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve24a5
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 1, 0, 1⟩ (by simp [variableChange_def, b₂, b₈])

/-- The curve 20.a3, `y² = x³ + x² - x`, of discriminant `2⁴ · 5`. -/
abbrev curve20a3 : WeierstrassCurve ℤ := ⟨0, 1, 0, -1, 0⟩

/-- **Tate's algorithm stops at `IV` on 20.a3 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve20a3_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve20a3.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve20a3.map (Int.castRingHom R)).IsTateTerminal 2 .IV :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve20a3
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 1, 0, 1⟩ (by simp [variableChange_def, b₂, b₆, b₈])

/-! ### Additive reduction, Steps 6 and 7: the symbols `Iₙ*` -/

/-- The curve 32.a1, `y² = x³ - 11 x - 14`, of discriminant `2⁹`. -/
abbrev curve32a1 : WeierstrassCurve ℤ := ⟨0, 0, 0, -11, -14⟩

/-- **Tate's algorithm stops at `I₀*` on 32.a1 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve32a1_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve32a1.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R,
        (C • curve32a1.map (Int.castRingHom R)).IsTateTerminal 2 (.IStar 0) :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve32a1
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 1, 1, 0⟩ (by simp [variableChange_def, Cubic.discr])

/-- The curve 24.a4, `y² = x³ - x² - 4 x + 4`, of discriminant `2⁸ · 3²`. -/
abbrev curve24a4 : WeierstrassCurve ℤ := ⟨0, -1, 0, -4, 4⟩

/-- **Tate's algorithm stops at `I₁*` on 24.a4 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve24a4_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve24a4.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R,
        (C • curve24a4.map (Int.castRingHom R)).IsTateTerminal 2 (.IStar 1) :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve24a4
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 0, 1, 2⟩ (by simp [variableChange_def, b₆])

/-- **Tate's algorithm stops at `I₂*` on 45.a8 at `3`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve45a8_3 (h : Irreducible (3 : R)) :
    IsMinimal R ((curve45a8.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R,
        (C • curve45a8.map (Int.castRingHom R)).IsTateTerminal 3 (.IStar 2) :=
  isMinimal_and_exists_isTateTerminal K (p := 3) (by norm_num) (by norm_num) h curve45a8
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 2, 1, 26⟩ (by simp [variableChange_def, discrim])

/-! ### Additive reduction, Steps 8 to 10: the symbols `IV*`, `III*` and `II*` -/

/-- The curve 20.a2, `y² = x³ + x² - 36 x - 140`, of discriminant `-2⁸ · 5⁶`. -/
abbrev curve20a2 : WeierstrassCurve ℤ := ⟨0, 1, 0, -36, -140⟩

/-- **Tate's algorithm stops at `IV*` on 20.a2 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve20a2_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve20a2.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve20a2.map (Int.castRingHom R)).IsTateTerminal 2 .IVStar :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve20a2
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 0, 1, 2⟩ (by simp [variableChange_def, b₆])

/-- The curve 24.a3, `y² = x³ - x² - 24 x - 36`, of discriminant `2¹⁰ · 3⁴`. -/
abbrev curve24a3 : WeierstrassCurve ℤ := ⟨0, -1, 0, -24, -36⟩

/-- **Tate's algorithm stops at `III*` on 24.a3 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve24a3_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve24a3.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R,
        (C • curve24a3.map (Int.castRingHom R)).IsTateTerminal 2 .IIIStar :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve24a3
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 2, 1, 4⟩ (by simp [variableChange_def])

/-- The curve 24.a1, `y² = x³ - x² - 384 x - 2772`, of discriminant `2¹¹ · 3²`. -/
abbrev curve24a1 : WeierstrassCurve ℤ := ⟨0, -1, 0, -384, -2772⟩

/-- **Tate's algorithm stops at `II*` on 24.a1 at `2`**, and the equation is
minimal there. -/
theorem isMinimal_and_exists_isTateTerminal_curve24a1_2 (h : Irreducible (2 : R)) :
    IsMinimal R ((curve24a1.map (Int.castRingHom R)).baseChange K) ∧
      ∃ C : VariableChange R, (C • curve24a1.map (Int.castRingHom R)).IsTateTerminal 2 .IIStar :=
  isMinimal_and_exists_isTateTerminal K (p := 2) (by norm_num) (by norm_num) h curve24a1
    (by simp [Δ, b₂, b₄, b₆, b₈]) ⟨1, 2, 1, 4⟩ (by simp [variableChange_def])

/-! ### Semistability read off the symbols

The symbols above are computed at one prime each. Together with good reduction at the primes not
dividing the discriminant, they decide the reduction type of the curve at every prime of `ℤ`, and
hence whether it is semistable (`WeierstrassCurve.IsSemistable`). On 11.a1, of discriminant `-11`,
the only bad prime is `11`, where the symbol `I₁` gives multiplicative reduction, as semistability
requires. On 27.a4, of discriminant `-3³`, the symbol `II` at `3` gives additive reduction: the
curve is not semistable. -/

section Semistable

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-- The discriminant of 11.a1 is `-11`. -/
theorem Δ_curve11a1 : curve11a1.Δ = -11 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- 11.a1 is an elliptic curve over `ℚ`. -/
instance : (curve11a1.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve11a1]
  norm_num

/-- The discriminant of 11.a2 is `-11⁵`. -/
@[simp]
theorem Δ_curve11a2 : curve11a2.Δ = -161051 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- 11.a2 is an elliptic curve over `ℚ`. -/
instance : (curve11a2.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve11a2]
  norm_num

/-- The `c₄` invariant of 11.a2 is `496 = 2⁴ ⋅ 31`. -/
@[simp]
theorem c₄_curve11a2 : curve11a2.c₄ = 496 := by
  simp [c₄, b₂, b₄]

/-- The discriminant of 27.a4 is `-3³`. -/
theorem Δ_curve27a4 : curve27a4.Δ = -27 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- 27.a4 is an elliptic curve over `ℚ`. -/
instance : (curve27a4.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve27a4]
  norm_num

variable (v : HeightOneSpectrum ℤ)

/-! #### 11.a1: semistable, of symbol `I₁` at its only bad prime -/

/-- **11.a1 has multiplicative reduction at `11`**: Tate's algorithm stops there at `I₁`, which is
neither `I₀` nor an additive symbol. -/
theorem hasMultiplicativeReduction_curve11a1 (hv : (11 : ℤ) ∈ v.asIdeal) :
    ((curve11a1.baseChange ℚ).minimal (Localization.AtPrime v.asIdeal)).HasMultiplicativeReduction
      (Localization.AtPrime v.asIdeal) := by
  have hϖ : Irreducible (11 : Localization.AtPrime v.asIdeal) := by
    exact_mod_cast irreducible_natCast_localizationAtPrime v (p := 11) (by norm_num) hv
  obtain ⟨_, C, hC⟩ := isMinimal_and_exists_isTateTerminal_curve11a1_11 ℚ hϖ
  exact (hC.hasMultiplicativeReduction_minimal_baseChange_iff (RingHom.ext_int _ _) C hϖ).2
    ⟨0, rfl⟩

/-- **11.a1 has good reduction exactly at the primes other than `11`.** Away from `11` its
discriminant `-11` is a unit; at `11` its reduction is multiplicative. -/
theorem hasGoodReduction_curve11a1_iff :
    ((curve11a1.baseChange ℚ).minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
      (Localization.AtPrime v.asIdeal) ↔ (11 : ℤ) ∉ v.asIdeal :=
  ⟨fun h hv ↦ (hasMultiplicativeReduction_curve11a1 v hv).not_hasGoodReduction _ h,
    fun hv ↦ hasGoodReduction_minimal_baseChange_of_Δ_notMem curve11a1 <| by
      rwa [Δ_curve11a1, neg_mem_iff]⟩

/-- The `c₄` invariant of 11.a1 is `375376 = 2⁴ · 23461`. -/
theorem c₄_curve11a1 : curve11a1.c₄ = 375376 := by
  simp [c₄, b₂, b₄]

/-- **11.a1 is semistable**: its discriminant `-11` and its `c₄ = 375376` are coprime, so at every
prime one of them is a unit. This agrees with the symbols: the reduction is good away from `11`
and multiplicative, of symbol `I₁`, at `11` (`hasGoodReduction_curve11a1_iff`,
`hasMultiplicativeReduction_curve11a1`). -/
theorem isSemistable_curve11a1 : IsSemistable ℤ (curve11a1.baseChange ℚ) :=
  isSemistable_baseChange_of_isCoprime curve11a1 <| by
    rw [Δ_curve11a1, c₄_curve11a1, Int.isCoprime_iff_gcd_eq_one]
    norm_num

/-! #### 27.a4: not semistable, of symbol `II` at `3` -/

/-- **27.a4 has additive reduction at `3`**: Tate's algorithm stops there at `II`. -/
theorem hasAdditiveReduction_curve27a4 (hv : (3 : ℤ) ∈ v.asIdeal) :
    ((curve27a4.baseChange ℚ).minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal) := by
  have hϖ : Irreducible (3 : Localization.AtPrime v.asIdeal) := by
    exact_mod_cast irreducible_natCast_localizationAtPrime v (p := 3) (by norm_num) hv
  obtain ⟨_, C, hC⟩ := isMinimal_and_exists_isTateTerminal_curve27a4_3 ℚ hϖ
  exact (hC.hasAdditiveReduction_minimal_baseChange_iff (RingHom.ext_int _ _) C hϖ).2
    fun _ ↦ nofun

/-- **27.a4 has good reduction exactly at the primes other than `3`.** Away from `3` its
discriminant `-3³` is a unit; at `3` its reduction is additive. -/
theorem hasGoodReduction_curve27a4_iff :
    ((curve27a4.baseChange ℚ).minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
      (Localization.AtPrime v.asIdeal) ↔ (3 : ℤ) ∉ v.asIdeal := by
  refine ⟨fun h hv ↦ (hasAdditiveReduction_curve27a4 v hv).not_hasGoodReduction _ h,
    fun hv ↦ hasGoodReduction_minimal_baseChange_of_Δ_notMem curve27a4 ?_⟩
  have h27 : (27 : ℤ) = 3 ^ 3 := by norm_num
  rw [Δ_curve27a4, neg_mem_iff, h27]
  exact fun h ↦ hv (v.isPrime.mem_of_pow_mem 3 h)

/-- **27.a4 is not semistable**: its reduction at `3`, of symbol `II`, is additive. -/
theorem not_isSemistable_curve27a4 : ¬ IsSemistable ℤ (curve27a4.baseChange ℚ) := fun h ↦ by
  let v : HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(3 : ℤ)}, (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three,
      by simp⟩
  exact h.not_hasAdditiveReduction v (hasAdditiveReduction_curve27a4 v
    (Ideal.mem_span_singleton_self _))

end Semistable

end TauCeti.WorkedExamples
