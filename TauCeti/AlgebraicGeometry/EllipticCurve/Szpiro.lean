/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor

/-!
# The Szpiro ratio and Szpiro's conjectures over `ℚ`

Let `E` be an elliptic curve over `ℚ`, with minimal discriminant `Δ_min` and conductor `N`. Here
`|Δ_min|` is the norm of the minimal discriminant ideal `WeierstrassCurve.minimalDiscriminantIdeal`
of `E` over `ℤ`, which is also `|Δ|` of the reduced minimal model
(`WeierstrassCurve.absNorm_minimalDiscriminantIdeal`), and `N` is the norm of the
algorithmic conductor `WeierstrassCurve.algorithmicConductor`, the product of the prime powers
`p ^ f_p` whose exponents `f_p = v_p(Δ_min) - m_p + 1` are read off Tate's algorithm.

The **Szpiro ratio** of `E` is `log |Δ_min| / log N`, defined when `N > 1`, that is, when `E` has
bad reduction at some prime (`WeierstrassCurve.one_lt_absNorm_algorithmicConductor_iff`). It is
the exponent `σ` with `N ^ σ = |Δ_min|`, and it is at least `1` because `N` divides `Δ_min`.
**Szpiro's conjecture** asserts `|Δ_min| ≪_ε N ^ (6 + ε)` for every
`ε > 0`, uniformly in `E`: with `|Δ_min| ≤ C N ^ (6 + ε)`, the Szpiro ratio is at most
`6 + ε + log C / log N`.
The **modified Szpiro conjecture** asserts the stronger bound
`max (|c₄|³, c₆²) ≪_ε N ^ (6 + ε)`, with `c₄` and `c₆` the invariants of a minimal equation. Since
`1728 Δ = c₄³ - c₆²`, the modified conjecture implies the original one. Neither conjecture is
proved here.

By Ogg's formula the algorithmic conductor is the conductor of `E`. That identification is not
formalised, so the ratio and the conjectures are stated against the algorithmic conductor and are
named for it. For a semistable curve, such as the Frey curve of a solution of Fermat's equation,
every exponent `f_p` is `0` or `1`, and `N` is the radical of `Δ_min`.

## Main definitions

* `WeierstrassCurve.algorithmicSzpiroRatio E h`: the Szpiro ratio `log |Δ_min| / log N`, for
  `h : 1 < N`.
* `TauCeti.AlgorithmicSzpiroConjecture`: Szpiro's conjecture `|Δ_min| ≪_ε N ^ (6 + ε)`.
* `TauCeti.AlgorithmicModifiedSzpiroConjecture`: the modified Szpiro conjecture
  `max (|c₄|³, c₆²) ≪_ε N ^ (6 + ε)`.

## Main results

* `TauCeti.algorithmicSzpiroConjecture_iff`, `TauCeti.algorithmicModifiedSzpiroConjecture_iff`:
  the defining characterizations of the two conjectures.
* `WeierstrassCurve.rpow_algorithmicSzpiroRatio`: `N ^ σ = |Δ_min|` for the Szpiro ratio `σ`, and
  `WeierstrassCurve.algorithmicSzpiroRatio_le_iff`: `σ ≤ r` exactly when `|Δ_min| ≤ N ^ r`.
* `WeierstrassCurve.one_le_algorithmicSzpiroRatio`: the Szpiro ratio is at least `1`.
* `WeierstrassCurve.algorithmicSzpiroRatio_smul`: the Szpiro ratio is invariant under a change of
  variables.
* `TauCeti.AlgorithmicModifiedSzpiroConjecture.algorithmicSzpiroConjecture`: the modified Szpiro
  conjecture implies Szpiro's conjecture.

## References

* L. Szpiro, *Discriminant et conducteur des courbes elliptiques*, Astérisque 183 (1990), 7–18.
* J. Oesterlé, *Nouvelles approches du « théorème » de Fermat*, Séminaire Bourbaki 694 (1988),
  Astérisque 161–162 (1988), 165–186.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1
  (`1728 Δ = c₄³ - c₆²`) and VIII.11.
-/

public section

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The Szpiro ratio** `log |Δ_min| / log N` of an elliptic curve over `ℚ`, where `|Δ_min|` is
the norm of the minimal discriminant ideal over `ℤ` and `N` that of the algorithmic conductor. The
hypothesis `1 < N` makes the denominator nonzero; without it the quotient would be `0` by division
by zero. -/
noncomputable def algorithmicSzpiroRatio (_h : 1 < Ideal.absNorm (algorithmicConductor ℤ E)) :
    ℝ :=
  Real.log (Ideal.absNorm (minimalDiscriminantIdeal ℤ E)) /
    Real.log (Ideal.absNorm (algorithmicConductor ℤ E))

/-- `algorithmicSzpiroRatio`, unfolded. This is the interface to
`WeierstrassCurve.algorithmicSzpiroRatio` outside its defining module. -/
theorem algorithmicSzpiroRatio_def (h : 1 < Ideal.absNorm (algorithmicConductor ℤ E)) :
    E.algorithmicSzpiroRatio h = Real.log (Ideal.absNorm (minimalDiscriminantIdeal ℤ E)) /
      Real.log (Ideal.absNorm (algorithmicConductor ℤ E)) :=
  (rfl)

/-- **The Szpiro ratio is the exponent of `N` giving `|Δ_min|`**: `N ^ σ = |Δ_min|`. -/
theorem rpow_algorithmicSzpiroRatio (h : 1 < Ideal.absNorm (algorithmicConductor ℤ E)) :
    (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ E.algorithmicSzpiroRatio h =
      Ideal.absNorm (minimalDiscriminantIdeal ℤ E) := by
  have hN : (1 : ℝ) < Ideal.absNorm (algorithmicConductor ℤ E) := by exact_mod_cast h
  have hΔ : (0 : ℝ) < Ideal.absNorm (minimalDiscriminantIdeal ℤ E) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.2 (minimalDiscriminantIdeal_ne_bot ℤ E))
  rw [algorithmicSzpiroRatio_def, Real.rpow_def_of_pos (by linarith),
    mul_div_cancel₀ _ (Real.log_pos hN).ne', Real.exp_log hΔ]

/-- **The Szpiro ratio is at most `r` exactly when `|Δ_min| ≤ N ^ r`.** -/
theorem algorithmicSzpiroRatio_le_iff (h : 1 < Ideal.absNorm (algorithmicConductor ℤ E))
    {r : ℝ} : E.algorithmicSzpiroRatio h ≤ r ↔
      (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) ≤
        (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ r := by
  have hN : (1 : ℝ) < Ideal.absNorm (algorithmicConductor ℤ E) := by exact_mod_cast h
  rw [← E.rpow_algorithmicSzpiroRatio h, Real.rpow_le_rpow_left_iff hN]

/-- **The Szpiro ratio is at least `1`**, since the algorithmic conductor divides the minimal
discriminant ideal. -/
theorem one_le_algorithmicSzpiroRatio (h : 1 < Ideal.absNorm (algorithmicConductor ℤ E)) :
    1 ≤ E.algorithmicSzpiroRatio h := by
  have hN : (1 : ℝ) < Ideal.absNorm (algorithmicConductor ℤ E) := by exact_mod_cast h
  rw [← Real.rpow_le_rpow_left_iff hN, Real.rpow_one, rpow_algorithmicSzpiroRatio]
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (minimalDiscriminantIdeal_ne_bot ℤ E)))
    (Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.le_of_dvd (algorithmicConductor_dvd_minimalDiscriminantIdeal E)))

/-- **The Szpiro ratio is invariant under a change of variables**, so it is an invariant of the
curve and not of the equation presenting it. -/
@[simp]
theorem algorithmicSzpiroRatio_smul (C : VariableChange ℚ)
    (h : 1 < Ideal.absNorm (algorithmicConductor ℤ (C • E))) :
    (C • E).algorithmicSzpiroRatio h =
      E.algorithmicSzpiroRatio (by rwa [algorithmicConductor_smul] at h) := by
  simp only [algorithmicSzpiroRatio_def, algorithmicConductor_smul, minimalDiscriminantIdeal_smul]

end WeierstrassCurve

namespace TauCeti

open WeierstrassCurve

/-- **Szpiro's conjecture**, against the algorithmic conductor: for every `ε > 0` there is a
constant `C` such that every elliptic curve over `ℚ` satisfies `|Δ_min| ≤ C N ^ (6 + ε)`, where
`|Δ_min|` is the norm of the minimal discriminant ideal over `ℤ` and `N` that of the algorithmic
conductor. -/
def AlgorithmicSzpiroConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) ≤
      C * (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + ε)

/-- The defining characterization of `TauCeti.AlgorithmicSzpiroConjecture`. This is the interface
to it outside its defining module. -/
theorem algorithmicSzpiroConjecture_iff :
    AlgorithmicSzpiroConjecture ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
        (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) ≤
          C * (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + ε) :=
  Iff.rfl

/-- **The modified Szpiro conjecture**, against the algorithmic conductor: for every `ε > 0` there
is a constant `C` such that every elliptic curve over `ℚ` satisfies
`max (|c₄|³, c₆²) ≤ C N ^ (6 + ε)`, where `c₄` and `c₆` are the invariants of the reduced minimal
model and `N` is the norm of the algorithmic conductor. The invariants of any globally minimal
equation have the same absolute values, as such equations differ by changes of variables over `ℤ`
with `u = ±1`. -/
def AlgorithmicModifiedSzpiroConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    max (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3) (((reducedMinimalModel E).c₆ : ℝ) ^ 2) ≤
      C * (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + ε)

/-- The defining characterization of `TauCeti.AlgorithmicModifiedSzpiroConjecture`. This is the
interface to it outside its defining module. -/
theorem algorithmicModifiedSzpiroConjecture_iff :
    AlgorithmicModifiedSzpiroConjecture ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
        max (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3) (((reducedMinimalModel E).c₆ : ℝ) ^ 2) ≤
          C * (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + ε) :=
  Iff.rfl

/-- **The modified Szpiro conjecture implies Szpiro's conjecture**, with the same constants: the
relation `1728 Δ = c₄³ - c₆²` on the reduced minimal model gives `|Δ_min| ≤ max (|c₄|³, c₆²)`. -/
theorem AlgorithmicModifiedSzpiroConjecture.algorithmicSzpiroConjecture
    (h : AlgorithmicModifiedSzpiroConjecture) : AlgorithmicSzpiroConjecture := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun E _ => le_trans ?_ (hC E)⟩
  set W := reducedMinimalModel E
  have hΔ : (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) = |(W.Δ : ℝ)| := by
    exact_mod_cast E.absNorm_minimalDiscriminantIdeal
  have hrel : (1728 : ℝ) * W.Δ = (W.c₄ : ℝ) ^ 3 - (W.c₆ : ℝ) ^ 2 := by
    exact_mod_cast W.c_relation
  -- `1728 |Δ| = |c₄³ - c₆²| ≤ |c₄|³ + c₆² ≤ 2 max (|c₄|³, c₆²)`.
  have key := abs_sub ((W.c₄ : ℝ) ^ 3) ((W.c₆ : ℝ) ^ 2)
  rw [← hrel, abs_mul, abs_pow, abs_sq] at key
  norm_num at key
  rw [hΔ]
  linarith [le_max_left (|(W.c₄ : ℝ)| ^ 3) ((W.c₆ : ℝ) ^ 2),
    le_max_right (|(W.c₄ : ℝ)| ^ 3) ((W.c₆ : ℝ) ^ 2), sq_nonneg (W.c₆ : ℝ)]

end TauCeti

end
