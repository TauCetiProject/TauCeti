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
public import TauCeti.NumberTheory.AbcConjecture
import Mathlib.Data.Nat.Squarefree

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

The **abc conjecture** (`TauCeti.AbcConjecture`) implies the modified Szpiro conjecture. Take the
reduced minimal model and divide `c₆² + 1728 Δ = c₄³` by `g = gcd (c₄³, c₆²)` to obtain a coprime
triple. abc bounds `max (|c₄|³, c₆²) / g` by a power `1 + ε` of the radical of `6 c₄ c₆ Δ`, and
`g` times that radical divides `432 c₄ c₆ N`: minimality bounds the common factor `g`
(`WeierstrassCurve.IsGlobalMinimal.dvd_six_of_pow_dvd`), and a prime `p ≥ 5` dividing `g` is a
prime of additive reduction, so `p²` divides `N`
(`WeierstrassCurve.IsGlobalMinimal.sq_dvd_absNorm_algorithmicConductor_iff`). Since
`|c₄ c₆| ≤ max (|c₄|³, c₆²) ^ (5 / 6)`, this gives `max (|c₄|³, c₆²) ≪_ε N ^ (6 + ε)`. When
`c₄ c₆ = 0`, that is, when `j` is `0` or `1728`, minimality alone bounds the invariants by `N⁶`.

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
* `TauCeti.AbcConjecture.algorithmicModifiedSzpiroConjecture`: the abc conjecture implies the
  modified Szpiro conjecture.

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

/-! ### The abc conjecture implies the modified Szpiro conjecture -/

open UniqueFactorizationMonoid

/-- A prime at least `5` does not divide `6`. -/
private theorem not_dvd_six_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 6 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h
  obtain rfl | rfl : p = 5 ∨ p = 6 := by omega
  · omega
  · exact absurd hp (by decide)

/-- The exponent of a prime `p` in `2 ^ a * 3 ^ b * n`. -/
private theorem factorization_two_pow_mul_three_pow_mul {n : ℕ} (hn : n ≠ 0) (a b : ℕ) {p : ℕ}
    (hp : p.Prime) : (2 ^ a * 3 ^ b * n).factorization p =
      (if p = 2 then a else 0) + (if p = 3 then b else 0) + n.factorization p := by
  rw [Nat.factorization_mul (by positivity) hn, Nat.factorization_mul (by positivity)
    (by positivity), Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rcases eq_or_ne p 2 with rfl | h2
  · simp
  rcases eq_or_ne p 3 with rfl | h3
  · simp
  simp [h2, h3, h2.symm, h3.symm]

/-- The exponent of a prime in a radical is at most `1`, and it vanishes unless the prime divides
the number. -/
private theorem factorization_radical_le (n p : ℕ) :
    (radical n).factorization p ≤ if p ∣ n then 1 else 0 := by
  have h1 := (squarefree_radical (a := n)).natFactorization_le_one p
  split_ifs with h
  · exact h1
  · exact (Nat.factorization_eq_zero_of_not_dvd fun hd => h (hd.trans radical_dvd_self)).le

/-- **The local bookkeeping behind abc implies modified Szpiro.** Let `x₄`, `x₆` and `D` be the
absolute values of `c₄`, `c₆` and `Δ` of a minimal equation, and `N` its conductor. Then
`g · rad (6 x₄ x₆ D)` divides `432 x₄ x₆ N`, where `g = gcd (x₄³, x₆²)`. At a prime `p ≥ 5` dividing
`g`, minimality gives `v_p(g) ≤ v_p(x₄) + v_p(x₆) + 1`, and the reduction is additive, so
`v_p(N) ≥ 2`; at `p = 2, 3` minimality bounds `v_p(g) - v_p(x₄) - v_p(x₆)` by `3` and `2`. -/
private theorem gcd_mul_radical_dvd {x₄ x₆ D N : ℕ} (h₄ : x₄ ≠ 0) (h₆ : x₆ ≠ 0) (hD : D ≠ 0)
    (hN : N ≠ 0) (hm₂ : ¬ (2 ^ 8 ∣ x₄ ∧ 2 ^ 11 ∣ x₆)) (hm₃ : ¬ (3 ^ 5 ∣ x₄ ∧ 3 ^ 9 ∣ x₆))
    (hm : ∀ p, p.Prime → 5 ≤ p → ¬ (p ^ 4 ∣ x₄ ∧ p ^ 6 ∣ x₆))
    (hΔ : ∀ p, p.Prime → 5 ≤ p → p ∣ x₄ → p ∣ x₆ → p ∣ D)
    (hN₁ : ∀ p, p.Prime → p ∣ D → p ∣ N) (hN₂ : ∀ p, p.Prime → p ∣ D → p ∣ x₄ → p ^ 2 ∣ N) :
    Nat.gcd (x₄ ^ 3) (x₆ ^ 2) * radical (6 * x₄ * x₆ * D) ∣ 432 * (x₄ * x₆ * N) := by
  rw [show (432 : ℕ) = 2 ^ 4 * 3 ^ 3 by norm_num]
  refine (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).1 fun p => ?_
  by_cases hp : p.Prime
  swap; · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hrad := factorization_radical_le (6 * x₄ * x₆ * D) p
  rw [factorization_two_pow_mul_three_pow_mul (by positivity) _ _ hp,
    Nat.factorization_mul (Nat.gcd_pos_of_pos_left _ (by positivity)).ne' (Nat.radical_pos _).ne',
    Finsupp.add_apply, Nat.factorization_gcd (by positivity) (by positivity), Finsupp.inf_apply,
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_mul (by positivity) hN,
    Nat.factorization_mul h₄ h₆]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  -- everything is now a statement about the exponents of `p`
  have hv {x : ℕ} (hx : x ≠ 0) (k : ℕ) : p ^ k ∣ x ↔ k ≤ x.factorization p :=
    hp.pow_dvd_iff_le_factorization hx
  have hv₁ {x : ℕ} (hx : x ≠ 0) : p ∣ x ↔ 1 ≤ x.factorization p := by
    simpa using hv hx 1
  have hN₁' := fun h => (hv₁ hN).1 (hN₁ p hp ((hv₁ hD).2 h))
  have hN₂' := fun h h' => (hv hN 2).1 (hN₂ p hp ((hv₁ hD).2 h) ((hv₁ h₄).2 h'))
  split_ifs at hrad with hpR
  · rcases eq_or_ne p 2 with rfl | h2
    · have : ¬ (8 ≤ x₄.factorization 2 ∧ 11 ≤ x₆.factorization 2) :=
        fun h => hm₂ ⟨(hv h₄ 8).2 h.1, (hv h₆ 11).2 h.2⟩
      simp only [ite_true, show (2 : ℕ) ≠ 3 by norm_num, ite_false]
      omega
    rcases eq_or_ne p 3 with rfl | h3
    · have : ¬ (5 ≤ x₄.factorization 3 ∧ 9 ≤ x₆.factorization 3) :=
        fun h => hm₃ ⟨(hv h₄ 5).2 h.1, (hv h₆ 9).2 h.2⟩
      simp only [ite_true, show (3 : ℕ) ≠ 2 by norm_num, ite_false]
      omega
    have h5 := hp.five_le_of_ne_two_of_ne_three h2 h3
    have : ¬ (4 ≤ x₄.factorization p ∧ 6 ≤ x₆.factorization p) :=
      fun h => hm p hp h5 ⟨(hv h₄ 4).2 h.1, (hv h₆ 6).2 h.2⟩
    have hΔ' := fun h h' => (hv₁ hD).1 (hΔ p hp h5 ((hv₁ h₄).2 h) ((hv₁ h₆).2 h'))
    -- as `p ∤ 6`, it divides `x₄`, `x₆` or `D`
    have hdiv : 1 ≤ x₄.factorization p ∨ 1 ≤ x₆.factorization p ∨ 1 ≤ D.factorization p := by
      rw [← hv₁ h₄, ← hv₁ h₆, ← hv₁ hD]
      rcases (Nat.Prime.dvd_mul hp).1 hpR with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact Or.inl (((Nat.Prime.dvd_mul hp).1 h).resolve_left
            (not_dvd_six_of_five_le hp h5))
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    simp only [h2, h3, ite_false]
    omega
  · -- a prime not dividing `6 x₄ x₆ D` does not divide `x₄`
    have : ¬ 1 ≤ x₄.factorization p := fun h =>
      hpR (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((hv₁ h₄).2 h) 6) _) _)
    omega

/-- The bookkeeping when one of `c₄` and `c₆` vanishes: a number `x` with bounded exponents at `2`
and `3`, and exponents below `m ≤ 2 k + 1` at the primes `p ≥ 5`, each of which divides `N` twice,
divides `2 ^ a * 3 ^ b * N ^ k`. -/
private theorem dvd_two_pow_mul_three_pow_mul_pow {x N a b k m : ℕ} (hx : x ≠ 0) (hN : N ≠ 0)
    (h₂ : ¬ 2 ^ (a + 1) ∣ x) (h₃ : ¬ 3 ^ (b + 1) ∣ x)
    (hm : ∀ p, p.Prime → 5 ≤ p → ¬ p ^ m ∣ x) (hmk : m ≤ 2 * k + 1)
    (hN₂ : ∀ p, p.Prime → 5 ≤ p → p ∣ x → p ^ 2 ∣ N) : x ∣ 2 ^ a * 3 ^ b * N ^ k := by
  refine (Nat.factorization_le_iff_dvd hx (by positivity)).1 fun p => ?_
  by_cases hp : p.Prime
  swap; · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [factorization_two_pow_mul_three_pow_mul (by positivity) _ _ hp, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul]
  have hv {y : ℕ} (hy : y ≠ 0) (j : ℕ) : p ^ j ∣ y ↔ j ≤ y.factorization p :=
    hp.pow_dvd_iff_le_factorization hy
  rcases eq_or_ne p 2 with rfl | h2
  · have := (hv hx (a + 1)).not.1 h₂
    simp only [ite_true, show (2 : ℕ) ≠ 3 by norm_num, ite_false]
    omega
  rcases eq_or_ne p 3 with rfl | h3
  · have := (hv hx (b + 1)).not.1 h₃
    simp only [ite_true, show (3 : ℕ) ≠ 2 by norm_num, ite_false]
    omega
  have h5 := hp.five_le_of_ne_two_of_ne_three h2 h3
  have := (hv hx m).not.1 (hm p hp h5)
  have hf : 1 ≤ x.factorization p → 2 * k ≤ k * N.factorization p := fun h =>
    (Nat.mul_comm 2 k).le.trans (Nat.mul_le_mul_left k ((hv hN 2).1
      (hN₂ p hp h5 (by simpa using (hv hx 1).2 h))))
  simp only [h2, h3, ite_false]
  omega

/-- The exponent bookkeeping: if `m ≤ C₀ y ^ (1 + ε₀)` and `y⁶ ≤ 432⁶ m⁵ n⁶`, then
`m ^ (1 - 5 ε₀) ≪ n ^ (6 (1 + ε₀))`, and `42 ε₀ ≤ min ε 1` makes the exponent of `n` at most
`6 + ε` once the root is taken. -/
private theorem le_mul_rpow_of_le_mul_rpow {ε ε₀ C₀ m n y : ℝ} (hε₀ : 0 < ε₀)
    (hεε₀ : 42 * ε₀ ≤ min ε 1) (hm : 1 ≤ m) (hn : 1 ≤ n) (hy : 1 ≤ y)
    (habc : m ≤ C₀ * y ^ (1 + ε₀)) (hy₆ : y ^ 6 ≤ 432 ^ 6 * m ^ 5 * n ^ 6) :
    m ≤ (C₀ ^ 6 * 432 ^ (6 * (1 + ε₀))) ^ (1 - 5 * ε₀)⁻¹ * n ^ (6 + ε) := by
  have hε : 42 * ε₀ ≤ ε := hεε₀.trans (min_le_left _ _)
  have hε₁ : 42 * ε₀ ≤ 1 := hεε₀.trans (min_le_right _ _)
  set t := 1 + ε₀ with ht
  set s := 1 - 5 * ε₀ with hs
  have hs₀ : 0 < s := by linarith
  have hm₀ : 0 < m := by linarith
  have hn₀ : 0 < n := by linarith
  have hy₀ : 0 < y := by linarith
  have hyt : 0 < y ^ t := Real.rpow_pos_of_pos hy₀ t
  have hC₀ : 0 < C₀ := pos_of_mul_pos_left (hm₀.trans_le habc) hyt.le
  set A := C₀ ^ 6 * (432 : ℝ) ^ (6 * t)
  -- `m⁶ ≤ C₀⁶ (y⁶)ᵗ ≤ A m^(5t) n^(6t)`
  have h₁ : m ^ (6 : ℝ) ≤ A * (m ^ (5 * t) * n ^ (6 * t)) := by
    have := pow_le_pow_left₀ hm₀.le habc 6
    have hyt₆ : (y ^ t) ^ 6 = (y ^ 6) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast y 6, ← Real.rpow_mul hy₀.le,
        ← Real.rpow_mul hy₀.le, mul_comm]
    rw [mul_pow, hyt₆] at this
    refine (Real.rpow_natCast m 6 ▸ this).trans ?_
    have hpow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (x ^ k) ^ t = x ^ (k * t) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have h432 := Real.rpow_le_rpow (by positivity) hy₆ (by linarith : 0 ≤ t)
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), hpow (x := 432) (by norm_num), hpow hm₀.le 5, hpow hn₀.le 6] at h432
    calc C₀ ^ 6 * (y ^ 6) ^ t ≤ C₀ ^ 6 * ((432 : ℝ) ^ ((6 : ℕ) * t) * m ^ ((5 : ℕ) * t) *
          n ^ ((6 : ℕ) * t)) := mul_le_mul_of_nonneg_left h432 (by positivity)
      _ = A * (m ^ (5 * t) * n ^ (6 * t)) := by push_cast; ring
  -- divide by `m^(5t)`: `m^s ≤ A n^(6t)`
  have h₂ : m ^ s ≤ A * n ^ (6 * t) := by
    have hs' : s = 6 - 5 * t := by rw [hs, ht]; ring
    rw [hs', Real.rpow_sub hm₀, div_le_iff₀ (Real.rpow_pos_of_pos hm₀ _)]
    linarith
  -- take the `s`-th root
  have h₃ : m ≤ A ^ s⁻¹ * n ^ (6 * t / s) := by
    have := Real.rpow_le_rpow (by positivity) h₂ (inv_nonneg.2 hs₀.le)
    rwa [← Real.rpow_mul hm₀.le, mul_inv_cancel₀ hs₀.ne', Real.rpow_one,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn₀.le, ← div_eq_mul_inv]
      at this
  refine h₃.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn ?_)
    (by positivity))
  rw [div_le_iff₀ hs₀]
  nlinarith

/-- The coprime triple `c₆² / g + 1728 Δ / g = c₄³ / g`, where `g = gcd (c₄³, c₆²)`. -/
private theorem exists_isCoprime_of_c_relation {c₄ c₆ Δ : ℤ} (hrel : 1728 * Δ = c₄ ^ 3 - c₆ ^ 2)
    (h₄ : c₄ ≠ 0) : ∃ a b c : ℤ, IsCoprime a b ∧ a + b = c ∧
      c₆ ^ 2 = (c₄ ^ 3).gcd (c₆ ^ 2) * a ∧ 1728 * Δ = (c₄ ^ 3).gcd (c₆ ^ 2) * b ∧
      c₄ ^ 3 = (c₄ ^ 3).gcd (c₆ ^ 2) * c := by
  set g := (c₄ ^ 3).gcd (c₆ ^ 2)
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left _ (pow_ne_zero 3 h₄)
  have ha : c₆ ^ 2 = g * (c₆ ^ 2 / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  have hc : c₄ ^ 3 = g * (c₄ ^ 3 / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hac : IsCoprime (c₆ ^ 2 / g) (c₄ ^ 3 / g) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact Int.gcd_div_gcd_div_gcd hg
  refine ⟨c₆ ^ 2 / g, c₄ ^ 3 / g - c₆ ^ 2 / g, c₄ ^ 3 / g, ?_, by ring, ha, ?_, hc⟩
  · simpa [sub_eq_add_neg] using hac.add_mul_left_right (-1)
  · rw [hrel]
    linear_combination hc - ha

/-- **The case `c₄ c₆ ≠ 0`**: abc, with constant `C₀` at the exponent `1 + ε₀`, applied to the
coprime triple of `c₆² + 1728 Δ = c₄³`, together with the bookkeeping of
`gcd_mul_radical_dvd`, bounds `max (|c₄|³, c₆²)` by a constant times `N ^ (6 + ε)`. -/
private theorem le_of_abc_of_ne_zero {ε ε₀ C₀ : ℝ} (hε₀ : 0 < ε₀) (hεε₀ : 42 * ε₀ ≤ min ε 1)
    (hC₀ : ∀ a b c : ℤ, IsCoprime a b → a + b = c →
      ((max (max a.natAbs b.natAbs) c.natAbs : ℕ) : ℝ) ≤
        C₀ * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (1 + ε₀))
    {c₄ c₆ Δ : ℤ} {N : ℕ} (hrel : 1728 * Δ = c₄ ^ 3 - c₆ ^ 2) (h₄ : c₄ ≠ 0) (h₆ : c₆ ≠ 0)
    (hΔ : Δ ≠ 0) (hN : N ≠ 0)
    (hdvd : Nat.gcd (c₄.natAbs ^ 3) (c₆.natAbs ^ 2) *
      radical (6 * c₄.natAbs * c₆.natAbs * Δ.natAbs) ∣ 432 * (c₄.natAbs * c₆.natAbs * N)) :
    ((max (c₄.natAbs ^ 3) (c₆.natAbs ^ 2) : ℕ) : ℝ) ≤
      (C₀ ^ 6 * 432 ^ (6 * (1 + ε₀))) ^ (1 - 5 * ε₀)⁻¹ * (N : ℝ) ^ (6 + ε) := by
  obtain ⟨a, b, c, hab, habc, ha, hb, hc⟩ := exists_isCoprime_of_c_relation hrel h₄
  set g := (c₄ ^ 3).gcd (c₆ ^ 2)
  have hg : g = Nat.gcd (c₄.natAbs ^ 3) (c₆.natAbs ^ 2) := by
    simp [g, Int.gcd_eq_natAbs, Int.natAbs_pow]
  set R := radical (6 * c₄.natAbs * c₆.natAbs * Δ.natAbs)
  set M := max (c₄.natAbs ^ 3) (c₆.natAbs ^ 2)
  have hR : (radical (a * b * c).natAbs) ≤ R := by
    have : a * b * c ∣ (6 * c₄ * c₆ * Δ) ^ 6 := ⟨g ^ 3 * 27 * Δ ^ 5 * c₄ ^ 3 * c₆ ^ 4, by
      linear_combination (27 * Δ ^ 5 * c₄ ^ 3 * c₆ ^ 4 * (g * b) * (g * c)) * ha
        + (27 * Δ ^ 5 * c₄ ^ 3 * c₆ ^ 4 * c₆ ^ 2 * (g * c)) * hb
        + (27 * Δ ^ 5 * c₄ ^ 3 * c₆ ^ 4 * c₆ ^ 2 * (1728 * Δ)) * hc⟩
    have h₀ : 6 * c₄.natAbs * c₆.natAbs * Δ.natAbs ≠ 0 := by
      simp [h₄, h₆, hΔ]
    refine Nat.le_of_dvd (Nat.radical_pos _) ?_
    rw [show R = radical ((6 * c₄.natAbs * c₆.natAbs * Δ.natAbs) ^ 6) from
      (radical_pow _ (by norm_num)).symm]
    refine radical_dvd_radical ?_ (pow_ne_zero 6 h₀)
    simpa [Int.natAbs_mul, Int.natAbs_pow] using Int.natAbs_dvd_natAbs.2 this
  have hc' : c₄.natAbs ^ 3 = g * c.natAbs := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs hc
  have ha' : c₆.natAbs ^ 2 = g * a.natAbs := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs ha
  have hc₀ : 1 ≤ c.natAbs := by
    rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero]
    rintro rfl
    exact h₄ (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 (by simpa using hc))
  have hg₀ : 1 ≤ g := Int.gcd_pos_of_ne_zero_left _ (pow_ne_zero 3 h₄)
  -- `M = g · max (|c|, |a|)` is at most `g · max (|a|, |b|, |c|)`, which abc bounds
  have hM : M ≤ g * max (max a.natAbs b.natAbs) c.natAbs := by
    simp only [M, hc', ha']
    exact max_le (Nat.mul_le_mul_left g (le_max_right _ _))
      (Nat.mul_le_mul_left g ((le_max_left _ _).trans (le_max_left _ _)))
  have habc' := hC₀ a b c hab habc
  have hC₀ : 0 < C₀ := by
    refine pos_of_mul_pos_left (lt_of_lt_of_le ?_ habc') (by positivity)
    exact_mod_cast hc₀.trans_lt' zero_lt_one |>.trans_le (le_max_right _ _)
  -- the product `g · rad (6 c₄ c₆ Δ)` is at most `432 |c₄ c₆| N`, whose sixth power is at most
  -- `432⁶ M⁵ N⁶`
  have hy : (g * R) ^ 6 ≤ 432 ^ 6 * M ^ 5 * N ^ 6 := by
    have h₁ : g * R ≤ 432 * (c₄.natAbs * c₆.natAbs * N) := Nat.le_of_dvd (by positivity) (hg ▸ hdvd)
    have h₂ : (c₄.natAbs * c₆.natAbs) ^ 6 ≤ M ^ 5 :=
      calc (c₄.natAbs * c₆.natAbs) ^ 6 = (c₄.natAbs ^ 3) ^ 2 * (c₆.natAbs ^ 2) ^ 3 := by ring
        _ ≤ M ^ 2 * M ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) 2)
          (Nat.pow_le_pow_left (le_max_right _ _) 3)
        _ = M ^ 5 := by ring
    calc (g * R) ^ 6 ≤ (432 * (c₄.natAbs * c₆.natAbs * N)) ^ 6 := Nat.pow_le_pow_left h₁ 6
      _ = 432 ^ 6 * (c₄.natAbs * c₆.natAbs) ^ 6 * N ^ 6 := by ring
      _ ≤ 432 ^ 6 * M ^ 5 * N ^ 6 := by gcongr
  refine le_mul_rpow_of_le_mul_rpow hε₀ hεε₀ (y := ((g * R : ℕ) : ℝ)) ?_ ?_ ?_ ?_
    (by exact_mod_cast hy)
  · exact_mod_cast (Nat.one_le_pow _ _ (by omega)).trans (le_max_left _ _)
  · exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
  · exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hR₁ : (1 : ℝ) ≤ R := by exact_mod_cast Nat.radical_pos _
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg₀
  calc (M : ℝ) ≤ g * ((max (max a.natAbs b.natAbs) c.natAbs : ℕ) : ℝ) := by exact_mod_cast hM
    _ ≤ g * (C₀ * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (1 + ε₀)) := by gcongr
    _ ≤ g * (C₀ * (R : ℝ) ^ (1 + ε₀)) := by gcongr
    _ = C₀ * (g * (R : ℝ) ^ (1 + ε₀)) := by ring
    _ ≤ C₀ * ((g : ℝ) ^ (1 + ε₀) * (R : ℝ) ^ (1 + ε₀)) := by
      gcongr; exact Real.self_le_rpow_of_one_le hg₁ (by linarith)
    _ = C₀ * ((g * R : ℕ) : ℝ) ^ (1 + ε₀) := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]



/-- The rescaling bound `u ∣ 6` of a minimal equation, read off at each prime from `|c₄|` and
`|c₆|`. -/
private theorem not_pow_dvd_and_pow_dvd_of_dvd_six {c₄ c₆ : ℤ}
    (hmin : ∀ u : ℤ, u ^ 4 ∣ 27 * c₄ → u ^ 6 ∣ 54 * c₆ → u ∣ 6) :
    ¬ (2 ^ 8 ∣ c₄.natAbs ∧ 2 ^ 11 ∣ c₆.natAbs) ∧ ¬ (3 ^ 5 ∣ c₄.natAbs ∧ 3 ^ 9 ∣ c₆.natAbs) ∧
      ∀ p, p.Prime → 5 ≤ p → ¬ (p ^ 4 ∣ c₄.natAbs ∧ p ^ 6 ∣ c₆.natAbs) := by
  refine ⟨fun ⟨h₄, h₆⟩ => ?_, fun ⟨h₄, h₆⟩ => ?_, fun p hp h5 ⟨h₄, h₆⟩ => ?_⟩ <;>
    rw [← Int.natCast_dvd] at h₄ h₆ <;> push_cast at h₄ h₆
  · -- `u = 4`
    have := hmin 4 (by simpa using h₄.mul_left 27)
      (by rw [show (4 : ℤ) ^ 6 = 2 * 2 ^ 11 by norm_num, show (54 : ℤ) * c₆ = 2 * (27 * c₆) by ring]
          exact mul_dvd_mul_left 2 (h₆.mul_left 27))
    norm_num at this
  · -- `u = 9`
    have := hmin 9
      (by rw [show (9 : ℤ) ^ 4 = 27 * 3 ^ 5 by norm_num]; exact mul_dvd_mul_left 27 h₄)
      (by rw [show (9 : ℤ) ^ 6 = 27 * 3 ^ 9 by norm_num, show (54 : ℤ) * c₆ = 27 * (2 * c₆) by ring]
          exact mul_dvd_mul_left 27 (h₆.mul_left 2))
    norm_num at this
  · -- `u = p`
    exact not_dvd_six_of_five_le hp h5 (by exact_mod_cast hmin p (h₄.mul_left 27) (h₆.mul_left 54))

/-- A prime `p ≥ 5` dividing `c₄³ - c₆² = 1728 Δ` divides `Δ`. -/
private theorem natCast_dvd_of_dvd_sub {c₄ c₆ Δ : ℤ} (hrel : 1728 * Δ = c₄ ^ 3 - c₆ ^ 2) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (h : (p : ℤ) ∣ c₄ ^ 3 - c₆ ^ 2) : (p : ℤ) ∣ Δ := by
  rw [← hrel] at h
  refine ((Nat.prime_iff_prime_int.1 hp).dvd_mul.1 h).resolve_left fun h1728 => ?_
  have : p ∣ 6 ^ 6 := (show p ∣ 1728 by exact_mod_cast h1728).trans ⟨27, by norm_num⟩
  exact not_dvd_six_of_five_le hp h5 (hp.dvd_of_dvd_pow this)

/-- **The case `c₄ c₆ = 0`**, where `j` is `0` or `1728`: abc says nothing there, but minimality
alone bounds the nonzero invariant by the conductor, `max (|c₄|³, c₆²) ≤ 2²¹ 3¹⁶ N⁶`. -/
private theorem natCast_max_le_of_mul_eq_zero {c₄ c₆ Δ : ℤ} {N : ℕ}
    (hrel : 1728 * Δ = c₄ ^ 3 - c₆ ^ 2) (hΔ : Δ ≠ 0) (hN : N ≠ 0)
    (hmin : ∀ u : ℤ, u ^ 4 ∣ 27 * c₄ → u ^ 6 ∣ 54 * c₆ → u ∣ 6)
    (hN₂ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ Δ → (p : ℤ) ∣ c₄ → p ^ 2 ∣ N) (h : c₄ * c₆ = 0) :
    ((max (c₄.natAbs ^ 3) (c₆.natAbs ^ 2) : ℕ) : ℝ) ≤ 2 ^ 21 * 3 ^ 16 * (N : ℝ) ^ 6 := by
  obtain ⟨hm₂, hm₃, hm⟩ := not_pow_dvd_and_pow_dvd_of_dvd_six hmin
  rcases mul_eq_zero.1 h with rfl | rfl
  · -- `j = 0`: `c₆ ∣ 2¹⁰ 3⁸ N³`
    have h₆ : c₆ ≠ 0 := by rintro rfl; exact hΔ (by linarith)
    have hdvd : c₆.natAbs ∣ 2 ^ 10 * 3 ^ 8 * N ^ 3 :=
      dvd_two_pow_mul_three_pow_mul_pow (by simpa using h₆) hN (fun h => hm₂ ⟨by simp, h⟩)
        (fun h => hm₃ ⟨by simp, h⟩) (fun p hp h5 h => hm p hp h5 ⟨by simp, h⟩) (by norm_num)
        (fun p hp h5 h => hN₂ p hp (natCast_dvd_of_dvd_sub hrel hp h5 (by
          simpa using (dvd_pow (Int.natCast_dvd.2 h) (by norm_num : 2 ≠ 0)).neg_right))
          (dvd_zero _))
    have := Nat.pow_le_pow_left (Nat.le_of_dvd (by positivity) hdvd) 2
    calc ((max (Int.natAbs 0 ^ 3) (c₆.natAbs ^ 2) : ℕ) : ℝ) = (c₆.natAbs ^ 2 : ℕ) := by simp
      _ ≤ ((2 ^ 10 * 3 ^ 8 * N ^ 3) ^ 2 : ℕ) := by exact_mod_cast this
      _ = 2 ^ 20 * 3 ^ 16 * (N : ℝ) ^ 6 := by push_cast; ring
      _ ≤ 2 ^ 21 * 3 ^ 16 * (N : ℝ) ^ 6 := by gcongr <;> norm_num
  · -- `j = 1728`: `c₄ ∣ 2⁷ 3⁴ N²`
    have h₄ : c₄ ≠ 0 := by rintro rfl; exact hΔ (by linarith)
    have hdvd : c₄.natAbs ∣ 2 ^ 7 * 3 ^ 4 * N ^ 2 :=
      dvd_two_pow_mul_three_pow_mul_pow (by simpa using h₄) hN (fun h => hm₂ ⟨h, by simp⟩)
        (fun h => hm₃ ⟨h, by simp⟩) (fun p hp h5 h => hm p hp h5 ⟨h, by simp⟩) (by norm_num)
        (fun p hp h5 h => hN₂ p hp (natCast_dvd_of_dvd_sub hrel hp h5 (by
          simpa using dvd_pow (Int.natCast_dvd.2 h) (by norm_num : 3 ≠ 0)))
          (Int.natCast_dvd.2 h))
    have := Nat.pow_le_pow_left (Nat.le_of_dvd (by positivity) hdvd) 3
    calc ((max (c₄.natAbs ^ 3) (Int.natAbs 0 ^ 2) : ℕ) : ℝ) = (c₄.natAbs ^ 3 : ℕ) := by simp
      _ ≤ ((2 ^ 7 * 3 ^ 4 * N ^ 2) ^ 3 : ℕ) := by exact_mod_cast this
      _ = 2 ^ 21 * 3 ^ 12 * (N : ℝ) ^ 6 := by push_cast; ring
      _ ≤ 2 ^ 21 * 3 ^ 16 * (N : ℝ) ^ 6 := by gcongr <;> norm_num

/-- **abc bounds the `c`-invariants of a minimal integral equation by its conductor**, stated on
the integers `c₄`, `c₆`, `Δ` and `N` with the properties of a minimal equation that the argument
uses: `1728 Δ = c₄³ - c₆²`, the rescaling bound `u ∣ 6`, and that each prime of `Δ` divides `N`,
twice when it also divides `c₄`. -/
private theorem exists_le_of_abcConjecture (h : AbcConjecture) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (c₄ c₆ Δ : ℤ) (N : ℕ), 1728 * Δ = c₄ ^ 3 - c₆ ^ 2 → Δ ≠ 0 → N ≠ 0 →
      (∀ u : ℤ, u ^ 4 ∣ 27 * c₄ → u ^ 6 ∣ 54 * c₆ → u ∣ 6) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ Δ → p ∣ N) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ Δ → (p : ℤ) ∣ c₄ → p ^ 2 ∣ N) →
      ((max (c₄.natAbs ^ 3) (c₆.natAbs ^ 2) : ℕ) : ℝ) ≤ C * (N : ℝ) ^ (6 + ε) := by
  -- abc is used with the exponent `1 + ε₀`
  set ε₀ := min ε 1 / 42
  have hε₀ : 0 < ε₀ := by positivity
  obtain ⟨C₀, hC₀⟩ := abcConjecture_iff.1 h ε₀ hε₀
  refine ⟨(C₀ ^ 6 * 432 ^ (6 * (1 + ε₀))) ^ (1 - 5 * ε₀)⁻¹ + 2 ^ 21 * 3 ^ 16, ?_⟩
  intro c₄ c₆ Δ N hrel hΔ hN hmin hN₁ hN₂
  have hN₀ : (0 : ℝ) ≤ (N : ℝ) ^ (6 + ε) := by positivity
  have hK : (0 : ℝ) ≤ (C₀ ^ 6 * 432 ^ (6 * (1 + ε₀))) ^ (1 - 5 * ε₀)⁻¹ * (N : ℝ) ^ (6 + ε) := by
    positivity
  rcases eq_or_ne (c₄ * c₆) 0 with h₀ | h₀
  · have hN₆ : (N : ℝ) ^ 6 ≤ (N : ℝ) ^ (6 + ε) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN)
        (by push_cast; linarith)
    have := natCast_max_le_of_mul_eq_zero hrel hΔ hN hmin hN₂ h₀
    nlinarith
  -- otherwise abc applies to `c₆² + 1728 Δ = c₄³`
  obtain ⟨h₄, h₆⟩ := mul_ne_zero_iff.1 h₀
  obtain ⟨hm₂, hm₃, hm⟩ := not_pow_dvd_and_pow_dvd_of_dvd_six hmin
  have := le_of_abc_of_ne_zero hε₀ (le_of_eq (by simp only [ε₀]; ring)) hC₀ hrel h₄ h₆ hΔ hN
    (gcd_mul_radical_dvd (by simpa using h₄) (by simpa using h₆) (by simpa using hΔ) hN hm₂ hm₃ hm
      (fun p hp h5 h h' => Int.natCast_dvd.1 (natCast_dvd_of_dvd_sub hrel hp h5 (dvd_sub
        (dvd_pow (Int.natCast_dvd.2 h) (by norm_num)) (dvd_pow (Int.natCast_dvd.2 h')
          (by norm_num)))))
      (fun p hp h => hN₁ p hp (Int.natCast_dvd.2 h))
      (fun p hp h h' => hN₂ p hp (Int.natCast_dvd.2 h) (Int.natCast_dvd.2 h')))
  linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 ^ 21 * 3 ^ 16) hN₀]

/-- **The abc conjecture implies the modified Szpiro conjecture** (Oesterlé), against the
algorithmic conductor: for every `ε > 0` there is a constant `C` with
`max (|c₄|³, c₆²) ≤ C N ^ (6 + ε)` for every elliptic curve over `ℚ`, where `c₄` and `c₆` are the
invariants of its reduced minimal model and `N` is the norm of its algorithmic conductor. With
`TauCeti.AlgorithmicModifiedSzpiroConjecture.algorithmicSzpiroConjecture`, abc therefore implies
Szpiro's conjecture as well. -/
theorem AbcConjecture.algorithmicModifiedSzpiroConjecture (h : AbcConjecture) :
    AlgorithmicModifiedSzpiroConjecture := by
  intro ε hε
  obtain ⟨C, hC⟩ := exists_le_of_abcConjecture h hε
  refine ⟨C, fun E _ => ?_⟩
  -- the reduced minimal model `W` is globally minimal, with integral model `W₀`
  set W := reducedMinimalModel E
  have hmin := (isReducedMinimal_reducedMinimalModel E).isGlobalMinimal
  have := hmin.isIntegral
  set W₀ := integralModel ℤ W
  have hW₀ : W₀.baseChange ℚ = W := baseChange_integralModel_eq ℤ W
  have hN : algorithmicConductor ℤ E = algorithmicConductor ℤ W := by
    obtain ⟨D, hD⟩ := exists_smul_eq_reducedMinimalModel E
    have := algorithmicConductor_smul ℤ D E
    simp only [hD] at this
    exact this.symm
  have hc₄ : W.c₄ = W₀.c₄ := by rw [← hW₀, baseChange, map_c₄]; rfl
  have hc₆ : W.c₆ = W₀.c₆ := by rw [← hW₀, baseChange, map_c₆]; rfl
  have hΔ : W₀.Δ ≠ 0 := fun h0 =>
    W.isUnit_Δ.ne_zero (by rw [← hW₀, baseChange, map_Δ, h0, map_zero])
  have key := hC W₀.c₄ W₀.c₆ W₀.Δ (Ideal.absNorm (algorithmicConductor ℤ W)) W₀.c_relation hΔ
    (Ideal.absNorm_eq_zero_iff.not.2 (algorithmicConductor_ne_bot ℤ W))
    (fun _ => hmin.dvd_six_of_pow_dvd hW₀)
    (fun _ hp => (hmin.dvd_absNorm_algorithmicConductor_iff hW₀ hp).2)
    (fun _ hp hpΔ hpc₄ => (hmin.sq_dvd_absNorm_algorithmicConductor_iff hW₀ hp).2 ⟨hpΔ, hpc₄⟩)
  rw [hN, hc₄, hc₆]
  simpa [Nat.cast_natAbs, sq_abs] using key

end TauCeti

end
