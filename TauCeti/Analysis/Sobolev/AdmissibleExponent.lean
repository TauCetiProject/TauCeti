/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Admissible exponents for real Cauchy–Riemann operators with Sobolev coefficients

A real Cauchy–Riemann operator of class `W^{ℓ-1,p}` on a surface, for an integer `ℓ ≥ 1` and a
finite exponent `p > 2`, is realized as a bounded operator `W^{k,q} → W^{k-1,q}` for the exponent
pairs `(k, q)` of McDuff–Salamon Theorem C.1.10: integers `1 ≤ k ≤ ℓ` and reals `q > 1` with
`k - 2/q ≤ ℓ - 2/p`. This file records that condition as `TauCeti.IsAdmissibleRealizationExponent`
and the arithmetic about it, independently of any operator.

## Main results

* `TauCeti.isAdmissibleRealizationExponent_iff`: the defining conditions.
* `TauCeti.isAdmissibleRealizationExponent_self_iff`: at the top order `k = ℓ` the condition is
  exactly `1 < q ≤ p`.
* `TauCeti.isAdmissibleRealizationExponent_one_iff`: for `ℓ = 1` the only order is `k = 1`, and
  the condition is `1 < q ≤ p`.
* `TauCeti.isAdmissibleRealizationExponent_of_lt`: below the top order, `k < ℓ`, every `q > 1` is
  admissible when `p > 2`. In particular a `W^{1,p}` operator (`ℓ = 2`) has a realization
  `W^{1,q} → L^q` for every `q > 1`.
* `TauCeti.not_forall_isAdmissibleRealizationExponent_imp_le`: the rule "`q ≤ p` for every `k`"
  is wrong.

The exponent bookkeeping for the compactness of multiplication by `α ∈ L^p` from `W^{1,q}` to
`L^q` in dimension two is `ENNReal.exists_inv_lt_inv_add_inv_two_and_inv_add_inv_le_iff` in
`TauCeti.Data.ENNReal.Inv`.

## References

D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
Definition C.1.5, Theorem C.1.10 and Lemma C.2.2.
-/

public section

namespace TauCeti

/-- The exponent pair `(k, q)` is admissible for a real Cauchy–Riemann operator of class
`W^{ℓ-1,p}` (McDuff–Salamon, Theorem C.1.10): `1 ≤ k ≤ ℓ`, `1 < q` and `k - 2/q ≤ ℓ - 2/p`.
The operator is then realized as a bounded operator `W^{k,q} → W^{k-1,q}`. -/
def IsAdmissibleRealizationExponent (ℓ : ℕ) (p : ℝ) (k : ℕ) (q : ℝ) : Prop :=
  1 ≤ k ∧ k ≤ ℓ ∧ 1 < q ∧ (k : ℝ) - 2 / q ≤ ℓ - 2 / p

/-- The defining conditions of an admissible exponent pair: `1 ≤ k ≤ ℓ`, `1 < q` and
`k - 2/q ≤ ℓ - 2/p`. -/
theorem isAdmissibleRealizationExponent_iff {ℓ : ℕ} {p : ℝ} {k : ℕ} {q : ℝ} :
    IsAdmissibleRealizationExponent ℓ p k q ↔
      1 ≤ k ∧ k ≤ ℓ ∧ 1 < q ∧ (k : ℝ) - 2 / q ≤ ℓ - 2 / p :=
  Iff.rfl

/-- At the top order `k = ℓ` the admissibility condition is exactly `1 < q ≤ p`. For `ℓ = 2`
this says that the realization `W^{2,q} → W^{1,q}` needs `q ≤ p`. -/
@[simp]
theorem isAdmissibleRealizationExponent_self_iff {ℓ : ℕ} {p q : ℝ} (hp : 0 < p) :
    IsAdmissibleRealizationExponent ℓ p ℓ q ↔ 1 ≤ ℓ ∧ 1 < q ∧ q ≤ p := by
  rw [isAdmissibleRealizationExponent_iff]
  constructor
  · rintro ⟨hℓ, -, hq, hle⟩
    have hq0 : 0 < q := by linarith
    refine ⟨hℓ, hq, ?_⟩
    have h : 2 / p ≤ 2 / q := by linarith
    rwa [div_le_div_iff_of_pos_left two_pos hp hq0] at h
  · rintro ⟨hℓ, hq, hqp⟩
    have hq0 : 0 < q := by linarith
    have h : 2 / p ≤ 2 / q := div_le_div_of_nonneg_left zero_le_two hq0 hqp
    exact ⟨hℓ, le_rfl, hq, by linarith⟩

/-- For `ℓ = 1` the only admissible order is `k = 1`, at the exponents `1 < q ≤ p`. -/
@[simp]
theorem isAdmissibleRealizationExponent_one_iff {k : ℕ} {p q : ℝ} (hp : 0 < p) :
    IsAdmissibleRealizationExponent 1 p k q ↔ k = 1 ∧ 1 < q ∧ q ≤ p := by
  constructor
  · intro h
    have hk : k = 1 := le_antisymm h.2.1 h.1
    subst hk
    exact ⟨rfl, ((isAdmissibleRealizationExponent_self_iff hp).1 h).2⟩
  · rintro ⟨rfl, hq⟩
    exact (isAdmissibleRealizationExponent_self_iff hp).2 ⟨le_rfl, hq⟩

/-- Below the top order every `q > 1` is admissible when `p > 2`: from `k ≤ ℓ - 1` and
`2/p < 1` one gets `k - 2/q < k ≤ ℓ - 1 < ℓ - 2/p`. For `ℓ = 2`, `k = 1` this is the realization
`W^{1,q} → L^q` of a `W^{1,p}` operator at every `q > 1`, including `q > p`. -/
theorem isAdmissibleRealizationExponent_of_lt {ℓ k : ℕ} {p q : ℝ} (hk : 1 ≤ k) (hkℓ : k < ℓ)
    (hp : 2 < p) (hq : 1 < q) : IsAdmissibleRealizationExponent ℓ p k q := by
  refine ⟨hk, hkℓ.le, hq, ?_⟩
  have hkℓ' : (k : ℝ) + 1 ≤ ℓ := by exact_mod_cast hkℓ
  have hq' : 0 < 2 / q := div_pos two_pos (by linarith)
  have hp' : 2 / p < 1 := (div_lt_one (by linarith)).2 hp
  linarith

/-- The plausible rule "`q ≤ p` at every order `k`" is wrong: for `ℓ = 2`, `p = 3` the pair
`(k, q) = (1, 4)` is admissible although `q > p`. -/
theorem not_forall_isAdmissibleRealizationExponent_imp_le :
    ¬ ∀ (ℓ : ℕ) (p : ℝ) (k : ℕ) (q : ℝ),
      2 < p → IsAdmissibleRealizationExponent ℓ p k q → q ≤ p := by
  intro h
  have := h 2 3 1 4 (by norm_num)
    (isAdmissibleRealizationExponent_of_lt le_rfl one_lt_two (by norm_num) (by norm_num))
  norm_num at this

end TauCeti
