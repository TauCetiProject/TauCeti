/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
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

* `TauCeti.isAdmissibleRealizationExponent_self_iff`: at the top order `k = ℓ` the condition is
  exactly `1 < q ≤ p`.
* `TauCeti.isAdmissibleRealizationExponent_one_iff`: for `ℓ = 1` the only order is `k = 1`, and
  the condition is `1 < q ≤ p`.
* `TauCeti.isAdmissibleRealizationExponent_of_lt`: below the top order, `k < ℓ`, every `q > 1` is
  admissible when `p > 2`. In particular a `W^{1,p}` operator (`ℓ = 2`) has a realization
  `W^{1,q} → L^q` for every `q > 1`.
* `TauCeti.not_forall_isAdmissibleRealizationExponent_imp_le`: the rule "`q ≤ p` for every `k`"
  is wrong.
* `TauCeti.exists_inv_lt_inv_add_inv_two_and_inv_add_inv_le_iff`: the exponent bookkeeping for
  the compactness of multiplication by `α ∈ L^p` from `W^{1,q}` to `L^q` in dimension two at
  `q < 2`. An exponent `s` below the Sobolev exponent `2q/(2-q)` with `1/p + 1/s ≤ 1/q` exists
  exactly when `p > 2`, so the argument has no room at `p = 2`.

## References

D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
Definition C.1.5, Theorem C.1.10 and Lemma C.2.2.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- The exponent pair `(k, q)` is admissible for a real Cauchy–Riemann operator of class
`W^{ℓ-1,p}` (McDuff–Salamon, Theorem C.1.10): `1 ≤ k ≤ ℓ`, `1 < q` and `k - 2/q ≤ ℓ - 2/p`.
The operator is then realized as a bounded operator `W^{k,q} → W^{k-1,q}`. -/
def IsAdmissibleRealizationExponent (ℓ : ℕ) (p : ℝ) (k : ℕ) (q : ℝ) : Prop :=
  1 ≤ k ∧ k ≤ ℓ ∧ 1 < q ∧ (k : ℝ) - 2 / q ≤ ℓ - 2 / p

/-- At the top order `k = ℓ` the admissibility condition is exactly `1 < q ≤ p`. For `ℓ = 2`
this says that the realization `W^{2,q} → W^{1,q}` needs `q ≤ p`. -/
theorem isAdmissibleRealizationExponent_self_iff {ℓ : ℕ} {p q : ℝ} (hp : 0 < p) :
    IsAdmissibleRealizationExponent ℓ p ℓ q ↔ 1 ≤ ℓ ∧ 1 < q ∧ q ≤ p := by
  unfold IsAdmissibleRealizationExponent
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

/-- Exponent bookkeeping for the compactness of multiplication by `α ∈ L^p` from `W^{1,q}` to
`L^q` in dimension two at `q < 2` (the local form of McDuff–Salamon Lemma C.2.2). `W^{1,q}` embeds
compactly in `L^s` for `s` below the Sobolev exponent `2q/(2-q)`, that is for `q⁻¹ < s⁻¹ + 2⁻¹`,
and Hölder maps `L^p × L^s` to `L^q` on a finite measure space when `p⁻¹ + s⁻¹ ≤ q⁻¹`. Such an
`s` exists exactly when `p > 2`: at `p = 2` the two conditions would force `q⁻¹ < q⁻¹`. -/
theorem exists_inv_lt_inv_add_inv_two_and_inv_add_inv_le_iff {p q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq2 : q < 2) :
    (∃ s : ℝ≥0∞, q⁻¹ < s⁻¹ + 2⁻¹ ∧ p⁻¹ + s⁻¹ ≤ q⁻¹) ↔ 2 < p := by
  have hqtop : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hq0
  have h2q : (2 : ℝ≥0∞)⁻¹ < q⁻¹ := ENNReal.inv_lt_inv.2 hq2
  constructor
  · rintro ⟨s, hlt, hle⟩
    have hstop : s⁻¹ ≠ ∞ := ne_top_of_le_ne_top hqtop (le_add_self.trans hle)
    have h : s⁻¹ + p⁻¹ < s⁻¹ + 2⁻¹ := by rw [add_comm]; exact hle.trans_lt hlt
    exact ENNReal.inv_lt_inv.1 ((ENNReal.add_lt_add_iff_left hstop).1 h)
  · intro hp
    have hp2 : p⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.2 hp
    have hpq : p⁻¹ ≤ q⁻¹ := (hp2.trans h2q).le
    have hptop : p⁻¹ ≠ ∞ := ne_top_of_le_ne_top hqtop hpq
    refine ⟨(q⁻¹ - p⁻¹)⁻¹, ?_, ?_⟩
    · rw [inv_inv]
      calc q⁻¹ = q⁻¹ - p⁻¹ + p⁻¹ := (tsub_add_cancel_of_le hpq).symm
        _ < q⁻¹ - p⁻¹ + 2⁻¹ := ENNReal.add_lt_add_left
          (ENNReal.sub_ne_top hqtop) hp2
    · rw [inv_inv, add_tsub_cancel_of_le hpq]

end TauCeti
