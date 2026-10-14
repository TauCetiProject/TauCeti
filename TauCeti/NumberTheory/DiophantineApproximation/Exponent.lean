/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Codex
-/
module

public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# The irrationality exponent

This file defines the irrationality exponent of a real number as the supremum of the exponents
for which it satisfies Mathlib's `LiouvilleWith` predicate.  It establishes the order-theoretic
API of this definition, identifies infinite irrationality exponent with the Liouville property,
computes the exponent of rational numbers, and records its elementary rational affine
invariances.

The definition follows Sondow, *Irrationality measures, irrationality bases, and a theorem of
Jarnik*, Definition 2.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- The irrationality exponent of `ξ` is the supremum of the real exponents `p` for which
`LiouvilleWith p ξ` holds. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : LiouvilleWith p ξ), ENNReal.ofReal p

/-- The irrationality exponent is the supremum of `ENNReal.ofReal p` over the exponents `p` for
which `LiouvilleWith p ξ` holds. -/
theorem irrationalityExponent_def (ξ : ℝ) :
    irrationalityExponent ξ = ⨆ (p : ℝ) (_ : LiouvilleWith p ξ), ENNReal.ofReal p :=
  (rfl)

/-- An exponent satisfying `LiouvilleWith` is at most the irrationality exponent. -/
theorem le_irrationalityExponent_of_liouvilleWith {p ξ : ℝ} (h : LiouvilleWith p ξ) :
    ENNReal.ofReal p ≤ irrationalityExponent ξ :=
  le_iSup_of_le p <| le_iSup_of_le h le_rfl

/-- The irrationality exponent of every real number is at least one. -/
theorem one_le_irrationalityExponent (ξ : ℝ) : 1 ≤ irrationalityExponent ξ := by
  simpa using le_irrationalityExponent_of_liouvilleWith (liouvilleWith_one ξ)

/-- A real exponent strictly below the irrationality exponent satisfies `LiouvilleWith`. -/
theorem liouvilleWith_of_lt_irrationalityExponent {p ξ : ℝ}
    (h : ENNReal.ofReal p < irrationalityExponent ξ) : LiouvilleWith p ξ := by
  by_cases hp : p ≤ 0
  · exact (liouvilleWith_one ξ).mono (hp.trans zero_le_one)
  rw [irrationalityExponent, lt_iSup_iff] at h
  obtain ⟨q, hq⟩ := h
  rw [lt_iSup_iff] at hq
  obtain ⟨hqL, hpq⟩ := hq
  exact hqL.mono <| (ENNReal.ofReal_lt_ofReal_iff'.mp hpq).1.le

/-- The irrationality exponent is bounded by `a` exactly when every exponent satisfying
`LiouvilleWith` maps below `a`. -/
theorem irrationalityExponent_le_iff {ξ : ℝ} {a : ℝ≥0∞} :
    irrationalityExponent ξ ≤ a ↔ ∀ p : ℝ, LiouvilleWith p ξ → ENNReal.ofReal p ≤ a := by
  simp [irrationalityExponent]

/-- A real number has infinite irrationality exponent exactly when it is a Liouville number. -/
theorem irrationalityExponent_eq_top_iff (ξ : ℝ) :
    irrationalityExponent ξ = ⊤ ↔ Liouville ξ := by
  constructor
  · intro h
    rw [← forall_liouvilleWith_iff]
    intro p
    apply liouvilleWith_of_lt_irrationalityExponent
    rw [h]
    exact ENNReal.ofReal_lt_top
  · intro h
    apply top_unique
    rw [← ENNReal.iSup_natCast]
    refine iSup_le fun n ↦ ?_
    simpa using le_irrationalityExponent_of_liouvilleWith (h.liouvilleWith n)

/-- The irrationality exponent of a rational number is one. -/
@[simp]
theorem irrationalityExponent_ratCast (q : ℚ) : irrationalityExponent (q : ℝ) = 1 := by
  apply le_antisymm
  · rw [irrationalityExponent_le_iff]
    intro p hp
    have hp_one : p ≤ 1 := by
      by_contra hp_one
      exact q.not_irrational (hp.irrational (lt_of_not_ge hp_one))
    simpa using ENNReal.ofReal_le_ofReal hp_one
  · exact one_le_irrationalityExponent q

/-- Adding a rational number does not change the irrationality exponent. -/
@[simp]
theorem irrationalityExponent_add_ratCast (ξ : ℝ) (q : ℚ) :
    irrationalityExponent (ξ + q) = irrationalityExponent ξ := by
  simp only [irrationalityExponent, LiouvilleWith.add_rat_iff]

/-- Multiplying by a nonzero rational number does not change the irrationality exponent. -/
@[simp]
theorem irrationalityExponent_ratCast_mul (q : ℚ) (ξ : ℝ) (hq : q ≠ 0) :
    irrationalityExponent (q * ξ) = irrationalityExponent ξ := by
  simp only [irrationalityExponent, LiouvilleWith.rat_mul_iff hq]

/-- Negation does not change the irrationality exponent. -/
@[simp]
theorem irrationalityExponent_neg (ξ : ℝ) :
    irrationalityExponent (-ξ) = irrationalityExponent ξ := by
  simp only [irrationalityExponent, LiouvilleWith.neg_iff]

/-- An irrationality exponent strictly greater than one forces irrationality. -/
theorem irrational_of_one_lt_irrationalityExponent {ξ : ℝ}
    (hξ : 1 < irrationalityExponent ξ) : Irrational ξ := by
  rw [irrationalityExponent, lt_iSup_iff] at hξ
  obtain ⟨p, hp⟩ := hξ
  rw [lt_iSup_iff] at hp
  obtain ⟨hpL, hp_one⟩ := hp
  exact hpL.irrational <| (ENNReal.ofReal_lt_ofReal_iff'.mp <| by simpa using hp_one).1

end TauCeti
