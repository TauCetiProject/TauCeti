/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.Ostrowski

/-!
# Weak approximation for absolute values restricting to standard ones on `ℚ`

Mathlib's `AbsoluteValue.denseRange_algebraMap_pi` approximates finitely many targets for a family
of nontrivial, pairwise inequivalent absolute values. This file states it for a finite set of
absolute values in which equivalent ones are equal, and supplies that hypothesis for absolute values
on a field of characteristic zero which restrict on `ℚ` to the real or to a `q`-adic absolute
value: two such that are equivalent are equal.

## Main definitions

* `TauCeti.Rat.AbsoluteValue.IsStandard`: being the real or a `q`-adic absolute value on `ℚ`.

## Main results

* `TauCeti.exists_forall_apply_sub_lt`: simultaneous approximation for a finite set of absolute
  values in which equivalent ones are equal.
* `AbsoluteValue.IsEquiv.eq_of_isStandard`: equivalent absolute values with standard restrictions
  to `ℚ` are equal.
* `NumberField.InfinitePlace.apply_ratCast_eq_real`: an infinite place restricts to the real
  absolute value.
-/

public section

open NumberField

namespace TauCeti

/-- **Weak approximation for a finite set of absolute values.** For a finite set `S` of nontrivial
absolute values on a field, any two of which are equal as soon as they are equivalent, every family
of targets is approximated simultaneously by one element of the field. -/
theorem exists_forall_apply_sub_lt {F : Type*} [Field F] (S : Finset (AbsoluteValue F ℝ))
    (hS : ∀ v ∈ S, v.IsNontrivial) (hS' : ∀ v ∈ S, ∀ w ∈ S, v.IsEquiv w → v = w)
    (t : AbsoluteValue F ℝ → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F, ∀ v ∈ S, v (x - t v) < ε := by
  obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi (v := fun v : S ↦ v.1)
    (fun v ↦ hS v.1 v.2)
    (fun v w hvw h ↦ hvw (Subtype.ext (hS' v.1 v.2 w.1 w.2 h)))).exists_dist_lt
      (fun v : S ↦ WithAbs.toAbs v.1 (t v.1)) hε
  refine ⟨x, fun v hv ↦ ?_⟩
  have h := (dist_pi_lt_iff hε).mp hx ⟨v, hv⟩
  rwa [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at h

/-- Two equivalent absolute values on a field of characteristic zero which agree on `ℚ`, and are
not trivial there, are equal. -/
theorem _root_.AbsoluteValue.IsEquiv.eq_of_forall_ratCast_eq {F : Type*} [Field F] [CharZero F]
    {v w : AbsoluteValue F ℝ} (h : v.IsEquiv w) (hvw : ∀ r : ℚ, v r = w r) {r₀ : ℚ}
    (hr₀ : r₀ ≠ 0) (hv : v r₀ ≠ 1) : v = w := by
  obtain ⟨c, hc, hcw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp h
  have hpos : 0 < v r₀ := v.pos (by exact_mod_cast hr₀)
  have h1 : v r₀ ^ c = v r₀ ^ (1 : ℝ) := by
    rw [Real.rpow_one, congrFun hcw (r₀ : F), hvw]
  have hc1 : c = 1 := (Real.rpow_right_inj hpos hv).mp h1
  ext x
  rw [← congrFun hcw x, hc1, Real.rpow_one]

/-- The standard absolute values on `ℚ`: the real one and the `q`-adic ones. -/
def Rat.AbsoluteValue.IsStandard (a : AbsoluteValue ℚ ℝ) : Prop :=
  a = Rat.AbsoluteValue.real ∨ ∃ (q : ℕ) (_ : Fact q.Prime), a = Rat.AbsoluteValue.padic q

/-- The real absolute value on `ℚ` is standard. -/
theorem Rat.AbsoluteValue.IsStandard.real :
    Rat.AbsoluteValue.IsStandard Rat.AbsoluteValue.real :=
  .inl rfl

/-- The `q`-adic absolute value on `ℚ` is standard. -/
theorem Rat.AbsoluteValue.IsStandard.padic (q : ℕ) [Fact q.Prime] :
    Rat.AbsoluteValue.IsStandard (Rat.AbsoluteValue.padic q) :=
  .inr ⟨q, inferInstance, rfl⟩

/-- Two equivalent standard absolute values on `ℚ` are equal. -/
theorem Rat.AbsoluteValue.IsStandard.eq_of_isEquiv {a b : AbsoluteValue ℚ ℝ}
    (ha : Rat.AbsoluteValue.IsStandard a) (hb : Rat.AbsoluteValue.IsStandard b) (h : a.IsEquiv b) :
    a = b := by
  rcases ha with rfl | ⟨q, _, rfl⟩ <;> rcases hb with rfl | ⟨q', _, rfl⟩
  · rfl
  · exact absurd h (Rat.AbsoluteValue.not_real_isEquiv_padic q')
  · exact absurd h.symm (Rat.AbsoluteValue.not_real_isEquiv_padic q)
  · have hlt : Rat.AbsoluteValue.padic q' (q : ℚ) < 1 := by
      refine h.lt_one_iff.mp ?_
      rw [Rat.AbsoluteValue.padic_eq_padicNorm]
      exact_mod_cast (padicNorm.nat_lt_one_iff q).mpr dvd_rfl
    rw [Rat.AbsoluteValue.padic_eq_padicNorm] at hlt
    have hdvd := (padicNorm.nat_lt_one_iff q).mp (by exact_mod_cast hlt)
    obtain rfl := (Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hdvd
    rfl

/-- A standard absolute value on `ℚ` takes a value other than `1` at a nonzero rational. -/
theorem Rat.AbsoluteValue.IsStandard.exists_ne_one {a : AbsoluteValue ℚ ℝ}
    (ha : Rat.AbsoluteValue.IsStandard a) : ∃ r : ℚ, r ≠ 0 ∧ a r ≠ 1 := by
  rcases ha with rfl | ⟨q, hq, rfl⟩
  · exact ⟨2, two_ne_zero, by norm_num⟩
  · refine ⟨q, Nat.cast_ne_zero.mpr hq.out.ne_zero, ?_⟩
    simp only [Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
    have : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    push_cast
    exact (inv_lt_one_of_one_lt₀ this).ne

/-- **Equivalent absolute values restricting to standard ones on `ℚ` are equal.** -/
theorem _root_.AbsoluteValue.IsEquiv.eq_of_isStandard {F : Type*} [Field F] [CharZero F]
    {v w : AbsoluteValue F ℝ} (h : v.IsEquiv w) {a b : AbsoluteValue ℚ ℝ}
    (ha : Rat.AbsoluteValue.IsStandard a) (hb : Rat.AbsoluteValue.IsStandard b)
    (hva : ∀ r : ℚ, v r = a r) (hwb : ∀ r : ℚ, w r = b r) : v = w := by
  have hab : a = b := ha.eq_of_isEquiv hb <| AbsoluteValue.isEquiv_iff_lt_one_iff.mpr fun r ↦ by
    rw [← hva, ← hwb]
    exact h.lt_one_iff
  obtain ⟨r₀, hr₀, hr₀'⟩ := ha.exists_ne_one
  exact h.eq_of_forall_ratCast_eq (fun r ↦ by rw [hva, hwb, hab]) hr₀
    (by rwa [hva])

/-- An absolute value restricting to a standard one on `ℚ` is nontrivial. -/
theorem _root_.AbsoluteValue.isNontrivial_of_isStandard {F : Type*} [Field F] [CharZero F]
    {v : AbsoluteValue F ℝ} {a : AbsoluteValue ℚ ℝ} (ha : Rat.AbsoluteValue.IsStandard a)
    (hva : ∀ r : ℚ, v r = a r) : v.IsNontrivial := by
  obtain ⟨r₀, hr₀, hr₀'⟩ := ha.exists_ne_one
  exact ⟨r₀, by exact_mod_cast hr₀, by rwa [hva]⟩

/-- An infinite place restricts on `ℚ` to the real absolute value. -/
theorem _root_.NumberField.InfinitePlace.apply_ratCast_eq_real {K : Type*} [Field K]
    (w : InfinitePlace K) (r : ℚ) : w (r : K) = Rat.AbsoluteValue.real r := by
  rw [InfinitePlace.map_ratCast, Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs, ← Real.norm_eq_abs,
    Rat.norm_cast_real]

end TauCeti
