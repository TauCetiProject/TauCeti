/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.NumberField.Global.Places.Basic

/-!
# The logarithmic height as a sum over the places

For a number field `K` and `x : K`, write `ℓ_v(x) = log ‖x‖_v` for the logarithm of the normalized
absolute value of `x` at a place `v` of `K`, finite or infinite. At an infinite place `w` this is
`w.mult * log (w x)`, the weighted logarithm, and at a finite place it is the logarithm of the
`v`-adic absolute value. For `x ≠ 0` only finitely many `ℓ_v(x)` are nonzero, and:

* `∑ᶠ v, ℓ_v(x) = 0`: the product formula in logarithmic form;
* `logHeight₁ x = ∑ᶠ v, ℓ_v(x)⁺`: the logarithmic height is the sum of the positive parts;
* `2 * logHeight₁ x = ∑ᶠ v, |ℓ_v(x)|`: since the `ℓ_v(x)` sum to zero, their positive and
  negative parts have the same total;
* `|ℓ_v(x)| ≤ logHeight₁ x` at every single place.

These identities say that the height of `x` is half the `ℓ¹` norm of its vector of weighted
logarithms. Applied to the units of `𝓞 K`, whose vector is supported on the infinite places, they
compare the height of a unit with its image under the logarithmic embedding of Dirichlet's unit
theorem, and applied to `S`-units they do the same for the `S`-logarithmic embedding. Every
statement holds for `x = 0` as well, where all the terms vanish.

## Main results

* `TauCeti.GlobalNumberFields.finsum_log_normalizedAbsValue`: the product formula,
  `∑ᶠ v, log ‖x‖_v = 0`.
* `TauCeti.GlobalNumberFields.logHeight₁_eq_finsum_posLog_normalizedAbsValue`:
  `logHeight₁ x = ∑ᶠ v, log⁺ ‖x‖_v`.
* `TauCeti.GlobalNumberFields.two_mul_logHeight₁_eq_finsum_abs_log_normalizedAbsValue`:
  `2 * logHeight₁ x = ∑ᶠ v, |log ‖x‖_v|`.
* `TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁`:
  `|log ‖x‖_v| ≤ logHeight₁ x`.
* `TauCeti.GlobalNumberFields.sum_log_adicAbv_add_sum_mult_mul_log_eq_zero` and
  `TauCeti.GlobalNumberFields.two_mul_logHeight₁_eq_sum_abs_log_adicAbv_add_sum_mult_mul_abs_log`:
  the same identities as finite sums over the infinite places and a finite set `S` of finite
  places outside which `x` is a unit.

## References

* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, formula (12).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.5.
-/

public section

open Function IsDedekindDomain NumberField Height Real
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The logarithms of the normalized absolute values of an element of a number field vanish at
all but finitely many places. -/
theorem hasFiniteSupport_log_normalizedAbsValue (x : K) :
    HasFiniteSupport fun v : Place K ↦ log (normalizedAbsValue v x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [HasFiniteSupport]
  · refine (hasFiniteMulSupport_normalizedAbsValue hx).subset fun v hv ↦ ?_
    contrapose! hv
    simp [notMem_mulSupport.mp hv]

/-- The positive parts of the logarithms of the normalized absolute values of an element of a
number field vanish at all but finitely many places. -/
private theorem hasFiniteSupport_posLog_normalizedAbsValue (x : K) :
    HasFiniteSupport fun v : Place K ↦ log⁺ (normalizedAbsValue v x) := by
  simpa only [← posLog_apply] using
    HasFiniteSupport.fun_comp (hasFiniteSupport_log_normalizedAbsValue x) (g := max 0)
      (max_self 0)

/-- **The product formula** in logarithmic form: the logarithms of the normalized absolute values
of an element of a number field sum to zero over all places. -/
@[simp]
theorem finsum_log_normalizedAbsValue (x : K) :
    ∑ᶠ v : Place K, log (normalizedAbsValue v x) = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← log_finprod fun v ↦ normalizedAbsValue_pos v hx, finprod_normalizedAbsValue_eq_one hx,
      log_one]

/-- The logarithmic height of an element of a number field is the sum, over all places, of the
positive parts `log⁺ ‖x‖_v` of the logarithms of its normalized absolute values. -/
theorem logHeight₁_eq_finsum_posLog_normalizedAbsValue (x : K) :
    logHeight₁ x = ∑ᶠ v : Place K, log⁺ (normalizedAbsValue v x) := by
  rw [finsum_sum_type _ (HasFiniteSupport.comp_of_injective Sum.inl_injective
      (hasFiniteSupport_posLog_normalizedAbsValue x)) (Set.toFinite _),
    finsum_eq_sum_of_fintype (α := InfinitePlace K), NumberField.logHeight₁_eq, add_comm,
    ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  simp [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]

/-- Twice the logarithmic height of an element of a number field is the sum, over all places, of
the absolute values `|log ‖x‖_v|`. Since these logarithms sum to zero, their positive and negative
parts contribute equally. -/
theorem two_mul_logHeight₁_eq_finsum_abs_log_normalizedAbsValue (x : K) :
    2 * logHeight₁ x = ∑ᶠ v : Place K, |log (normalizedAbsValue v x)| := by
  simp_rw [abs_log_eq_posLog_add_posLog_inv, ← map_inv₀]
  rw [finsum_add_distrib (hasFiniteSupport_posLog_normalizedAbsValue x)
      (hasFiniteSupport_posLog_normalizedAbsValue x⁻¹),
    ← logHeight₁_eq_finsum_posLog_normalizedAbsValue,
    ← logHeight₁_eq_finsum_posLog_normalizedAbsValue, logHeight₁_inv, two_mul]

/-- The logarithm of the normalized absolute value of `x` at any single place is at most the
logarithmic height of `x`. -/
theorem log_normalizedAbsValue_le_logHeight₁ (v : Place K) (x : K) :
    log (normalizedAbsValue v x) ≤ logHeight₁ x := by
  rw [logHeight₁_eq_finsum_posLog_normalizedAbsValue]
  exact ((le_max_right 0 _).trans_eq posLog_apply.symm).trans <|
    single_le_finsum v (hasFiniteSupport_posLog_normalizedAbsValue x) fun _ ↦ posLog_nonneg

/-- The logarithm of the normalized absolute value of `x` at any single place is at most the
logarithmic height of `x` in absolute value. This sharpens the classical bound by `2 * h(x)`. -/
theorem abs_log_normalizedAbsValue_le_logHeight₁ (v : Place K) (x : K) :
    |log (normalizedAbsValue v x)| ≤ logHeight₁ x := by
  refine abs_le.mpr ⟨?_, log_normalizedAbsValue_le_logHeight₁ v x⟩
  have := log_normalizedAbsValue_le_logHeight₁ v x⁻¹
  rwa [map_inv₀, log_inv, logHeight₁_inv, neg_le] at this

section Finset

variable (S : Finset (HeightOneSpectrum (𝓞 K))) {x : K}

/-- If `x` is a unit outside a finite set `S` of finite places and `f 0 = 0`, then the sum of
`f (log ‖x‖_v)` over all places is a sum over the places of `S` plus a sum over the infinite
places. -/
private theorem finsum_comp_log_normalizedAbsValue_eq_sum {f : ℝ → ℝ} (hf : f 0 = 0)
    (hS : ∀ v ∉ S, HeightOneSpectrum.adicAbv K v x = 1) :
    ∑ᶠ v : Place K, f (log (normalizedAbsValue v x)) =
      ∑ v ∈ S, f (log (HeightOneSpectrum.adicAbv K v x)) +
        ∑ w : InfinitePlace K, f (w.mult * log (w x)) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := S.disjSum Finset.univ), Finset.sum_disjSum]
  · simp [log_pow]
  · rintro (v | w) hv
    · contrapose! hv
      simp [hS v (by simpa using hv), hf]
    · simp

/-- **The product formula** in logarithmic form, for an element `x` of a number field which is a
unit outside a finite set `S` of finite places: the logarithms of its absolute values at the
places of `S`, and its weighted logarithms at the infinite places, sum to zero. -/
theorem sum_log_adicAbv_add_sum_mult_mul_log_eq_zero
    (hS : ∀ v ∉ S, HeightOneSpectrum.adicAbv K v x = 1) :
    ∑ v ∈ S, log (HeightOneSpectrum.adicAbv K v x) +
      ∑ w : InfinitePlace K, w.mult * log (w x) = 0 := by
  simpa using (finsum_comp_log_normalizedAbsValue_eq_sum S (f := id) rfl hS).symm.trans
    (finsum_log_normalizedAbsValue x)

/-- Twice the logarithmic height of an element `x` of a number field which is a unit outside a
finite set `S` of finite places is the `ℓ¹` norm of its vector of logarithms at the places of `S`
and weighted logarithms at the infinite places. -/
theorem two_mul_logHeight₁_eq_sum_abs_log_adicAbv_add_sum_mult_mul_abs_log
    (hS : ∀ v ∉ S, HeightOneSpectrum.adicAbv K v x = 1) :
    2 * logHeight₁ x = ∑ v ∈ S, |log (HeightOneSpectrum.adicAbv K v x)| +
      ∑ w : InfinitePlace K, w.mult * |log (w x)| := by
  rw [two_mul_logHeight₁_eq_finsum_abs_log_normalizedAbsValue,
    finsum_comp_log_normalizedAbsValue_eq_sum S (f := abs) abs_zero hS]
  simp [abs_mul]

end Finset

end TauCeti.GlobalNumberFields
