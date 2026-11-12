/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations on spanned ideals

If `v ≤ δ` on a generating set `s` and `v ≤ 1` on the ideal `Ideal.span s`, then
`v ≤ δ ^ n` on `Ideal.span s ^ (n + 1)`.

`s` is an arbitrary `Set R`: the bound needs no finiteness. Finiteness enters only at the
intended call site, Wedhorn's Theorem 7.10, where `δ` is chosen as the maximum of `v` over a
*finite* generating set of an ideal of definition — a maximum that needs the set to be finite,
whereas this bound does not.

## Why the two hypotheses, and why the shift

Both are needed and neither can be dropped. An element of `Ideal.span s ^ (n + 1)` is a sum of
terms `c * t₀ * ⋯ * tₙ` with `tᵢ ∈ s` and the coefficient `c` **arbitrary**, so a bound on the
generators alone says nothing: `v c` can be as large as it likes. The trick is to attach the
coefficient to one generator — `c * t₀` lies in the ideal, so `v (c * t₀) ≤ 1` — and to bound the
remaining `n` bare generators by `δ` each. That is exactly where the shift comes from: `n + 1`
factors give `δ ^ n`, because one of them is spent absorbing the coefficient.

It is also why the proof does not simply induct along `I ^ (n + 1) = I ^ n * I`: splitting off an
element of `I` rather than a generator only ever yields the bound `1`, so the exponent never
grows. Instead the power is rewritten as the span of the pointwise power `s ^ n`
(`Submodule.span_pow`), which keeps the generators visible.

A finite set also contains a nonvanishing element of greatest value whenever the radical
of its span contains an element of nonzero value. This maximum needs no bound on the ideal.

## Main results

* `Valuation.map_le_pow_of_mem_span_pow_succ`
* `Valuation.exists_mem_max_restrict_ne_zero`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Theorem 7.10.
-/

public section

namespace Valuation

open scoped Pointwise

variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {s : Set R} {δ : Γ₀}

/-- The engine of `map_le_pow_of_mem_span_pow_succ`: for `y` in the span of the `n`-fold pointwise
power of `s` and `r` in the ideal, `v (r * y) ≤ δ ^ n`. -/
private theorem map_mul_le_pow_of_mem_span_pow (hs : ∀ t ∈ s, v t ≤ δ)
    (h1 : ∀ a ∈ Ideal.span s, v a ≤ 1) (n : ℕ) :
    ∀ y ∈ Ideal.span (s ^ n), ∀ r ∈ Ideal.span s, v (r * y) ≤ δ ^ n := by
  induction n with
  | zero => intro y _ r hr; simpa using h1 _ (Ideal.mul_mem_right y _ hr)
  | succ n ih =>
    intro y hy
    induction hy using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨q', hq', t, ht, rfl⟩ := Set.mem_mul.mp (by rwa [pow_succ] at hq)
      intro r hr
      rw [← mul_assoc, map_mul, pow_succ]
      exact mul_le_mul' (ih _ (Ideal.subset_span hq') r hr) (hs t ht)
    | zero => intro r _; simp
    | add y₁ y₂ _ _ ih₁ ih₂ =>
      intro r hr
      rw [mul_add]
      exact v.map_add_le (ih₁ r hr) (ih₂ r hr)
    | smul c y _ ih' =>
      intro r hr
      rw [smul_eq_mul, ← mul_assoc]
      exact ih' _ (Ideal.mul_mem_right c _ hr)

/-- **A valuation on a power of a span.** If `v ≤ δ` on a generating set `s` and `v ≤ 1` on
`Ideal.span s`, then `v ≤ δ ^ n` on `Ideal.span s ^ (n + 1)`.

One of the `n + 1` factors is spent absorbing the arbitrary coefficient, which is why the exponent
on the right is `n` and not `n + 1`; see the module docstring. -/
theorem map_le_pow_of_mem_span_pow_succ (hs : ∀ t ∈ s, v t ≤ δ)
    (h1 : ∀ a ∈ Ideal.span s, v a ≤ 1) {n : ℕ} {a : R}
    (ha : a ∈ Ideal.span s ^ (n + 1)) : v a ≤ δ ^ n := by
  have hspan : Ideal.span s ^ n = Ideal.span (s ^ n) := Submodule.span_pow s n
  rw [pow_succ', hspan] at ha
  refine Submodule.mul_induction_on ha (fun r hr y hy ↦ ?_) fun x y hx hy ↦ ?_
  · exact v.map_mul_le_pow_of_mem_span_pow hs h1 n y hy r hr
  · exact v.map_add_le hx hy

/-- A finite set has a nonvanishing element of greatest value if the radical of its span
contains an element of nonzero value. -/
theorem exists_mem_max_restrict_ne_zero {A Γ : Type*} [CommRing A]
    [LinearOrderedCommGroupWithZero Γ] {v : Valuation A Γ} {T : Finset A} {a₀ : A}
    (ha₀ : a₀ ∈ (Ideal.span (T : Set A)).radical) (ha₀0 : v a₀ ≠ 0) :
    ∃ t₀ ∈ T, v t₀ ≠ 0 ∧ ∀ t ∈ T, v.restrict t ≤ v.restrict t₀ := by
  have hsupp : ¬ ∀ t ∈ T, t ∈ v.supp := by
    intro hall
    have hspan : Ideal.span (T : Set A) ≤ v.supp := Ideal.span_le.mpr hall
    have ha₀supp := (inferInstance : v.supp.IsPrime).radical_le_iff.mpr hspan ha₀
    exact ha₀0 ((v.mem_supp_iff _).mp ha₀supp)
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with rfl | hne'
    · exact absurd (by simp) hsupp
    · exact hne'
  obtain ⟨t₀, ht₀T, ht₀max⟩ := T.exists_max_image (fun t ↦ v.restrict t) hTne
  refine ⟨t₀, ht₀T, fun hz ↦ hsupp fun t ht ↦ ?_, ht₀max⟩
  rw [v.mem_supp_iff]
  have hle : v.restrict t ≤ v.restrict t₀ := ht₀max t ht
  rw [v.restrict_eq_zero_iff.mpr hz] at hle
  exact v.restrict_eq_zero_iff.mp (le_antisymm hle zero_le)

end Valuation
