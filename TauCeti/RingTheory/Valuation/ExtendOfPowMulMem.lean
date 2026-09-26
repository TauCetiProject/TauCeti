/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Extending a valuation from a subring reached by the powers of an element

Let `R` be a subring of a commutative ring `A`, and let `s ∈ R` be an element some power of which
carries each element of `A` into `R`: for every `a` there is an `n` with `sⁿ * a ∈ R`. A
valuation `w` of `R` that does not vanish at `s` then has only one possible extension to `A`,

`v a = w (sⁿ * a) * (w s)⁻ⁿ`,

and this file shows that the formula is well defined, is a valuation, and is the only valuation
of `A` restricting to `w`.

No topology is involved. The hypothesis is met by a ring of definition of a Huber ring — it is
open, so a topologically nilpotent `s` satisfies it — and
`TauCeti.RingTheory.Huber.ExtendValuation` is that specialisation.

## Why this is not `Valuation.extendToLocalization`

Mathlib extends a valuation along a localisation that inverts a set on which the valuation is
nonzero. That does not apply here: the hypothesis does not make `s` invertible in `A`, so there
need be no ring map `R[1/s] → A` at all. Take `R = A = ℤ_[p]` and `s = p`, where `R[1/s] = ℚ_[p]`.
What is true, and is all the formula needs, is the one-sided statement that every element of `A`
is carried into `R` by a power of `s`.

## Well-definedness

Independence of `n` reduces to the case of comparing `n` with `n + j`, where
`s ^ (n + j) * a = s ^ j * (sⁿ * a)` splits off a factor whose `w`-value is `(w s) ^ j`, exactly
cancelling the extra `(w s)⁻ʲ`. Two arbitrary exponents are then compared through their sum.

The two valuation axioms reach a shared exponent differently. For a product, each argument keeps
its *own* workable exponent — `x` at `m` and `y` at `n` — and only the product is evaluated at
`m + n`, because `s ^ (m + n) * (x * y) = (sᵐ * x) * (sⁿ * y)` already splits that way. A sum has
no such splitting, so there both terms are raised to the common exponent `m + n`. In each case
the axiom is then inherited from `w` once the shared factor `(w s)⁻⁽ᵐ⁺ⁿ⁾` is divided out.

## Main definitions

* `Valuation.extendOfPowMulMem` : the extension of `w` to `A`.

## Main results

* `Valuation.extendOfPowMulMem_apply` : the defining formula, at **every** exponent that works,
  not just the chosen one. This is the interface; the definition goes through
  `Classical.choose` and is not meant to be unfolded.
* `Valuation.extendOfPowMulMem_coe` : the extension restricts to `w`.
* `Valuation.eq_extendOfPowMulMem` : **uniqueness** — any valuation of `A` restricting to `w`
  *is* this one, so the extension is canonical.
* `Valuation.extendOfPowMulMem_congr` : consequently the extension does not depend on which `s`
  is used to build it.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(3), which uses this
  extension for a ring of definition of a Huber ring.

## Provenance

Adapted from [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch
`dev/adic-spaces`, commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/Lemma745.lean`,
declarations `vExtFun_step`, `vExtFun_well_defined`, `vExtFun_map_mul`,
`vExtFun_map_add_le_max` and `exists_valuation_extension`. **Adapted, not copied**: that
development states the result existentially, as `∃ v_ext, …`, for a pair of definition of a
Huber ring, and threads the value `w s` through five separate lemmas as an explicit parameter
with its own defining equation. Here the extension is a `def`, so it can be named and rewritten
at a call site, the arithmetic is one private lemma rather than four public ones, and the whole
construction is carried out for a subring reached by the powers of `s`. The uniqueness theorem
and the resulting independence of `s` have no counterpart there.
-/

public section

namespace Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {R : Subring A}

/-- Raising the exponent keeps the product in the subring. -/
private theorem pow_add_mul_mem {s : A} (hs : s ∈ R) {a : A} {k : ℕ} (hk : s ^ k * a ∈ R)
    (j : ℕ) : s ^ (k + j) * a ∈ R := by
  rw [add_comm, pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem hs j) hk

/-- The quotient `w (sⁿ * a) * (w s)⁻ⁿ` does not depend on `n`. -/
private theorem extend_aux (w : Valuation R Γ₀) {s : A} (hs : s ∈ R) (hw : w ⟨s, hs⟩ ≠ 0)
    {a : A} {m n : ℕ} (hm : s ^ m * a ∈ R) (hn : s ^ n * a ∈ R) :
    w ⟨s ^ m * a, hm⟩ * (w ⟨s, hs⟩)⁻¹ ^ m = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n := by
  -- one step: comparing `k` with `k + j`
  have step : ∀ {k : ℕ} (hk : s ^ k * a ∈ R) (j : ℕ),
      w ⟨s ^ k * a, hk⟩ * (w ⟨s, hs⟩)⁻¹ ^ k =
        w ⟨s ^ (k + j) * a, pow_add_mul_mem hs hk j⟩ * (w ⟨s, hs⟩)⁻¹ ^ (k + j) := by
    intro k hk j
    have hsplit : (⟨s ^ (k + j) * a, pow_add_mul_mem hs hk j⟩ : R) =
        ⟨s, hs⟩ ^ j * ⟨s ^ k * a, hk⟩ :=
      Subtype.ext (by push_cast; ring)
    rw [hsplit, map_mul, map_pow, pow_add, mul_comm (w ⟨s, hs⟩ ^ j), mul_mul_mul_comm,
      ← mul_pow, mul_inv_cancel₀ hw, one_pow, mul_one]
  -- compare both exponents with their sum
  rw [step hm n, step hn m]
  exact congrArg₂ (· * ·) (congrArg w (Subtype.ext (by push_cast; ring))) (by rw [add_comm])

/-- **The extension of `w` from `R` to `A`**, when every element of `A` is carried into `R` by
some power of `s`. For any `n` with `sⁿ * a ∈ R` the value is `w (sⁿ * a) * (w s)⁻ⁿ`, and
`extendOfPowMulMem_apply` says so at every such `n`. -/
noncomputable def extendOfPowMulMem (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) : Valuation A Γ₀ where
  toFun a := w ⟨s ^ (hpow a).choose * a, (hpow a).choose_spec⟩ * (w ⟨s, hs⟩)⁻¹ ^ (hpow a).choose
  map_zero' := by
    rw [extend_aux w hs hw _ (n := 0) (by simp), pow_zero (w ⟨s, hs⟩)⁻¹, mul_one,
      ← w.map_zero]
    exact congrArg w (Subtype.ext (by simp))
  map_one' := by
    rw [extend_aux w hs hw _ (n := 0) (by simp), pow_zero (w ⟨s, hs⟩)⁻¹, mul_one,
      ← w.map_one]
    exact congrArg w (Subtype.ext (by simp))
  map_mul' x y := by
    obtain ⟨m, hm⟩ := hpow x
    obtain ⟨n, hn⟩ := hpow y
    have hxy : s ^ (m + n) * (x * y) ∈ R := by
      convert R.mul_mem hm hn using 1
      ring
    have hsplit : (⟨s ^ (m + n) * (x * y), hxy⟩ : R) = ⟨s ^ m * x, hm⟩ * ⟨s ^ n * y, hn⟩ :=
      Subtype.ext (by push_cast; ring)
    rw [extend_aux w hs hw _ hxy, extend_aux w hs hw _ hm, extend_aux w hs hw _ hn, hsplit,
      map_mul, pow_add, mul_mul_mul_comm]
  map_add_le_max' x y := by
    -- a sum needs one exponent that works for both terms, so take the sum of the two
    obtain ⟨m, hm⟩ := hpow x
    obtain ⟨n, hn⟩ := hpow y
    have hx : s ^ (m + n) * x ∈ R := pow_add_mul_mem hs hm n
    have hy : s ^ (m + n) * y ∈ R := add_comm n m ▸ pow_add_mul_mem hs hn m
    have hxy : s ^ (m + n) * (x + y) ∈ R := mul_add (s ^ (m + n)) x y ▸ R.add_mem hx hy
    have hsplit : (⟨s ^ (m + n) * (x + y), hxy⟩ : R) =
        ⟨s ^ (m + n) * x, hx⟩ + ⟨s ^ (m + n) * y, hy⟩ :=
      Subtype.ext (by push_cast; ring)
    rw [extend_aux w hs hw _ hxy, extend_aux w hs hw _ hx, extend_aux w hs hw _ hy, hsplit,
      max_mul_mul_right]
    exact mul_le_mul_left (w.map_add _ _) _

/-- The value of `extendOfPowMulMem` at the chosen exponent. -/
private theorem extendOfPowMulMem_apply_choose (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : A) :
    w.extendOfPowMulMem hs hpow hw a =
      w ⟨s ^ (hpow a).choose * a, (hpow a).choose_spec⟩ * (w ⟨s, hs⟩)⁻¹ ^ (hpow a).choose :=
  rfl

/-- **The defining formula**, at every exponent that carries `a` into the subring. -/
theorem extendOfPowMulMem_apply (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : A) {n : ℕ}
    (hn : s ^ n * a ∈ R) :
    w.extendOfPowMulMem hs hpow hw a = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n := by
  rw [extendOfPowMulMem_apply_choose, extend_aux w hs hw _ hn]

/-- **The extension restricts to `w`.** -/
@[simp]
theorem extendOfPowMulMem_coe (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : R) :
    w.extendOfPowMulMem hs hpow hw (a : A) = w a := by
  rw [extendOfPowMulMem_apply w hs hpow hw (a : A) (n := 0) (by simp)]
  simp

/-- **The extension is the only one**: a valuation of `A` restricting to `w` on `R` is
`extendOfPowMulMem`. In particular the extension is canonical. -/
theorem eq_extendOfPowMulMem (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (v : Valuation A Γ₀)
    (hv : ∀ a : R, v (a : A) = w a) : v = w.extendOfPowMulMem hs hpow hw := by
  ext a
  obtain ⟨n, hn⟩ := hpow a
  have hval : w ⟨s ^ n * a, hn⟩ = w ⟨s, hs⟩ ^ n * v a := by
    rw [← hv ⟨s ^ n * a, hn⟩, ← hv ⟨s, hs⟩, ← map_pow, ← map_mul]
  rw [extendOfPowMulMem_apply w hs hpow hw a hn, hval, mul_right_comm, ← mul_pow,
    mul_inv_cancel₀ hw, one_pow, one_mul]

/-- **The extension does not depend on `s`**: two elements of `R` whose powers carry `A` into `R`
and at which `w` is nonzero give the same extension. -/
theorem extendOfPowMulMem_congr (w : Valuation R Γ₀) {s t : A} (hs : s ∈ R)
    (hpows : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hws : w ⟨s, hs⟩ ≠ 0) (ht : t ∈ R)
    (hpowt : ∀ a : A, ∃ n : ℕ, t ^ n * a ∈ R) (hwt : w ⟨t, ht⟩ ≠ 0) :
    w.extendOfPowMulMem hs hpows hws = w.extendOfPowMulMem ht hpowt hwt :=
  eq_extendOfPowMulMem w ht hpowt hwt _ (extendOfPowMulMem_coe w hs hpows hws)

end Valuation
