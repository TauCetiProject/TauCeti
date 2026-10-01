/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Derivations preserve nilpotence in characteristic zero

Let `D` be a derivation of a commutative ring `A`, and let `p` be a prime ideal of `A`
containing no positive integer, so that `A ⧸ p` has characteristic zero. Then `D` carries every
nilpotent element of `A` into `p`. Over a `ℚ`-algebra every prime ideal qualifies, so a
derivation of a `ℚ`-algebra carries nilpotent elements to nilpotent elements: the nilradical is
a differential ideal.

The characteristic hypothesis cannot be dropped. Over `𝔽ₚ[t] ⧸ (tᵖ)` the derivation `d/dt`
sends the nilpotent class of `t` to `1`.

These facts are the commutative-algebra input to Cartier's theorem that affine group schemes of
finite type over a field of characteristic zero are smooth: a tangent vector at the identity
extends to a derivation of the whole coordinate ring, and the result here shows that it must
vanish on nilpotent functions.

## Main results

* `Derivation.apply_mem_of_isNilpotent`: a derivation sends nilpotent elements into every prime
  ideal of residual characteristic zero.
* `Derivation.isNilpotent_apply`: a derivation of a `ℚ`-algebra sends nilpotent elements to
  nilpotent elements.

## References

* I. Kaplansky, *An Introduction to Differential Algebra* (1957), Chapter I: the radical of a
  differential ideal in a ring containing `ℚ` is differential.
-/

public section

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- **A derivation sends nilpotent elements into every prime ideal of residual characteristic
zero.** The hypothesis `hchar` says that `p` contains no positive integer. -/
theorem apply_mem_of_isNilpotent (D : Derivation R A A) {p : Ideal A} [hp : p.IsPrime]
    (hchar : ∀ n : ℕ, (n : A) ∈ p → n = 0) {x : A} (hx : IsNilpotent x) : D x ∈ p := by
  by_contra hDx
  obtain ⟨m, hm⟩ := hx
  -- Differentiating an annihilation relation and multiplying by `s` lowers the exponent;
  -- if `D x ∉ p`, the new annihilator `(n + 1) s² D(x)` still lies outside `p`.
  have step : ∀ n : ℕ, (∃ s ∉ p, s * x ^ (n + 1) = 0) → ∃ s ∉ p, s * x ^ n = 0 := by
    rintro n ⟨s, hs, hsx⟩
    have hn : ((n + 1 : ℕ) : A) ∉ p := fun h ↦ n.succ_ne_zero (hchar _ h)
    refine ⟨((n + 1 : ℕ) : A) * (s * s * D x),
      hp.mul_notMem hn (hp.mul_notMem (hp.mul_notMem hs hs) hDx), ?_⟩
    have hD := congrArg D hsx
    rw [D.leibniz, D.leibniz_pow, map_zero, Nat.add_sub_cancel] at hD
    simp only [smul_eq_mul, nsmul_eq_mul] at hD
    linear_combination s * hD - D s * hsx
  -- Descend from a vanishing power to `x ^ 0`, forcing an element outside `p` to be zero.
  have key : ∀ j ≤ m, ∃ s ∉ p, s * x ^ (m - j) = 0 := by
    intro j hj
    induction j with
    | zero => exact ⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, by rw [Nat.sub_zero, hm, mul_zero]⟩
    | succ j ih =>
      apply step
      have hsub : m - (j + 1) + 1 = m - j := by omega
      rw [hsub]
      exact ih (by omega)
  obtain ⟨s, hs, hsx⟩ := key m le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hsx
  exact hs (hsx ▸ p.zero_mem)

/-- **In a `ℚ`-algebra, a derivation sends nilpotent elements to nilpotent elements**: the
nilradical is a differential ideal. -/
theorem isNilpotent_apply [Algebra ℚ A] (D : Derivation R A A) {x : A} (hx : IsNilpotent x) :
    IsNilpotent (D x) := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  intro p (hp : Ideal.IsPrime p)
  refine D.apply_mem_of_isNilpotent (fun n hn ↦ ?_) hx
  by_contra hn0
  have hunit : IsUnit (n : A) := by
    simpa using (IsUnit.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn0)).map (algebraMap ℚ A)
  exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hn hunit)

end Derivation
