/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Minimal primes over a differential ideal

Let `D` be a derivation of a commutative ring `A` and `I` an ideal with `D I ⊆ I`. In
characteristic zero the minimal primes over `I` and the radical of `I` are again stable under `D`:
if a prime `P` is minimal over `I` and contains no positive integer, then `D P ⊆ P`; and if `A` is
a `ℚ`-algebra, then `D` maps the radical of `I` into itself. No Noetherian hypothesis is needed.

The proof descends along powers. If `s * x ^ (n + 1) ∈ I` with `s ∉ P`, then differentiating and
multiplying by `s` shows `(n + 1) * s ^ 2 * D x * x ^ n ∈ I`, so if `D x ∉ P` the multiplier stays
outside `P` while the exponent drops; at exponent zero this contradicts `I ≤ P`. A prime minimal
over `I` supplies such a multiplier for each of its elements
(`Ideal.exists_mul_pow_mem_of_mem_minimalPrimes`). The case `I = 0`, `s = 1` is
`Derivation.apply_mem_of_isNilpotent`, which holds over semirings; for a nonzero `I` the descent
subtracts inside `I`, so `A` is a ring here.

The characteristic hypothesis cannot be dropped. In `𝔽ₚ[x]` the ideal `(xᵖ)` is stable under
`d/dx`, while its minimal prime `(x)` is not; in `ℤ[x]` the ideal `(2, x²)` is stable under
`d/dx`, while its minimal prime `(2, x)` is not.

Stability of minimal primes over a stable ideal enters the differential smoothness criterion in
characteristic zero: applied to the annihilator of a module of differentials stable under a family
of Lie derivatives, it produces a prime stable under coordinate derivations.

## Main results

* `Derivation.apply_mem_of_mul_pow_mem`: if `I ≤ p` with `p` prime of residual characteristic
  zero, `D I ⊆ I` and `s * x ^ n ∈ I` for some `s ∉ p`, then `D x ∈ p`.
* `Derivation.apply_mem_of_mem_minimalPrimes`: a derivation maps every prime of residual
  characteristic zero that is minimal over a stable ideal into itself.
* `Derivation.apply_mem_radical_of_mem_radical`: in a `ℚ`-algebra, the radical of a stable ideal
  is stable.

## References

* I. Kaplansky, *An Introduction to Differential Algebra* (1957), Chapter I: in a ring containing
  `ℚ`, the radical of a differential ideal is differential and its prime components are
  differential.
* A. Seidenberg, *Differential ideals in rings of finitely generated type*, Amer. J. Math. 89
  (1967): the minimal primes of a differential ideal in a Noetherian `ℚ`-algebra are differential.
-/

public section

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- **A derivation maps `x` into a prime `p` of residual characteristic zero above a stable ideal
whenever some `s ∉ p` carries a power of `x` into that ideal.** Let `D I ⊆ I`, let `p` be a prime
containing `I` and no positive integer, and let `s * x ^ n ∈ I` for some `s ∉ p`. Then
`D x ∈ p`. -/
theorem apply_mem_of_mul_pow_mem (D : Derivation R A A) {I p : Ideal A} [hp : p.IsPrime]
    (hI : ∀ a ∈ I, D a ∈ I) (hIp : I ≤ p) (hchar : ∀ n : ℕ, (n : A) ∈ p → n = 0) {s x : A}
    (hs : s ∉ p) {n : ℕ} (hx : s * x ^ n ∈ I) : D x ∈ p := by
  by_contra hDx
  -- Descend from `s * x ^ n ∈ I` to `t * x ^ 0 ∈ I` with `t ∉ p`, contradicting `I ≤ p`:
  -- differentiating `s * x ^ (n + 1) ∈ I` and multiplying by `s` puts `(n + 1) s² D(x) x ^ n`
  -- in `I`, and `(n + 1) s² D(x)` stays outside `p` as long as `D x ∉ p`.
  suffices ∀ n, ∀ s ∉ p, s * x ^ n ∉ I from this n s hs hx
  intro n
  induction n with
  | zero => simpa using fun s hs h ↦ hs (hIp h)
  | succ n ih =>
    intro s hs hsx
    have hn : ((n + 1 : ℕ) : A) ∉ p := fun h ↦ n.succ_ne_zero (hchar _ h)
    refine ih _ (hp.mul_notMem hn (hp.mul_notMem (hp.mul_notMem hs hs) hDx)) ?_
    have key : ((n + 1 : ℕ) : A) * (s * s * D x) * x ^ n =
        s * D (s * x ^ (n + 1)) - D s * (s * x ^ (n + 1)) := by
      rw [D.leibniz, D.leibniz_pow, Nat.add_sub_cancel]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring
    rw [key]
    exact I.sub_mem (I.mul_mem_left _ (hI _ hsx)) (I.mul_mem_left _ hsx)

/-- **The minimal primes over a stable ideal are stable** (in residual characteristic zero). If
`D I ⊆ I` and `P` is a prime minimal over `I` that contains no positive integer, then
`D P ⊆ P`. In a `ℚ`-algebra every prime satisfies the characteristic hypothesis, since every
positive integer is a unit (`TauCeti.isUnit_natCast_of_ne_zero`). -/
theorem apply_mem_of_mem_minimalPrimes (D : Derivation R A A) {I P : Ideal A}
    (hI : ∀ a ∈ I, D a ∈ I) (hP : P ∈ I.minimalPrimes) (hchar : ∀ n : ℕ, (n : A) ∈ P → n = 0)
    {x : A} (hx : x ∈ P) : D x ∈ P := by
  have := hP.isPrime
  obtain ⟨s, hs, n, hsx⟩ := Ideal.exists_mul_pow_mem_of_mem_minimalPrimes hP hx
  exact D.apply_mem_of_mul_pow_mem hI hP.le hchar hs hsx

/-- **In a `ℚ`-algebra, the radical of a stable ideal is stable**: if `D I ⊆ I`, then `D` maps
the radical of `I` into itself. -/
theorem apply_mem_radical_of_mem_radical [Algebra ℚ A] (D : Derivation R A A) {I : Ideal A}
    (hI : ∀ a ∈ I, D a ∈ I) {x : A} (hx : x ∈ I.radical) : D x ∈ I.radical := by
  rw [← Ideal.sInf_minimalPrimes] at hx ⊢
  refine Submodule.mem_sInf.mpr fun P hP ↦ D.apply_mem_of_mem_minimalPrimes hI hP
    (fun n hn ↦ ?_) (Submodule.mem_sInf.mp hx P hP)
  by_contra hn0
  exact hP.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem P hn (TauCeti.isUnit_natCast_of_ne_zero ℚ hn0))

end Derivation
