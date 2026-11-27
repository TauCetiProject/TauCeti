/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# A norm bound for a nonzero congruence

Let `I` be an ideal of the integers of a number field `K`, contracting to `(ℓ)` in `ℤ`.
If a nonzero algebraic integer `x` lies in `I` and every complex conjugate of `x` has
absolute value at most `B`, then

```text
ℓ ≤ |Norm(K/ℚ)(x)| ≤ B ^ [K : ℚ].
```

This is the norm argument that turns a congruence between Hecke eigenvalues and rational
integers into a bound on the residue characteristic; see Bennett–Siksek, proof of Lemma 2.2.
The upper estimate reuses `NumberField.abs_norm_le_pow`. For the lower estimate, the
absolute ideal norm belongs to `I` and divides the integral norm of `x`.

The result applies to any ideal with the stated contraction, including a prime above `ℓ`.
It requires neither a Galois hypothesis on `K` nor a separate sign assumption on `B`.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short
  character sums*, Annals of Mathematics 191 (2020), 355–392, §2, proof of Lemma 2.2, p. 359.
-/

public section

open scoped NumberField

namespace Ideal

/-- A nonzero algebraic integer in an ideal above `(ℓ)` has norm at least `ℓ` in absolute
value. Bounds on all its complex conjugates give the matching degree-power upper bound.
Primality of the ideal and of `ℓ` is unnecessary: the contraction identity suffices. -/
theorem norm_bound {K : Type*} [Field K] [NumberField K] (I : Ideal (𝓞 K)) {ℓ : ℕ}
    (hI : I.comap (algebraMap ℤ (𝓞 K)) = span {(ℓ : ℤ)}) {x : 𝓞 K}
    (hx : x ∈ I) (hx0 : x ≠ 0) {B : ℝ}
    (hB : ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ B) :
    (ℓ : ℝ) ≤ |(Algebra.norm ℚ (x : K) : ℝ)| ∧
      |(Algebra.norm ℚ (x : K) : ℝ)| ≤ B ^ Module.finrank ℚ K := by
  have hdvd : (ℓ : ℤ) ∣ (I.absNorm : ℤ) := by
    rw [← mem_span_singleton, ← hI, mem_comap]
    simpa using I.absNorm_mem
  have hnorm : (ℓ : ℤ) ∣ Algebra.norm ℤ x :=
    hdvd.trans (absNorm_dvd_norm_of_mem hx)
  refine ⟨?_, NumberField.abs_norm_le_pow (x : K) hB⟩
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs]
  exact_mod_cast Int.le_abs_of_dvd (Algebra.norm_ne_zero_iff.mpr hx0) hnorm

end Ideal
