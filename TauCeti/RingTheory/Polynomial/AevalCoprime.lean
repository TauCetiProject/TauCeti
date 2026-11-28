/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Coprime factor cancellation for polynomial evaluation

If a polynomial `P` satisfies `(P * a)(x) = 0` and `(P * b)(x) = 0` with `a` and `b` coprime
(`IsCoprime a b`), then `P(x) = 0`, via Bézout's identity `u * a + v * b = 1`. More generally,
if `(P * f i)(x) = 0` for a family `f : ι → R[X]` whose ideal span is `⊤`, then `P(x) = 0`.

## Main results

* `TauCeti.aeval_eq_zero_of_mul_of_isCoprime`: Bézout cancellation of coprime factors for
  `Polynomial.aeval` in any `R`-algebra `A`.
* `TauCeti.eval₂_eq_zero_of_mul_of_isCoprime`: Bézout cancellation of coprime factors for
  `Polynomial.eval₂` along any ring homomorphism `φ : R →+* S` into a commutative ring `S`.
* `TauCeti.aeval_eq_zero_of_forall_mul_eq_zero_of_span_eq_top`: cancellation for any family of
  factors generating the unit ideal `⊤` in `R[X]`.

## References

* Provenance: adapted from `New.GaloisRep.PolyKillsAt.of_mul_of_isCoprime` in
  `grh/src/Lib/GaloisRep/Main/AllRanks.lean` of `grh-lean`
  (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R]

/-- If `aeval x (P * a) = 0`, `aeval x (P * b) = 0`, and `IsCoprime a b`, then `aeval x P = 0`. -/
theorem aeval_eq_zero_of_mul_of_isCoprime {A : Type*} [Ring A] [Algebra R A]
    {x : A} {P a b : R[X]} (ha : aeval x (P * a) = 0) (hb : aeval x (P * b) = 0)
    (hab : IsCoprime a b) : aeval x P = 0 := by
  obtain ⟨u, v, huv⟩ := hab
  have hP : P = P * a * u + P * b * v := by
    calc P = P * (u * a + v * b) := by rw [huv, mul_one]
      _ = P * a * u + P * b * v := by ring
  rw [hP, map_add, map_mul, ha, zero_mul, zero_add, map_mul, hb, zero_mul]

/-- If `eval₂ φ x (P * a) = 0`, `eval₂ φ x (P * b) = 0`, and `IsCoprime a b`, then
`eval₂ φ x P = 0`. -/
theorem eval₂_eq_zero_of_mul_of_isCoprime {S : Type*} [CommRing S] (φ : R →+* S)
    {x : S} {P a b : R[X]} (ha : eval₂ φ x (P * a) = 0) (hb : eval₂ φ x (P * b) = 0)
    (hab : IsCoprime a b) : eval₂ φ x P = 0 := by
  obtain ⟨u, v, huv⟩ := hab
  have hP : P = P * a * u + P * b * v := by
    calc P = P * (u * a + v * b) := by rw [huv, mul_one]
      _ = P * a * u + P * b * v := by ring
  rw [hP, eval₂_add, eval₂_mul, ha, zero_mul, zero_add, eval₂_mul, hb, zero_mul]

/-- If `aeval x (P * f i) = 0` for every `i : ι` and the family `f` generates the unit ideal
`⊤` in `R[X]`, then `aeval x P = 0`. -/
theorem aeval_eq_zero_of_forall_mul_eq_zero_of_span_eq_top {A ι : Type*} [Ring A] [Algebra R A]
    {x : A} {P : R[X]} {f : ι → R[X]} (hf : ∀ i : ι, aeval x (P * f i) = 0)
    (h_span : Ideal.span (Set.range f) = ⊤) : aeval x P = 0 := by
  have h1 : (1 : R[X]) ∈ Ideal.span (Set.range f) := h_span.symm ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  have hc' : (c.sum fun i g ↦ g * f i) = 1 := by simpa [smul_eq_mul] using hc
  have hP : P = c.sum fun i g ↦ P * f i * g := by
    calc P = P * (c.sum fun i g ↦ g * f i) := by rw [hc', mul_one]
      _ = c.sum fun i g ↦ P * (g * f i) := by simp [Finsupp.sum, Finset.mul_sum]
      _ = c.sum fun i g ↦ P * f i * g := Finsupp.sum_congr fun i _ ↦ by ring
  rw [hP, Finsupp.sum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [map_mul, hf i, zero_mul]

end TauCeti
