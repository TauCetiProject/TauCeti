/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Unramified.AdjoinRoot
public import TauCeti.RingTheory.Localization.Away.Units

/-!
# Invertibility of the exponent of an unramified root extraction

For a positive exponent `n`, formal unramifiedness of `R[X]/(X^n - a)` forces `n` to be a unit
of `R`: the derivative is `n X^(n-1)`, and the finite free positive-rank algebra reflects units.
The radicand need not be invertible, and `R` need not be a domain.

If this condition is established after inverting a prime element `f`, and `n` does not vanish
along `f`, it descends to `R`. This is the exponent-invertibility step in the local structure
of tame covers along a regular divisor; see the proof of Stacks Project, Lemma 58.31.5
([Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)).
-/

public section

open Polynomial AdjoinRoot

namespace TauCeti

/-- Formal unramifiedness of a positive-degree root extraction forces its exponent to be
invertible in the base ring. No invertibility assumption on the radicand is needed. -/
theorem isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C {R : Type*} [CommRing R]
    (a : R) {n : ℕ} (hn : n ≠ 0)
    [Algebra.FormallyUnramified R (AdjoinRoot (X ^ n - C a))] : IsUnit (n : R) := by
  nontriviality R
  have : IsLocalHom (algebraMap R (AdjoinRoot (X ^ n - C a))) :=
    AdjoinRoot.isLocalHom_of_monic_of_degree_pos (monic_X_pow_sub_C a hn)
      (by simpa [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)] using Nat.pos_of_ne_zero hn)
  have hd := (X ^ n - C a).isUnit_mk_derivative_of_formallyUnramified_adjoinRoot
  simp only [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, mk_C] at hd
  exact (isUnit_map_iff (algebraMap R (AdjoinRoot (X ^ n - C a))) _).mp
    (isUnit_of_mul_isUnit_left hd)

end TauCeti

namespace Prime

/-- An exponent of an unramified root extraction over `R[1/f]` descends to a unit of `R`
if it is not divisible by the prime element `f`. In particular this applies to an étale root
algebra and an exponent nonzero in the residue field at `(f)`. -/
theorem isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C_away {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] {f : R}
    [IsLocalization.Away f S] (hf : Prime f) (a : S) {n : ℕ} (hfn : ¬f ∣ (n : R))
    [Algebra.FormallyUnramified S (AdjoinRoot (X ^ n - C a))] : IsUnit (n : R) := by
  have hn : n ≠ 0 := by rintro rfl; exact hfn (by simp)
  apply hf.isUnit_of_isUnit_away_of_not_dvd (S := S) _ hfn
  simpa using TauCeti.isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C a hn

end Prime
