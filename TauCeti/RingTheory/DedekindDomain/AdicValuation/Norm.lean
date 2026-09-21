/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree

/-!
# Normalized absolute values under extension of adic completions

Let `R ⊆ B` be infinite Dedekind domains with finite quotients and fraction fields `K ⊆ L`.
For height-one primes `w ∣ v`, the canonical map `K_v → L_w` raises the residue-cardinality
normalized absolute value to the local degree `[L_w : K_v]`. In particular, this map need
not preserve the norm.

The local degree is the product of the ramification index and inertia degree, as in
`IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion`; the residue cardinalities are
related by
`IsDedekindDomain.HeightOneSpectrum.natCard_residueField_adicCompletion_eq_pow_inertiaDeg`.

## Main results

* `TauCeti.norm_adicCompletionExtension`: the normalized
  absolute value under the canonical extension of completions.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdicCompletionExtension

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Ring.HasFiniteQuotients R] [Infinite R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Ring.HasFiniteQuotients B] [Infinite B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

/-- The normalized absolute value of the image in `L_w` is the normalized absolute value in
`K_v` raised to the local degree `[L_w : K_v]`. No Galois hypothesis is needed. -/
@[simp]
theorem norm_adicCompletionExtension (v : HeightOneSpectrum R) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion K) :
    ‖v.adicCompletionExtension K L w x‖ =
      ‖x‖ ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : Finite (B ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  by_cases hx : x = 0
  · have := finite_of_valuativeExtension (v.adicCompletion K) (w.adicCompletion L)
    simp only [hx, map_zero, norm_zero,
      zero_pow (Module.finrank_pos (R := v.adicCompletion K) (M := w.adicCompletion L)).ne']
  have hcard : w.asIdeal.absNorm = v.asIdeal.absNorm ^ w.asIdeal.inertiaDeg R := by
    simpa only [natCard_residueField_adicCompletion_eq_absNorm] using
      natCard_residueField_adicCompletion_eq_pow_inertiaDeg (K := K) (L := L) v w
  rw [finrank_adicCompletion, FinitePlace.norm_def, FinitePlace.norm_def,
    valued_adicCompletionExtension, map_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa using hx),
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa using hx)]
  simp only [hcard, Nat.cast_pow, NNReal.coe_zpow,
    ← zpow_natCast, ← zpow_mul, Nat.cast_mul]
  congr 1
  ring

end TauCeti
