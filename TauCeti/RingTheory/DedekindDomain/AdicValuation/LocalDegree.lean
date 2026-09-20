/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.InertiaDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# The local degree of a completion is `e · f`

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime of
`B` lying over the height-one prime `v` of `R`, both with finite residue fields. The completions
`K_v` and `L_w` are nonarchimedean local fields and the canonical map `K_v → L_w` makes `L_w` a
valuative extension of `K_v`, so the fundamental identity `e · f = [L_w : K_v]` of
`TauCeti.ramificationIndex_mul_inertiaDegree` applies to it. Combining it with the two comparisons
`IsDedekindDomain.HeightOneSpectrum.ramificationIndex_adicCompletion` and
`IsDedekindDomain.HeightOneSpectrum.finrank_residueField_adicCompletion` expresses the local
degree through the two global invariants of `w` over `v`:

`[L_w : K_v] = e(w ∣ v) · f(w ∣ v)`.

This is the form in which the local degrees are summed over the primes above `v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion`: the degree of `L_w` over `K_v` is
  `w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §6.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)]

/-- **The local degree of a completion.** For `w` a height-one prime of `B` over the height-one
prime `v` of `R`, with finite residue fields, the degree of `L_w` over `K_v` for the canonical
algebra structure of `adicCompletionExtension` is the product of the ramification index and the
inertia degree of `w` over `R`. -/
theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  rw [← TauCeti.ramificationIndex_mul_inertiaDegree (v.adicCompletion K) (w.adicCompletion L),
    ramificationIndex_adicCompletion, TauCeti.inertiaDegree_def,
    finrank_residueField_adicCompletion]

end IsDedekindDomain.HeightOneSpectrum
