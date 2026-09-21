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
`B` lying over the height-one prime `v` of `R`, with `w` of finite residue field. The completions
`K_v` and `L_w` are then nonarchimedean local fields for the canonical algebra structure of the
`AdicCompletionExtension` scope, and the degree of the second over the first is

`[L_w : K_v] = e(w ∣ v) · f(w ∣ v)`,

the product of the ramification index and the inertia degree of `w` over `R`. Both factors on the
right are global invariants of the extension `R ⊆ B`, so this formula turns a sum of local degrees
over the primes `w` above `v` into `∑_{w ∣ v} e(w ∣ v) · f(w ∣ v)`, which the fundamental identity
of Dedekind domains evaluates as the global degree `[L : K]`.

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
  [Finite (B ⧸ w.asIdeal)]

/-- **The local degree of a completion.** For `w` a height-one prime of `B` over the height-one
prime `v` of `R`, with finite residue field, the degree of `L_w` over `K_v` for the canonical
algebra structure of `adicCompletionExtension` is the product of the ramification index and the
inertia degree of `w` over `R`. -/
@[simp]
theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  -- the residue field of `v` embeds in the residue field of `w`, so it is finite too
  have : Finite (R ⧸ v.asIdeal) :=
    .of_injective _ (FaithfulSMul.algebraMap_injective (R ⧸ v.asIdeal) (B ⧸ w.asIdeal))
  rw [← TauCeti.ramificationIndex_mul_inertiaDegree (v.adicCompletion K) (w.adicCompletion L),
    ramificationIndex_adicCompletion, TauCeti.inertiaDegree_def,
    finrank_residueField_adicCompletion]

end IsDedekindDomain.HeightOneSpectrum
