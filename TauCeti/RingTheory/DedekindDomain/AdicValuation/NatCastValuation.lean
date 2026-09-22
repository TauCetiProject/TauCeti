/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Natural-number valuations in adic completions

Let `v` be a height-one prime of a Dedekind domain `R`, with finite residue field and fraction
field `K`. For a natural number whose image in the completion `K_v` is nonzero, its normalized
additive valuation there is the exponent of `v` in the principal ideal that the number generates
in `R`.

This identifies the local-field normalization, in which a uniformizer has valuation one, with
the global ideal-theoretic normalization by prime multiplicity. It is the bridge needed when a
local ramification bound contains the valuation of a natural number and is transported back to a
global prime.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.natCastValuation_completion_eq_multiplicity_span`:
  for `v` with finite residue field, if the image of `n` in `K_v` is nonzero, its normalized
  valuation there is the multiplicity of `v` in `(n)`.
-/

public section
noncomputable section

open scoped WithZero algebraMap

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- If a height-one prime has finite residue field and a natural number has nonzero image in its
adic completion, the normalized valuation there is its multiplicity in the corresponding global
principal ideal. -/
@[simp] theorem natCastValuation_completion_eq_multiplicity_span
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] (n : ℕ)
    (hn : (n : v.adicCompletion K) ≠ 0) :
    TauCeti.natCastValuation (v.adicCompletion K) n hn =
      multiplicity v.asIdeal (Ideal.span {(n : R)}) := by
  have hnR : (n : R) ≠ 0 := by
    intro h
    apply hn
    rw [← map_natCast (algebraMap R (v.adicCompletion K)) n, h, map_zero]
  have h := v.normalizedValuationWithZero_adicCompletion (K := K)
    (n : v.adicCompletion K)
  rw [TauCeti.normalizedValuationWithZero_natCast (v.adicCompletion K) n hn,
    ← map_natCast (algebraMap R (v.adicCompletion K)) n, valuedAdicCompletion_eq_valuation,
    valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity hnR, ← WithZero.exp_neg, neg_neg] at h
  exact_mod_cast WithZero.exp_inj.mp h

end IsDedekindDomain.HeightOneSpectrum

end

end
