/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic
public import TauCeti.RingTheory.Ideal.Norm.RelNorm

/-!
# Coefficients of the relative discriminant

The relative discriminant `relDiscr A B` is the relative norm of the different ideal, so its
coefficient at a nonzero maximal ideal `p` of `A` is determined by the coefficients of the
different at the primes of `B` above `p`, each weighted by a residue degree:

`mult_p(relDiscr A B) = Σ_{P ∣ p} f(P / p) · mult_P(𝔇(B / A))`.

This is the coefficient formula for `relDiscr` specifically: it is `TauCeti.multiplicity_relNorm`
applied to the different, through `relDiscr_def`. The hypotheses are that `p` is a nonzero maximal
ideal of `A` and that the different is nonzero, the latter holding whenever the extension is
separable.

The coefficient `mult_p(I)` is Mathlib's `multiplicity`, the normalization in which
`Ideal.finprod_heightOneSpectrum_pow_multiplicity` recovers an ideal from its coefficients.

## Main results

* `TauCeti.multiplicity_relDiscr`: the coefficient of the relative discriminant at `p` is the
  weighted sum of the coefficients of the different at the primes above `p`.

## References

* [J. Neukirch, *Algebraic number theory*][neukirch1999], Chapter III, §2.
-/

public section

open Ideal

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)]

variable (B) in
/-- **The coefficients of the relative discriminant.** At a nonzero maximal ideal `p` of `A`,
the coefficient of `relDiscr A B` is the sum of the coefficients of the different at the primes
above `p`, each weighted by its residue degree. -/
theorem multiplicity_relDiscr (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (hd : differentIdeal A B ≠ ⊥) :
    multiplicity p (relDiscr A B) =
      ∑ P ∈ (p.primesOver B).toFinset,
        P.inertiaDeg A * multiplicity P (differentIdeal A B) := by
  rw [relDiscr_def]
  exact multiplicity_relNorm B p hp hd

end TauCeti

end
