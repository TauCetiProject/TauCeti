/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.RamificationComparison
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.ValuationSubring

/-!
# Finite places of `F^alg` and primes of the algebraic integers

Let `F` be a number field, `F^alg = AlgebraicClosure F`, `G_F` its absolute Galois group and `O`
the integral closure of `𝓞 F` in `F^alg`. A finite place `w` of `F^alg` (a nonarchimedean
`ℚ`-normalised absolute value, `AbsoluteValue.Place`) is at most `1` on `O`, and the `b ∈ O` with
`w b < 1` form a prime `Q` of `O`. This file identifies the decomposition and inertia groups of
`w`, defined through absolute values in `TauCeti/Analysis/AbsoluteValue/Inertia.lean`, with Tau
Ceti's prime-ideal vocabulary at `Q`:

* `MulAction.stabilizer G_F w` is `TauCeti.GaloisRep.decompositionGroup F Q`;
* `AbsoluteValue.inertia G_F w` is `TauCeti.GaloisRep.inertiaGroup F Q`.

The prime `Q` enters through the hypothesis `∀ b : O, b ∈ Q ↔ w b < 1`, rather than as a function
of `w`. The proofs combine the comparisons of
`TauCeti/Analysis/AbsoluteValue/RamificationComparison.lean` with the fact that `O` is a Prüfer
domain whose localizations are the valuation subrings of `F^alg`
(`TauCeti/NumberTheory/NumberField/AbsoluteGaloisGroup/ValuationSubring.lean`).

The groups are stated for `F^alg ≃ₐ[F] F^alg`, of which `Field.absoluteGaloisGroup F` is a
definitional copy, as in `TauCeti.GaloisRep.decompositionGroup_eq_decompositionSubgroup`.

## Main results

* `TauCeti.GaloisRep.stabilizer_place_eq_decompositionGroup`,
  `TauCeti.GaloisRep.inertia_place_eq_inertiaGroup`: decomposition and inertia groups.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. I, §9 and Ch. II, §9.
-/

public section

open NumberField AbsoluteValue

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F] [NumberField F] (w : Place (AlgebraicClosure F))
  (hw : IsNonarchimedean w.val) {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))}

include hw

/-- The valuation subring of a finite place `w` of `F^alg` is centred at the prime `Q` of `O`
consisting of the `b` with `w b < 1`. -/
private theorem isCenteredAt_valuationSubring_place
    (hQ : ∀ b : integralClosure (𝓞 F) (AlgebraicClosure F), b ∈ Q ↔ w b < 1) :
    (w.val.valuationSubring hw).IsCenteredAt Q where
  algebraMap_mem b := algebraMap_mem_valuationSubring F (w.val.valuationSubring hw) b
  algebraMap_mem_nonunits_iff b := by rw [mem_nonunits_valuationSubring_iff, hQ]; rfl

/-- **Decomposition groups.** The stabiliser in `G_F` of a finite place `w` of `F^alg` is the
decomposition group `D_Q` of the prime `Q = {b ∈ O | w b < 1}`. -/
theorem stabilizer_place_eq_decompositionGroup
    (hQ : ∀ b : integralClosure (𝓞 F) (AlgebraicClosure F), b ∈ Q ↔ w b < 1) :
    MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) w =
      decompositionGroup F Q :=
  have h := isCenteredAt_valuationSubring_place w hw hQ
  have := h.isPrime
  Place.stabilizer_eq_stabilizer_of_isCenteredAt w hw h

/-- **Inertia groups.** The inertia group in `G_F` of a finite place `w` of `F^alg` is the inertia
group `I_Q` of the prime `Q = {b ∈ O | w b < 1}`. -/
theorem inertia_place_eq_inertiaGroup
    (hQ : ∀ b : integralClosure (𝓞 F) (AlgebraicClosure F), b ∈ Q ↔ w b < 1) :
    w.val.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) = inertiaGroup F Q :=
  have h := isCenteredAt_valuationSubring_place w hw hQ
  have := h.isPrime
  Place.inertia_eq_inertia_of_isCenteredAt w hw h

end TauCeti.GaloisRep
