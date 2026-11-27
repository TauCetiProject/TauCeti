/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.SubfieldSplitting

/-!
# Complete splitting of the theta-lift level primes

The level primes are chosen in the class `1` modulo `q₂(s)²`. In fact the congruence
modulo `q₂(s)` already forces complete splitting in any field embedded in the
cyclotomic field of order `q₁(s) d`, because `q₁(s) d` divides `q₂(s)`.

The splitting condition is the input for the residue degree and place count in
`New.Parameters.q_eq_of_modEq_one` of `lsernau/grh-lean` (`72fead1`,
`grh/src/New/Derivatives/Field/WeilData.lean`).
-/

public section

open NumberField Ideal Module

namespace TauCeti.OneSidedBound.Parameters

/-- A level prime splits completely in the host field. Only congruence modulo `q₂(s)`
is needed, rather than modulo its square. The host is supplied by its rational embedding
into the cyclotomic field of order `q₁(s) d`. -/
theorem ncard_primesOver_eq_finrank_of_level_modEq_one (P : Parameters) (s : ℕ)
    {E F : Type*} [Field E] [Field F] [CharZero E] [CharZero F]
    [IsCyclotomicExtension {P.q₁ s * P.d} ℚ F] (e : E →ₐ[ℚ] F)
    {p : ℕ} [Fact p.Prime] (hp : p ≡ 1 [MOD P.q₂ s]) :
    ((span {(p : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℚ E :=
  e.ncard_primesOver_eq_finrank_of_modEq_one_cyclotomic (hp.of_dvd (P.q₁_mul_d_dvd_q₂ s))

end TauCeti.OneSidedBound.Parameters
