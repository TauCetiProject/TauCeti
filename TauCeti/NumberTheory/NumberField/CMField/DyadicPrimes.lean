/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.ResidueField
import TauCeti.Data.ZMod.DyadicPower
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Rational primes below conjugation-fixed primes of CM fields

If a prime at odd residue characteristic is fixed by complex conjugation, then the
rational prime below it is `-1` modulo the order of any dyadic root of unity in the
field. The Frobenius action first gives the congruence for the residue cardinality in
the maximal real subfield; the dyadic modulus allows us to descend from this power of
the rational prime to the prime itself.

This congruence occurs as `New.Parameters.natCast_eq_neg_one_of_star_eq` in
`grh/src/New/Derivatives/Field/PrimeDecomposition.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace NumberField.IsCMField

/-- Let `w` be a conjugation-fixed prime above an odd rational prime `p` in a CM field.
If the field contains a primitive `2 ^ (s + 1)`-th root of unity, then `p` is `-1`
modulo `2 ^ (s + 1)`. No unramifiedness in the ambient field is required. -/
theorem natCast_eq_neg_one_of_conj_fixed {K : Type*} [Field K] [NumberField K] [IsCMField K]
    {p s : ℕ} (w : Ideal (𝓞 K)) [w.IsMaximal] [w.LiesOver (Ideal.span {(p : ℤ)})]
    (hw : w.map (ringOfIntegersComplexConj K) = w) (h₂ : (2 : 𝓞 K) ∉ w)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ (2 ^ (s + 1))) :
    (p : ZMod (2 ^ (s + 1))) = -1 := by
  have hn : ((2 ^ (s + 1) : ℕ) : 𝓞 K) ∉ w := by
    push_cast
    exact fun h ↦ h₂ (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h)
  have h := natCast_card_quotient_under_eq_neg_one w hw hζ hn
  let v := w.under (𝓞 (maximalRealSubfield K))
  have : v.IsPrime := inferInstanceAs (Ideal.IsPrime (w.under (𝓞 (maximalRealSubfield K))))
  have : v.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨(w.over_def (Ideal.span {(p : ℤ)})).trans (Ideal.under_under w).symm⟩
  have hv : p ^ v.inertiaDeg ℤ = Nat.card (𝓞 (maximalRealSubfield K) ⧸ v) :=
    (Ideal.pow_inertiaDeg p v).trans (Ideal.absNorm_apply v)
  rw [← hv, Nat.cast_pow] at h
  exact ZMod.eq_neg_one_of_pow_eq_neg_one_two_pow (Ideal.inertiaDeg_pos v ℤ).ne' h

end NumberField.IsCMField
