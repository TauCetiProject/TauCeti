/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.RamificationInertia.Splitting

/-!
# Complete splitting in subfields of cyclotomic fields

A rational prime congruent to `1` modulo the cyclotomic level splits completely in
any field embedded in the cyclotomic field. This combines the cyclotomic splitting
law with descent of complete splitting along an extension, without a Galois
hypothesis on the subfield.
-/

public section

open NumberField Ideal Module

namespace AlgHom

/-- A rational prime congruent to `1` modulo `n` splits completely in every subfield
of an `n`-th cyclotomic field over `ℚ`. The subfield can be given by any `ℚ`-embedding. -/
theorem ncard_primesOver_eq_finrank_of_modEq_one_cyclotomic
    {E F : Type*} [Field E] [Field F] [CharZero E] [CharZero F] {n p : ℕ}
    [IsCyclotomicExtension {n} ℚ F] [Fact p.Prime] (e : E →ₐ[ℚ] F) (hp : p ≡ 1 [MOD n]) :
    ((span {(p : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℚ E := by
  have hpos : 0 < n := by
    by_contra! hn
    have hp₁ : p = 1 := by simpa [Nat.eq_zero_of_le_zero hn, Nat.ModEq] using hp
    exact (Fact.out : p.Prime).ne_one hp₁
  have : NeZero n := ⟨hpos.ne'⟩
  have : NumberField F := IsCyclotomicExtension.numberField {n} ℚ F
  have htop : ((span {(p : ℤ)}).primesOver (𝓞 F)).ncard = n.totient := by
    by_cases hn : n % 4 = 2
    · have hdiv : n / 2 ∣ n := ⟨2, by omega⟩
      apply (TauCeti.NumberField.ncard_primesOver_eq_totient_iff_of_mod_four_eq_two (K := F) hn).2
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p 1 (n / 2)).2 (hp.of_dvd hdiv)
    · exact (TauCeti.NumberField.ncard_primesOver_eq_totient_iff (K := F) hn).2
        (by simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p 1 n).2 hp)
  let : Algebra E F := e.toRingHom.toAlgebra
  have : IsScalarTower ℚ E F := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  have : NumberField E := NumberField.of_tower ℚ F E
  rw [← RingOfIntegers.rank]
  apply Ideal.ncard_primesOver_eq_finrank_tower_bot (T := 𝓞 F)
  rw [RingOfIntegers.rank,
    IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hpos)]
  exact htop

end AlgHom
