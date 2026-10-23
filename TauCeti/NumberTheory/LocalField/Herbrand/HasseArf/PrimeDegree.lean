/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Jump

/-!
# The prime-degree case of Hasse--Arf

For a finite Galois extension of prime degree, every upper ramification break is integral. More
precisely, an upper break is either `-1`, accounting for the jump from the full Galois group to
inertia in the unramified case, or is a natural number.

This is the base case for the prime-order induction in the Hasse--Arf theorem. The proof uses the
integrality of lower breaks and the fact that a subgroup of a group of prime order is either
trivial or the whole group. At a nonnegative lower break `t`, the lower filtration is therefore
constant through `t`, so the inverse Herbrand function fixes `t`.

## Main results

* `TauCeti.LocalFieldsRamification.UpperJump.eq_neg_one_or_exists_eq_natCast_of_finrank_prime`:
  a prime-degree upper break is `-1` or a natural number.
* `TauCeti.LocalFieldsRamification.UpperJump.exists_eq_intCast_of_finrank_prime`: the
  prime-degree case of the Hasse--Arf integrality statement.
* `TauCeti.LocalFieldsRamification.UpperJump.eq_of_finrank_prime`: a prime-degree extension has
  at most one upper break.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §7.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

variable {K L} in
/-- A finite Galois extension of prime degree has at most one upper ramification break. -/
theorem UpperJump.eq_of_finrank_prime {u v : RamificationIndexDomain}
    (hu : UpperJump K L u) (hv : UpperJump K L v)
    (hdegree : (Module.finrank K L).Prime) : u = v := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime :=
    ⟨IsGalois.card_aut_eq_finrank K L ▸ hdegree⟩
  have no_two_jumps : ∀ {a b : RamificationIndexDomain},
      UpperJump K L a → UpperJump K L b → ¬a < b := by
    intro a b ha hb hab
    let w : RamificationIndexDomain :=
      ⟨(b : ℝ) + 1, b.property.trans (by linarith)⟩
    have hbw : b < w := Subtype.mk_lt_mk.2 (by linarith)
    have hab_groups := (upperJump_iff K L a).1 ha b hab
    have hbw_groups := (upperJump_iff K L b).1 hb w hbw
    rcases (upperRamificationGroup K L b).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact (not_lt_of_ge bot_le) (by simpa only [hbot] using hbw_groups)
    · exact (not_lt_of_ge le_top) (by simpa only [htop] using hab_groups)
  exact le_antisymm (le_of_not_gt (no_two_jumps hv hu)) (le_of_not_gt (no_two_jumps hu hv))

variable {K L} in
/-- In a prime-degree Galois extension, an upper ramification break is either the possible
unramified break at `-1` or a nonnegative integer.

The nonnegative alternative is stated with a natural number so that the norm-conductor API can
consume it directly. -/
theorem UpperJump.eq_neg_one_or_exists_eq_natCast_of_finrank_prime
    {u : RamificationIndexDomain} (hu : UpperJump K L u)
    (hdegree : (Module.finrank K L).Prime) :
    (u : ℝ) = -1 ∨ ∃ t : ℕ, (u : ℝ) = t := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime :=
    ⟨IsGalois.card_aut_eq_finrank K L ▸ hdegree⟩
  have hlower : LowerJump K L (inverseHerbrand K L u) :=
    (lowerJump_inverseHerbrand_iff K L u).2 hu
  obtain ⟨i, hi, hinverse⟩ := lowerJump_eq_intCast (K := K) (L := L) hlower
  by_cases hineg : i < 0
  · left
    have hi_eq : i = -1 := by
      have : (-1 : ℤ) ≤ i := by exact_mod_cast hi
      omega
    subst i
    have hinverse_neg_one :
        inverseHerbrand K L
            ⟨(-1 : ℝ), le_rfl⟩ =
          ⟨(-1 : ℝ), le_rfl⟩ :=
      inverseHerbrand_of_coe_le_zero K L (by norm_num)
    have hpoint :
        (⟨((-1 : ℤ) : ℝ), hi⟩ : RamificationIndexDomain) =
          ⟨-1, le_rfl⟩ :=
      Subtype.ext (by norm_num)
    have hu_eq : u = ⟨(-1 : ℝ), le_rfl⟩ :=
      (inverseHerbrand_strictMono K L).injective <|
        hinverse.trans (hpoint.trans hinverse_neg_one.symm)
    exact congrArg Subtype.val hu_eq
  · right
    have hi_nonneg : 0 ≤ i := le_of_not_gt hineg
    let t := i.toNat
    have hi_eq : i = t := (Int.toNat_of_nonneg hi_nonneg).symm
    let t' : RamificationIndexDomain :=
      ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩
    have hpoint : (⟨(i : ℝ), hi⟩ : RamificationIndexDomain) = t' := by
      apply Subtype.ext
      dsimp only [t']
      exact_mod_cast hi_eq
    have ht_lower : LowerJump K L
        ⟨(t : ℝ), Nat.cast_mem_ramificationIndexDomain t⟩ := by
      rw [hinverse, hpoint] at hlower
      exact hlower
    have hdrop : lowerRamificationGroup K L (t + 1) < lowerRamificationGroup K L t :=
      (lowerJump_intCast_iff K L (i := (t : ℤ))
        (Nat.cast_mem_ramificationIndexDomain t)).1 ht_lower
    have ht_ne : lowerRamificationGroup K L t ≠ ⊥ :=
      (bot_le.trans_lt hdrop).ne'
    have ht_top : lowerRamificationGroup K L t = ⊤ :=
      ((lowerRamificationGroup K L t).eq_bot_or_eq_top_of_prime_card).resolve_left ht_ne
    have hzero_top : lowerRamificationGroup K L 0 = ⊤ :=
      top_le_iff.1 <| ht_top ▸ lowerRamificationGroup_antitone K L (by positivity)
    have hpsi : psiNat K L t = t :=
      (psiNat_eq_self_iff K L).2 (ht_top.trans hzero_top.symm)
    have hinverse_t : inverseHerbrand K L t' = t' := by
      apply Subtype.ext
      simpa only [t', hpsi] using (coe_psiNat K L t).symm
    have hinverse_u : inverseHerbrand K L u = t' := by
      exact hinverse.trans hpoint
    have hu_eq : u = t' :=
      (inverseHerbrand_strictMono K L).injective <| hinverse_u.trans hinverse_t.symm
    exact ⟨t, congrArg Subtype.val hu_eq⟩

variable {K L} in
/-- **Hasse--Arf in prime degree.** Every upper ramification break of a finite Galois extension
of prime degree is an integer. -/
theorem UpperJump.exists_eq_intCast_of_finrank_prime
    {u : RamificationIndexDomain} (hu : UpperJump K L u)
    (hdegree : (Module.finrank K L).Prime) :
    ∃ z : ℤ, (u : ℝ) = (z : ℝ) := by
  rcases hu.eq_neg_one_or_exists_eq_natCast_of_finrank_prime hdegree with hu | ⟨t, hu⟩
  · exact ⟨-1, by simpa using hu⟩
  · exact ⟨t, by exact_mod_cast hu⟩

end TauCeti.LocalFieldsRamification
