/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.HasseArf
public import TauCeti.NumberTheory.LocalField.Norm.Surjectivity
public import TauCeti.NumberTheory.LocalField.Norm.Unramified

/-!
# Unit norm indices and the conductor in prime degree

For a Galois extension of prime degree with upper ramification break at a natural number `t`,
the norm of the whole integer-unit group has index equal to the degree. More generally, the
norm from `U(L, ψℕ(v))` has that same index in `U(K,v)` at every depth `v ≤ t`.

The intersection with the full unit norm group is determined by the unit filtration up to the
break. Together with norm surjectivity above the break, this gives the sharp conductor
criterion: `U(K,v)` is contained in the field norm group exactly when `t < v`. Thus the least
natural unit depth contained in the norm group is `t + 1`. This includes a tame break at zero.

Since a prime-degree upper break is `-1` or a natural number by the prime-degree case of
Hasse--Arf, the criterion extends to every prime-degree upper break `u`: `U(K,v)` lies in the
norm group exactly when `u < v`. At the unramified break `-1` the conductor is zero.

## Main results

* `TauCeti.LocalFieldsRamification.UpperJump.unitFiltration_le_normGroup_iff_of_finrank_prime`:
  the conductor criterion at any prime-degree upper break, including the unramified break `-1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3, Proposition 5 and its corollaries,
  and §7.
-/

public section
noncomputable section

open TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

private theorem map_normUnits_unitFiltration_inf_succ_before_break
    (hℓ : (Module.finrank K L).Prime) {v t : ℕ} (hvt : v < t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) ⊓
      unitFiltration K (v + 1) =
        (unitFiltration L (psiNat K L (v + 1))).map (Algebra.normUnits K) := by
  have hψ := psiNat_eq_self_of_le_break K L hℓ hvt.le ht
  have hψ' := psiNat_eq_self_of_le_break K L hℓ (Nat.succ_le_of_lt hvt) ht
  apply le_antisymm
  · intro x hx
    obtain ⟨hyx, hx⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hy, rfl⟩ := hyx
    have hnorm : normGradedMap K L v
        (QuotientGroup.mk (⟨y, hy⟩ : unitFiltration L (psiNat K L v))) = 1 := by
      simpa only [normGradedMap_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using hx
    have hyclass : (QuotientGroup.mk (⟨y, hy⟩ : unitFiltration L (psiNat K L v)) :
        UnitFiltrationGraded L (psiNat K L v)) = 1 :=
      (normGradedMap_positive_before_break hℓ hvt ht).injective
        (hnorm.trans (map_one _).symm)
    have hy' : y ∈ unitFiltration L (psiNat K L v + 1) := by
      simpa only [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using hyclass
    exact Subgroup.mem_map_of_mem _ (by simpa only [hψ, hψ'] using hy')
  · exact le_inf (Subgroup.map_mono (unitFiltration_antitone
      ((psiNat_strictMono K L).monotone v.le_succ)))
      (map_normUnits_unitFiltration_psiNat_le K L (v + 1))

/-- Up to a prime-degree break, the norms of integer units that lie in `U(K,v)` are exactly
norms from the Herbrand-shifted step `U(L, ψℕ(v))`. -/
theorem map_normUnits_unitFiltration_zero_inf_of_le_break
    (hℓ : (Module.finrank K L).Prime) {v t : ℕ} (hvt : v ≤ t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    (unitFiltration L 0).map (Algebra.normUnits K) ⊓ unitFiltration K v =
      (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) := by
  induction v with
  | zero =>
    rw [psiNat_zero]
    exact inf_of_le_left (by
      simpa only [psiNat_zero] using map_normUnits_unitFiltration_psiNat_le K L 0)
  | succ v ih =>
    rw [← inf_of_le_right (unitFiltration_antitone v.le_succ), ← inf_assoc,
      ih (by omega), map_normUnits_unitFiltration_inf_succ_before_break hℓ (by omega) ht]

/-- At every depth up to a prime-degree upper break, the full norm image of the
Herbrand-shifted unit step has relative index equal to the extension degree. -/
theorem relIndex_normUnits_unitFiltration_of_le_break (hℓ : (Module.finrank K L).Prime)
    {v t : ℕ} (hvt : v ≤ t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    ((unitFiltration L (psiNat K L v)).map (Algebra.normUnits K)).relIndex
      (unitFiltration K v) = Module.finrank K L := by
  have hat : unitFiltration K (t + 1) ≤
      (unitFiltration L (psiNat K L t)).map (Algebra.normUnits K) := by
    rw [← map_normUnits_unitFiltration_after_break hℓ t.lt_succ_self ht]
    exact Subgroup.map_mono (unitFiltration_antitone
      ((psiNat_strictMono K L).monotone t.le_succ))
  have hbase := relIndex_normUnits_unitFiltration_sup_at_break hℓ ht
  rw [sup_of_le_left hat] at hbase
  induction hvt using Nat.decreasingInduction with
  | self => exact hbase
  | of_succ v hvt ih =>
    have hsup : unitFiltration K (v + 1) ⊔
        (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v := by
      apply le_antisymm
      · exact sup_le (unitFiltration_antitone v.le_succ)
          (map_normUnits_unitFiltration_psiNat_le K L v)
      · simpa only [sup_comm] using Subgroup.relIndex_eq_one.1
          (relIndex_normUnits_unitFiltration_sup_before_break hℓ hvt ht)
    rw [← hsup, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right,
      map_normUnits_unitFiltration_inf_succ_before_break hℓ hvt ht]
    exact ih

/-- The norm image of the entire integer-unit group has index equal to the degree in a
prime-degree Galois extension with a natural upper break. -/
theorem relIndex_normUnits_unitFiltration_zero (hℓ : (Module.finrank K L).Prime)
    {t : ℕ} (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    ((unitFiltration L 0).map (Algebra.normUnits K)).relIndex (unitFiltration K 0) =
      Module.finrank K L := by
  simpa only [psiNat_zero] using
    relIndex_normUnits_unitFiltration_of_le_break hℓ (Nat.zero_le t) ht

/-- A unit-filtration step is contained in the field norm group exactly when its depth is
strictly above the prime-degree upper break. Equivalently, the conductor is `t + 1`. This
natural-break case is the input to
`LocalFieldsRamification.UpperJump.unitFiltration_le_normGroup_iff_of_finrank_prime`. -/
private theorem unitFiltration_le_normGroup_iff (hℓ : (Module.finrank K L).Prime) {t v : ℕ}
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    unitFiltration K v ≤ normGroup K L ↔ t < v := by
  constructor
  · intro hv
    by_contra htv
    have hvt : v ≤ t := by omega
    have hunit : unitFiltration K v ≤ (unitFiltration L 0).map (Algebra.normUnits K) := by
      intro x hx
      obtain ⟨y, hy⟩ := mem_normGroup_iff.1 (hv hx)
      have hyx : Algebra.normUnits K y = x :=
        Units.ext (by simpa only [Algebra.coe_normUnits] using hy)
      exact ⟨y, normUnits_mem_unitFiltration_zero_iff.1
        (hyx ▸ unitFiltration_antitone (Nat.zero_le v) hx), hyx⟩
    have hstep : unitFiltration K v ≤
        (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) := by
      rw [← map_normUnits_unitFiltration_zero_inf_of_le_break hℓ hvt ht]
      exact le_inf hunit le_rfl
    have hone := Subgroup.relIndex_eq_one.2 hstep
    rw [relIndex_normUnits_unitFiltration_of_le_break hℓ hvt ht] at hone
    exact hℓ.ne_one hone
  · intro htv x hx
    rw [← map_normUnits_unitFiltration_after_break hℓ htv ht] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact mem_normGroup_iff.2 ⟨y, by simp⟩

namespace LocalFieldsRamification

/-- At an upper break of a prime-degree Galois extension, a unit-filtration step lies in the norm
group exactly when its depth is strictly above the break. Thus the conductor is one more than the
unique break; this is zero when the break is `-1` in the unramified case. -/
theorem UpperJump.unitFiltration_le_normGroup_iff_of_finrank_prime
    {u : RamificationIndexDomain} (hu : UpperJump K L u)
    (hdegree : (Module.finrank K L).Prime) (v : ℕ) :
    unitFiltration K v ≤ normGroup K L ↔ (u : ℝ) < v := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime :=
    ⟨IsGalois.card_aut_eq_finrank K L ▸ hdegree⟩
  rcases hu.eq_neg_one_or_exists_eq_natCast_of_finrank_prime hdegree with hneg | ⟨t, hut⟩
  · have hu_eq : u = ⟨(-1 : ℝ), le_rfl⟩ := Subtype.ext hneg
    subst u
    let zero : RamificationIndexDomain := ⟨(0 : ℝ), by norm_num⟩
    have hdrop := (upperJump_iff K L ⟨(-1 : ℝ), le_rfl⟩).1 hu zero
      (Subtype.mk_lt_mk.2 (by norm_num))
    have hzero_ne_top : upperRamificationGroup K L zero ≠ ⊤ :=
      (hdrop.trans_le le_top).ne
    have hzero_bot : upperRamificationGroup K L zero = ⊥ :=
      (upperRamificationGroup K L zero).eq_bot_or_eq_top_of_prime_card.resolve_right hzero_ne_top
    have hGzero : lowerRamificationGroup K L 0 = ⊥ := by
      rw [upperRamificationGroup_of_coe_le_zero K L (v := zero) (by norm_num)] at hzero_bot
      rw [← lowerRamificationGroupReal_intCast K L (0 : ℤ)]
      convert hzero_bot using 1
      norm_num [zero]
    have he : ramificationIndex K L = 1 := by
      rw [← natCard_lowerRamificationGroup_zero K L, hGzero]
      simp
    have hunramified : IsUnramified K L :=
      (isUnramified_iff_ramificationIndex_eq_one K L).2 he
    let _ : IsUnramified K L := hunramified
    constructor
    · intro
      have : (0 : ℝ) ≤ v := Nat.cast_nonneg v
      linarith
    · intro
      rw [← map_normUnits_unitFiltration K L v]
      rintro _ ⟨y, -, rfl⟩
      exact mem_normGroup_iff.2 ⟨y, by simp⟩
  · have hu_eq : u = ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := Subtype.ext hut
    subst u
    simpa only [Nat.cast_lt] using unitFiltration_le_normGroup_iff hdegree hu

end LocalFieldsRamification

end TauCeti
