/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Graded
import TauCeti.NumberTheory.LocalField.Norm.PrimeDegree

/-!
# The graded norm above a prime-degree ramification break

For a Galois extension `L/K` of prime degree `ℓ` with break `t`, the graded norm at every
unit depth `v > t` is bijective. Unlike the calculation below the break, the surviving term
in `N(1 + x)` is the trace, not `N(x)`. The trace maps `𝓂[L] ^ ψℕ(v)` onto `𝓂[K] ^ v`,
while the remaining terms lie in `𝓂[K] ^ (v + 1)`.

This supplies the successive approximation step for norm surjectivity above the break.
It is a statement about successive quotients, not yet about surjectivity on entire unit groups.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3, Proposition 5.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing Module TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- The trace at the Herbrand depth above a single break, together with the inequalities that
put the nonlinear terms of the prime-degree norm expansion in the next ideal power. -/
private theorem trace_depth_after_break {t v : ℕ} (hvt : t < v)
    (hG : lowerRamificationGroup K L t = ⊤)
    (hG' : lowerRamificationGroup K L (t + 1 : ℕ) = ⊥) (h2 : 2 ≤ finrank K L) :
    (psiNat K L v + differentExponent K L) / ramificationIndex K L = v ∧
      v + 1 ≤ psiNat K L v ∧
      ramificationIndex K L * (v + 1) ≤ 2 * psiNat K L v + differentExponent K L := by
  have hpos : 0 < finrank K L := by omega
  have hG0 : lowerRamificationGroup K L 0 = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (Int.natCast_nonneg t))
  have he : ramificationIndex K L = finrank K L :=
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1
      ((lowerRamificationGroup_zero_eq_top_iff K L).1 hG0)
  have hψ : psiNat K L v = t + finrank K L * (v - t) := by
    rw [psiNat_eq_add_card_mul_sub K L (hG.trans hG0.symm) hG' hvt.le,
      hG0, Subgroup.card_top, IsGalois.card_aut_eq_finrank]
  have hd := differentExponent_eq_of_lowerRamificationGroup_eq_at_zero_eq_bot K L
    (hG.trans hG0.symm) hG'
  rw [hG0, Subgroup.card_top, IsGalois.card_aut_eq_finrank] at hd
  have hsum : psiNat K L v + differentExponent K L =
      finrank K L * v + (finrank K L - 1) := by
    rw [hψ, hd]
    have h₁ : finrank K L * (v - t) + finrank K L * t = finrank K L * v := by
      rw [← mul_add, Nat.sub_add_cancel hvt.le]
    have h₂ : finrank K L - 1 + 1 = finrank K L := Nat.sub_add_cancel hpos
    nlinarith
  have hm : v + 1 ≤ psiNat K L v := by
    rw [hψ]
    have h₁ : v - t + t = v := Nat.sub_add_cancel hvt.le
    nlinarith
  refine ⟨?_, hm, ?_⟩
  · rw [he, hsum, Nat.mul_add_div hpos,
      Nat.div_eq_of_lt (Nat.sub_lt hpos zero_lt_one), add_zero]
  · rw [he]
    nlinarith

/-- **Above a prime-degree break the norm is the trace to first order.** For `x` at depth
`ψℕ(v)` with `v > t`, the nonlinear terms in `N(1 + x)` vanish modulo `𝓂[K] ^ (v + 1)`. -/
theorem norm_one_add_sub_one_sub_trace_mem_after_break (hℓ : (finrank K L).Prime)
    {t v : ℕ} (hvt : t < v)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩)
    {x : 𝒪[L]} (hx : x ∈ 𝓂[L] ^ psiNat K L v) :
    Algebra.norm 𝒪[K] (1 + x) - 1 - Algebra.trace 𝒪[K] 𝒪[L] x ∈ 𝓂[K] ^ (v + 1) := by
  have hG := lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht
  have hG' := lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump K L hℓ ht
  obtain ⟨-, hm, htr⟩ := trace_depth_after_break hvt hG hG' hℓ.two_le
  obtain ⟨y, hy, hN⟩ := exists_norm_one_add_eq_of_mem_maximalIdeal_pow hℓ hx
  have htotal : IsTotallyRamified K L := (lowerRamificationGroup_zero_eq_top_iff K L).1 <|
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (Int.natCast_nonneg t))
  have htrace : Algebra.trace 𝒪[K] 𝒪[L] y ∈ 𝓂[K] ^ (v + 1) := by
    rw [← Algebra.intTrace_eq_trace]
    exact intTrace_mem_maximalIdeal_pow_of_mem hy htr
  have hnorm : Algebra.norm 𝒪[K] x ∈ 𝓂[K] ^ (v + 1) := by
    rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at hx ⊢
    rw [addVal_norm, htotal.inertiaDegree_eq_one, one_nsmul]
    exact le_trans (by exact_mod_cast hm) hx
  have heq : Algebra.norm 𝒪[K] (1 + x) - 1 - Algebra.trace 𝒪[K] 𝒪[L] x =
      Algebra.trace 𝒪[K] 𝒪[L] y + Algebra.norm 𝒪[K] x := by
    rw [hN]
    ring
  rw [heq]
  exact add_mem htrace hnorm

/-- **The graded norm is bijective above the break.** In a Galois extension of prime degree
with an upper break at a natural number `t`, every graded norm at unit depth `v > t` is
bijective. The source depth is the canonical integral inverse Herbrand value `ψℕ(v)`. -/
theorem normGradedMap_after_break (hℓ : (finrank K L).Prime) {t v : ℕ} (hvt : t < v)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    Function.Bijective (normGradedMap K L v) := by
  have hG := lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht
  have hG' := lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump K L hℓ ht
  obtain ⟨hdiv, hm, -⟩ := trace_depth_after_break hvt hG hG' hℓ.two_le
  have htotal : IsTotallyRamified K L := (lowerRamificationGroup_zero_eq_top_iff K L).1 <|
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (Int.natCast_nonneg t))
  -- Surjectivity on the graded piece follows by lifting `u - 1` through the trace.
  have hsurj : Function.Surjective (normGradedMap K L v) := by
    intro c
    induction c using QuotientGroup.induction_on with | H u => ?_
    obtain ⟨a, ha, hau⟩ := mem_unitFiltration_iff_exists.1 u.2
    have hmap := map_intTrace_maximalIdeal_pow K L (psiNat K L v)
    rw [hdiv] at hmap
    obtain ⟨x, hx, hxa⟩ := Submodule.mem_map.1 (hmap.symm ▸ ha)
    have hx' : x ∈ 𝓂[L] ^ psiNat K L v := (Submodule.restrictScalars_mem ..).1 hx
    have hx1 : x ∈ 𝓂[L] := Ideal.pow_le_self (by omega) hx'
    have hunit : IsUnit (1 + x) := by
      apply isUnit_of_mem_nonunits_one_sub_self
      simpa using (mem_maximalIdeal _).1 (neg_mem hx1)
    let z : Lˣ := Units.map (Subring.subtype 𝒪[L]).toMonoidHom hunit.unit
    have hz : z ∈ unitFiltration L (psiNat K L v) :=
      mem_unitFiltration_iff_exists.2 ⟨hunit.unit, by simpa [hunit.unit_spec] using hx', rfl⟩
    refine ⟨QuotientGroup.mk (⟨z, hz⟩ : unitFiltration L (psiNat K L v)), ?_⟩
    rw [normGradedMap_mk, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have hNa : Algebra.norm 𝒪[K] (1 + x) - (a : 𝒪[K]) ∈ 𝓂[K] ^ (v + 1) := by
      have herr := norm_one_add_sub_one_sub_trace_mem_after_break hℓ hvt ht hx'
      rw [← Algebra.intTrace_eq_trace, hxa] at herr
      simpa only [sub_sub_sub_cancel_right] using herr
    let b : 𝒪[K]ˣ := Units.map (Algebra.norm 𝒪[K]) hunit.unit
    have hb : (b : 𝒪[K]) = Algebra.norm 𝒪[K] (1 + x) := by
      simp only [b, Units.coe_map, hunit.unit_spec]
    have hNb : Algebra.normUnits K z = Units.map (Subring.subtype 𝒪[K]).toMonoidHom b := by
      apply Units.ext
      simp [z, b, Algebra.coe_normUnits, coe_norm_integerRing]
    refine mem_unitFiltration_iff_exists.2 ⟨a * b⁻¹, ?_, ?_⟩
    · have heq : (↑(a * b⁻¹) : 𝒪[K]) - 1 =
          -(Algebra.norm 𝒪[K] (1 + x) - ↑a) * ↑b⁻¹ := by
        rw [Units.val_mul, ← hb]
        linear_combination (Units.mul_inv b)
      rw [heq]
      exact Ideal.mul_mem_right _ _ (neg_mem hNa)
    · have hbInv : ((↑b⁻¹ : 𝒪[K]) : K) = ((↑b : 𝒪[K]) : K)⁻¹ :=
        map_units_inv (Subring.subtype 𝒪[K]) b
      simp [hNb, ← hau, mul_comm, hbInv]
  -- Both positive-depth graded pieces have the same finite cardinality.
  have hv0 : 0 < v := by omega
  have hm0 : 0 < psiNat K L v := by omega
  have hcard : Nat.card (UnitFiltrationGraded L (psiNat K L v)) =
      Nat.card (UnitFiltrationGraded K v) := by
    obtain ⟨v', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0.ne'
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0.ne'
    rw [hm, natCard_unitFiltrationGraded_succ, natCard_unitFiltrationGraded_succ,
      natCard_residueField K L, htotal.inertiaDegree_eq_one, pow_one]
  have : Finite (UnitFiltrationGraded L (psiNat K L v)) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0.ne'
    rw [hm]
    exact Nat.finite_of_card_ne_zero <| by
      rw [natCard_unitFiltrationGraded_succ]
      exact Nat.card_pos.ne'
  exact hsurj.bijective_of_nat_card_le hcard.le

end TauCeti
