/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic

import TauCeti.NumberTheory.LocalField.Squares
import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Counting Eisenstein unit-norm square classes

Over a nonarchimedean local field `K` with `2 ≠ 0`, the rational composition bijection from
`TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic` gives the subgroup
`TauCeti.eisensteinNormSquareSubgroup K ht hc` uniform fibres on `𝒪[K] ⧸ 𝓂[K]^N` once `N` is deep
enough that `r ∈ 𝓂[K]^N` makes `1 - t r + c r²` a square in `K`. Counting the single trivial fibre
shows that `eisensteinNormSquareSubgroup K ht hc` has cardinality `#𝓀[K] ^ v_K(2)` (where
`v_K(2) = natCastValuation K 2 h2`) and index `2` inside `TauCeti.unitSquareClasses K`:

* When `valuation K t < valuation K 2` (including `t = 0` and odd residue characteristic),
  completing the square identifies `eisensteinNormSquareSubgroup K ht hc` with a `t = 0` Eisenstein
  subgroup in bijection with `𝒪[K] ⧸ 𝓂[K] ^ v_K(2)`.
* When `valuation K 2 ≤ valuation K t`, factoring `t = c r₀` and writing `r = r₀ s` converts
  `1 - t r + c r²` into `1 + c r₀² (s² - s)`, relating the trivial fibre to the Artin–Schreier map
  `s ↦ s² - s` and the squaring homomorphism on the positive unit filtration below `v_K(2)`.

## Main results

* `TauCeti.natCard_eisensteinNormSquareSubgroup`: over a nonarchimedean local field with `2 ≠ 0`,
  `eisensteinNormSquareSubgroup K ht hc` has cardinality `#𝓀[K] ^ natCastValuation K 2 h2`.
* `TauCeti.ncard_range_eisensteinNormSquareClass`: set-cardinality form on the range of
  `eisensteinNormSquareClass K ht hc`.
* `TauCeti.relIndex_eisensteinNormSquareSubgroup`: `eisensteinNormSquareSubgroup K ht hc` has
  index `2` inside `unitSquareClasses K`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- At `t = 0`, `1 + c r²` is a square in `K` if and only if `r ∈ 𝓂[K] ^ v_K(2)`. -/
private theorem eisensteinNormSquareClass_zero_t_eq_one_iff (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : Irreducible c) (r : 𝒪[K]) :
    eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc r = 1 ↔
      r ∈ 𝓂[K] ^ natCastValuation K 2 h2 := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hmem : ∀ y : 𝒪[K], y ∈ 𝓂[K] ^ e ↔ valuation K (y : K) ≤ valuation K (c : K) ^ e :=
    fun y ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) e) y
  constructor
  · -- If `r ∉ 𝓂[K] ^ e`, write `r = u c ^ ρ` with `ρ < e`; then `1 + c r²` has odd defect `2ρ + 1`.
    intro hsq
    by_contra hr
    have hr0 : r ≠ 0 := fun h ↦ hr (h ▸ zero_mem _)
    obtain ⟨ρ, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hc
    have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    have hρlt : ρ < e := by
      by_contra! hge
      apply hr
      rw [hmem]
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1, one_mul]
      exact pow_le_pow_right_of_le_one' hc1.le hge
    obtain ⟨ξ, hξ⟩ := (eisensteinNormSquareClass_eq_one_iff (zero_mem 𝓂[K]) hc _).mp hsq
    apply valuation_sq_sub_one_ne_pow_odd h2 hc hρlt ξ
    have hξ2 : ξ ^ 2 - 1 = (c : K) * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) ^ 2 := by
      have hξ' : 1 - 0 * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) +
          (c : K) * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) ^ 2 = ξ ^ 2 := by
        simpa only [sq, ZeroMemClass.coe_zero, Subring.coe_mul, SubmonoidClass.coe_pow] using hξ
      linear_combination -hξ'
    simp only [hξ2, mul_pow, map_mul, map_pow, hu1, one_pow, one_mul, ← pow_mul, ← pow_succ']
    congr 1
    omega
  · -- Conversely, if `r ∈ 𝓂[K] ^ e`, then `1 + c r² ∈ U(K, 2e + 1) ≤ (Kˣ)²`.
    intro hr
    have hrv : valuation K (r : K) ≤ valuation K (c : K) ^ e := (hmem r).mp hr
    have hu_mem : eisensteinNormUnit K (zero_mem 𝓂[K]) hc r ∈
        unitFiltration K (2 * dyadicLevel K h2 + 1) := by
      rw [dyadicLevel_def, mem_unitFiltration_succ_valuation (2 * e) _ c hc, map_pow]
      simp only [coe_eisensteinNormUnit, ZeroMemClass.coe_zero, zero_mul, sub_zero,
        add_sub_cancel_left, map_mul, map_pow]
      calc valuation K (c : K) * valuation K (r : K) ^ 2
          ≤ valuation K (c : K) * (valuation K (c : K) ^ e) ^ 2 :=
            mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrv 2)
        _ = valuation K (c : K) ^ (2 * e + 1) := by
            rw [← pow_mul, ← pow_succ']
            congr 1
            omega
    rw [eisensteinNormSquareClass_def]
    exact (squareClassHom_eq_one_iff _).mpr
      (Subgroup.mem_square.mp (unitFiltration_le_square h2 hu_mem))

/-- When `t = 0`, `eisensteinNormSquareSubgroup` is in bijection with `𝒪[K] ⧸ 𝓂[K] ^ v_K(2)` and
therefore has `#𝓀[K] ^ v_K(2)` elements. -/
private theorem natCard_eisensteinNormSquareSubgroup_zero (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : Irreducible c) :
    Nat.card (eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  set e := natCastValuation K 2 h2
  have hcm : c ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal c).mpr hc.not_isUnit
  have hrel : ∀ v s : 𝒪[K],
      eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc v =
        eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc s ↔ v - s ∈ 𝓂[K] ^ e := by
    intro v s
    rw [eisensteinNormSquareClass_eq_iff, ← eisensteinNormSquareClass_eq_one_iff (zero_mem 𝓂[K]) hc,
      eisensteinNormSquareClass_zero_t_eq_one_iff h2 hc]
    have hsub := eisensteinNormCompose_sub_mem_iff (zero_mem 𝓂[K]) hcm (𝓂[K] ^ e) v s s
    simpa only [eisensteinNormCompose_self, sub_zero] using hsub
  let f : (𝒪[K] ⧸ 𝓂[K] ^ e) → eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc :=
    Quotient.lift (fun v ↦ ⟨eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc v,
      (mem_eisensteinNormSquareSubgroup_iff (zero_mem 𝓂[K]) hc _).mpr ⟨v, rfl⟩⟩)
      fun v s hvs ↦ Subtype.ext ((hrel v s).mpr ((Submodule.quotientRel_def _).mp hvs))
  have hf_bij : Function.Bijective f := by
    refine ⟨fun x y hxy ↦ ?_, ?_⟩
    · obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq.mpr ((hrel v s).mp (congrArg Subtype.val hxy))
    · rintro ⟨q, hq⟩
      obtain ⟨v, rfl⟩ := (mem_eisensteinNormSquareSubgroup_iff (zero_mem 𝓂[K]) hc q).mp hq
      exact ⟨Ideal.Quotient.mk _ v, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf_bij)]
  exact TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow e

/-- When `valuation K t < valuation K 2`, completing the square identifies
`eisensteinNormSquareSubgroup K ht hc` with a `t = 0` Eisenstein subgroup, giving cardinality
`#𝓀[K] ^ v_K(2)`. -/
private theorem natCard_eisensteinNormSquareSubgroup_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  -- Step 1: Set `μ = t / 2 ∈ 𝓂[K]` and verify that `c' = c - μ²` is again irreducible in `𝒪[K]`.
  have h2pos : 0 < valuation K (2 : K) := (Valuation.pos_iff _).mpr h2
  have hμlt : valuation K ((t : K) / 2) < 1 := by rwa [map_div₀, div_lt_one₀ h2pos]
  let μ : 𝒪[K] := ⟨(t : K) / 2, hμlt.le⟩
  have hμm : μ ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.mpr hμlt
  have htμ : (t : K) = 2 * (μ : K) := (mul_div_cancel₀ (t : K) h2).symm
  let c' : 𝒪[K] := c - μ ^ 2
  have hc'eq : (c' : K) = (c : K) - (μ : K) ^ 2 := by
    dsimp only [c']
    push_cast
    rfl
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hc0 : 0 < valuation K (c : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hc
  have hμc : valuation K (μ : K) ≤ valuation K (c : K) :=
    (Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) μ).mp hμm
  have hμ2lt : valuation K ((μ : K) ^ 2) < valuation K (c : K) := by
    rw [map_pow, sq]
    calc valuation K (μ : K) * valuation K (μ : K)
        ≤ valuation K (c : K) * valuation K (c : K) := mul_le_mul' hμc hμc
      _ < 1 * valuation K (c : K) := mul_lt_mul_of_pos_right hc1 hc0
      _ = valuation K (c : K) := one_mul _
  have hc'v : valuation K (c' : K) = valuation K (c : K) := by
    rw [hc'eq]
    exact (valuation K).map_sub_eq_of_lt_left hμ2lt
  have hc' : Irreducible c' := irreducible_of_valuation_eq hc hc'v
  -- Step 2: Completing the square via `w = v / (1 - μ v)` equates the square-class subgroups.
  have heq : eisensteinNormSquareSubgroup K ht hc =
      eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc' := by
    ext q
    simp only [mem_eisensteinNormSquareSubgroup_iff]
    constructor
    · rintro ⟨v, rfl⟩
      have hu : IsUnit (1 - μ * v) := by
        simpa only [sub_eq_add_neg] using
          isUnit_add_of_isUnit_of_not_isUnit isUnit_one
            ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_right v _ hμm)))
      let w : 𝒪[K] := v * (↑hu.unit⁻¹ : 𝒪[K])
      refine ⟨w, ?_⟩
      let uK : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) hu.unit
      have hw₀ : w * (hu.unit : 𝒪[K]) = v := by
        dsimp only [w]
        rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      have hw : (w : K) * ((hu.unit : 𝒪[K]) : K) = (v : K) := by
        simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hw₀
      have hu_spec : ((hu.unit : 𝒪[K]) : K) = 1 - (μ : K) * (v : K) := by
        have h := congrArg ((↑) : 𝒪[K] → K) hu.unit_spec; push_cast at h; exact h
      have hunit : eisensteinNormUnit K ht hc v =
          uK ^ 2 * eisensteinNormUnit K (zero_mem 𝓂[K]) hc' w := by
        ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_eisensteinNormUnit,
          ZeroMemClass.coe_zero, zero_mul, sub_zero, uK, Units.coe_map, MonoidHom.coe_ofClass,
          Subring.coe_subtype, hc'eq]
        calc 1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2
            = ((hu.unit : 𝒪[K]) : K) ^ 2 + ((c : K) - (μ : K) ^ 2) * (v : K) ^ 2 := by
              rw [htμ, hu_spec]; ring
          _ = ((hu.unit : 𝒪[K]) : K) ^ 2 * (1 + ((c : K) - (μ : K) ^ 2) * (w : K) ^ 2) := by
              rw [← hw]; ring
      rw [eisensteinNormSquareClass_def, eisensteinNormSquareClass_def, hunit, map_mul,
        (squareClassHom_eq_one_iff _).mpr ⟨uK, sq uK⟩, one_mul]
    · rintro ⟨w, rfl⟩
      have hu : IsUnit (1 + μ * w) :=
        isUnit_add_of_isUnit_of_not_isUnit isUnit_one
          ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right w _ hμm))
      let v : 𝒪[K] := w * (↑hu.unit⁻¹ : 𝒪[K])
      refine ⟨v, ?_⟩
      let uK : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) hu.unit
      have hv₀ : v * (hu.unit : 𝒪[K]) = w := by
        dsimp only [v]
        rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      have hv : (v : K) * ((hu.unit : 𝒪[K]) : K) = (w : K) := by
        simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hv₀
      have hu_spec : ((hu.unit : 𝒪[K]) : K) = 1 + (μ : K) * (w : K) := by
        have h := congrArg ((↑) : 𝒪[K] → K) hu.unit_spec; push_cast at h; exact h
      have hunit : eisensteinNormUnit K (zero_mem 𝓂[K]) hc' w =
          uK ^ 2 * eisensteinNormUnit K ht hc v := by
        ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_eisensteinNormUnit,
          ZeroMemClass.coe_zero, zero_mul, sub_zero, uK, Units.coe_map, MonoidHom.coe_ofClass,
          Subring.coe_subtype, hc'eq]
        calc 1 + ((c : K) - (μ : K) ^ 2) * (w : K) ^ 2
            = (((hu.unit : 𝒪[K]) : K) - (μ : K) * (w : K)) ^ 2 +
                ((c : K) - (μ : K) ^ 2) * (w : K) ^ 2 := by
              rw [hu_spec]; ring
          _ = ((hu.unit : 𝒪[K]) : K) ^ 2 *
                (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
              rw [htμ, ← hv]; ring
      rw [eisensteinNormSquareClass_def, eisensteinNormSquareClass_def, hunit, map_mul,
        (squareClassHom_eq_one_iff _).mpr ⟨uK, sq uK⟩, one_mul]
  rw [heq]
  exact natCard_eisensteinNormSquareSubgroup_zero h2 hc'

/-- Below the threshold `v_K(2)`, squaring carries `U(K, e - k)` (`k < e`) into `U(K, 2e - 2k)`,
onto the square cosets modulo `U(K, 2e + 1)`, with kernel of index `2` over `U(K, e + 1)`. Hence
twice the number of square cosets in `U(K, 2e - 2k) ⧸ U(K, 2e + 1)` equals `#𝓀[K] ^ (k + 1)`. -/
private theorem two_mul_natCard_squareCosets_unitFiltration (h2 : (2 : K) ≠ 0) {k : ℕ}
    (hk : k < natCastValuation K 2 h2) :
    2 * Nat.card {q : unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k) ⧸
        (unitFiltration K (2 * natCastValuation K 2 h2 + 1)).subgroupOf
          (unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k)) //
        ∃ u : unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k),
          QuotientGroup.mk u = q ∧ IsSquare (u : Kˣ)} =
      Nat.card 𝓀[K] ^ (k + 1) := by
  set e := natCastValuation K 2 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hπ0 : 0 < valuation K (π : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hπ
  have hv2 : valuation K (2 : K) = valuation K (π : K) ^ e := valuation_natCast_eq_pow hπ 2 h2
  -- Step 1: Squaring maps `U(K, e - k)` into `U(K, 2e - 2k)`.
  have hsq_mem : ∀ z : Kˣ, z ∈ unitFiltration K (e - k) →
      z ^ 2 ∈ unitFiltration K (2 * e - 2 * k) := by
    intro z hz
    rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ] at hz ⊢
    have hid : ((z ^ 2 : Kˣ) : K) - 1 = 2 * ((z : K) - 1) + ((z : K) - 1) ^ 2 := by
      push_cast; ring
    rw [hid]
    refine ((valuation K).map_add _ _).trans (max_le ?_ ?_)
    · rw [map_mul, hv2]
      calc valuation K (π : K) ^ e * valuation K ((z : K) - 1)
          ≤ valuation K (π : K) ^ e * valuation K (π : K) ^ (e - k) :=
            mul_le_mul' le_rfl hz
        _ = valuation K (π : K) ^ (e + (e - k)) := (pow_add _ _ _).symm
        _ ≤ valuation K (π : K) ^ (2 * e - 2 * k) :=
            pow_le_pow_right_of_le_one' hπ1.le (by omega)
    · rw [map_pow]
      calc valuation K ((z : K) - 1) ^ 2
          ≤ (valuation K (π : K) ^ (e - k)) ^ 2 := pow_le_pow_left₀ zero_le hz 2
        _ = valuation K (π : K) ^ (2 * e - 2 * k) := by rw [← pow_mul]; congr 1; omega
  -- Step 2: Conversely, any `z : Kˣ` with `z² ∈ U(K, 2e - 2k)` already lies in `U(K, e - k)`.
  have hmem_of_sq : ∀ z : Kˣ, z ^ 2 ∈ unitFiltration K (2 * e - 2 * k) →
      z ∈ unitFiltration K (e - k) := by
    intro z hz2
    rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ] at hz2 ⊢
    by_contra! hgt
    have hlt2 : valuation K (2 : K) < valuation K ((z : K) - 1) := by
      rw [hv2]
      exact (pow_le_pow_right_of_le_one' hπ1.le (by omega : e - k ≤ e)).trans_lt hgt
    have hplus : valuation K ((z : K) + 1) = valuation K ((z : K) - 1) := by
      calc valuation K ((z : K) + 1) = valuation K (((z : K) - 1) + 2) := by congr 1; ring
        _ = valuation K ((z : K) - 1) := (valuation K).map_add_eq_of_lt_left hlt2
    have hsq_eq : valuation K (((z ^ 2 : Kˣ) : K) - 1) = valuation K ((z : K) - 1) ^ 2 := by
      have hid : ((z ^ 2 : Kˣ) : K) - 1 = ((z : K) - 1) * ((z : K) + 1) := by push_cast; ring
      rw [hid, map_mul, hplus, sq]
    have hgt2 : valuation K (π : K) ^ (2 * e - 2 * k) < valuation K ((z : K) - 1) ^ 2 := by
      calc valuation K (π : K) ^ (2 * e - 2 * k)
          = (valuation K (π : K) ^ (e - k)) ^ 2 := by rw [← pow_mul]; congr 1; omega
        _ < valuation K ((z : K) - 1) ^ 2 := pow_lt_pow_left₀ hgt zero_le (by decide)
    exact (hsq_eq ▸ hz2).not_gt hgt2
  set G₀ := unitFiltration K (e - k)
  set U₂ := unitFiltration K (2 * e - 2 * k)
  set H₂ := (unitFiltration K (2 * e + 1)).subgroupOf U₂
  let sqMap : G₀ →* U₂ :=
    { toFun := fun z ↦ ⟨(z : Kˣ) ^ 2, hsq_mem z.1 z.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y ↦ by ext; simp [mul_pow] }
  let sqHom : G₀ →* U₂ ⧸ H₂ := (QuotientGroup.mk' H₂).comp sqMap
  -- Identify `sqHom.range` with the set of square cosets in `U₂ ⧸ H₂`.
  have hrange_eq : (sqHom.range : Set (U₂ ⧸ H₂)) =
      {q | ∃ u : U₂, QuotientGroup.mk u = q ∧ IsSquare (u : Kˣ)} := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨sqMap z, rfl, ⟨z.1, sq z.1⟩⟩
    · rintro ⟨u, rfl, ⟨z, hz⟩⟩
      have hz2 : z ^ 2 = u.1 := by simpa only [sq] using hz.symm
      refine ⟨⟨z, hmem_of_sq z (hz2 ▸ u.2)⟩, ?_⟩
      dsimp only [sqHom]
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext hz2
  -- Step 3: `H_deep = U(K, e + 1)` has index `2` in `sqHom.ker` (generated by `-1`).
  let H_deep : Subgroup G₀ := (unitFiltration K (e + 1)).subgroupOf G₀
  have hle_ker : H_deep ≤ sqHom.ker := by
    intro z hz
    dsimp only [sqHom]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hz1 : (z : Kˣ) ∈ unitFiltration K (e + 1) := hz
    rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ] at hz1 ⊢
    have hid : (((sqMap z : U₂) : Kˣ) : K) - 1 =
        2 * (((z : Kˣ) : K) - 1) + (((z : Kˣ) : K) - 1) ^ 2 := by
      simp only [sqMap, MonoidHom.coe_mk, OneHom.coe_mk]; push_cast; ring
    rw [hid]
    refine ((valuation K).map_add _ _).trans (max_le ?_ ?_)
    · rw [map_mul, hv2]
      calc valuation K (π : K) ^ e * valuation K (((z : Kˣ) : K) - 1)
          ≤ valuation K (π : K) ^ e * valuation K (π : K) ^ (e + 1) := mul_le_mul' le_rfl hz1
        _ = valuation K (π : K) ^ (2 * e + 1) := by rw [← pow_add]; congr 1; omega
    · rw [map_pow]
      calc valuation K (((z : Kˣ) : K) - 1) ^ 2
          ≤ (valuation K (π : K) ^ (e + 1)) ^ 2 := pow_le_pow_left₀ zero_le hz1 2
        _ ≤ valuation K (π : K) ^ (2 * e + 1) := by
            rw [← pow_mul]
            exact pow_le_pow_right_of_le_one' hπ1.le (by omega)
  have hneg1_G₀ : (-1 : Kˣ) ∈ G₀ := by
    rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ]
    have hneg2 : ((-1 : Kˣ) : K) - 1 = -(2 : K) := by push_cast; ring
    rw [hneg2, Valuation.map_neg, hv2]
    exact pow_le_pow_right_of_le_one' hπ1.le (by omega)
  let negOne : sqHom.ker := ⟨⟨-1, hneg1_G₀⟩, by
    dsimp only [sqHom, sqMap]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simp⟩
  have hrel2 : H_deep.relIndex sqHom.ker = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨negOne, ?_, fun w ↦ ?_⟩
    · intro hmem
      have h1 : (-1 : Kˣ) ∈ unitFiltration K (e + 1) := hmem
      rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ] at h1
      have hneg2 : ((-1 : Kˣ) : K) - 1 = -(2 : K) := by push_cast; ring
      rw [hneg2, Valuation.map_neg, hv2] at h1
      exact (pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (Nat.lt_succ_self e)).not_ge h1
    · have hw2 : (w.1.1 : Kˣ) ^ 2 ∈ unitFiltration K (2 * e + 1) := by
        have hwker := w.2
        dsimp only [sqHom, sqMap] at hwker
        rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hwker
      rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ] at hw2
      by_cases hw_in : w ∈ H_deep.subgroupOf sqHom.ker
      · exact Or.inr hw_in
      · refine Or.inl ?_
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
          mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ]
        have hwnot : ¬ valuation K ((w.1.1 : K) - 1) ≤ valuation K (π : K) ^ (e + 1) :=
          fun hle ↦ hw_in ((mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ).mpr hle)
        have hprod : valuation K ((w.1.1 : K) - 1) * valuation K ((w.1.1 : K) + 1) ≤
            valuation K (π : K) ^ (2 * e + 1) := by
          have hid : (((w.1.1 : Kˣ) ^ 2 : Kˣ) : K) - 1 =
              ((w.1.1 : K) - 1) * ((w.1.1 : K) + 1) := by
            push_cast; ring
          rwa [hid, map_mul] at hw2
        have hw_ge_e : valuation K (π : K) ^ e ≤ valuation K ((w.1.1 : K) - 1) := by
          have hint : (w.1.1 : K) - 1 ∈ 𝒪[K] := by
            have hw0 : (w.1.1 : Kˣ) ∈ unitFiltration K 0 :=
              unitFiltration_antitone (Nat.zero_le _) w.1.2
            have hv1 : valuation K (w.1.1 : K) = 1 := (mem_unitFiltration_zero _).mp hw0
            exact sub_mem ((Valuation.mem_integer_iff _ _).mpr hv1.le) (one_mem _)
          let δ : 𝒪[K] := ⟨(w.1.1 : K) - 1, hint⟩
          have hδ0 : δ ≠ 0 := by
            intro h0
            apply hwnot
            have h0' : (w.1.1 : K) - 1 = 0 := congrArg Subtype.val h0
            simp [h0']
          obtain ⟨ρ, u, hδu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hδ0 hπ
          have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
            (Valuation.integer.integers (valuation K)).valuation_unit u
          have hδv : valuation K ((w.1.1 : K) - 1) = valuation K (π : K) ^ ρ := by
            have := congrArg (fun x : 𝒪[K] ↦ valuation K (x : K)) hδu
            simpa only [δ, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1,
              one_mul] using this
          have hρle : ρ ≤ e := by
            by_contra! hρgt
            exact hwnot (hδv ▸ pow_le_pow_right_of_le_one' hπ1.le hρgt)
          exact hδv ▸ pow_le_pow_right_of_le_one' hπ1.le hρle
        have hneg_eq : ((w.1.1 * negOne.1.1 : Kˣ) : K) - 1 = -((w.1.1 : K) + 1) := by
          dsimp only [negOne]
          push_cast
          ring
        rw [hneg_eq, Valuation.map_neg]
        have hpos_e : 0 < valuation K (π : K) ^ e := pow_pos hπ0 e
        have hle_div : valuation K (π : K) ^ e * valuation K ((w.1.1 : K) + 1) ≤
            valuation K (π : K) ^ e * valuation K (π : K) ^ (e + 1) := by
          calc valuation K (π : K) ^ e * valuation K ((w.1.1 : K) + 1)
              ≤ valuation K ((w.1.1 : K) - 1) * valuation K ((w.1.1 : K) + 1) :=
                mul_le_mul' hw_ge_e le_rfl
            _ ≤ valuation K (π : K) ^ (2 * e + 1) := hprod
            _ = valuation K (π : K) ^ e * valuation K (π : K) ^ (e + 1) := by
                rw [← pow_add]; congr 1; omega
        exact le_of_mul_le_mul_left hle_div hpos_e
  -- Step 4: Multiply relative indices along `H_deep ≤ sqHom.ker ≤ G₀`.
  have hindex_H : H_deep.index = Nat.card 𝓀[K] ^ (k + 1) := by
    rw [← Subgroup.relIndex]
    have hrel := relIndex_unitFiltration_add_succ_succ (K := K) (e - k - 1) (k + 1)
    have he1 : (e - k - 1) + (k + 1) + 1 = e + 1 := by omega
    have he2 : (e - k - 1) + 1 = e - k := by omega
    rwa [he1, he2] at hrel
  have hmul_idx := Subgroup.relIndex_mul_index hle_ker
  rw [hrel2, Subgroup.index_ker, hindex_H] at hmul_idx
  have hcard_range : Nat.card sqHom.range =
      Nat.card {q : U₂ ⧸ H₂ // ∃ u : U₂, QuotientGroup.mk u = q ∧ IsSquare (u : Kˣ)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (Set.ext_iff.mp hrange_eq))
  rwa [hcard_range] at hmul_idx

/-- Whenever every element of an ideal `I` maps to the trivial square class,
`eisensteinNormSquareClass` descends to `𝒪[K] ⧸ I`. -/
private def eisensteinNormSquareClassQuotient {t c : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) :
    (𝒪[K] ⧸ I) → Kˣ ⧸ Subgroup.square Kˣ :=
  Quotient.lift (eisensteinNormSquareClass K ht hc) fun v s hvs ↦ by
    have hcm : c ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal c).mpr hc.not_isUnit
    rw [eisensteinNormSquareClass_eq_iff, ← eisensteinNormSquareClass_eq_one_iff ht hc]
    refine hI _ ?_
    have hsub := eisensteinNormCompose_sub_mem_iff ht hcm I v s s
    rw [eisensteinNormCompose_self, sub_zero] at hsub
    exact hsub.mpr ((Submodule.quotientRel_def I).mp hvs)

@[simp]
private theorem eisensteinNormSquareClassQuotient_mk {t c : 𝒪[K]} (ht : t ∈ 𝓂[K])
    (hc : Irreducible c) (I : Ideal 𝒪[K])
    (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) (v : 𝒪[K]) :
    eisensteinNormSquareClassQuotient ht hc I hI (Ideal.Quotient.mk I v) =
      eisensteinNormSquareClass K ht hc v :=
  (rfl)

/-- On any quotient `𝒪[K] ⧸ I` where `I` maps to `1`, the composition bijection makes all nonempty
fibres of `eisensteinNormSquareClassQuotient` equinumerous with the `1`-fibre. -/
private theorem natCard_quotient_eq_mul_natCard_eisenstein_fiber {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (I : Ideal 𝒪[K])
    (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) :
    Nat.card (𝒪[K] ⧸ I) =
      Nat.card (eisensteinNormSquareSubgroup K ht hc) *
        Nat.card {x : 𝒪[K] ⧸ I // eisensteinNormSquareClassQuotient ht hc I hI x = 1} := by
  let F := eisensteinNormSquareClassQuotient ht hc I hI
  have hcm : c ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal c).mpr hc.not_isUnit
  have hrange : Set.range F =
      (eisensteinNormSquareSubgroup K ht hc : Set (Kˣ ⧸ Subgroup.square Kˣ)) := by
    ext q
    simp only [Set.mem_range, SetLike.mem_coe, mem_eisensteinNormSquareSubgroup_iff]
    refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨v, hv⟩ ↦ ⟨Ideal.Quotient.mk I v, hv⟩⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨v, hx⟩
  have hfiber : ∀ y : 𝒪[K] ⧸ I,
      Nonempty ({x : 𝒪[K] ⧸ I // F x = F y} ≃ {x : 𝒪[K] ⧸ I // F x = 1}) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Equiv.subtypeEquiv (eisensteinNormComposeQuotientEquiv ht hcm I s) fun x ↦ ?_⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [F, eisensteinNormComposeQuotientEquiv_mk, eisensteinNormSquareClassQuotient_mk,
      eisensteinNormSquareClass_eq_iff, eisensteinNormSquareClass_eq_one_iff]
  have heq : (𝒪[K] ⧸ I) ≃ Set.range F × {x : 𝒪[K] ⧸ I // F x = 1} :=
    (Equiv.sigmaFiberEquiv (Set.rangeFactorization F)).symm.trans <|
      (Equiv.sigmaCongrRight fun z ↦ by
        let y := z.2.choose
        have hy : F y = z.1 := z.2.choose_spec
        exact (Equiv.subtypeEquivRight fun x ↦ by
          simp [Set.rangeFactorization, Subtype.ext_iff, hy]).trans
          (hfiber y).some).trans
        (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr heq, Nat.card_prod,
    Nat.card_congr (Equiv.subtypeEquivRight (Set.ext_iff.mp hrange))]
  rfl

/-- When `t = c * r₀` with `v(r₀) = v(c) ^ (e - k - 1)` (`k < e`), any `r ∈ 𝒪[K]` for which
`1 - t r + c r²` is a square is divisible by `r₀`, and the quotient `s = r / r₀` satisfies
`s ∈ 𝓂[K]` or `1 - s ∈ 𝓂[K]`. -/
private theorem dvd_and_mem_maximalIdeal_of_eisensteinNormSquareClass_eq_one (h2 : (2 : K) ≠ 0)
    {t c r₀ : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t)
    {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1))
    {r : 𝒪[K]} (hr : eisensteinNormSquareClass K ht hc r = 1) :
    ∃ s : 𝒪[K], r = r₀ * s ∧ (s ∈ 𝓂[K] ∨ 1 - s ∈ 𝓂[K]) := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  obtain ⟨ξ, hξ⟩ := (eisensteinNormSquareClass_eq_one_iff ht hc r).mp hr
  have htK : (t : K) = (c : K) * (r₀ : K) := by
    simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hcr₀.symm
  have hξ2 : ξ ^ 2 - 1 = (c : K) * (r : K) * ((r : K) - (r₀ : K)) := by
    have hξ' : 1 - (c : K) * (r₀ : K) * (r : K) + (c : K) * (r : K) ^ 2 = ξ ^ 2 := by
      simpa only [htK, sq] using hξ
    linear_combination -hξ'
  -- If `v(r₀) < v(r)`, then `v(ξ² - 1) = v(c) ^ (2ρ + 1)` with `ρ < e`, contradicting `ξ²`.
  have hle : valuation K (r : K) ≤ valuation K (r₀ : K) := by
    by_contra! hlt
    have hr0 : r ≠ 0 := by
      intro h0
      simp [h0] at hlt
    obtain ⟨ρ, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hc
    have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    have hrv : valuation K (((u : 𝒪[K]) * c ^ ρ : 𝒪[K]) : K) = valuation K (c : K) ^ ρ := by
      simp [hu1]
    have hρlt : ρ < e - k - 1 := by
      by_contra! hge
      exact (hrv ▸ hvr₀ ▸ hlt).not_ge (pow_le_pow_right_of_le_one' hc1.le hge)
    have hsub : valuation K ((((u : 𝒪[K]) * c ^ ρ : 𝒪[K]) : K) - (r₀ : K)) =
        valuation K (c : K) ^ ρ := by
      rw [(valuation K).map_sub_eq_of_lt_left hlt, hrv]
    apply valuation_sq_sub_one_ne_pow_odd h2 hc (by omega : ρ < e) ξ
    rw [hξ2, map_mul, map_mul, hrv, hsub, ← pow_succ', ← pow_add]
    congr 1
    omega
  -- Write `r = r₀ * s`; if both `s` and `1 - s` were units, `ξ² - 1` would have odd valuation.
  obtain ⟨s, rfl⟩ := (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr hle
  refine ⟨s, rfl, ?_⟩
  by_contra! hnot
  rcases hnot with ⟨hs, h1s⟩
  have hsv : valuation K (s : K) = 1 :=
    le_antisymm ((Valuation.mem_integer_iff _ _).mp s.2)
      (not_lt.mp (mt (valuation K).mem_maximalIdeal_iff.mpr hs))
  have h1sv : valuation K ((s : K) - 1) = 1 := by
    have hv' : valuation K ((1 - s : 𝒪[K]) : K) = 1 :=
      le_antisymm ((Valuation.mem_integer_iff _ _).mp (1 - s).2)
        (not_lt.mp (mt (valuation K).mem_maximalIdeal_iff.mpr h1s))
    have hneg : (s : K) - 1 = -((1 - s : 𝒪[K]) : K) := by push_cast; ring
    rw [hneg, Valuation.map_neg, hv']
  apply valuation_sq_sub_one_ne_pow_odd h2 hc (by omega : e - k - 1 < e) ξ
  have hξ2' : ξ ^ 2 - 1 = (c : K) * (r₀ : K) ^ 2 * (s : K) * ((s : K) - 1) := by
    rw [hξ2]
    push_cast
    ring
  rw [hξ2', map_mul, map_mul, map_mul, map_pow, hvr₀, hsv, h1sv, mul_one, mul_one,
    ← pow_mul, ← pow_succ']
  congr 1
  omega

/-- Counting the Artin–Schreier square locus in `𝒪[K] ⧸ 𝓂[K] ^ (2k + 2)`: when
`v(β) = v(c) ^ (2e - 2k - 1)`, there are `#𝓀[K] ^ (k + 1)` classes `[s]` for which
`1 + β (s² - s)` is a square and `s ∈ 𝓂[K]` or `1 - s ∈ 𝓂[K]`. -/
private theorem natCard_artinSchreier_square_maximalIdeal_quotient (h2 : (2 : K) ≠ 0)
    {c β : 𝒪[K]} (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1))
    (P : (𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2)) → Prop)
    (hP_mk : ∀ s : 𝒪[K], P (Ideal.Quotient.mk _ s) ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))))
    (hP_dichot : ∀ s : 𝒪[K], P (Ideal.Quotient.mk _ s) → s ∈ 𝓂[K] ∨ 1 - s ∈ 𝓂[K]) :
    Nat.card {y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2) // P y} = Nat.card 𝓀[K] ^ (k + 1) := by
  set e := natCastValuation K 2 h2
  let M := 2 * k + 2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hc0 : 0 < valuation K (c : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hc
  have hM_le : 𝓂[K] ^ M ≤ 𝓂[K] := Ideal.pow_le_self (by omega : M ≠ 0)
  let isMax : (𝒪[K] ⧸ 𝓂[K] ^ M) → Prop :=
    Quotient.lift (· ∈ 𝓂[K]) fun s₁ s₂ h ↦ propext <| by
      have hsub : s₁ - s₂ ∈ 𝓂[K] := hM_le ((Submodule.quotientRel_def _).mp h)
      refine ⟨fun hs₁ ↦ ?_, fun hs₂ ↦ ?_⟩
      · have := sub_mem hs₁ hsub
        rwa [sub_sub_cancel] at this
      · have := add_mem hsub hs₂
        rwa [sub_add_cancel] at this
  have isMax_mk : ∀ s : 𝒪[K], isMax (Ideal.Quotient.mk (𝓂[K] ^ M) s) ↔ s ∈ 𝓂[K] :=
    fun _ ↦ Iff.rfl
  have hP_symm : ∀ y : 𝒪[K] ⧸ 𝓂[K] ^ M, P (1 - y) ↔ P y := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ M)), ← map_sub, hP_mk, hP_mk]
    have hid : ((1 - s : 𝒪[K]) : K) ^ 2 - ((1 - s : 𝒪[K]) : K) = (s : K) ^ 2 - (s : K) := by
      push_cast; ring
    rw [hid]
  have hnot_both : ∀ y : 𝒪[K] ⧸ 𝓂[K] ^ M, ¬ (isMax y ∧ isMax (1 - y)) := by
    rintro y ⟨hy, h1y⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hs : s ∈ 𝓂[K] := hy
    have h1s : 1 - s ∈ 𝓂[K] := by
      rwa [← map_one (Ideal.Quotient.mk (𝓂[K] ^ M)), ← map_sub, isMax_mk] at h1y
    have h1 : (1 : 𝒪[K]) ∈ 𝓂[K] := by simpa only [add_sub_cancel] using add_mem hs h1s
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  -- Step 1: Split `{y // P y}` into `s ∈ 𝓂[K]` and `1 - s ∈ 𝓂[K]`, doubling `{x : A // P x.1}`.
  let A := {y : 𝒪[K] ⧸ 𝓂[K] ^ M // isMax y}
  let splitFn : Bool × {x : A // P x.1} → {y : 𝒪[K] ⧸ 𝓂[K] ^ M // P y} :=
    fun ⟨b, x⟩ ↦ if b then ⟨x.1.1, x.2⟩ else ⟨1 - x.1.1, (hP_symm x.1.1).mpr x.2⟩
  have hsplit_bij : Function.Bijective splitFn := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b₁, ⟨⟨y₁, hy₁⟩, hP₁⟩⟩ ⟨b₂, ⟨⟨y₂, hy₂⟩, hP₂⟩⟩ heq
      cases b₁ <;> cases b₂
      · simp only [splitFn, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at heq
        have hy : y₁ = y₂ := by linear_combination -heq
        subst hy
        rfl
      · simp only [splitFn, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at heq
        exact False.elim (hnot_both y₁ ⟨hy₁, heq ▸ hy₂⟩)
      · simp only [splitFn, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at heq
        exact False.elim (hnot_both y₂ ⟨hy₂, heq.symm ▸ hy₁⟩)
      · simp only [splitFn, ↓reduceIte, Subtype.mk.injEq] at heq
        subst heq
        rfl
    · rintro ⟨y, hyP⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      rcases hP_dichot s hyP with hs | h1s
      · exact ⟨⟨true, ⟨⟨Ideal.Quotient.mk _ s, hs⟩, hyP⟩⟩, rfl⟩
      · have h1y : isMax (1 - Ideal.Quotient.mk (𝓂[K] ^ M) s) := by
          rwa [← map_one (Ideal.Quotient.mk (𝓂[K] ^ M)), ← map_sub, isMax_mk]
        refine ⟨⟨false, ⟨⟨1 - Ideal.Quotient.mk _ s, h1y⟩, (hP_symm _).mpr hyP⟩⟩, ?_⟩
        ext
        simp only [splitFn, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel]
  have hcard_split : Nat.card {y : 𝒪[K] ⧸ 𝓂[K] ^ M // P y} = 2 * Nat.card {x : A // P x.1} := by
    rw [← Nat.card_congr (Equiv.ofBijective splitFn hsplit_bij), Nat.card_prod]
    simp
  -- Step 2: `s ↦ s² - s` is a bijection on the finite maximal-ideal locus `A`.
  have : Finite (𝒪[K] ⧸ 𝓂[K] ^ M) := by
    apply Nat.finite_of_card_ne_zero
    rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]
    exact (pow_pos Finite.card_pos M).ne'
  let sqSubQuot : (𝒪[K] ⧸ 𝓂[K] ^ M) → (𝒪[K] ⧸ 𝓂[K] ^ M) :=
    Quotient.lift (fun s ↦ Ideal.Quotient.mk (𝓂[K] ^ M) (s ^ 2 - s)) fun s₁ s₂ h ↦ by
      apply Ideal.Quotient.eq.mpr
      have hsub : s₁ - s₂ ∈ 𝓂[K] ^ M := (Submodule.quotientRel_def _).mp h
      have hid : (s₁ ^ 2 - s₁) - (s₂ ^ 2 - s₂) = (s₁ - s₂) * (s₁ + s₂ - 1) := by ring
      rw [hid]
      exact Ideal.mul_mem_right _ _ hsub
  have sqSubQuot_mk : ∀ s : 𝒪[K],
      sqSubQuot (Ideal.Quotient.mk (𝓂[K] ^ M) s) = Ideal.Quotient.mk (𝓂[K] ^ M) (s ^ 2 - s) :=
    fun _ ↦ rfl
  let sqSubMap : A → A := fun ⟨y, hy⟩ ↦ ⟨sqSubQuot y, by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [sqSubQuot_mk, isMax_mk]
    have hmul_s : s ^ 2 - s = s * (s - 1) := by ring
    rw [hmul_s]
    exact Ideal.mul_mem_right _ _ ((isMax_mk s).mp hy)⟩
  have hsqSub_bij : Function.Bijective sqSubMap := by
    refine Finite.injective_iff_bijective.mp fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ h ↦ ?_
    obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
    obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
    apply Subtype.ext
    apply Ideal.Quotient.eq.mpr
    have hmem : (s₁ ^ 2 - s₁) - (s₂ ^ 2 - s₂) ∈ 𝓂[K] ^ M :=
      Ideal.Quotient.eq.mp (congrArg Subtype.val h)
    have hid : (s₁ ^ 2 - s₁) - (s₂ ^ 2 - s₂) = (s₁ - s₂) * (s₁ + s₂ - 1) := by ring
    rw [hid] at hmem
    have hw : IsUnit (s₁ + s₂ - 1) :=
      isUnit_sub_of_not_isUnit_of_isUnit
        ((IsLocalRing.mem_maximalIdeal _).mp (add_mem hy₁ hy₂)) isUnit_one
    have hcancel := (𝓂[K] ^ M).mul_mem_right (↑hw.unit⁻¹ : 𝒪[K]) hmem
    rwa [mul_assoc, hw.mul_val_inv, mul_one] at hcancel
  -- Step 3: `m ↦ [1 + β m]` is a bijection `A → U(K, 2e - 2k) ⧸ U(K, 2e + 1)`.
  set U₂ := unitFiltration K (2 * e - 2 * k)
  set H₂ := (unitFiltration K (2 * e + 1)).subgroupOf U₂
  have hmemM : ∀ z : 𝒪[K], z ∈ 𝓂[K] ^ M ↔ valuation K (z : K) ≤ valuation K (c : K) ^ M :=
    fun z ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) M) z
  have hbm_lt1 : ∀ m : 𝒪[K], m ∈ 𝓂[K] → valuation K ((β : K) * (m : K)) < 1 := by
    intro m hm
    rw [map_mul, hvβ]
    calc valuation K (c : K) ^ (2 * e - 2 * k - 1) * valuation K (m : K)
        ≤ valuation K (c : K) ^ (2 * e - 2 * k - 1) * valuation K (c : K) :=
          mul_le_mul' le_rfl
            ((Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) m).mp hm)
      _ = valuation K (c : K) ^ (2 * e - 2 * k) := by
          rw [← pow_succ]; congr 1; omega
      _ < 1 := pow_lt_one₀ zero_le hc1 (by omega)
  let mkUnit : ∀ m : 𝒪[K], m ∈ 𝓂[K] → U₂ := fun m hm ↦
    ⟨Units.mk0 (1 + (β : K) * (m : K)) (by
        intro h0
        have hv1 := (valuation K).map_one_add_of_lt (hbm_lt1 m hm)
        simp [h0] at hv1),
      by
        rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc]
        simp only [Units.val_mk0, add_sub_cancel_left, map_mul, hvβ]
        calc valuation K (c : K) ^ (2 * e - 2 * k - 1) * valuation K (m : K)
            ≤ valuation K (c : K) ^ (2 * e - 2 * k - 1) * valuation K (c : K) :=
              mul_le_mul' le_rfl
                ((Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) m).mp hm)
          _ = valuation K (c : K) ^ (2 * e - 2 * k) := by rw [← pow_succ]; congr 1; omega⟩
  have hrel_unit : ∀ (m₁ m₂ : 𝒪[K]) (hm₁ : m₁ ∈ 𝓂[K]) (hm₂ : m₂ ∈ 𝓂[K]),
      (QuotientGroup.mk (s := H₂) (mkUnit m₁ hm₁) = QuotientGroup.mk (s := H₂) (mkUnit m₂ hm₂)) ↔
        m₁ - m₂ ∈ 𝓂[K] ^ M := by
    intro m₁ m₂ hm₁ hm₂
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc, hmemM]
    have hv1 : valuation K (1 + (β : K) * (m₁ : K)) = 1 :=
      (valuation K).map_one_add_of_lt (hbm_lt1 m₁ hm₁)
    have h10 : 1 + (β : K) * (m₁ : K) ≠ 0 := by intro h0; simp [h0] at hv1
    have hval_diff : (((mkUnit m₁ hm₁ : Kˣ)⁻¹ * (mkUnit m₂ hm₂ : Kˣ) : Kˣ) : K) - 1 =
        (β : K) * ((m₂ - m₁ : 𝒪[K]) : K) / (1 + (β : K) * (m₁ : K)) := by
      simp only [mkUnit, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      push_cast
      field_simp
      ring
    have hneg_m : (m₂ - m₁ : 𝒪[K]) = -(m₁ - m₂) := by ring
    rw [hval_diff, map_div₀, hv1, div_one, map_mul, hvβ, hneg_m, Subring.coe_neg,
      Valuation.map_neg]
    have hpos : 0 < valuation K (c : K) ^ (2 * e - 2 * k - 1) := pow_pos hc0 _
    have hexp : valuation K (c : K) ^ (2 * e + 1) =
        valuation K (c : K) ^ (2 * e - 2 * k - 1) * valuation K (c : K) ^ M := by
      rw [← pow_add]; congr 1; omega
    rw [hexp]
    exact ⟨fun h ↦ le_of_mul_le_mul_left h hpos, fun h ↦ mul_le_mul' le_rfl h⟩
  let cosetMap : A → U₂ ⧸ H₂ := fun x ↦
    Quotient.hrecOn x.1 (fun m hm ↦ QuotientGroup.mk (s := H₂) (mkUnit m hm))
      (fun m₁ m₂ h ↦ Function.hfunext
        (propext <| by
          have hsub : m₁ - m₂ ∈ 𝓂[K] := hM_le ((Submodule.quotientRel_def _).mp h)
          exact ⟨fun hm₁ ↦ (isMax_mk m₂).mpr (sub_sub_cancel m₁ m₂ ▸ sub_mem hm₁ hsub),
            fun hm₂ ↦ (isMax_mk m₁).mpr (sub_add_cancel m₁ m₂ ▸ add_mem hsub hm₂)⟩)
        fun hm₁ hm₂ _ ↦ heq_of_eq <|
          (hrel_unit m₁ m₂ hm₁ hm₂).mpr ((Submodule.quotientRel_def _).mp h))
      x.2
  have cosetMap_mk : ∀ (m : 𝒪[K]) (hm : m ∈ 𝓂[K]),
      cosetMap ⟨Ideal.Quotient.mk (𝓂[K] ^ M) m, hm⟩ =
        QuotientGroup.mk (s := H₂) (mkUnit m hm) :=
    fun _ _ ↦ rfl
  have hcoset_bij : Function.Bijective cosetMap := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ heq
      obtain ⟨m₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨m₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      apply Subtype.ext
      exact Ideal.Quotient.eq.mpr ((hrel_unit m₁ m₂ hy₁ hy₂).mp heq)
    · intro q
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
      have hu_le : valuation K (((u : Kˣ) : K) - 1) ≤ valuation K (c : K) ^ (2 * e - 2 * k) :=
        (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mp u.2
      have hβpos : 0 < valuation K (β : K) := hvβ ▸ pow_pos hc0 _
      have hβ0 : (β : K) ≠ 0 := (Valuation.pos_iff _).mp hβpos
      let mK : K := (((u : Kˣ) : K) - 1) / (β : K)
      have hmKv : valuation K mK ≤ valuation K (c : K) := by
        apply le_of_mul_le_mul_left _ hβpos
        have hbm : (β : K) * mK = ((u : Kˣ) : K) - 1 := mul_div_cancel₀ _ hβ0
        have hmul : valuation K (β : K) * valuation K mK = valuation K (((u : Kˣ) : K) - 1) := by
          rw [← map_mul, hbm]
        rw [hmul, hvβ]
        exact hu_le.trans_eq (by rw [← pow_succ]; congr 1; omega)
      let m : 𝒪[K] := ⟨mK, hmKv.trans hc1.le⟩
      have hm_max : m ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.mpr (hmKv.trans_lt hc1)
      refine ⟨⟨Ideal.Quotient.mk _ m, hm_max⟩, ?_⟩
      rw [cosetMap_mk]
      congr 1
      ext
      simp only [mkUnit, Units.val_mk0, m, mK]
      rw [mul_div_cancel₀ _ hβ0, add_sub_cancel]
  -- Step 4: Match `P x.1` with square cosets under `cosetMap ∘ sqSubMap`.
  have hcomp_iff : ∀ x : A, P x.1 ↔
      ∃ u : U₂, QuotientGroup.mk u = cosetMap (sqSubMap x) ∧ IsSquare (u : Kˣ) := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hsm : s ^ 2 - s ∈ 𝓂[K] := (isMax_mk _).mp (sqSubMap ⟨Ideal.Quotient.mk _ s, hy⟩).2
    have hcos_eq : cosetMap (sqSubMap ⟨Ideal.Quotient.mk (𝓂[K] ^ M) s, hy⟩) =
        QuotientGroup.mk (s := H₂) (mkUnit (s ^ 2 - s) hsm) := by
      dsimp only [sqSubMap]
      simp_rw [sqSubQuot_mk]
      exact cosetMap_mk (s ^ 2 - s) hsm
    dsimp only
    rw [hcos_eq, hP_mk]
    constructor
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        have hv1 := (valuation K).map_one_add_of_lt (hbm_lt1 (s ^ 2 - s) hsm)
        have hr' : 1 + (β : K) * ((s ^ 2 - s : 𝒪[K]) : K) = 0 := by
          push_cast
          linear_combination hr
        rw [hr', map_zero] at hv1
        exact zero_ne_one hv1
      refine ⟨mkUnit (s ^ 2 - s) hsm, rfl, ⟨Units.mk0 r hr0, ?_⟩⟩
      ext
      simp only [mkUnit, Units.val_mul, Units.val_mk0]
      push_cast
      exact hr
    · rintro ⟨u, hu_eq, hsq_u⟩
      have hdiff : (u : Kˣ)⁻¹ * (mkUnit (s ^ 2 - s) hsm : Kˣ) ∈
          unitFiltration K (2 * dyadicLevel K h2 + 1) := by
        rw [dyadicLevel_def]
        exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hu_eq)
      have hsq_diff : IsSquare ((u : Kˣ)⁻¹ * (mkUnit (s ^ 2 - s) hsm : Kˣ)) :=
        Subgroup.mem_square.mp (unitFiltration_le_square h2 hdiff)
      have hsq_mk : IsSquare (mkUnit (s ^ 2 - s) hsm : Kˣ) := by
        simpa only [mul_inv_cancel_left] using hsq_u.mul hsq_diff
      obtain ⟨u₀, hu₀⟩ := hsq_mk
      refine ⟨(u₀ : K), ?_⟩
      have hval := congrArg (Units.val : Kˣ → K) hu₀
      simp only [mkUnit, Units.val_mk0, Units.val_mul] at hval
      push_cast at hval
      exact hval
  have heq_card : Nat.card {x : A // P x.1} =
      Nat.card {q : U₂ ⧸ H₂ // ∃ u : U₂, QuotientGroup.mk u = q ∧ IsSquare (u : Kˣ)} :=
    Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ (hcoset_bij.comp hsqSub_bij)) hcomp_iff)
  rw [hcard_split, heq_card]
  exact two_mul_natCard_squareCosets_unitFiltration h2 hk

/-- When `valuation K 2 ≤ valuation K t`, factoring `t = c * r₀` and reducing the `1`-fibre to the
Artin–Schreier square locus gives `#(eisensteinNormSquareSubgroup K ht hc) = #𝓀[K] ^ v_K(2)`. -/
private theorem natCard_eisensteinNormSquareSubgroup_of_le (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hle : valuation K (2 : K) ≤ valuation K (t : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  -- Step 1: Factor `t = c * r₀` with `v(r₀) = v(c) ^ (e - k - 1)` (`k < e`) and set `β = c * r₀²`.
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hc0 : 0 < valuation K (c : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hc
  have hv2 : valuation K (2 : K) = valuation K (c : K) ^ e := by
    simpa only [Nat.cast_ofNat] using valuation_natCast_eq_pow hc 2 h2
  have ht0 : t ≠ 0 := by
    intro h0
    have hpos : 0 < valuation K (2 : K) := (Valuation.pos_iff _).mpr h2
    rw [h0, ZeroMemClass.coe_zero, map_zero] at hle
    exact hpos.not_ge hle
  obtain ⟨m, u_t, hut⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hc
  have hu_t1 : valuation K ((u_t : 𝒪[K]) : K) = 1 :=
    (Valuation.integer.integers (valuation K)).valuation_unit u_t
  have hvt : valuation K (t : K) = valuation K (c : K) ^ m := by
    have := congrArg (fun x : 𝒪[K] ↦ valuation K (x : K)) hut
    simpa only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu_t1, one_mul]
      using this
  have hm1 : 1 ≤ m := by
    by_contra! hm0
    have h1 : valuation K (t : K) = 1 := by simp [hvt, Nat.le_zero.mp (Nat.lt_succ_iff.mp hm0)]
    exact ((valuation K).mem_maximalIdeal_iff.mp ht).ne h1
  have hme : m ≤ e := by
    by_contra! hgt
    exact (hv2 ▸ hvt ▸ hle).not_gt (pow_lt_pow_right_of_lt_one₀ hc0 hc1 hgt)
  set k := e - m
  have hk : k < e := by omega
  have hmk : m = e - k := by omega
  let r₀ : 𝒪[K] := (u_t : 𝒪[K]) * c ^ (e - k - 1)
  have hcr₀ : c * r₀ = t := by
    have hexp : e - k - 1 + 1 = e - k := by omega
    rw [hut, hmk]
    dsimp only [r₀]
    calc c * ((u_t : 𝒪[K]) * c ^ (e - k - 1))
        = (u_t : 𝒪[K]) * (c ^ (e - k - 1) * c) := by ring
      _ = (u_t : 𝒪[K]) * c ^ (e - k) := by rw [← pow_succ, hexp]
  have hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (e - k - 1) := by
    simp [r₀, hu_t1]
  let β : 𝒪[K] := c * r₀ ^ 2
  have hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * e - 2 * k - 1) := by
    simp only [β, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvr₀,
      ← pow_mul, ← pow_succ']
    congr 1
    omega
  -- Step 2: Descend `eisensteinNormSquareClass` to `𝒪[K] ⧸ 𝓂[K] ^ N` at `N = e + k + 1`.
  set N := e + k + 1
  let M := 2 * k + 2
  have hmemN : ∀ z : 𝒪[K], z ∈ 𝓂[K] ^ N ↔ valuation K (z : K) ≤ valuation K (c : K) ^ N :=
    fun z ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) N) z
  have hmemM : ∀ z : 𝒪[K], z ∈ 𝓂[K] ^ M ↔ valuation K (z : K) ≤ valuation K (c : K) ^ M :=
    fun z ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) M) z
  have hIN : ∀ r ∈ 𝓂[K] ^ N, eisensteinNormSquareClass K ht hc r = 1 := by
    intro r hr
    have hrv : valuation K (r : K) ≤ valuation K (c : K) ^ N := (hmemN r).mp hr
    have hu_mem : eisensteinNormUnit K ht hc r ∈ unitFiltration K (2 * dyadicLevel K h2 + 1) := by
      rw [dyadicLevel_def, mem_unitFiltration_succ_valuation (2 * e) _ c hc, map_pow]
      have hdiff : (eisensteinNormUnit K ht hc r : K) - 1 =
          -(t : K) * (r : K) + (c : K) * (r : K) ^ 2 := by
        rw [coe_eisensteinNormUnit]; ring
      rw [hdiff]
      refine ((valuation K).map_add _ _).trans (max_le ?_ ?_)
      · rw [map_mul, Valuation.map_neg, hvt, hmk]
        calc valuation K (c : K) ^ (e - k) * valuation K (r : K)
            ≤ valuation K (c : K) ^ (e - k) * valuation K (c : K) ^ N := mul_le_mul' le_rfl hrv
          _ = valuation K (c : K) ^ (2 * e + 1) := by rw [← pow_add]; congr 1; omega
      · rw [map_mul, map_pow]
        calc valuation K (c : K) * valuation K (r : K) ^ 2
            ≤ valuation K (c : K) * (valuation K (c : K) ^ N) ^ 2 :=
              mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrv 2)
          _ ≤ valuation K (c : K) ^ (2 * e + 1) := by
              rw [← pow_mul, ← pow_succ']
              exact pow_le_pow_right_of_le_one' hc1.le (by omega)
    rw [eisensteinNormSquareClass_def]
    exact (squareClassHom_eq_one_iff _).mpr
      (Subgroup.mem_square.mp (unitFiltration_le_square h2 hu_mem))
  have hprod := natCard_quotient_eq_mul_natCard_eisenstein_fiber ht hc (𝓂[K] ^ N) hIN
  rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow] at hprod
  let F := eisensteinNormSquareClassQuotient ht hc (𝓂[K] ^ N) hIN
  -- Step 3: Identify the `1`-fibre on `𝒪[K] ⧸ 𝓂[K]^N` with the Artin–Schreier locus mod `𝓂[K]^M`.
  have hcong_r₀ : ∀ s₁ s₂ : 𝒪[K], r₀ * s₁ - r₀ * s₂ ∈ 𝓂[K] ^ N ↔ s₁ - s₂ ∈ 𝓂[K] ^ M := by
    intro s₁ s₂
    have hmul_sub : r₀ * s₁ - r₀ * s₂ = r₀ * (s₁ - s₂) := by ring
    have hexpN : valuation K (c : K) ^ N =
        valuation K (c : K) ^ (e - k - 1) * valuation K (c : K) ^ M := by
      rw [← pow_add]; congr 1; omega
    rw [hmemN, hmemM, hmul_sub, Subring.coe_mul, map_mul, hvr₀, hexpN]
    exact ⟨fun h ↦ le_of_mul_le_mul_left h (pow_pos hc0 _), fun h ↦ mul_le_mul' le_rfl h⟩
  let ι : (𝒪[K] ⧸ 𝓂[K] ^ M) → (𝒪[K] ⧸ 𝓂[K] ^ N) :=
    Quotient.lift (fun s ↦ Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s)) fun s₁ s₂ h ↦
      Ideal.Quotient.eq.mpr ((hcong_r₀ s₁ s₂).mpr ((Submodule.quotientRel_def _).mp h))
  have ι_mk : ∀ s : 𝒪[K],
      ι (Ideal.Quotient.mk (𝓂[K] ^ M) s) = Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s) :=
    fun _ ↦ rfl
  have hι_inj : Function.Injective ι := by
    intro y₁ y₂ h
    obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
    obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
    exact Ideal.Quotient.eq.mpr ((hcong_r₀ s₁ s₂).mp (Ideal.Quotient.eq.mp h))
  let ιFiber : {y : 𝒪[K] ⧸ 𝓂[K] ^ M // F (ι y) = 1} → {x : 𝒪[K] ⧸ 𝓂[K] ^ N // F x = 1} :=
    fun y ↦ ⟨ι y.1, y.2⟩
  have hιFiber_bij : Function.Bijective ιFiber := by
    refine ⟨fun y₁ y₂ h ↦ Subtype.ext (hι_inj (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl, -⟩ :=
      dvd_and_mem_maximalIdeal_of_eisensteinNormSquareClass_eq_one h2 ht hc hcr₀ hk hvr₀ hx
    exact ⟨⟨Ideal.Quotient.mk _ s, hx⟩, rfl⟩
  have hfiber_card : Nat.card {x : 𝒪[K] ⧸ 𝓂[K] ^ N // F x = 1} = Nat.card 𝓀[K] ^ (k + 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective ιFiber hιFiber_bij)]
    refine natCard_artinSchreier_square_maximalIdeal_quotient h2 hc hk hvβ (fun y ↦ F (ι y) = 1)
      (fun s ↦ ?_) (fun s hs ↦ ?_)
    · dsimp only [F]
      rw [ι_mk, eisensteinNormSquareClassQuotient_mk, eisensteinNormSquareClass_eq_one_iff]
      have htK : (t : K) = (c : K) * (r₀ : K) := by
        simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hcr₀.symm
      have hid : 1 - (t : K) * ((r₀ * s : 𝒪[K]) : K) + (c : K) * ((r₀ * s : 𝒪[K]) : K) ^ 2 =
          1 + (β : K) * ((s : K) ^ 2 - (s : K)) := by
        simp only [htK, β, Subring.coe_mul, SubmonoidClass.coe_pow]
        ring
      rw [hid]
    · obtain ⟨s', hs', hdich⟩ :=
        dvd_and_mem_maximalIdeal_of_eisensteinNormSquareClass_eq_one h2 ht hc hcr₀ hk hvr₀ hs
      have hr₀0 : r₀ ≠ 0 := by
        intro h0
        simp [h0] at hvr₀
        exact (pow_ne_zero _ hc0.ne') hvr₀.symm
      have hss' : s = s' := mul_left_cancel₀ hr₀0 hs'
      exact hss' ▸ hdich
  have hN_eq : N = e + (k + 1) := by omega
  dsimp only [F] at hfiber_card
  rw [hfiber_card, hN_eq, pow_add] at hprod
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos Finite.card_pos (k + 1)) hprod).symm

/-- **Square-class count for Eisenstein unit norms.** Over a nonarchimedean local field with
`2 ≠ 0`, for any `t ∈ 𝓂[K]` and irreducible `c ∈ 𝒪[K]`, the subgroup
`eisensteinNormSquareSubgroup K ht hc` has cardinality `#𝓀[K] ^ natCastValuation K 2 h2`. -/
theorem natCard_eisensteinNormSquareSubgroup (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rcases lt_or_ge (valuation K (t : K)) (valuation K (2 : K)) with hlt | hge
  · exact natCard_eisensteinNormSquareSubgroup_of_lt h2 ht hc hlt
  · exact natCard_eisensteinNormSquareSubgroup_of_le h2 ht hc hge

/-- Set-cardinality form of `TauCeti.natCard_eisensteinNormSquareSubgroup`: the range of
`eisensteinNormSquareClass K ht hc` has `#𝓀[K] ^ natCastValuation K 2 h2` square classes. -/
theorem ncard_range_eisensteinNormSquareClass (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) :
    (Set.range (eisensteinNormSquareClass K ht hc)).ncard =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rw [← Nat.card_coe_set_eq, ← coe_eisensteinNormSquareSubgroup ht hc]
  exact natCard_eisensteinNormSquareSubgroup h2 ht hc

/-- **Index inside the unit square classes.** Over a nonarchimedean local field with `2 ≠ 0`,
`eisensteinNormSquareSubgroup K ht hc` has index `2` inside `unitSquareClasses K`. -/
theorem relIndex_eisensteinNormSquareSubgroup (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) :
    (eisensteinNormSquareSubgroup K ht hc).relIndex (unitSquareClasses K) = 2 := by
  set H := eisensteinNormSquareSubgroup K ht hc
  let e : H ≃ H.subgroupOf (unitSquareClasses K) :=
    { toFun := fun x ↦ ⟨⟨x.1, eisensteinNormSquareSubgroup_le_unitSquareClasses ht hc x.2⟩, x.2⟩
      invFun := fun y ↦ ⟨y.1.1, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hmul : Nat.card (H.subgroupOf (unitSquareClasses K)) * H.relIndex (unitSquareClasses K) =
      Nat.card (unitSquareClasses K) :=
    Subgroup.card_mul_index (H.subgroupOf (unitSquareClasses K))
  rw [Nat.card_congr e.symm, natCard_eisensteinNormSquareSubgroup h2 ht hc,
    card_unitSquareClasses K h2, mul_comm 2] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Finite.card_pos _) hmul

end TauCeti
