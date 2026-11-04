/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic

import TauCeti.NumberTheory.LocalField.Squares
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Counting Eisenstein unit-norm square classes

Over a valued field `K` and any `t, c ∈ 𝓂[K]`, the composition bijection from
`TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic` descends
`TauCeti.eisensteinNormSquareClass` to any quotient `𝒪[K] ⧸ I` on which `I` maps to `1`
(`TauCeti.eisensteinNormSquareClassQuotient`), giving `TauCeti.eisensteinNormSquareSubgroup K ht hc`
uniform fibres of the size of the `1`-fibre
(`TauCeti.natCard_quotient_eq_mul_natCard_eisenstein_fiber`).

Over a nonarchimedean local field `K` (`2 ≠ 0`) with irreducible `c ∈ 𝒪[K]`, choosing `I = 𝓂[K]^N`
deep enough reduces the subgroup cardinality to the `1`-fibre:
* When `valuation K t < valuation K 2`, completing the square reduces to `t = 0`, where the
  `1`-fibre on `𝒪[K] ⧸ 𝓂[K] ^ v_K(2)` is trivial.
* When `valuation K 2 ≤ valuation K t`, factoring `t = c r₀` and writing `r = r₀ s` converts
  `1 - t r + c r²` into `1 + c r₀² (s² - s)`, counted by
  `TauCeti.natCard_artinSchreier_square_maximalIdeal_quotient`.

Hence `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has cardinality
`#𝓀[K] ^ natCastValuation K 2 h2` (`TauCeti.natCard_eisensteinNormSquareSubgroup`) and index `2`
inside `TauCeti.unitSquareClasses K` (`TauCeti.relIndex_eisensteinNormSquareSubgroup`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

section ValuedField

variable {K : Type*} [Field K] [ValuativeRel K]

/-- Whenever every element of an ideal `I` maps to the trivial square class,
`eisensteinNormSquareClass` descends to `𝒪[K] ⧸ I`. -/
def eisensteinNormSquareClassQuotient {t c : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : c ∈ 𝓂[K])
    (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) :
    (𝒪[K] ⧸ I) → Kˣ ⧸ Subgroup.square Kˣ :=
  Quotient.lift (eisensteinNormSquareClass K ht hc) fun v s hvs ↦ by
    rw [eisensteinNormSquareClass_eq_iff, ← eisensteinNormSquareClass_eq_one_iff ht hc]
    have hsub := eisensteinNormCompose_sub_mem_iff ht hc I v s s
    rw [eisensteinNormCompose_self, sub_zero] at hsub
    exact hI _ (hsub.mpr ((Submodule.quotientRel_def I).mp hvs))

/-- Evaluating `eisensteinNormSquareClassQuotient` on a residue class applies
`eisensteinNormSquareClass`. -/
@[simp]
theorem eisensteinNormSquareClassQuotient_mk {t c : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : c ∈ 𝓂[K])
    (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) (v : 𝒪[K]) :
    eisensteinNormSquareClassQuotient ht hc I hI (Ideal.Quotient.mk I v) =
      eisensteinNormSquareClass K ht hc v := by
  rw [eisensteinNormSquareClassQuotient]; rfl

/-- On any quotient `𝒪[K] ⧸ I` where `I` maps to `1`, the composition bijection makes all nonempty
fibres of `eisensteinNormSquareClassQuotient` equinumerous with the `1`-fibre. -/
theorem natCard_quotient_eq_mul_natCard_eisenstein_fiber {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : c ∈ 𝓂[K]) (I : Ideal 𝒪[K])
    (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) :
    Nat.card (𝒪[K] ⧸ I) =
      Nat.card (eisensteinNormSquareSubgroup K ht hc) *
        Nat.card {x : 𝒪[K] ⧸ I // eisensteinNormSquareClassQuotient ht hc I hI x = 1} := by
  let F := eisensteinNormSquareClassQuotient ht hc I hI
  have hrange : Set.range F =
      (eisensteinNormSquareSubgroup K ht hc : Set (Kˣ ⧸ Subgroup.square Kˣ)) := by
    ext q; simp only [Set.mem_range, SetLike.mem_coe, mem_eisensteinNormSquareSubgroup_iff]
    exact ⟨fun ⟨x, hx⟩ ↦ by
        obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨v, by simpa only [F, eisensteinNormSquareClassQuotient_mk] using hx⟩,
      fun ⟨v, hv⟩ ↦ ⟨Ideal.Quotient.mk I v,
        by simpa only [F, eisensteinNormSquareClassQuotient_mk] using hv⟩⟩
  have hfiber : ∀ y : 𝒪[K] ⧸ I,
      Nonempty ({x : 𝒪[K] ⧸ I // F x = F y} ≃ {x : 𝒪[K] ⧸ I // F x = 1}) := fun y ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Equiv.subtypeEquiv (eisensteinNormComposeQuotientEquiv ht hc I s) fun x ↦ ?_⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [F, eisensteinNormComposeQuotientEquiv_mk, eisensteinNormSquareClassQuotient_mk,
      eisensteinNormSquareClass_eq_iff, eisensteinNormSquareClass_eq_one_iff]
  have heq : (𝒪[K] ⧸ I) ≃ Set.range F × {x : 𝒪[K] ⧸ I // F x = 1} :=
    (Equiv.sigmaFiberEquiv (Set.rangeFactorization F)).symm.trans <|
      (Equiv.sigmaCongrRight fun z ↦
        (Equiv.subtypeEquivRight fun x ↦ by
          simp [Set.rangeFactorization, Subtype.ext_iff, z.2.choose_spec]).trans
          (hfiber z.2.choose).some).trans (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr heq, Nat.card_prod,
    Nat.card_congr (Equiv.subtypeEquivRight fun q ↦ by rw [hrange, SetLike.mem_coe])]

end ValuedField

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- At `t = 0`, `1 + c r²` is a square in `K` if and only if `r ∈ 𝓂[K] ^ v_K(2)`. -/
private theorem eisensteinNormSquareClass_zero_t_eq_one_iff (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : Irreducible c) (r : 𝒪[K]) :
    eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc.mem_maximalIdeal r = 1 ↔
      r ∈ 𝓂[K] ^ natCastValuation K 2 h2 := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 := Valuation.integer.v_irreducible_lt_one hc
  have hmem : ∀ y : 𝒪[K], y ∈ 𝓂[K] ^ e ↔ valuation K (y : K) ≤ valuation K (c : K) ^ e := fun y ↦ by
    rw [← SetLike.mem_coe, hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) e,
      Set.mem_ofPred_eq]
  constructor
  · intro hsq
    by_contra hr
    have hr0 : r ≠ 0 := fun h ↦ hr (h ▸ zero_mem _)
    obtain ⟨ρ, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hc
    have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    have hρlt : ρ < e := not_le.mp fun hge ↦ hr ((hmem _).mpr <| by
      simpa [hu1] using pow_le_pow_right_of_le_one' hc1.le hge)
    obtain ⟨ξ, hξ⟩ :=
      (eisensteinNormSquareClass_eq_one_iff (zero_mem 𝓂[K]) hc.mem_maximalIdeal _).mp hsq
    apply valuation_sq_sub_one_ne_pow_odd h2 hc hρlt ξ
    have hξ2 : ξ ^ 2 - 1 = (c : K) * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) ^ 2 := by
      have hξ' : 1 + (c : K) * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) ^ 2 = ξ ^ 2 := by
        simpa [sq] using hξ
      linear_combination -hξ'
    simp only [hξ2, mul_pow, map_mul, map_pow, hu1, one_pow, one_mul, ← pow_mul, ← pow_succ']
    congr 1; omega
  · intro hr
    have hu_mem : eisensteinNormUnit K (zero_mem 𝓂[K]) hc.mem_maximalIdeal r ∈
        unitFiltration K (2 * dyadicLevel K h2 + 1) := by
      rw [dyadicLevel_def, mem_unitFiltration_succ_valuation (2 * e) _ c hc, map_pow]
      simp only [coe_eisensteinNormUnit, ZeroMemClass.coe_zero, zero_mul, sub_zero,
        add_sub_cancel_left, map_mul, map_pow]
      refine (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le ((hmem r).mp hr) 2)).trans_eq ?_
      rw [← pow_mul, ← pow_succ']; congr 1; omega
    rw [eisensteinNormSquareClass_def]
    exact (squareClassHom_eq_one_iff _).mpr
      (Subgroup.mem_square.mp (unitFiltration_le_square h2 hu_mem))

/-- When `t = 0`, `eisensteinNormSquareSubgroup` has trivial `1`-fibre on `𝒪[K] ⧸ 𝓂[K] ^ v_K(2)`
and therefore has `#𝓀[K] ^ v_K(2)` elements. -/
private theorem natCard_eisensteinNormSquareSubgroup_zero (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : Irreducible c) :
    Nat.card (eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  set e := natCastValuation K 2 h2
  have hIe : ∀ r ∈ 𝓂[K] ^ e,
      eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc.mem_maximalIdeal r = 1 :=
    fun r hr ↦ (eisensteinNormSquareClass_zero_t_eq_one_iff h2 hc r).mpr hr
  have hprod := natCard_quotient_eq_mul_natCard_eisenstein_fiber
    (zero_mem 𝓂[K]) hc.mem_maximalIdeal (𝓂[K] ^ e) hIe
  have h1 : Nat.card {x : 𝒪[K] ⧸ 𝓂[K] ^ e //
      eisensteinNormSquareClassQuotient (zero_mem 𝓂[K]) hc.mem_maximalIdeal _ hIe x = 1} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨0, by rw [← map_zero (Ideal.Quotient.mk _),
      eisensteinNormSquareClassQuotient_mk, eisensteinNormSquareClass_zero]⟩, fun ⟨x, hx⟩ ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [eisensteinNormSquareClassQuotient_mk] at hx
      exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr
        ((eisensteinNormSquareClass_zero_t_eq_one_iff h2 hc r).mp hx))⟩
  rw [h1, mul_one, TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow] at hprod
  exact hprod.symm

/-- When `v(t) < v(2)`, setting `μ = t / 2 ∈ 𝓂[K]` gives an irreducible `c' = c - μ² ∈ 𝒪[K]`. -/
private theorem exists_irreducible_sub_sq_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    ∃ μ c' : 𝒪[K], μ ∈ 𝓂[K] ∧ Irreducible c' ∧ t = 2 * μ ∧ c' = c - μ ^ 2 := by
  have hμlt : valuation K ((t : K) / 2) < 1 := by
    rwa [map_div₀, div_lt_one₀ ((Valuation.pos_iff _).mpr h2)]
  let μ : 𝒪[K] := ⟨(t : K) / 2, hμlt.le⟩
  have hμm : μ ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.mpr hμlt
  have hμc : valuation K (μ : K) ≤ valuation K (c : K) :=
    (Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) μ).mp hμm
  have hμ2lt : valuation K ((μ : K) ^ 2) < valuation K (c : K) := by
    rw [map_pow]
    refine (pow_le_pow_left₀ zero_le hμc 2).trans_lt ?_
    simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀
      (Valuation.integer.v_irreducible_pos hc) (Valuation.integer.v_irreducible_lt_one hc)
      one_lt_two
  have hc'v : valuation K ((c - μ ^ 2 : 𝒪[K]) : K) = valuation K (c : K) := by
    push_cast; exact (valuation K).map_sub_eq_of_lt_left hμ2lt
  exact ⟨μ, c - μ ^ 2, hμm, irreducible_of_valuation_eq hc hc'v,
    Subtype.ext (by push_cast; exact (mul_div_cancel₀ (t : K) h2).symm), rfl⟩

/-- Completing the square when `v(t) < v(2)` identifies `eisensteinNormSquareSubgroup` with the
`t = 0` subgroup at `c' = c - (t / 2)²`. -/
private theorem eisensteinNormSquareSubgroup_eq_zero_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    ∃ (c' : 𝒪[K]) (hc' : Irreducible c'),
      eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal =
        eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc'.mem_maximalIdeal := by
  obtain ⟨μ, c', hμm, hc', htμ, hc'eq⟩ := exists_irreducible_sub_sq_of_lt h2 hc hlt
  refine ⟨c', hc', Subgroup.ext fun q ↦ ?_⟩
  simp only [mem_eisensteinNormSquareSubgroup_iff]
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨u₀, hu₀⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right v _ hμm))
    let w : 𝒪[K] := v * (↑u₀⁻¹ : 𝒪[K])
    have hw : w * (u₀ : 𝒪[K]) = v := by dsimp only [w]; rw [mul_assoc, Units.inv_mul, mul_one]
    have hid : 1 - t * v + c * v ^ 2 = (u₀ : 𝒪[K]) ^ 2 * (1 - 0 * w + c' * w ^ 2) := by
      calc 1 - t * v + c * v ^ 2 = (1 - μ * v) ^ 2 + (c - μ ^ 2) * v ^ 2 := by rw [htμ]; ring
        _ = (u₀ : 𝒪[K]) ^ 2 * (1 - 0 * w + c' * w ^ 2) := by rw [← hu₀, ← hw, hc'eq]; ring
    exact ⟨w, ((eisensteinNormSquareClass_def ht hc.mem_maximalIdeal v).trans <|
      squareClassHom_eq_eisensteinNormSquareClass_of_eq (zero_mem 𝓂[K]) hc'.mem_maximalIdeal
        (u := u₀) (by simpa [coe_eisensteinNormUnit] using congrArg ((↑) : 𝒪[K] → K) hid)).symm⟩
  · rintro ⟨w, rfl⟩
    have hu : IsUnit (1 + μ * w) := by
      simpa only [sub_neg_eq_add] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(μ * w))
        ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_right w _ hμm)))
    obtain ⟨u₀, hu₀⟩ := hu
    let v : 𝒪[K] := w * (↑u₀⁻¹ : 𝒪[K])
    have hv : v * (u₀ : 𝒪[K]) = w := by dsimp only [v]; rw [mul_assoc, Units.inv_mul, mul_one]
    have hid : 1 - 0 * w + c' * w ^ 2 = (u₀ : 𝒪[K]) ^ 2 * (1 - t * v + c * v ^ 2) := by
      calc 1 - 0 * w + c' * w ^ 2
          = (1 + μ * w) ^ 2 - 2 * μ * (1 + μ * w) * w + c * w ^ 2 := by rw [hc'eq]; ring
        _ = (u₀ : 𝒪[K]) ^ 2 * (1 - t * v + c * v ^ 2) := by rw [← hu₀, ← hv, htμ]; ring
    exact ⟨v, ((eisensteinNormSquareClass_def (zero_mem 𝓂[K]) hc'.mem_maximalIdeal w).trans <|
      squareClassHom_eq_eisensteinNormSquareClass_of_eq ht hc.mem_maximalIdeal
        (u := u₀) (by simpa [coe_eisensteinNormUnit] using congrArg ((↑) : 𝒪[K] → K) hid)).symm⟩

private theorem natCard_eisensteinNormSquareSubgroup_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨c', hc', heq⟩ := eisensteinNormSquareSubgroup_eq_zero_of_lt h2 ht hc hlt
  rw [heq]; exact natCard_eisensteinNormSquareSubgroup_zero h2 hc'

/-- When `t = c * r₀` with `v(r₀) = v(c) ^ (e - k - 1)` (`k < e`), any `r ∈ 𝒪[K]` for which
`1 - t r + c r²` is a square is divisible by `r₀`. -/
private theorem dvd_of_eisensteinNormSquareClass_eq_one (h2 : (2 : K) ≠ 0)
    {t c r₀ : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t)
    {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1))
    {r : 𝒪[K]} (hr : eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1) :
    ∃ s : 𝒪[K], r = r₀ * s := by
  set e := natCastValuation K 2 h2
  obtain ⟨ξ, hξ⟩ := (eisensteinNormSquareClass_eq_one_iff ht hc.mem_maximalIdeal r).mp hr
  have hξ2 : ξ ^ 2 - 1 = (c : K) * (r : K) * ((r : K) - (r₀ : K)) := by
    have hξ' : 1 - (c : K) * (r₀ : K) * (r : K) + (c : K) * (r : K) ^ 2 = ξ ^ 2 := by
      simpa only [← hcr₀, Subring.coe_mul, sq] using hξ
    linear_combination -hξ'
  refine (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr (not_lt.mp fun hlt ↦ ?_)
  have hr0 : r ≠ 0 := fun h0 ↦ by simp [h0] at hlt
  obtain ⟨ρ, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hc
  have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
    (Valuation.integer.integers (valuation K)).valuation_unit u
  have hrv : valuation K (((u : 𝒪[K]) * c ^ ρ : 𝒪[K]) : K) = valuation K (c : K) ^ ρ := by
    simp [hu1]
  have hρlt : ρ < e - k - 1 := not_le.mp fun hge ↦
    (hrv ▸ hvr₀ ▸ hlt).not_ge
      (pow_le_pow_right_of_le_one' (Valuation.integer.v_irreducible_lt_one hc).le hge)
  apply valuation_sq_sub_one_ne_pow_odd h2 hc (by omega : ρ < e) ξ
  have hlt' : valuation K (r₀ : K) < valuation K (((u : 𝒪[K]) * c ^ ρ : 𝒪[K]) : K) := hlt
  rw [hξ2, map_mul, map_mul, (valuation K).map_sub_eq_of_lt_left hlt', hrv, ← pow_succ', ← pow_add]
  congr 1; omega

/-- When `v(2) ≤ v(t)` and `t ∈ 𝓂[K]`, factoring out `c` writes `t = c * r₀` with
`v(r₀) = v(c) ^ (e - k - 1)` for some `k < e = v_K(2)`. -/
private theorem exists_factor_of_valuation_two_le (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hle : valuation K (2 : K) ≤ valuation K (t : K)) :
    ∃ (k : ℕ) (r₀ : 𝒪[K]), k < natCastValuation K 2 h2 ∧ c * r₀ = t ∧
      valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1) := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 := Valuation.integer.v_irreducible_lt_one hc
  have ht0 : t ≠ 0 := fun h0 ↦ h2 (by simpa [h0] using hle)
  obtain ⟨m, u_t, hut⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hc
  have hu_t1 : valuation K ((u_t : 𝒪[K]) : K) = 1 :=
    (Valuation.integer.integers (valuation K)).valuation_unit u_t
  have hvt : valuation K (t : K) = valuation K (c : K) ^ m := by
    simpa [hu_t1] using congrArg (fun x : 𝒪[K] ↦ valuation K (x : K)) hut
  have hm1 : 1 ≤ m := not_lt.mp fun hm0 ↦ ((valuation K).mem_maximalIdeal_iff.mp ht).ne
    (by simp [hvt, Nat.lt_one_iff.mp hm0])
  have hme : m ≤ e := not_lt.mp fun hgt ↦
    (valuation_natCast_eq_pow hc 2 h2 ▸ hvt ▸ hle).not_gt
      (pow_lt_pow_right_of_lt_one₀ (Valuation.integer.v_irreducible_pos hc) hc1 hgt)
  refine ⟨e - m, (u_t : 𝒪[K]) * c ^ (m - 1), by omega, ?_,
    by simp [hu_t1, show m - 1 = e - (e - m) - 1 by omega]⟩
  rw [hut, show c * ((u_t : 𝒪[K]) * c ^ (m - 1)) = (u_t : 𝒪[K]) * (c ^ (m - 1) * c) by ring,
    ← pow_succ, show m - 1 + 1 = m by omega]

private theorem eisensteinNormSquareClass_eq_one_of_mem_pow (h2 : (2 : K) ≠ 0) {t c r₀ : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t) {k : ℕ}
    (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1)) :
    ∀ r ∈ 𝓂[K] ^ (natCastValuation K 2 h2 + k + 1),
      eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1 := by
  set e := natCastValuation K 2 h2
  set N := e + k + 1
  have hvt : valuation K (t : K) = valuation K (c : K) ^ (e - k) := by
    rw [← hcr₀, Subring.coe_mul, map_mul, hvr₀, ← pow_succ', show e - k - 1 + 1 = e - k by omega]
  intro r hr
  have hrv : valuation K (r : K) ≤ valuation K (c : K) ^ N :=
    (Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) N) r).mp hr
  have hu_mem : eisensteinNormUnit K ht hc.mem_maximalIdeal r ∈
      unitFiltration K (2 * dyadicLevel K h2 + 1) := by
    rw [dyadicLevel_def, mem_unitFiltration_succ_valuation (2 * e) _ c hc, map_pow,
      show (eisensteinNormUnit K ht hc.mem_maximalIdeal r : K) - 1 =
        -(t : K) * (r : K) + (c : K) * (r : K) ^ 2 by rw [coe_eisensteinNormUnit]; ring]
    refine ((valuation K).map_add _ _).trans (max_le ?_ ?_)
    · rw [map_mul, Valuation.map_neg, hvt]
      refine (mul_le_mul' le_rfl hrv).trans_eq ?_
      rw [← pow_add]; congr 1; omega
    · rw [map_mul, map_pow]
      exact (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrv 2)).trans <| by
        rw [← pow_mul, ← pow_succ']
        exact pow_le_pow_right_of_le_one' (Valuation.integer.v_irreducible_lt_one hc).le (by omega)
  rw [eisensteinNormSquareClass_def]
  exact (squareClassHom_eq_one_iff _).mpr
    (Subgroup.mem_square.mp (unitFiltration_le_square h2 hu_mem))

private theorem natCard_eisenstein_fiber_of_factor (h2 : (2 : K) ≠ 0) {t c r₀ : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t) {k : ℕ}
    (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1))
    (hIN : ∀ r ∈ 𝓂[K] ^ (natCastValuation K 2 h2 + k + 1),
      eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1) :
    Nat.card {x : 𝒪[K] ⧸ 𝓂[K] ^ (natCastValuation K 2 h2 + k + 1) //
      eisensteinNormSquareClassQuotient ht hc.mem_maximalIdeal _ hIN x = 1} =
      Nat.card 𝓀[K] ^ (k + 1) := by
  set e := natCastValuation K 2 h2
  set N := e + k + 1
  let M := 2 * k + 2
  let β : 𝒪[K] := c * r₀ ^ 2
  let F := eisensteinNormSquareClassQuotient ht hc.mem_maximalIdeal (𝓂[K] ^ N) hIN
  have hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * e - 2 * k - 1) := by
    simp only [β, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvr₀,
      ← pow_mul, ← pow_succ']; congr 1; omega
  have hcong_r₀ : ∀ s₁ s₂ : 𝒪[K], r₀ * s₁ - r₀ * s₂ ∈ 𝓂[K] ^ N ↔ s₁ - s₂ ∈ 𝓂[K] ^ M :=
    fun s₁ s₂ ↦ by
      rw [← SetLike.mem_coe, hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) N,
        Set.mem_ofPred_eq, ← SetLike.mem_coe,
        hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) M, Set.mem_ofPred_eq,
        show r₀ * s₁ - r₀ * s₂ = r₀ * (s₁ - s₂) by ring, Subring.coe_mul, map_mul, hvr₀,
        show valuation K (c : K) ^ N = valuation K (c : K) ^ (e - k - 1) * valuation K (c : K) ^ M
          by rw [← pow_add]; congr 1; omega]
      exact ⟨fun h ↦ le_of_mul_le_mul_left h (pow_pos (Valuation.integer.v_irreducible_pos hc) _),
        fun h ↦ mul_le_mul' le_rfl h⟩
  let ι : (𝒪[K] ⧸ 𝓂[K] ^ M) →ₗ[𝒪[K]] (𝒪[K] ⧸ 𝓂[K] ^ N) :=
    (𝓂[K] ^ M).mapQ (𝓂[K] ^ N) (LinearMap.mulLeft 𝒪[K] r₀) fun s hs ↦ by
      simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, sub_zero, mul_zero] using
        (hcong_r₀ s 0).mpr (by simpa only [sub_zero] using hs)
  have hι_mk : ∀ s : 𝒪[K],
      ι (Ideal.Quotient.mk (𝓂[K] ^ M) s) = Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s) := fun s ↦ by
    rw [← Ideal.Quotient.mk_eq_mk, Submodule.mapQ_apply, Ideal.Quotient.mk_eq_mk,
      LinearMap.mulLeft_apply]
  have hF_mk : ∀ s : 𝒪[K], F (ι (Ideal.Quotient.mk (𝓂[K] ^ M) s)) = 1 ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) := fun s ↦ by
    dsimp only [F]
    rw [hι_mk, eisensteinNormSquareClassQuotient_mk, eisensteinNormSquareClass_eq_one_iff,
      show 1 - (t : K) * ((r₀ * s : 𝒪[K]) : K) + (c : K) * ((r₀ * s : 𝒪[K]) : K) ^ 2 =
        1 + (β : K) * ((s : K) ^ 2 - (s : K)) by
        simp only [← hcr₀, β, Subring.coe_mul, SubmonoidClass.coe_pow]; ring]
  let ιFiber : {y : 𝒪[K] ⧸ 𝓂[K] ^ M // ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ M) s = y ∧
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} → {x : 𝒪[K] ⧸ 𝓂[K] ^ N // F x = 1} :=
    fun ⟨y, hy⟩ ↦ ⟨ι y, by obtain ⟨s, rfl, hsq⟩ := hy; exact (hF_mk s).mpr hsq⟩
  refine (Nat.card_congr (Equiv.ofBijective ιFiber ⟨fun ⟨y₁, _⟩ ⟨y₂, _⟩ h ↦ Subtype.ext ?_,
      fun ⟨x, hx⟩ ↦ ?_⟩).symm).trans
    (natCard_artinSchreier_square_maximalIdeal_quotient h2 hc hk hvβ)
  · obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
    obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
    have hι : Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s₁) = Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s₂) := by
      simpa only [ιFiber, hι_mk] using congrArg Subtype.val h
    exact Ideal.Quotient.eq.mpr ((hcong_r₀ s₁ s₂).mp (Ideal.Quotient.eq.mp hι))
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxr : eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1 := by
      simpa only [F, eisensteinNormSquareClassQuotient_mk] using hx
    obtain ⟨s, rfl⟩ := dvd_of_eisensteinNormSquareClass_eq_one h2 ht hc hcr₀ hk hvr₀ hxr
    have hxs : F (ι (Ideal.Quotient.mk (𝓂[K] ^ M) s)) = 1 := by rwa [hι_mk]
    exact ⟨⟨Ideal.Quotient.mk _ s, s, rfl, (hF_mk s).mp hxs⟩, Subtype.ext (hι_mk s)⟩

/-- When `valuation K 2 ≤ valuation K t`, factoring `t = c * r₀` and reducing the `1`-fibre to the
Artin–Schreier square locus gives
`#(eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) = #𝓀[K] ^ v_K(2)`. -/
private theorem natCard_eisensteinNormSquareSubgroup_of_le (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hle : valuation K (2 : K) ≤ valuation K (t : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨k, r₀, hk, hcr₀, hvr₀⟩ := exists_factor_of_valuation_two_le h2 ht hc hle
  have hIN := eisensteinNormSquareClass_eq_one_of_mem_pow h2 ht hc hcr₀ hk hvr₀
  have hprod := natCard_quotient_eq_mul_natCard_eisenstein_fiber
    ht hc.mem_maximalIdeal (𝓂[K] ^ (natCastValuation K 2 h2 + k + 1)) hIN
  rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    natCard_eisenstein_fiber_of_factor h2 ht hc hcr₀ hk hvr₀ hIN,
    Nat.add_assoc, pow_add] at hprod
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos Finite.card_pos (k + 1)) hprod).symm

/-- **Square-class count for Eisenstein unit norms.** Over a nonarchimedean local field with
`2 ≠ 0`, for any `t ∈ 𝓂[K]` and irreducible `c ∈ 𝒪[K]`, the subgroup
`eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has cardinality
`#𝓀[K] ^ natCastValuation K 2 h2`. -/
theorem natCard_eisensteinNormSquareSubgroup (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rcases lt_or_ge (valuation K (t : K)) (valuation K (2 : K)) with hlt | hge
  · exact natCard_eisensteinNormSquareSubgroup_of_lt h2 ht hc hlt
  · exact natCard_eisensteinNormSquareSubgroup_of_le h2 ht hc hge

/-- **Index inside the unit square classes.** Over a nonarchimedean local field with `2 ≠ 0`,
`eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has index `2` inside
`unitSquareClasses K`. -/
theorem relIndex_eisensteinNormSquareSubgroup (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) :
    (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal).relIndex (unitSquareClasses K) = 2 := by
  set H := eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal
  have hmul := Subgroup.card_mul_index (H.subgroupOf (unitSquareClasses K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (eisensteinNormSquareSubgroup_le_unitSquareClasses ht hc.mem_maximalIdeal)).toEquiv,
    natCard_eisensteinNormSquareSubgroup h2 ht hc, card_unitSquareClasses K h2, mul_comm 2] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Finite.card_pos _) hmul

end LocalField

end TauCeti
