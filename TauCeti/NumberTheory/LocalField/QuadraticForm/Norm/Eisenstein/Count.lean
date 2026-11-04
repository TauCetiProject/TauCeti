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

Over a valued field `K` and any `t, c ∈ 𝓂[K]`, the rational composition bijection from
`TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic` descends
`TauCeti.eisensteinNormSquareClass` to any quotient `𝒪[K] ⧸ I` on which `I` maps to `1`
(`TauCeti.eisensteinNormSquareClassQuotient`), giving `TauCeti.eisensteinNormSquareSubgroup K ht hc`
uniform fibres of size equal to the `1`-fibre
(`TauCeti.natCard_quotient_eq_mul_natCard_eisenstein_fiber`).

Over a nonarchimedean local field `K` with `2 ≠ 0` and irreducible `c ∈ 𝒪[K]`, choosing `I = 𝓂[K]^N`
deep enough that `1 - t r + c r²` is a square for every `r ∈ 𝓂[K]^N` reduces the subgroup size to a
single fibre count, showing that `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has
cardinality `#𝓀[K] ^ v_K(2)` (where `v_K(2) = natCastValuation K 2 h2`) and index `2` inside
`TauCeti.unitSquareClasses K`:

* When `valuation K t < valuation K 2` (including `t = 0` and odd residue characteristic),
  completing the square identifies `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` with a
  `t = 0` Eisenstein subgroup whose `1`-fibre on `𝒪[K] ⧸ 𝓂[K] ^ v_K(2)` is trivial.
* When `valuation K 2 ≤ valuation K t`, factoring `t = c r₀` and writing `r = r₀ s` converts
  `1 - t r + c r²` into `1 + c r₀² (s² - s)`, identifying the `1`-fibre with the Artin–Schreier
  square locus counted by `TauCeti.natCard_artinSchreier_square_maximalIdeal_quotient`.

## Main definitions

* `TauCeti.eisensteinNormSquareClassQuotient`: for `t, c ∈ 𝓂[K]`, the descent of
  `eisensteinNormSquareClass K ht hc` to `𝒪[K] ⧸ I` when `I` maps to `1`.

## Main results

* `TauCeti.natCard_quotient_eq_mul_natCard_eisenstein_fiber`: over any valued field with
  `t, c ∈ 𝓂[K]`, `#(𝒪[K] ⧸ I)` factors as `#(eisensteinNormSquareSubgroup K ht hc)` times the
  cardinality of the `1`-fibre.
* `TauCeti.natCard_eisensteinNormSquareSubgroup`: over a nonarchimedean local field with `2 ≠ 0`,
  `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has cardinality
  `#𝓀[K] ^ natCastValuation K 2 h2`.
* `TauCeti.relIndex_eisensteinNormSquareSubgroup`:
  `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has index `2` inside
  `unitSquareClasses K`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

/-! ### Uniform fibres over a general valued field -/

section ValuedField

variable {K : Type*} [Field K] [ValuativeRel K]

/-- Whenever every element of an ideal `I` maps to the trivial square class,
`eisensteinNormSquareClass` descends to `𝒪[K] ⧸ I`. -/
def eisensteinNormSquareClassQuotient {t c : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : c ∈ 𝓂[K])
    (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) :
    (𝒪[K] ⧸ I) → Kˣ ⧸ Subgroup.square Kˣ :=
  Quotient.lift (eisensteinNormSquareClass K ht hc) fun v s hvs ↦ by
    rw [eisensteinNormSquareClass_eq_iff, ← eisensteinNormSquareClass_eq_one_iff ht hc]
    refine hI _ ?_
    have hsub := eisensteinNormCompose_sub_mem_iff ht hc I v s s
    rw [eisensteinNormCompose_self, sub_zero] at hsub
    exact hsub.mpr ((Submodule.quotientRel_def I).mp hvs)

/-- Evaluating `eisensteinNormSquareClassQuotient` on a residue class applies
`eisensteinNormSquareClass`. -/
@[simp]
theorem eisensteinNormSquareClassQuotient_mk {t c : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : c ∈ 𝓂[K])
    (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) (v : 𝒪[K]) :
    eisensteinNormSquareClassQuotient ht hc I hI (Ideal.Quotient.mk I v) =
      eisensteinNormSquareClass K ht hc v := by
  rfl

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
    ext q
    simp only [Set.mem_range, SetLike.mem_coe, mem_eisensteinNormSquareSubgroup_iff]
    refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨v, hv⟩ ↦ ⟨Ideal.Quotient.mk I v, hv⟩⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨v, hx⟩
  have hfiber : ∀ y : 𝒪[K] ⧸ I,
      Nonempty ({x : 𝒪[K] ⧸ I // F x = F y} ≃ {x : 𝒪[K] ⧸ I // F x = 1}) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Equiv.subtypeEquiv (eisensteinNormComposeQuotientEquiv ht hc I s) fun x ↦ ?_⟩
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

end ValuedField

/-! ### Square-class count over a nonarchimedean local field -/

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- At `t = 0`, `1 + c r²` is a square in `K` if and only if `r ∈ 𝓂[K] ^ v_K(2)`. -/
private theorem eisensteinNormSquareClass_zero_t_eq_one_iff (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : Irreducible c) (r : 𝒪[K]) :
    eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc.mem_maximalIdeal r = 1 ↔
      r ∈ 𝓂[K] ^ natCastValuation K 2 h2 := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hmem : ∀ y : 𝒪[K], y ∈ 𝓂[K] ^ e ↔ valuation K (y : K) ≤ valuation K (c : K) ^ e :=
    fun y ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) e) y
  constructor
  · intro hsq
    by_contra hr
    have hr0 : r ≠ 0 := fun h ↦ hr (h ▸ zero_mem _)
    obtain ⟨ρ, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hc
    have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    have hρlt : ρ < e := by
      by_contra! hge
      exact hr ((hmem _).mpr <| by
        simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1, one_mul]
        exact pow_le_pow_right_of_le_one' hc1.le hge)
    obtain ⟨ξ, hξ⟩ :=
      (eisensteinNormSquareClass_eq_one_iff (zero_mem 𝓂[K]) hc.mem_maximalIdeal _).mp hsq
    apply valuation_sq_sub_one_ne_pow_odd h2 hc hρlt ξ
    have hξ2 : ξ ^ 2 - 1 = (c : K) * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) ^ 2 := by
      have hξ' : 1 - 0 * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) +
          (c : K) * (((u : 𝒪[K]) : K) * (c : K) ^ ρ) ^ 2 = ξ ^ 2 := by
        simpa only [sq, ZeroMemClass.coe_zero, Subring.coe_mul, SubmonoidClass.coe_pow] using hξ
      linear_combination -hξ'
    simp only [hξ2, mul_pow, map_mul, map_pow, hu1, one_pow, one_mul, ← pow_mul, ← pow_succ']
    congr 1; omega
  · intro hr
    have hrv : valuation K (r : K) ≤ valuation K (c : K) ^ e := (hmem r).mp hr
    have hu_mem : eisensteinNormUnit K (zero_mem 𝓂[K]) hc.mem_maximalIdeal r ∈
        unitFiltration K (2 * dyadicLevel K h2 + 1) := by
      rw [dyadicLevel_def, mem_unitFiltration_succ_valuation (2 * e) _ c hc, map_pow]
      simp only [coe_eisensteinNormUnit, ZeroMemClass.coe_zero, zero_mul, sub_zero,
        add_sub_cancel_left, map_mul, map_pow]
      calc valuation K (c : K) * valuation K (r : K) ^ 2
          ≤ valuation K (c : K) * (valuation K (c : K) ^ e) ^ 2 :=
            mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrv 2)
        _ = valuation K (c : K) ^ (2 * e + 1) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
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
  have hcard1 : Nat.card {x : 𝒪[K] ⧸ 𝓂[K] ^ e //
      eisensteinNormSquareClassQuotient (zero_mem 𝓂[K]) hc.mem_maximalIdeal _ hIe x = 1} = 1 := by
    refine (Nat.card_congr ⟨fun _ ↦ (), fun _ ↦ ⟨0, by
      rw [← map_zero (Ideal.Quotient.mk _), eisensteinNormSquareClassQuotient_mk,
        eisensteinNormSquareClass_zero]⟩, fun ⟨x, hx⟩ ↦ ?_, fun _ ↦ rfl⟩).trans Nat.card_unique
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr
      ((eisensteinNormSquareClass_zero_t_eq_one_iff h2 hc r).mp hx)).symm
  rw [hcard1, mul_one,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow] at hprod
  exact hprod.symm

/-- When `v(t) < v(2)`, setting `μ = t / 2 ∈ 𝓂[K]` gives an irreducible `c' = c - μ² ∈ 𝒪[K]`. -/
private theorem exists_irreducible_sub_sq_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    ∃ μ c' : 𝒪[K], μ ∈ 𝓂[K] ∧ Irreducible c' ∧
      (t : K) = 2 * (μ : K) ∧ (c' : K) = (c : K) - (μ : K) ^ 2 := by
  have hμlt : valuation K ((t : K) / 2) < 1 := by
    rwa [map_div₀, div_lt_one₀ ((Valuation.pos_iff _).mpr h2)]
  let μ : 𝒪[K] := ⟨(t : K) / 2, hμlt.le⟩
  have hμm : μ ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.mpr hμlt
  let c' : 𝒪[K] := c - μ ^ 2
  have hc'eq : (c' : K) = (c : K) - (μ : K) ^ 2 := by dsimp only [c']; push_cast; rfl
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hc0 : 0 < valuation K (c : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hc
  have hμc : valuation K (μ : K) ≤ valuation K (c : K) :=
    (Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) μ).mp hμm
  have hμ2lt : valuation K ((μ : K) ^ 2) < valuation K (c : K) := by
    rw [map_pow, sq]
    exact (mul_le_mul' hμc hμc).trans_lt
      (by simpa only [one_mul] using mul_lt_mul_of_pos_right hc1 hc0)
  have hc'v : valuation K (c' : K) = valuation K (c : K) := by
    rw [hc'eq]
    exact (valuation K).map_sub_eq_of_lt_left hμ2lt
  exact ⟨μ, c', hμm, irreducible_of_valuation_eq hc hc'v, (mul_div_cancel₀ (t : K) h2).symm, hc'eq⟩

/-- Completing the square when `v(t) < v(2)` identifies `eisensteinNormSquareSubgroup` with the
`t = 0` subgroup at `c' = c - (t / 2)²`. -/
private theorem eisensteinNormSquareSubgroup_eq_zero_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    ∃ (c' : 𝒪[K]) (hc' : Irreducible c'),
      eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal =
        eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc'.mem_maximalIdeal := by
  obtain ⟨μ, c', hμm, hc', htμ, hc'eq⟩ := exists_irreducible_sub_sq_of_lt h2 hc hlt
  refine ⟨c', hc', ?_⟩
  ext q
  simp only [mem_eisensteinNormSquareSubgroup_iff]
  constructor
  · rintro ⟨v, rfl⟩
    have hu : IsUnit (1 - μ * v) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right v _ hμm))
    let w : 𝒪[K] := v * (↑hu.unit⁻¹ : 𝒪[K])
    have hw : (w : K) * ((hu.unit : 𝒪[K]) : K) = (v : K) := by
      simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K)
        (show w * (hu.unit : 𝒪[K]) = v by dsimp [w]; rw [mul_assoc, hu.val_inv_mul, mul_one])
    have huK : ((hu.unit : 𝒪[K]) : K) = 1 - (μ : K) * (v : K) := by
      have h := congrArg ((↑) : 𝒪[K] → K) hu.unit_spec; push_cast at h; exact h
    refine ⟨w, (squareClassHom_eq_eisensteinNormSquareClass_of_eq (zero_mem 𝓂[K])
      hc'.mem_maximalIdeal (b := eisensteinNormUnit K ht hc.mem_maximalIdeal v)
      (u := hu.unit) (v := w) ?_).symm.trans (eisensteinNormSquareClass_def _ _ _).symm⟩
    calc (eisensteinNormUnit K ht hc.mem_maximalIdeal v : K)
        = (1 - (μ : K) * (v : K)) ^ 2 + ((c : K) - (μ : K) ^ 2) * (v : K) ^ 2 := by
          rw [coe_eisensteinNormUnit, htμ]; ring
      _ = ((hu.unit : 𝒪[K]) : K) ^ 2 + (c' : K) * ((w : K) * ((hu.unit : 𝒪[K]) : K)) ^ 2 := by
          rw [hw, huK, hc'eq]
      _ = ((hu.unit : 𝒪[K]) : K) ^ 2 *
          (1 - ((0 : 𝒪[K]) : K) * (w : K) + (c' : K) * (w : K) ^ 2) := by
          rw [ZeroMemClass.coe_zero]; ring
  · rintro ⟨w, rfl⟩
    have hu : IsUnit (1 + μ * w) := by
      simpa only [sub_neg_eq_add] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(μ * w))
        ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_right w _ hμm)))
    let v : 𝒪[K] := w * (↑hu.unit⁻¹ : 𝒪[K])
    have hv : (v : K) * ((hu.unit : 𝒪[K]) : K) = (w : K) := by
      simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K)
        (show v * (hu.unit : 𝒪[K]) = w by dsimp [v]; rw [mul_assoc, hu.val_inv_mul, mul_one])
    have huK : ((hu.unit : 𝒪[K]) : K) = 1 + (μ : K) * (w : K) := by
      have h := congrArg ((↑) : 𝒪[K] → K) hu.unit_spec; push_cast at h; exact h
    refine ⟨v, (squareClassHom_eq_eisensteinNormSquareClass_of_eq ht hc.mem_maximalIdeal
      (b := eisensteinNormUnit K (zero_mem 𝓂[K]) hc'.mem_maximalIdeal w)
      (u := hu.unit) (v := v) ?_).symm.trans (eisensteinNormSquareClass_def _ _ _).symm⟩
    calc (eisensteinNormUnit K (zero_mem 𝓂[K]) hc'.mem_maximalIdeal w : K)
        = (1 + (μ : K) * (w : K)) ^ 2 - 2 * (μ : K) * (1 + (μ : K) * (w : K)) * (w : K) +
            (c : K) * (w : K) ^ 2 := by
          rw [coe_eisensteinNormUnit, ZeroMemClass.coe_zero, hc'eq]; ring
      _ = ((hu.unit : 𝒪[K]) : K) ^ 2 - (t : K) * ((hu.unit : 𝒪[K]) : K) *
            ((v : K) * ((hu.unit : 𝒪[K]) : K)) +
            (c : K) * ((v : K) * ((hu.unit : 𝒪[K]) : K)) ^ 2 := by
          rw [hv, huK, htμ]
      _ = ((hu.unit : 𝒪[K]) : K) ^ 2 *
          (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by ring

private theorem natCard_eisensteinNormSquareSubgroup_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨c', hc', heq⟩ := eisensteinNormSquareSubgroup_eq_zero_of_lt h2 ht hc hlt
  rw [heq]
  exact natCard_eisensteinNormSquareSubgroup_zero h2 hc'

/-- When `t = c * r₀` with `v(r₀) = v(c) ^ (e - k - 1)` (`k < e`), any `r ∈ 𝒪[K]` for which
`1 - t r + c r²` is a square is divisible by `r₀`. -/
private theorem dvd_of_eisensteinNormSquareClass_eq_one (h2 : (2 : K) ≠ 0)
    {t c r₀ : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t)
    {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1))
    {r : 𝒪[K]} (hr : eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1) :
    ∃ s : 𝒪[K], r = r₀ * s := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  obtain ⟨ξ, hξ⟩ := (eisensteinNormSquareClass_eq_one_iff ht hc.mem_maximalIdeal r).mp hr
  have htK : (t : K) = (c : K) * (r₀ : K) := by
    simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hcr₀.symm
  have hξ2 : ξ ^ 2 - 1 = (c : K) * (r : K) * ((r : K) - (r₀ : K)) := by
    have hξ' : 1 - (c : K) * (r₀ : K) * (r : K) + (c : K) * (r : K) ^ 2 = ξ ^ 2 := by
      simpa only [htK, sq] using hξ
    linear_combination -hξ'
  have hle : valuation K (r : K) ≤ valuation K (r₀ : K) := by
    by_contra! hlt
    have hr0 : r ≠ 0 := fun h0 ↦ by simp [h0] at hlt
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
    congr 1; omega
  exact (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr hle

/-- When `v(2) ≤ v(t)` and `t ∈ 𝓂[K]`, factoring out `c` writes `t = c * r₀` with
`v(r₀) = v(c) ^ (e - k - 1)` for some `k < e = v_K(2)`. -/
private theorem exists_factor_of_valuation_two_le (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hle : valuation K (2 : K) ≤ valuation K (t : K)) :
    ∃ (k : ℕ) (r₀ : 𝒪[K]), k < natCastValuation K 2 h2 ∧ c * r₀ = t ∧
      valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1) := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hc0 : 0 < valuation K (c : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hc
  have hv2 : valuation K (2 : K) = valuation K (c : K) ^ e := by
    simpa only [Nat.cast_ofNat] using valuation_natCast_eq_pow hc 2 h2
  have ht0 : t ≠ 0 := fun h0 ↦ by
    rw [h0, ZeroMemClass.coe_zero, map_zero] at hle
    exact ((Valuation.pos_iff _).mpr h2).not_ge hle
  obtain ⟨m, u_t, hut⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hc
  have hu_t1 : valuation K ((u_t : 𝒪[K]) : K) = 1 :=
    (Valuation.integer.integers (valuation K)).valuation_unit u_t
  have hvt : valuation K (t : K) = valuation K (c : K) ^ m := by
    simpa only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu_t1, one_mul] using
      congrArg (fun x : 𝒪[K] ↦ valuation K (x : K)) hut
  have hm1 : 1 ≤ m := by
    by_contra! hm0
    exact ((valuation K).mem_maximalIdeal_iff.mp ht).ne
      (by simp [hvt, Nat.le_zero.mp (Nat.lt_succ_iff.mp hm0)])
  have hme : m ≤ e := by
    by_contra! hgt
    exact (hv2 ▸ hvt ▸ hle).not_gt (pow_lt_pow_right_of_lt_one₀ hc0 hc1 hgt)
  refine ⟨e - m, (u_t : 𝒪[K]) * c ^ (m - 1), by omega, ?_, ?_⟩
  · rw [hut, show c * ((u_t : 𝒪[K]) * c ^ (m - 1)) = (u_t : 𝒪[K]) * (c ^ (m - 1) * c) by ring,
      ← pow_succ, show m - 1 + 1 = m by omega]
  · simp [hu_t1, show m - 1 = e - (e - m) - 1 by omega]

private theorem eisensteinNormSquareClass_eq_one_of_mem_pow (h2 : (2 : K) ≠ 0) {t c r₀ : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t) {k : ℕ}
    (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1)) :
    ∀ r ∈ 𝓂[K] ^ (natCastValuation K 2 h2 + k + 1),
      eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1 := by
  set e := natCastValuation K 2 h2
  set N := e + k + 1
  have hc1 : valuation K (c : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hc
  have hvt : valuation K (t : K) = valuation K (c : K) ^ (e - k) := by
    have htK : (t : K) = (c : K) * (r₀ : K) := by
      simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hcr₀.symm
    rw [htK, map_mul, hvr₀, ← pow_succ', show e - k - 1 + 1 = e - k by omega]
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
      exact (mul_le_mul' le_rfl hrv).trans_eq (by rw [← pow_add]; congr 1; omega)
    · rw [map_mul, map_pow]
      exact (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrv 2)).trans <| by
        rw [← pow_mul, ← pow_succ']
        exact pow_le_pow_right_of_le_one' hc1.le (by omega)
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
  have hc0 : 0 < valuation K (c : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hc
  have hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * e - 2 * k - 1) := by
    simp only [β, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvr₀,
      ← pow_mul, ← pow_succ']
    congr 1; omega
  have hmemN : ∀ z : 𝒪[K], z ∈ 𝓂[K] ^ N ↔ valuation K (z : K) ≤ valuation K (c : K) ^ N :=
    fun z ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) N) z
  have hmemM : ∀ z : 𝒪[K], z ∈ 𝓂[K] ^ M ↔ valuation K (z : K) ≤ valuation K (c : K) ^ M :=
    fun z ↦ Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) M) z
  have hcong_r₀ : ∀ s₁ s₂ : 𝒪[K], r₀ * s₁ - r₀ * s₂ ∈ 𝓂[K] ^ N ↔ s₁ - s₂ ∈ 𝓂[K] ^ M := by
    intro s₁ s₂
    rw [hmemN, hmemM, show r₀ * s₁ - r₀ * s₂ = r₀ * (s₁ - s₂) by ring, Subring.coe_mul,
      map_mul, hvr₀, show valuation K (c : K) ^ N =
        valuation K (c : K) ^ (e - k - 1) * valuation K (c : K) ^ M by
        rw [← pow_add]; congr 1; omega]
    exact ⟨fun h ↦ le_of_mul_le_mul_left h (pow_pos hc0 _), fun h ↦ mul_le_mul' le_rfl h⟩
  let ι : (𝒪[K] ⧸ 𝓂[K] ^ M) → (𝒪[K] ⧸ 𝓂[K] ^ N) :=
    Quotient.lift (fun s ↦ Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s)) fun s₁ s₂ h ↦
      Ideal.Quotient.eq.mpr ((hcong_r₀ s₁ s₂).mpr ((Submodule.quotientRel_def _).mp h))
  have hF_mk : ∀ s : 𝒪[K], F (ι (Ideal.Quotient.mk (𝓂[K] ^ M) s)) = 1 ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) := fun s ↦ by
    have htK : (t : K) = (c : K) * (r₀ : K) := by
      simpa only [Subring.coe_mul] using congrArg ((↑) : 𝒪[K] → K) hcr₀.symm
    change eisensteinNormSquareClass K ht hc.mem_maximalIdeal (r₀ * s) = 1 ↔ _
    rw [eisensteinNormSquareClass_eq_one_iff,
      show 1 - (t : K) * ((r₀ * s : 𝒪[K]) : K) + (c : K) * ((r₀ * s : 𝒪[K]) : K) ^ 2 =
        1 + (β : K) * ((s : K) ^ 2 - (s : K)) by
        simp only [htK, β, Subring.coe_mul, SubmonoidClass.coe_pow]; ring]
  let ιFiber : {y : 𝒪[K] ⧸ 𝓂[K] ^ M // ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ M) s = y ∧
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} → {x : 𝒪[K] ⧸ 𝓂[K] ^ N // F x = 1} :=
    fun ⟨y, hy⟩ ↦ ⟨ι y, by obtain ⟨s, rfl, hsq⟩ := hy; exact (hF_mk s).mpr hsq⟩
  have hbij : Function.Bijective ιFiber := by
    refine ⟨fun ⟨y₁, _⟩ ⟨y₂, _⟩ h ↦ Subtype.ext ?_, fun ⟨x, hx⟩ ↦ ?_⟩
    · obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      exact Ideal.Quotient.eq.mpr ((hcong_r₀ s₁ s₂).mp
        (Ideal.Quotient.eq.mp (congrArg Subtype.val h)))
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨s, rfl⟩ := dvd_of_eisensteinNormSquareClass_eq_one h2 ht hc hcr₀ hk hvr₀ hx
      exact ⟨⟨Ideal.Quotient.mk _ s, s, rfl, (hF_mk s).mp hx⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective ιFiber hbij)]
  exact natCard_artinSchreier_square_maximalIdeal_quotient h2 hc hk hvβ

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
  have hmul : Nat.card (H.subgroupOf (unitSquareClasses K)) * H.relIndex (unitSquareClasses K) =
      Nat.card (unitSquareClasses K) :=
    Subgroup.card_mul_index (H.subgroupOf (unitSquareClasses K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (eisensteinNormSquareSubgroup_le_unitSquareClasses ht hc.mem_maximalIdeal)).toEquiv,
    natCard_eisensteinNormSquareSubgroup h2 ht hc, card_unitSquareClasses K h2, mul_comm 2] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Finite.card_pos _) hmul

end LocalField

end TauCeti
