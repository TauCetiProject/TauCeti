/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic

import Mathlib.Data.Set.Card
import TauCeti.NumberTheory.LocalField.IntegerRing.Quotient
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClass
import TauCeti.NumberTheory.LocalField.Squares
import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Square
import TauCeti.NumberTheory.LocalField.UnitFiltration.Quotient
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Valuation.Irreducible

/-!
# Counting Eisenstein unit-norm square classes

Over a valued field `K` and `t, c ∈ 𝓂[K]`, the composition bijection descends
`TauCeti.eisensteinNormSquareClass` to any `𝒪[K] ⧸ I` where `I` maps to `1`
(`TauCeti.eisensteinNormSquareClassQuotient`), giving `TauCeti.eisensteinNormSquareSubgroup K ht hc`
uniform `1`-fibre size (`TauCeti.natCard_quotient_eq_mul_natCard_eisenstein_fiber`).

Over a nonarchimedean local field `K` (`2 ≠ 0`) with irreducible `c ∈ 𝒪[K]`, choosing `I = 𝓂[K]^N`
deep enough shows `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has
`#𝓀[K] ^ natCastValuation K 2 h2` elements (`TauCeti.natCard_eisensteinNormSquareSubgroup`) and
index `2` in `TauCeti.unitSquareClasses K` (`TauCeti.relIndex_eisensteinNormSquareSubgroup`):
* For `valuation K t < valuation K 2`, completing the square reduces to `t = 0`, where
  `1 + c v² = 1 - (-c) v²` reduces to `TauCeti.ncard_range_uniformizerNormSquareClass`.
* For `valuation K 2 ≤ valuation K t`, factoring `t = c r₀` and writing `r = r₀ s` turns
  `1 - t r + c r²` into `1 + c r₀² (s² - s)`, splitting around `s = 0, 1`
  (`TauCeti.mem_maximalIdeal_or_one_sub_mem_of_isSquare_one_add_mul_sq_sub`) and counting the
  Artin–Schreier square locus (`TauCeti.natCard_artinSchreier_square_maximalIdeal_quotient`).

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

/-- Evaluating `eisensteinNormSquareClassQuotient` on `[v]` gives `eisensteinNormSquareClass`. -/
@[simp]
theorem eisensteinNormSquareClassQuotient_mk {t c : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : c ∈ 𝓂[K])
    (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) (v : 𝒪[K]) :
    eisensteinNormSquareClassQuotient ht hc I hI (Ideal.Quotient.mk I v) =
      eisensteinNormSquareClass K ht hc v := by rw [eisensteinNormSquareClassQuotient]; rfl

/-- On any quotient `𝒪[K] ⧸ I` where `I` maps to `1`, the composition bijection makes all nonempty
fibres of `eisensteinNormSquareClassQuotient` equinumerous with the `1`-fibre. -/
theorem natCard_quotient_eq_mul_natCard_eisenstein_fiber {t c : 𝒪[K]} (ht : t ∈ 𝓂[K])
    (hc : c ∈ 𝓂[K]) (I : Ideal 𝒪[K]) (hI : ∀ r ∈ I, eisensteinNormSquareClass K ht hc r = 1) :
    Nat.card (𝒪[K] ⧸ I) = Nat.card (eisensteinNormSquareSubgroup K ht hc) *
      Nat.card {x : 𝒪[K] ⧸ I // eisensteinNormSquareClassQuotient ht hc I hI x = 1} := by
  let F := eisensteinNormSquareClassQuotient ht hc I hI
  have hrange : Set.range F =
      (eisensteinNormSquareSubgroup K ht hc : Set (Kˣ ⧸ Subgroup.square Kˣ)) := by
    ext q; simp only [Set.mem_range, SetLike.mem_coe, mem_eisensteinNormSquareSubgroup_iff]
    exact ⟨fun ⟨x, hx⟩ ↦ by
        obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨v, by simpa only [F, eisensteinNormSquareClassQuotient_mk] using hx⟩,
      fun ⟨v, hv⟩ ↦ ⟨Ideal.Quotient.mk I v, by simpa only [F, eisensteinNormSquareClassQuotient_mk]
        using hv⟩⟩
  have hfiber : ∀ y : 𝒪[K] ⧸ I,
      Nonempty ({x : 𝒪[K] ⧸ I // F x = F y} ≃ {x : 𝒪[K] ⧸ I // F x = 1}) := fun y ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Equiv.subtypeEquiv (eisensteinNormComposeQuotientEquiv ht hc I s) fun x ↦ ?_⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [F, eisensteinNormComposeQuotientEquiv_mk, eisensteinNormSquareClassQuotient_mk,
      eisensteinNormSquareClass_eq_iff, eisensteinNormSquareClass_eq_one_iff]
  have heq : (𝒪[K] ⧸ I) ≃ Set.range F × {x : 𝒪[K] ⧸ I // F x = 1} :=
    (Equiv.sigmaFiberEquiv (Set.rangeFactorization F)).symm.trans <|
      (Equiv.sigmaCongrRight fun z ↦ (Equiv.subtypeEquivRight fun x ↦ by
          simp [Set.rangeFactorization, Subtype.ext_iff, z.2.choose_spec]).trans
        (hfiber z.2.choose).some).trans (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr heq, Nat.card_prod,
    Nat.card_congr (Equiv.subtypeEquivRight fun q ↦ by rw [hrange, SetLike.mem_coe])]

private theorem eisensteinNormSquareSubgroup_le_of_eq {t₁ c₁ t₂ c₂ μ : 𝒪[K]}
    (ht₁ : t₁ ∈ 𝓂[K]) (hc₁ : c₁ ∈ 𝓂[K]) (ht₂ : t₂ ∈ 𝓂[K]) (hc₂ : c₂ ∈ 𝓂[K]) (hμ : μ ∈ 𝓂[K])
    (ht : t₁ = t₂ + 2 * μ) (hc : c₁ = c₂ + t₂ * μ + μ ^ 2) :
    eisensteinNormSquareSubgroup K ht₁ hc₁ ≤ eisensteinNormSquareSubgroup K ht₂ hc₂ := by
  intro q hq
  obtain ⟨v, rfl⟩ := (mem_eisensteinNormSquareSubgroup_iff ht₁ hc₁ q).mp hq
  obtain ⟨u₀, hu₀⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right v _ hμ))
  let w : 𝒪[K] := v * (↑u₀⁻¹ : 𝒪[K])
  have hw : w * (u₀ : 𝒪[K]) = v := by dsimp only [w]; rw [mul_assoc, Units.inv_mul, mul_one]
  have hid : 1 - t₁ * v + c₁ * v ^ 2 = (u₀ : 𝒪[K]) ^ 2 * (1 - t₂ * w + c₂ * w ^ 2) := by
    calc 1 - t₁ * v + c₁ * v ^ 2
        = (1 - μ * v) ^ 2 - t₂ * (1 - μ * v) * v + c₂ * v ^ 2 := by rw [ht, hc]; ring
      _ = (u₀ : 𝒪[K]) ^ 2 * (1 - t₂ * w + c₂ * w ^ 2) := by rw [← hu₀, ← hw]; ring
  exact (mem_eisensteinNormSquareSubgroup_iff ht₂ hc₂ _).mpr ⟨w,
    ((eisensteinNormSquareClass_def ht₁ hc₁ v).trans <|
      squareClassHom_eq_eisensteinNormSquareClass_of_eq ht₂ hc₂ (u := u₀)
        (by simpa [coe_eisensteinNormUnit] using congrArg ((↑) : 𝒪[K] → K) hid)).symm⟩

end ValuedField

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Below `2 v_K(2)`, if `v(β) = v(c) ^ (2e - 2k - 1)` (`k < e = v_K(2)`) and `1 + β (s² - s)` is a
square in `K`, then either `s ∈ 𝓂[K]` or `1 - s ∈ 𝓂[K]`. -/
theorem mem_maximalIdeal_or_one_sub_mem_of_isSquare_one_add_mul_sq_sub (h2 : (2 : K) ≠ 0)
    {c β : 𝒪[K]} (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1))
    {s : 𝒪[K]} (hs : IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))) :
    s ∈ 𝓂[K] ∨ 1 - s ∈ 𝓂[K] := by
  by_contra! hnot
  obtain ⟨ξ, hξ⟩ := hs
  have hsv : valuation K (s : K) = 1 := le_antisymm ((Valuation.mem_integer_iff _ _).mp s.2)
    (not_lt.mp (mt (valuation K).mem_maximalIdeal_iff.mpr hnot.1))
  have h1sv : valuation K ((s : K) - 1) = 1 := by
    rw [show (s : K) - 1 = -((1 - s : 𝒪[K]) : K) by push_cast; ring, Valuation.map_neg]
    exact le_antisymm ((Valuation.mem_integer_iff _ _).mp (1 - s).2)
      (not_lt.mp (mt (valuation K).mem_maximalIdeal_iff.mpr hnot.2))
  apply valuation_sq_sub_one_ne_pow_odd h2 hc (by omega : natCastValuation K 2 h2 - k - 1 < _) ξ
  rw [show ξ ^ 2 - 1 = (β : K) * (s : K) * ((s : K) - 1) by rw [← sq] at hξ; linear_combination -hξ,
    map_mul, map_mul, hvβ, hsv, h1sv, mul_one, mul_one]
  congr 1; omega

private theorem natCard_subtype_eq_two_mul_of_symm (m : ℕ)
    {P : (𝒪[K] ⧸ 𝓂[K] ^ (m + 1)) → Prop} (hsym : ∀ y, P (1 - y) ↔ P y)
    (hdich : ∀ y, P y →
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0 ∨
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) (1 - y) = 0) :
    Nat.card {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) // P y} =
      2 * Nat.card {x : {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} // P x.1} := by
  let fac := Ideal.Quotient.factor (Ideal.pow_le_self (I := 𝓂[K]) (Nat.succ_ne_zero m))
  have : Nontrivial (𝒪[K] ⧸ 𝓂[K]) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
  have hnot_both : ∀ y, ¬ (fac y = 0 ∧ fac (1 - y) = 0) := fun y ⟨hy, h1y⟩ ↦ by
    rw [map_sub, map_one, hy, sub_zero] at h1y; exact one_ne_zero h1y
  let splitFn : Bool × {x : {y // fac y = 0} // P x.1} → {y // P y} :=
    fun ⟨b, x⟩ ↦ if b then ⟨x.1.1, x.2⟩ else ⟨1 - x.1.1, (hsym x.1.1).mpr x.2⟩
  refine (Nat.card_congr (Equiv.ofBijective splitFn ⟨?_, fun ⟨y, hyP⟩ ↦ ?_⟩).symm).trans
    (by rw [Nat.card_prod]; simp [fac])
  · rintro ⟨b₁, ⟨⟨y₁, hy₁⟩, _⟩⟩ ⟨b₂, ⟨⟨y₂, hy₂⟩, _⟩⟩ heq
    cases b₁ <;> cases b₂ <;>
      simp only [splitFn, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at heq
    · cases (by linear_combination -heq : y₁ = y₂); rfl
    · exact (hnot_both y₁ ⟨hy₁, heq ▸ hy₂⟩).elim
    · exact (hnot_both y₂ ⟨hy₂, heq.symm ▸ hy₁⟩).elim
    · subst heq; rfl
  · rcases hdich y hyP with hy0 | h1y0
    · exact ⟨⟨true, ⟨⟨y, hy0⟩, hyP⟩⟩, rfl⟩
    · exact ⟨⟨false, ⟨⟨1 - y, h1y0⟩, (hsym y).mpr hyP⟩⟩, by ext; simp [splitFn]⟩

private theorem isSquare_one_add_mul_sq_sub_congr (h2 : (2 : K) ≠ 0) {c β : 𝒪[K]}
    (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1))
    {s₁ s₂ : 𝒪[K]} (h : s₁ - s₂ ∈ 𝓂[K] ^ (2 * k + 2)) :
    IsSquare (1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K))) ↔
      IsSquare (1 + (β : K) * ((s₂ : K) ^ 2 - (s₂ : K))) := by
  have hc1 : valuation K (c : K) < 1 := Valuation.integer.v_irreducible_lt_one hc
  have hlt : ∀ s : 𝒪[K], valuation K ((β : K) * ((s : K) ^ 2 - (s : K))) < 1 := fun s ↦ by
    rw [map_mul, hvβ]
    exact (mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).mp
      (sub_mem (pow_mem s.2 2) s.2))).trans_lt (by simpa using pow_lt_one₀ zero_le hc1 (by omega))
  let u : 𝒪[K] → Kˣ := fun s ↦ Units.mk0 (1 + (β : K) * ((s : K) ^ 2 - (s : K))) fun h0 ↦ by
    simpa [h0] using (valuation K).map_one_add_of_lt (hlt s)
  have hdiff : (u s₁)⁻¹ * u s₂ ∈ unitFiltration K (2 * dyadicLevel K h2 + 1) := by
    rw [dyadicLevel_def, mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc]
    have hd0 : 1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K)) ≠ 0 := (u s₁).ne_zero
    have hid : (((u s₁)⁻¹ * u s₂ : Kˣ) : K) - 1 =
        (β : K) * (((s₂ ^ 2 - s₂) - (s₁ ^ 2 - s₁) : 𝒪[K]) : K) /
          (1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K))) := by
      simp only [u, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [eq_div_iff hd0, sub_mul, inv_mul_eq_div, div_mul_cancel₀ _ hd0, one_mul]; push_cast; ring
    have hmem : (s₂ ^ 2 - s₂) - (s₁ ^ 2 - s₁) ∈ 𝓂[K] ^ (2 * k + 2) := by
      rw [show (s₂ ^ 2 - s₂) - (s₁ ^ 2 - s₁) = -(s₁ - s₂) * (s₁ + s₂ - 1) by ring]
      exact Ideal.mul_mem_right _ _ (neg_mem h)
    rw [hid, map_div₀, (valuation K).map_one_add_of_lt (hlt s₁), div_one, map_mul, hvβ]
    refine (mul_le_mul' le_rfl ((mem_maximalIdeal_pow_iff_valuation_le hc _).mp hmem)).trans_eq ?_
    rw [← pow_add]; congr 1; omega
  have hu (s : 𝒪[K]) : ((u s : Kˣ) : K) = 1 + (β : K) * ((s : K) ^ 2 - (s : K)) := Units.val_mk0 _
  have hsq := Subgroup.mem_square.mp (unitFiltration_le_square h2 hdiff)
  rw [← hu s₁, ← hu s₂, Units.isSquare_coe_iff, Units.isSquare_coe_iff]
  exact ⟨fun h1 ↦ by simpa only [mul_inv_cancel_left] using h1.mul hsq,
    fun h2' ↦ by simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h2'.mul hsq.inv⟩

private theorem exists_mk_isSquare_one_add_mul_sq_sub_iff (h2 : (2 : K) ≠ 0) {c β : 𝒪[K]}
    (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1))
    (s : 𝒪[K]) :
    (∃ s' : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s' =
        Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s ∧
      IsSquare (1 + (β : K) * ((s' : K) ^ 2 - (s' : K)))) ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) :=
  ⟨fun ⟨_, hs', hsq⟩ ↦ (isSquare_one_add_mul_sq_sub_congr h2 hc hk hvβ
    (Ideal.Quotient.eq.mp hs')).mp hsq, fun hsq ↦ ⟨s, rfl, hsq⟩⟩

private def artinSchreierMaximalIdealSquareEquiv (h2 : (2 : K) ≠ 0) {c β : 𝒪[K]}
    (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1)) :
    {x : {y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2) //
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero (2 * k + 1))) y = 0} //
      ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s = x.1 ∧
        IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} ≃
    {q : unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k) ⧸
        (unitFiltration K (2 * natCastValuation K 2 h2 + 1)).subgroupOf
          (unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k)) //
      ∃ u : unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k),
        QuotientGroup.mk u = q ∧ IsSquare (u : Kˣ)} := by
  let e := natCastValuation K 2 h2
  let E := (artinSchreierMaximalIdealQuotientEquiv K (2 * k + 1)).trans
    (maximalIdealQuotientEquivUnitFiltrationQuotient hc hvβ (2 * k + 1)
      (n₁ := 2 * e - 2 * k) (n₂ := 2 * e + 1) (by omega) (by omega))
  refine Equiv.subtypeEquiv E fun ⟨y, hy⟩ ↦ ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hs : s ∈ 𝓂[K] := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy)
  have hsm : s ^ 2 - s ∈ 𝓂[K] := by
    rw [show s ^ 2 - s = s * (s - 1) by ring]; exact Ideal.mul_mem_right _ _ hs
  have hsm0 : Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero (2 * k + 1)))
      (Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) (s ^ 2 - s)) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hsm
  let u_s : unitFiltration K (2 * e - 2 * k) := mkScaledUnit hc hvβ (by omega) hsm
  have hE_eq : E ⟨Ideal.Quotient.mk _ s, hy⟩ = QuotientGroup.mk u_s := by
    dsimp only [E, Equiv.trans_apply]
    rw [show artinSchreierMaximalIdealQuotientEquiv K (2 * k + 1) ⟨Ideal.Quotient.mk _ s, hy⟩ =
        ⟨Ideal.Quotient.mk _ (s ^ 2 - s), hsm0⟩ by ext; simp [map_sub, map_pow],
      maximalIdealQuotientEquivUnitFiltrationQuotient_mk hc hvβ (2 * k + 1) (by omega) (by omega)
        hsm hsm0]
  rw [hE_eq, exists_mk_isSquare_one_add_mul_sq_sub_iff h2 hc hk hvβ s]
  refine ⟨fun hsq ↦ ⟨u_s, rfl,
    Units.isSquare_coe_iff.mp (by simpa [u_s, coe_mkScaledUnit] using hsq)⟩, ?_⟩
  rintro ⟨u, hu_eq, hsq_u⟩
  have hdiff : (u : Kˣ)⁻¹ * (u_s : Kˣ) ∈ unitFiltration K (2 * dyadicLevel K h2 + 1) := by
    rw [dyadicLevel_def]; simpa only [e, Subgroup.coe_mul, Subgroup.coe_inv] using
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hu_eq)
  have hsq_mk : IsSquare ((u_s : Kˣ) : K) := Units.isSquare_coe_iff.mpr <| by
    simpa only [mul_inv_cancel_left] using
      hsq_u.mul (Subgroup.mem_square.mp (unitFiltration_le_square h2 hdiff))
  simpa [u_s, coe_mkScaledUnit] using hsq_mk

/-- Counting the Artin–Schreier square locus in `𝒪[K] ⧸ 𝓂[K] ^ (2k + 2)`: when
`v(β) = v(c) ^ (2e - 2k - 1)` (`k < e = v_K(2)`), there are `#𝓀[K] ^ (k + 1)` classes `[s]` for
which `1 + β (s² - s)` is a square in `K`. -/
theorem natCard_artinSchreier_square_maximalIdeal_quotient (h2 : (2 : K) ≠ 0) {c β : 𝒪[K]}
    (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1)) :
    Nat.card {y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2) //
      ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s = y ∧
        IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} = Nat.card 𝓀[K] ^ (k + 1) := by
  let P (y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2)) : Prop := ∃ s : 𝒪[K],
    Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s = y ∧ IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))
  have hP_mk : ∀ s : 𝒪[K], P (Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s) ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) :=
    exists_mk_isSquare_one_add_mul_sq_sub_iff h2 hc hk hvβ
  have hsplit := natCard_subtype_eq_two_mul_of_symm (2 * k + 1) (P := P)
    (fun y ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_one (Ideal.Quotient.mk _), ← map_sub, hP_mk, hP_mk, show
        ((1 - s : 𝒪[K]) : K) ^ 2 - ((1 - s : 𝒪[K]) : K) = (s : K) ^ 2 - (s : K) by push_cast; ring])
    (fun y hy ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      simpa only [← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem] using
        mem_maximalIdeal_or_one_sub_mem_of_isSquare_one_add_mul_sq_sub h2 hc hk hvβ
          ((hP_mk s).mp hy))
  rw [hsplit, Nat.card_congr (artinSchreierMaximalIdealSquareEquiv h2 hc hk hvβ)]
  exact two_mul_natCard_squareCosets_unitFiltration h2 hk

private theorem natCard_eisensteinNormSquareSubgroup_zero (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : Irreducible c) :
    Nat.card (eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  have hc' : Irreducible (-c) := irreducible_of_valuation_eq hc (by simp)
  have hfun : eisensteinNormSquareClass K (zero_mem 𝓂[K]) hc.mem_maximalIdeal =
      uniformizerNormSquareClass K hc' := funext fun r ↦ by
    rw [eisensteinNormSquareClass_def, uniformizerNormSquareClass_def]
    exact congrArg squareClassHom (Units.ext (by simp [coe_eisensteinNormUnit]))
  have hrange : (eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc.mem_maximalIdeal :
      Set (Kˣ ⧸ Subgroup.square Kˣ)) = Set.range (uniformizerNormSquareClass K hc') := by
    rw [coe_eisensteinNormSquareSubgroup, hfun]
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun q ↦ by rw [← SetLike.mem_coe, hrange]),
    Nat.card_coe_set_eq]
  exact ncard_range_uniformizerNormSquareClass h2 hc'

private theorem exists_irreducible_sub_sq_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    ∃ μ c' : 𝒪[K], μ ∈ 𝓂[K] ∧ Irreducible c' ∧ t = 2 * μ ∧ c' = c - μ ^ 2 := by
  have hμlt : valuation K ((t : K) / 2) < 1 := by
    rwa [map_div₀, div_lt_one₀ ((Valuation.pos_iff _).mpr h2)]
  let μ : 𝒪[K] := ⟨(t : K) / 2, hμlt.le⟩
  have hμm : μ ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.mpr hμlt
  have hμ2lt : valuation K ((μ : K) ^ 2) < valuation K (c : K) := by
    rw [map_pow]
    refine (pow_le_pow_left₀ zero_le (valuation_le_of_mem_maximalIdeal hc hμm) 2).trans_lt ?_
    simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ (Valuation.integer.v_irreducible_pos hc)
      (Valuation.integer.v_irreducible_lt_one hc) one_lt_two
  have hc'v : valuation K ((c - μ ^ 2 : 𝒪[K]) : K) = valuation K (c : K) := by
    push_cast; exact (valuation K).map_sub_eq_of_lt_left hμ2lt
  exact ⟨μ, c - μ ^ 2, hμm, irreducible_of_valuation_eq hc hc'v,
    Subtype.ext (by push_cast; exact (mul_div_cancel₀ (t : K) h2).symm), rfl⟩

private theorem eisensteinNormSquareSubgroup_eq_zero_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    ∃ (c' : 𝒪[K]) (hc' : Irreducible c'),
      eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal =
        eisensteinNormSquareSubgroup K (zero_mem 𝓂[K]) hc'.mem_maximalIdeal := by
  obtain ⟨μ, c', hμm, hc', htμ, hc'eq⟩ := exists_irreducible_sub_sq_of_lt h2 hc hlt
  exact ⟨c', hc', le_antisymm
    (eisensteinNormSquareSubgroup_le_of_eq ht hc.mem_maximalIdeal (zero_mem 𝓂[K])
      hc'.mem_maximalIdeal hμm (by rw [htμ]; ring) (by rw [hc'eq]; ring))
    (eisensteinNormSquareSubgroup_le_of_eq (zero_mem 𝓂[K]) hc'.mem_maximalIdeal ht
      hc.mem_maximalIdeal (neg_mem hμm) (by rw [htμ]; ring) (by rw [hc'eq, htμ]; ring))⟩

private theorem natCard_eisensteinNormSquareSubgroup_of_lt (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hlt : valuation K (t : K) < valuation K (2 : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨c', hc', heq⟩ := eisensteinNormSquareSubgroup_eq_zero_of_lt h2 ht hc hlt
  rw [heq]; exact natCard_eisensteinNormSquareSubgroup_zero h2 hc'

private theorem dvd_of_eisensteinNormSquareClass_eq_one (h2 : (2 : K) ≠ 0)
    {t c r₀ : 𝒪[K]} (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hcr₀ : c * r₀ = t)
    {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1))
    {r : 𝒪[K]} (hr : eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1) :
    ∃ s : 𝒪[K], r = r₀ * s := by
  set e := natCastValuation K 2 h2
  obtain ⟨ξ, hξ⟩ := (eisensteinNormSquareClass_eq_one_iff ht hc.mem_maximalIdeal r).mp hr
  have hξ' : 1 - (c : K) * (r₀ : K) * (r : K) + (c : K) * (r : K) ^ 2 = ξ ^ 2 := by
    simpa only [← hcr₀, Subring.coe_mul, sq] using hξ
  refine (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr
    (not_lt.mp fun (hlt : valuation K (r₀ : K) < valuation K (r : K)) ↦ ?_)
  have hr0 : r ≠ 0 := fun h0 ↦ by simp [h0] at hlt
  obtain ⟨ρ, hrv⟩ := exists_valuation_eq_pow_irreducible (valuation K) hr0 hc
  have hρlt : ρ < e - k - 1 := not_le.mp fun hge ↦ (hrv ▸ hvr₀ ▸ hlt).not_ge
    (pow_le_pow_right_of_le_one' (Valuation.integer.v_irreducible_lt_one hc).le hge)
  apply valuation_sq_sub_one_ne_pow_odd h2 hc (by omega : ρ < e) ξ
  rw [show ξ ^ 2 - 1 = (c : K) * (r : K) * ((r : K) - (r₀ : K)) by linear_combination -hξ',
    map_mul, map_mul, (valuation K).map_sub_eq_of_lt_left hlt, hrv, ← pow_succ', ← pow_add]
  congr 1; omega

private theorem exists_factor_of_valuation_two_le (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hle : valuation K (2 : K) ≤ valuation K (t : K)) :
    ∃ (k : ℕ) (r₀ : 𝒪[K]), k < natCastValuation K 2 h2 ∧ c * r₀ = t ∧
      valuation K (r₀ : K) = valuation K (c : K) ^ (natCastValuation K 2 h2 - k - 1) := by
  set e := natCastValuation K 2 h2
  have hc1 : valuation K (c : K) < 1 := Valuation.integer.v_irreducible_lt_one hc
  have hc0 : valuation K (c : K) ≠ 0 := (Valuation.integer.v_irreducible_pos hc).ne'
  have ht0 : t ≠ 0 := fun h0 ↦ h2 (by simpa [h0] using hle)
  obtain ⟨r₀, hcr₀⟩ : c ∣ t := Ideal.mem_span_singleton.mp (hc.maximalIdeal_eq ▸ ht)
  obtain ⟨m, hvt⟩ := exists_valuation_eq_pow_irreducible (valuation K) ht0 hc
  have hm1 : 1 ≤ m := not_lt.mp fun hm0 ↦ ((valuation K).mem_maximalIdeal_iff.mp ht).ne
    (by simp [hvt, Nat.lt_one_iff.mp hm0])
  have hme : m ≤ e := not_lt.mp fun hgt ↦ (valuation_natCast_eq_pow hc 2 h2 ▸ hvt ▸ hle).not_gt
    (pow_lt_pow_right_of_lt_one₀ (Valuation.integer.v_irreducible_pos hc) hc1 hgt)
  refine ⟨e - m, r₀, by omega, hcr₀.symm, mul_left_cancel₀ hc0 ?_⟩
  rw [← map_mul, ← Subring.coe_mul, ← hcr₀, hvt, ← pow_succ',
    show e - (e - m) - 1 + 1 = m by omega]

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
  have hrv := (mem_maximalIdeal_pow_iff_valuation_le hc N).mp hr
  refine (eisensteinNormSquareClass_def ht hc.mem_maximalIdeal r).trans <|
    (squareClassHom_eq_one_iff _).mpr (Subgroup.mem_square.mp (unitFiltration_le_square h2 ?_))
  rw [dyadicLevel_def, mem_unitFiltration_succ_valuation (2 * e) _ c hc, map_pow,
    show (eisensteinNormUnit K ht hc.mem_maximalIdeal r : K) - 1 =
      -(t : K) * (r : K) + (c : K) * (r : K) ^ 2 by rw [coe_eisensteinNormUnit]; ring]
  refine ((valuation K).map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul, Valuation.map_neg, hvt]
    exact (mul_le_mul' le_rfl hrv).trans_eq (by rw [← pow_add]; congr 1; omega)
  · rw [map_mul, map_pow]
    refine (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrv 2)).trans ?_
    rw [← pow_mul, ← pow_succ']
    exact pow_le_pow_right_of_le_one' (Valuation.integer.v_irreducible_lt_one hc).le (by omega)

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
  have hNM : N = (e - k - 1) + M := by omega
  let ι := mulLeftMaximalIdealPowQuotient hc hvr₀ hNM
  have hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * e - 2 * k - 1) := by
    simp only [β, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvr₀,
      ← pow_mul, ← pow_succ']; congr 1; omega
  -- Substituting `r = r₀ * s` turns `1 - t r + c r²` into the Artin–Schreier form `1 + β (s² - s)`.
  have hF_mk : ∀ s : 𝒪[K], F (ι (Ideal.Quotient.mk (𝓂[K] ^ M) s)) = 1 ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) := fun s ↦ by
    dsimp only [F, ι]
    rw [mulLeftMaximalIdealPowQuotient_mk, eisensteinNormSquareClassQuotient_mk,
      eisensteinNormSquareClass_eq_one_iff,
      show 1 - (t : K) * ((r₀ * s : 𝒪[K]) : K) + (c : K) * ((r₀ * s : 𝒪[K]) : K) ^ 2 =
        1 + (β : K) * ((s : K) ^ 2 - (s : K)) by
        simp only [← hcr₀, β, Subring.coe_mul, SubmonoidClass.coe_pow]; ring]
  -- Multiplication by `r₀` identifies the Artin–Schreier square locus modulo `𝓂[K] ^ M` with the
  -- `1`-fibre modulo `𝓂[K] ^ N`: injectivity cancels `r₀`, and surjectivity divides `r` by `r₀`.
  let ιFiber : {y : 𝒪[K] ⧸ 𝓂[K] ^ M // ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ M) s = y ∧
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} → {x : 𝒪[K] ⧸ 𝓂[K] ^ N // F x = 1} :=
    fun ⟨y, hy⟩ ↦ ⟨ι y, by obtain ⟨s, rfl, hsq⟩ := hy; exact (hF_mk s).mpr hsq⟩
  refine (Nat.card_congr (Equiv.ofBijective ιFiber ⟨fun _ _ h ↦
      Subtype.ext (mulLeftMaximalIdealPowQuotient_injective hc hvr₀ hNM (congrArg Subtype.val h)),
    fun ⟨x, hx⟩ ↦ ?_⟩).symm).trans
    (natCard_artinSchreier_square_maximalIdeal_quotient h2 hc hk hvβ)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hxr : eisensteinNormSquareClass K ht hc.mem_maximalIdeal r = 1 := by
    simpa only [F, eisensteinNormSquareClassQuotient_mk] using hx
  obtain ⟨s, rfl⟩ := dvd_of_eisensteinNormSquareClass_eq_one h2 ht hc hcr₀ hk hvr₀ hxr
  have hxs : F (ι (Ideal.Quotient.mk (𝓂[K] ^ M) s)) = 1 := by
    dsimp only [ι]; rwa [mulLeftMaximalIdealPowQuotient_mk]
  exact ⟨⟨Ideal.Quotient.mk _ s, s, rfl, (hF_mk s).mp hxs⟩,
    Subtype.ext (mulLeftMaximalIdealPowQuotient_mk hc hvr₀ hNM s)⟩

private theorem natCard_eisensteinNormSquareSubgroup_of_le (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) (hle : valuation K (2 : K) ≤ valuation K (t : K)) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨k, r₀, hk, hcr₀, hvr₀⟩ := exists_factor_of_valuation_two_le h2 ht hc hle
  have hIN := eisensteinNormSquareClass_eq_one_of_mem_pow h2 ht hc hcr₀ hk hvr₀
  have hprod := natCard_quotient_eq_mul_natCard_eisenstein_fiber ht hc.mem_maximalIdeal
    (𝓂[K] ^ (natCastValuation K 2 h2 + k + 1)) hIN
  rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    natCard_eisenstein_fiber_of_factor h2 ht hc hcr₀ hk hvr₀ hIN, Nat.add_assoc, pow_add] at hprod
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos Finite.card_pos (k + 1)) hprod).symm

/-- **Square-class count for Eisenstein unit norms.** Over a nonarchimedean local field (`2 ≠ 0`),
for `t ∈ 𝓂[K]` and irreducible `c ∈ 𝒪[K]`, `eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal`
has cardinality `#𝓀[K] ^ natCastValuation K 2 h2`. -/
theorem natCard_eisensteinNormSquareSubgroup (h2 : (2 : K) ≠ 0) {t c : 𝒪[K]}
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c) :
    Nat.card (eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rcases lt_or_ge (valuation K (t : K)) (valuation K (2 : K)) with hlt | hge
  · exact natCard_eisensteinNormSquareSubgroup_of_lt h2 ht hc hlt
  · exact natCard_eisensteinNormSquareSubgroup_of_le h2 ht hc hge

/-- **Index inside the unit square classes.** Over a nonarchimedean local field (`2 ≠ 0`),
`eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal` has index `2` in `unitSquareClasses K`. -/
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
