/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Iwasawa.Delta
public import TauCeti.RingTheory.Iwasawa.GrowthFormula

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Iwasawa.EulerQuotient
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The cyclotomic cutoff for transition quotients of an Iwasawa module

Let `O` be a discrete valuation ring, complete for its maximal ideal, with finite residue field,
let `Λ = O⟦X⟧`, and let `M` be a finitely generated torsion `Λ`-module with characteristic
polynomial `F_M` (`TauCeti.Iwasawa.charPoly`). Write `ν_{n₀,k}`
(`TauCeti.Iwasawa.growthTransition`) for the cyclotomic transition polynomial
`∏_{n₀ ≤ j ≤ k} ξ_j`, where `ξ_j = Φ_{p ^ j}(X + 1)`.

This file characterizes the cutoff levels `n₀` above which every transition quotient
`M ⧸ ν_{n₀,k} M` (`k ≥ n₀`) is finite:

1. Over any such `O` (with no characteristic assumption), `M ⧸ ν_{n₀,k} M` is finite for every
   `k ≥ n₀` if and only if `Res(F_M, ξ_j) ≠ 0` for every `j ≥ n₀`
   (`TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`).
2. When `O` has characteristic zero, the shifted cyclotomic polynomials `ξ_j` are pairwise coprime
   over the fraction field of `O`. Consequently an irreducible distinguished factor `F` of `F_M`
   divides `ξ_j` for some `j ≥ n₀` if and only if it divides some `ω_m` while dividing none of the
   factors `ξ_i` (`i < n₀`) of `ω_{n₀ - 1} = ∏_{i < n₀} ξ_i`, which happens exactly when
   `ω_{n₀ - 1} • M_δ` is infinite on the corresponding horizontal block `Λ ⧸ (F ^ n)`. Passing
   along a pseudo-isomorphism to an elementary module yields the intrinsic *cyclotomic cutoff*
   (`TauCeti.Iwasawa.finite_quotient_growthTransition_iff`): all quotients `M ⧸ ν_{n₀,k} M`
   (`k ≥ n₀`) are finite if and only if `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite, where
   `M_δ = ⨆_m M[ν_{0,m}]` is `TauCeti.Iwasawa.deltaSubmodule`.
3. Since `M_δ = M[ω_m]` for some `m` on the noetherian module `M`, taking `n₀ = m + 1` makes
   `(∏_{j < n₀} ν_{j,j}) • M_δ = ω_m • M[ω_m] = 0`, so every finitely generated torsion module in
   characteristic zero admits a cutoff `n₀`
   (`TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`). Combining this cutoff with
   Iwasawa's conditional growth formula
   (`TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq`) yields the
   unconditional mixed-characteristic growth formula for every finitely generated torsion module
   (`TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion`, and
   `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt_of_isTorsion`
   over `ℤ_p`).

Two equal-characteristic `𝔽_p⟦ϖ⟧` examples at the end show that `[CharZero O]` is essential:
`ξ_1 = X ^ (p - 1)` is not coprime to `ξ_0 = X`, so on `M = 𝔽_p⟦ϖ⟧⟦X⟧ ⧸ (X)` the element
`ω_0 = X` annihilates `M_δ = M` while `M ⧸ ξ_1 M = M` is infinite; and on
`M = 𝔽_p⟦ϖ⟧⟦X⟧ ⧸ (X - ϖ)`, `μ = 0` and `λ = 1` while `#(M ⧸ ω_n M) = p ^ p ^ n`.

## Main results

* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`: all
  `M ⧸ ν_{n₀,k} M` (`k ≥ n₀`) are finite iff `Res(F_M, ξ_j) ≠ 0` for all `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero`
  — in characteristic zero, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite iff `Res(F_M, ξ_j) ≠ 0` for all
  `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_quotient_growthTransition_iff`: in characteristic zero, all
  `M ⧸ ν_{n₀,k} M` (`k ≥ n₀`) are finite iff `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite.
* `TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`: in characteristic zero, every
  finitely generated torsion module has a cutoff `n₀` above which all `M ⧸ ν_{n₀,k} M` are finite.
* `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion` and
  `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt_of_isTorsion`:
  the unconditional growth formula `#(M ⧸ ν_{n₀,k} M) = q ^ (μ p ^ k + e λ k + ν)` for every
  finitely generated torsion module over a mixed-characteristic coefficient ring (and over `ℤ_p`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition 5.3.17.
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public noncomputable section

open IsLocalRing PowerSeries Submodule
open scoped Pointwise Polynomial PowerSeries

namespace TauCeti.Iwasawa

section Blocks

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

/-- On a horizontal block `O⟦X⟧ ⧸ (F ^ n)`, if `Res(F ^ n, ξ_j) ≠ 0` for all `j ≥ n₀`, then
`∏_{j < n₀} ν_{j,j}` annihilates the delta submodule. -/
private theorem smul_deltaSubmodule_quotient_span_pow_eq_bot {F : O[X]}
    (hF : F.IsDistinguishedAt (maximalIdeal O)) (n n₀ : ℕ)
    (hres : ∀ j, n₀ ≤ j →
      (F ^ n).resultant ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0) :
    ((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm⟩ := (mem_deltaSubmodule p O _ x).mp hx
  rw [← coe_growthTransition_zero_left (p := p)] at hm
  let k := max m n₀
  obtain ⟨q, hq⟩ := _root_.map_dvd Polynomial.coeToPowerSeries.ringHom
    (growthTransition_dvd_growthTransition (p := p) (O := O) 0 (le_max_left m n₀))
  have hxk : (growthTransition p O 0 k : O⟦X⟧) • x = 0 := by
    simpa only [Polynomial.coeToPowerSeries.ringHom_apply, mul_comm, mul_smul, hm,
      smul_zero] using congrArg (· • x) hq
  have hkres : (F ^ n).resultant (growthTransition p O n₀ k) ≠ 0 := by
    rw [growthTransition_def, (hF.pow n).monic.resultant_prod_right, Finset.prod_ne_zero_iff]
    exact fun j hj ↦ hres j (Finset.mem_Icc.mp hj).1
  have H := (hF.pow n).isWeierstrassFactorizationAt
  have hbot : torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})
      (growthTransition p O n₀ k : O⟦X⟧) = ⊥ :=
    H.torsionBy_eq_bot_iff _ |>.mpr (H.norm_mk_coe_eq_resultant _ ▸ hkres)
  have hmem : ((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) • x ∈
      torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})
        (growthTransition p O n₀ k : O⟦X⟧) := by
    rw [mem_torsionBy_iff, smul_smul, mul_comm,
      coe_prod_range_mul_growthTransition (le_trans (le_max_right m n₀) (Nat.le_succ k)),
      ← coe_growthTransition_zero_left (p := p), hxk]
  rwa [hbot, mem_bot] at hmem

/-- On a horizontal block `O⟦X⟧ ⧸ (F ^ n)` (`n ≠ 0`) in characteristic zero, if `F ∣ ξ_{j₀}` for
some `j₀ ≥ n₀`, then `(∏_{j < n₀} ν_{j,j}) • M_δ` is infinite. -/
private theorem infinite_smul_deltaSubmodule_quotient_span_pow_of_dvd [CharZero O] {F : O[X]}
    (hF : F.IsDistinguishedAt (maximalIdeal O)) (hirr : Irreducible F) {n n₀ j₀ : ℕ}
    (hn : n ≠ 0) (hj₀ : n₀ ≤ j₀)
    (hdvd : F ∣ (Polynomial.cyclotomic (p ^ j₀) O).comp (Polynomial.X + 1)) :
    Infinite ↥(((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hspan : Ideal.span {((F ^ (m + 1) : O[X]) : O⟦X⟧)} =
      ((F : O⟦X⟧) ^ m) • Ideal.span {(F : O⟦X⟧)} := by
    rw [Polynomial.coe_pow, pow_succ, ← Ideal.span_singleton_mul_span_singleton,
      ← smul_eq_mul, Submodule.ideal_span_singleton_smul]
  rw [hspan]
  set W : O[X] := ∏ j ∈ Finset.range n₀, growthTransition p O j j
  have hWres : F.resultant W ≠ 0 := by
    rw [hF.monic.resultant_prod_right, Finset.prod_ne_zero_iff]
    intro j hj
    rw [growthTransition_self, Ne, hF.monic.resultant_eq_zero_iff_dvd hirr]
    have hne : j ≠ j₀ := by have := Finset.mem_range.mp hj; omega
    exact Polynomial.not_dvd_cyclotomic_comp_X_add_one_of_dvd hirr.not_isUnit
      ((Nat.pow_right_injective (Fact.out : p.Prime).one_lt).ne hne) hdvd
  have hQtor : torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) (W : O⟦X⟧) = ⊥ :=
    hF.isWeierstrassFactorizationAt.torsionBy_eq_bot_iff _ |>.mpr
      (hF.isWeierstrassFactorizationAt.norm_mk_coe_eq_resultant _ ▸ hWres)
  have hFm_ne : (F : O⟦X⟧) ^ m ≠ 0 :=
    pow_ne_zero m ((Polynomial.coe_eq_zero_iff).not.mpr hF.monic.ne_zero)
  let ι := Ideal.mulQuot ((F : O⟦X⟧) ^ m) (Ideal.span {(F : O⟦X⟧)})
  let ψ := ι ∘ₗ LinearMap.lsmul O⟦X⟧ _ (W : O⟦X⟧)
  have hψ_inj : Function.Injective ψ :=
    (Ideal.mulQuot_injective _ (mem_nonZeroDivisors_of_ne_zero hFm_ne)).comp
      ((isSMulRegular_iff_torsionBy_eq_bot _ _).mpr hQtor)
  obtain ⟨u, hu⟩ : F ∣ growthTransition p O 0 j₀ := by
    rw [growthTransition_def]
    exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩))
  have hcoe : ((1 + X) ^ p ^ j₀ - 1 : O⟦X⟧) = (F : O⟦X⟧) * (u : O⟦X⟧) := by
    rw [← coe_growthTransition_zero_left (p := p), hu, Polynomial.coe_mul]
  have hι_delta (q : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) : ι q ∈ deltaSubmodule p O _ := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine (mem_deltaSubmodule p O _ _).mpr ⟨j₀, ?_⟩
    -- `Ideal.mulQuot` in Mathlib has no `@[simp]` evaluation lemma; unfold it to `Submodule.mapQ`
    -- and evaluate via `Submodule.mapQ_apply`.
    have hι_mk : ι (Ideal.Quotient.mk (Ideal.span {(F : O⟦X⟧)}) s) =
        Ideal.Quotient.mk (((F : O⟦X⟧) ^ m) • Ideal.span {(F : O⟦X⟧)}) (((F : O⟦X⟧) ^ m) * s) := by
      dsimp only [ι, Ideal.mulQuot]
      rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk]
      exact (Submodule.mapQ_apply (p := Ideal.span {(F : O⟦X⟧)})
        (q := ((F : O⟦X⟧) ^ m) • Ideal.span {(F : O⟦X⟧)})
        (LinearMap.mul O⟦X⟧ O⟦X⟧ ((F : O⟦X⟧) ^ m)) s).trans
        (congrArg Submodule.Quotient.mk (LinearMap.mul_apply' _ _))
    rw [hι_mk, Ideal.Quotient.smul_mk, Ideal.Quotient.eq_zero_iff_mem, ← hspan,
      Polynomial.coe_pow, pow_succ, Ideal.mem_span_singleton, hcoe]
    exact ⟨(u : O⟦X⟧) * s, by ring⟩
  have hψ_mem (q : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) :
      ψ q ∈ (W : O⟦X⟧) • deltaSubmodule p O _ := by
    simpa only [ψ, LinearMap.comp_apply, LinearMap.lsmul_apply, map_smul] using
      Submodule.smul_mem_pointwise_smul (ι q) (W : O⟦X⟧) _ (hι_delta q)
  have hdeg : 0 < F.natDegree := Nat.pos_of_ne_zero fun h0 ↦
    hirr.not_isUnit (Polynomial.eq_one_of_monic_natDegree_zero hF.monic h0 ▸ isUnit_one)
  have := hF.isWeierstrassFactorizationAt.infinite_quotient hdeg
  exact Infinite.of_injective (fun q ↦ (⟨ψ q, hψ_mem q⟩ : _)) fun q₁ q₂ h ↦
    hψ_inj (congrArg Subtype.val h)

/-- On an elementary module `E = Elementary O ϖ r m F n` with distinguished `Fᵢ`, if
`Res(∏ᵢ Fᵢ ^ nᵢ, ξ_j) ≠ 0` for all `j ≥ n₀`, then `(∏_{j < n₀} ν_{j,j}) • M_δ = ⊥`. -/
private theorem smul_deltaSubmodule_elementary_eq_bot {ϖ : O} (hϖ : Irreducible ϖ) {r a b : ℕ}
    (m : Fin a → ℕ) {F : Fin b → O[X]} (hF : ∀ i, (F i).IsDistinguishedAt (maximalIdeal O))
    (n : Fin b → ℕ) (n₀ : ℕ)
    (hres : ∀ j, n₀ ≤ j →
      (∏ i, F i ^ n i).resultant
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0) :
    ((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
      deltaSubmodule p O (Elementary O ϖ r m F n) = ⊥ := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [eq_bot_iff]
  rintro _ ⟨⟨x₀, x₁, x₂⟩, hx, rfl⟩
  refine Prod.ext (funext fun k ↦ ?_) (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_))
  · let π₀ : Elementary O ϖ r m F n →ₗ[O⟦X⟧] O⟦X⟧ :=
      (LinearMap.proj k).comp (LinearMap.fst O⟦X⟧ _ _)
    have hx₀ : x₀ k ∈ deltaSubmodule p O O⟦X⟧ :=
      π₀.map_deltaSubmodule_le p ⟨(x₀, x₁, x₂), hx, rfl⟩
    rw [deltaSubmodule_eq_bot, mem_bot] at hx₀
    simp [hx₀]
  · let π₁ : Elementary O ϖ r m F n →ₗ[O⟦X⟧] O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m i)} :=
      (LinearMap.proj i).comp ((LinearMap.fst O⟦X⟧ _ _).comp (LinearMap.snd O⟦X⟧ _ _))
    have hx₁ : x₁ i ∈ deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m i)}) :=
      π₁.map_deltaSubmodule_le p ⟨(x₀, x₁, x₂), hx, rfl⟩
    rw [deltaSubmodule_quotient_span_C_pow_eq_bot hϖ.prime (m i), mem_bot] at hx₁
    simp [hx₁]
  · let π₂ : Elementary O ϖ r m F n →ₗ[O⟦X⟧] O⟦X⟧ ⧸ Ideal.span {((F i ^ n i : O[X]) : O⟦X⟧)} :=
      (LinearMap.proj i).comp ((LinearMap.snd O⟦X⟧ _ _).comp (LinearMap.snd O⟦X⟧ _ _))
    have hx₂ : x₂ i ∈ deltaSubmodule p O _ := π₂.map_deltaSubmodule_le p ⟨(x₀, x₁, x₂), hx, rfl⟩
    have hires (j : ℕ) (hj : n₀ ≤ j) :
        (F i ^ n i).resultant ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
      have h := hres j hj
      rw [Polynomial.resultant_prod_left_of_monic _ fun l _ ↦ (hF l).monic.pow _,
        Finset.prod_ne_zero_iff] at h
      exact h i (Finset.mem_univ i)
    have hmem : ((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) • x₂ i ∈
        ((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
          deltaSubmodule p O _ := ⟨x₂ i, hx₂, rfl⟩
    rwa [smul_deltaSubmodule_quotient_span_pow_eq_bot (hF i) (n i) n₀ hires, mem_bot] at hmem

/-- On an elementary module `E = Elementary O ϖ r m F n` with irreducible distinguished `Fᵢ` and
`nᵢ ≠ 0` over a characteristic-zero ring `O`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite iff
`Res(∏ᵢ Fᵢ ^ nᵢ, ξ_j) ≠ 0` for all `j ≥ n₀`. -/
private theorem finite_smul_deltaSubmodule_elementary_iff [CharZero O] {ϖ : O}
    (hϖ : Irreducible ϖ) {r a b : ℕ} (m : Fin a → ℕ) {F : Fin b → O[X]}
    (hF : ∀ i, (F i).IsDistinguishedAt (maximalIdeal O)) (hirr : ∀ i, Irreducible (F i))
    {n : Fin b → ℕ} (hn : ∀ i, n i ≠ 0) (n₀ : ℕ) :
    Finite ↥(((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
        deltaSubmodule p O (Elementary O ϖ r m F n)) ↔
      ∀ j, n₀ ≤ j →
        (∏ i, F i ^ n i).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  refine ⟨fun hfin j hj hzero ↦ ?_, fun hres ↦ ?_⟩
  · rw [Polynomial.resultant_prod_left_of_monic _ fun i _ ↦ (hF i).monic.pow _,
      Finset.prod_eq_zero_iff] at hzero
    obtain ⟨i, -, hi⟩ := hzero
    rw [Polynomial.resultant_pow_left (F i) _ (n i) _ (by simp [(hF i).monic.leadingCoeff]) le_rfl,
      pow_eq_zero_iff (hn i), (hF i).monic.resultant_eq_zero_iff_dvd (hirr i)] at hi
    let H (j : Fin b) := O⟦X⟧ ⧸ Ideal.span {((F j ^ n j : O[X]) : O⟦X⟧)}
    let ι : H i →ₗ[O⟦X⟧] Elementary O ϖ r m F n :=
      (LinearMap.inr O⟦X⟧ _ _).comp ((LinearMap.inr O⟦X⟧ _ _).comp (LinearMap.single O⟦X⟧ H i))
    have hι : Function.Injective ι := fun x y hxy ↦ by
      simpa [ι] using congrFun (congrArg (Prod.snd ∘ Prod.snd) hxy) i
    have : Subsingleton (LinearMap.ker ι) :=
      Submodule.subsingleton_iff_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hι)
    exact not_finite_iff_infinite.mpr
      (infinite_smul_deltaSubmodule_quotient_span_pow_of_dvd (hF i) (hirr i) (hn i) hj hi)
      (finite_smul_deltaSubmodule_of_finite_ker (f := ι) inferInstance _ hfin)
  · rw [smul_deltaSubmodule_elementary_eq_bot hϖ m hF n n₀ hres]
    infer_instance

end Blocks

section Cutoff

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- When `(p : O) ∉ maximalIdeal O`, a finitely generated torsion `O⟦X⟧`-module `M` has finite
quotients `M ⧸ ν_{n₀,k} M` for all `k ≥ n₀` if and only if `Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all
`j ≥ n₀`. -/
private theorem finite_quotSMulTop_growthTransition_iff_of_notMem {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M)
    (hpO : (p : O) ∉ maximalIdeal O) (n₀ : ℕ) :
    (∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M)) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  have hpu : IsUnit (p : O) := notMem_maximalIdeal.mp hpO
  have hunit_gt {m k : ℕ} (hm : 0 < m) : IsUnit (growthTransition p O m k : O⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe,
      coeff_zero_growthTransition hm]
    exact hpu.pow _
  have hres_pos {j : ℕ} (hj : 0 < j) :
      (charPoly O M).resultant
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact (isDistinguishedAt_charPoly.isUnit_resultant_of_isUnit_coeff_zero
      (ringJacobson_eq_maximalIdeal (R := O)).ge (by simpa)).ne_zero
  rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
  · have hXdist : (Polynomial.X : O[X]).IsDistinguishedAt (maximalIdeal O) :=
      ⟨⟨fun {k} hk ↦ by rw [Polynomial.natDegree_X, Nat.lt_one_iff] at hk; simp [hk]⟩,
        Polynomial.monic_X⟩
    have hξ₀ : (Polynomial.cyclotomic (p ^ 0) O).comp (Polynomial.X + 1) = Polynomial.X := by
      simp [Polynomial.cyclotomic_one]
    have hmul (k : ℕ) : growthTransition p O 0 k =
        Polynomial.X * growthTransition p O 1 k := by
      rw [growthTransition_zero_left,
        ← prod_range_mul_growthTransition (p := p) (O := O) (Nat.succ_le_succ (Nat.zero_le k)),
        Finset.prod_range_one, growthTransition_self, hξ₀]
    have hsmul (k : ℕ) :
        (growthTransition p O 0 k : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ M) =
          ((Polynomial.X : O[X]) : O⟦X⟧) • ⊤ := by
      rw [hmul, Polynomial.coe_mul, mul_smul,
        Submodule.smul_eq_self_of_isUnit (hunit_gt Nat.one_pos)]
    refine ⟨fun hfin j _ ↦ ?_, fun hres k _ ↦ ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · have h0 := hfin 0 le_rfl
        rw [QuotSMulTop, hsmul 0] at h0
        rwa [hξ₀, ← finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM hXdist]
      · exact hres_pos hj
    · rw [QuotSMulTop, hsmul k]
      exact (finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM hXdist).mpr
        (hξ₀ ▸ hres 0 (Nat.zero_le 0))
  · refine ⟨fun _ j hj ↦ hres_pos (hn₀.trans_le hj), fun _ k _ ↦ ?_⟩
    have := QuotSMulTop.subsingleton_of_isUnit (M := M) (hunit_gt (k := k) hn₀)
    infer_instance

/-- **Resultant criterion for finite transition quotients.** For a finitely generated torsion
`O⟦X⟧`-module `M` (with no characteristic assumption on `O`), the quotients `M ⧸ ν_{n₀,k} M` are
finite for all `k ≥ n₀` if and only if `Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero {M : Type*}
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M)
    (n₀ : ℕ) :
    (∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M)) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  by_cases hpO : (p : O) ∈ maximalIdeal O
  · refine ⟨fun hfin j hj ↦ ?_, fun hres k _ ↦ ?_⟩
    · have h := resultant_charPoly_ne_zero_of_finite_quotSMulTop (hfin j hj)
      rw [growthTransition_def, monic_charPoly.resultant_prod_right, Finset.prod_ne_zero_iff] at h
      exact h j (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩)
    · rw [finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM
          (isDistinguishedAt_growthTransition hpO n₀ k),
        growthTransition_def, monic_charPoly.resultant_prod_right, Finset.prod_ne_zero_iff]
      exact fun j hj ↦ hres j (Finset.mem_Icc.mp hj).1
  · exact finite_quotSMulTop_growthTransition_iff_of_notMem hM hpO n₀

/-- **Resultant criterion for the delta submodule.** Over a characteristic-zero ring `O`, for a
finitely generated `O⟦X⟧`-module `M`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite if and only if
`Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero
    [CharZero O] {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (n₀ : ℕ) :
    Finite ↥(((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
        deltaSubmodule p O M) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  have hF (i : Fin b) := (hFn i).1
  have hirr (i : Fin b) := (hFn i).2.1
  have hn (i : Fin b) := (hFn i).2.2
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  rw [hf.finite_smul_deltaSubmodule_iff hdim, hf.charPoly_eq_prod hϖ hF hirr]
  exact finite_smul_deltaSubmodule_elementary_iff hϖ m hF hirr hn n₀

end Cutoff

/-- **The cyclotomic cutoff** (Neukirch–Schmidt–Wingberg, Proposition 5.3.17): over a
characteristic-zero coefficient ring `O`, for a finitely generated torsion `O⟦X⟧`-module `M`, the
quotients by the transitions `ν_{n₀,k}` (`k ≥ n₀`) are all finite if and only if
`∏_{j < n₀} ν_{j,j}` carries `M_δ` to a finite submodule. -/
theorem finite_quotient_growthTransition_iff (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CharZero O] (M : Type*) [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hM : Module.IsTorsion O⟦X⟧ M) (n₀ : ℕ) :
    (∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M)) ↔
      Finite ↥(((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
        deltaSubmodule p O M) :=
  (finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero hM n₀).trans
    (finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero n₀).symm

/-- Every finitely generated torsion `O⟦X⟧`-module over a characteristic-zero complete discrete
valuation ring with finite residue field admits a cutoff `n₀` above which all transition quotients
`M ⧸ ν_{n₀,k} M` (`k ≥ n₀`) are finite. -/
theorem exists_finite_quotSMulTop_growthTransition (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CharZero O] {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) := by
  obtain ⟨m, hm⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  refine ⟨m + 1, (finite_quotient_growthTransition_iff p O M hM (m + 1)).mpr ?_⟩
  have hprod : ((∏ j ∈ Finset.range (m + 1), growthTransition p O j j : O[X]) : O⟦X⟧) =
      (1 + X) ^ p ^ m - 1 := by
    have h := coe_prod_range_mul_growthTransition (p := p) (O := O) (n₀ := m + 1) (n := m) le_rfl
    rwa [growthTransition_of_lt (Nat.lt_succ_self m), Polynomial.coe_one, mul_one] at h
  suffices ((∏ j ∈ Finset.range (m + 1), growthTransition p O j j : O[X]) : O⟦X⟧) •
      deltaSubmodule p O M = ⊥ by
    rw [this]
    infer_instance
  rw [hm, hprod, eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_torsionBy_iff _ _).mp hx

/-- **Unconditional Iwasawa growth formula.** Let `O` be a complete discrete valuation ring with
finite residue field of cardinality `q`, in which `(p) = 𝔪 ^ e` for a prime `p` and some `e > 0`,
and let `M` be a finitely generated torsion `O⟦X⟧`-module with Iwasawa invariants `μ = μ(M)` and
`λ = λ(M)`. Then there exist a cutoff level `n₀` and an integer `ν` such that
`#(M ⧸ ν_{n₀,k} M) = q ^ (μ p ^ k + e λ k + ν)` for all sufficiently large `k`. -/
theorem exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion {p : ℕ}
    [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {e : ℕ} (he : 0 < e)
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∃ ν : ℤ, ∀ᶠ k in Filter.atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) : ℚ) =
        (Nat.card (ResidueField O) : ℚ) ^
          (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) := by
  have := TauCeti.IsDiscreteValuationRing.charZero_of_span_natCast_eq_maximalIdeal_pow he hpe
  obtain ⟨n₀, hn₀⟩ := exists_finite_quotSMulTop_growthTransition p hM
  exact ⟨n₀, exists_eventually_natCard_quotSMulTop_growthTransition_eq he hpe n₀
    (Filter.eventually_atTop.mpr ⟨n₀, hn₀⟩)⟩

/-- **Unconditional Iwasawa growth formula over `ℤ_p`.** For any finitely generated torsion
`ℤ_p⟦X⟧`-module `M`, there exist a cutoff level `n₀` and an integer `ν` such that
`#(M ⧸ ν_{n₀,k} M) = p ^ (μ(M) p ^ k + λ(M) k + ν)` for all sufficiently large `k`. -/
theorem exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt_of_isTorsion (p : ℕ)
    [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M) :
    ∃ n₀ : ℕ, ∃ ν : ℤ, ∀ᶠ k in Filter.atTop,
      (Nat.card (QuotSMulTop (growthTransition p ℤ_[p] n₀ k : ℤ_[p]⟦X⟧) M) : ℚ) =
        (p : ℚ) ^ (((muInvariant ℤ_[p] M * p ^ k + lambdaInvariant ℤ_[p] M * k : ℕ) : ℤ) + ν) := by
  simpa [PadicInt.card_residueField p] using
    exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion one_pos
      (by rw [pow_one, PadicInt.maximalIdeal_eq_span_p]) hM

-- Equal characteristic: over `O = 𝔽_p⟦ϖ⟧` and `M = O⟦X⟧ ⧸ (X)`, `ω_0 = X` kills `M_δ = M`, yet
-- `M ⧸ ξ_1 M = M` is infinite, since `ξ_1 = X ^ (p - 1)`: the cutoff criterion needs
-- characteristic zero.
example (p : ℕ) [Fact p.Prime] :
    let O := PowerSeries (ZMod p)
    let M := O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}
    (growthTransition p O 0 0 : O⟦X⟧) • deltaSubmodule p O M = ⊥ ∧
      ¬ Finite (QuotSMulTop (growthTransition p O 1 1 : O⟦X⟧) M) := by
  intro O M
  have hX0 : (growthTransition p O 0 0 : O⟦X⟧) = X := by
    rw [coe_growthTransition_zero_left]
    simp
  have hXsmul : (X : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ M) = ⊥ := by
    simp [M, Ideal.Quotient.smul_top]
  refine ⟨eq_bot_iff.mpr ((smul_mono_right _ le_top).trans_eq (by rw [hX0, hXsmul])), ?_⟩
  have : CharP O p := charP_of_injective_ringHom C_injective p
  have hξ : (growthTransition p O 1 1 : O⟦X⟧) = X ^ (p ^ 1).totient := by
    rw [growthTransition_self, Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_X_pow]
    simp
  have hpos : 0 < (p ^ 1).totient :=
    Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos 1)
  have hsmul₁ : (growthTransition p O 1 1 : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ M) = ⊥ := by
    rw [hξ, ← Nat.sub_add_cancel hpos, pow_succ, mul_smul, hXsmul]
    simp
  refine not_finite_iff_infinite.mpr
    (Infinite.of_injective
      (fun b : O ↦ Submodule.Quotient.mk (Ideal.Quotient.mk _ (C b))) fun b₁ b₂ hb ↦ ?_)
  rw [Submodule.Quotient.eq, hsmul₁, mem_bot, sub_eq_zero, Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at hb
  simpa [PowerSeries.X_dvd_iff, sub_eq_zero] using hb

-- Equal characteristic: `O = 𝔽_p⟦ϖ⟧` and `M = O⟦X⟧ ⧸ (X - ϖ)` have `μ = 0` and `λ = 1`, yet
-- `ω_n = ϖ ^ p ^ n` on `M ≅ O` and `#(M ⧸ ω_n M) = p ^ p ^ n`.
example (p : ℕ) [Fact p.Prime] :
    let O := PowerSeries (ZMod p)
    let M := O⟦X⟧ ⧸ Ideal.span {(X - C (X : O) : O⟦X⟧)}
    ∀ n : ℕ, Nat.card (QuotSMulTop (growthTransition p O 0 n : O⟦X⟧) M) = p ^ (p ^ n) := by
  intro O M n
  have : IsAdicComplete (maximalIdeal (ZMod p)) (ZMod p) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let F : O[X] := Polynomial.X - Polynomial.C (X : O)
  have hF : F.IsDistinguishedAt (maximalIdeal O) := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, Polynomial.monic_X_sub_C _⟩
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hk
    subst hk
    simpa [F, mem_maximalIdeal, mem_nonunits_iff] using
      (PowerSeries.irreducible_X (R := ZMod p)).not_isUnit
  have hFcoe : (F : O⟦X⟧) = X - C (X : O) := by simp [F]
  have : CharP O p := charP_of_injective_ringHom C_injective p
  have : CharP O[X] p := charP_of_injective_ringHom Polynomial.C_injective p
  have hG : growthTransition p O 0 n = Polynomial.X ^ p ^ n := by
    rw [growthTransition_zero_left, add_pow_char_pow, one_pow, add_sub_cancel_left]
  have H : (X - C (X : O) : O⟦X⟧).IsWeierstrassFactorizationAt F 1 (maximalIdeal O) :=
    hFcoe ▸ hF.isWeierstrassFactorizationAt
  have hres : F.resultant (growthTransition p O 0 n) = (X : O) ^ p ^ n := by
    dsimp only [F]
    rw [hG, Polynomial.natDegree_X_sub_C, Polynomial.resultant_X_sub_C_left _ _ _ le_rfl]
    simp
  have hnorm := (H.norm_mk_coe_eq_resultant (growthTransition p O 0 n)).trans hres
  have hne : (X : O) ^ p ^ n ≠ 0 := pow_ne_zero _ (PowerSeries.irreducible_X (R := ZMod p)).ne_zero
  have hcard := H.natCard_quotSMulTop (hnorm.symm ▸ hne)
  rw [hcard, hnorm, ← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    Nat.card_congr PowerSeries.residueFieldOfPowerSeries.toEquiv, Nat.card_zmod]

end TauCeti.Iwasawa
