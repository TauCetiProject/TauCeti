/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.Delta
public import TauCeti.RingTheory.Iwasawa.EulerQuotient
public import TauCeti.RingTheory.Iwasawa.Growth.Transition

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The cyclotomic cutoff for transition quotients of an Iwasawa module

Let `O` be a discrete valuation ring, complete for its maximal ideal, with finite residue field,
let `Λ = O⟦X⟧`, and let `M` be a finitely generated torsion `Λ`-module with characteristic
polynomial `F_M` (`TauCeti.Iwasawa.charPoly`). Write `ν_{k,n₀}` (`TauCeti.Iwasawa.growthTransition`)
for the cyclotomic transition `∏_{n₀ ≤ j ≤ k} ξ_j`, where `ξ_j = Φ_{p ^ j}(1 + X)`.

This file characterizes the cutoff levels `n₀` above which every transition quotient
`M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) is finite:

1. Over any such `O` (with no characteristic assumption), `M ⧸ ν_{k,n₀} M` is finite for every
   `k ≥ n₀` if and only if `Res(F_M, ξ_j) ≠ 0` for every `j ≥ n₀`
   (`TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`).
2. When `O` has characteristic zero, the shifted cyclotomic polynomials `ξ_j` are pairwise coprime
   over the fraction field of `O`. Consequently an irreducible distinguished factor `F` of `F_M`
   divides `ξ_j` for some `j ≥ n₀` if and only if it divides some `ω_m` while dividing none of the
   factors `ξ_i` (`i < n₀`) of `ω_{n₀ - 1} = ∏_{i < n₀} ξ_i`, which happens exactly when
   `ω_{n₀ - 1} • M_δ` is infinite on the corresponding horizontal block `Λ ⧸ (F ^ n)`. Passing
   along a pseudo-isomorphism to an elementary module yields the intrinsic *cyclotomic cutoff*
   (`TauCeti.Iwasawa.finite_quotient_growthTransition_iff`): all quotients `M ⧸ ν_{k,n₀} M`
   (`k ≥ n₀`) are finite if and only if `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite, where
   `M_δ = ⨆_m M[ν_{m,0}]` is `TauCeti.Iwasawa.deltaSubmodule`.
3. Since `M_δ = M[ω_m]` for some `m` on the noetherian module `M`, taking `n₀ = m + 1` makes
   `(∏_{j < n₀} ν_{j,j}) • M_δ = ω_m • M[ω_m] = 0`, so every finitely generated torsion module in
   characteristic zero admits a cutoff `n₀`
   (`TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`).

In equal characteristic `p`, `ξ_1 = X ^ (p - 1)` is no longer coprime to `ξ_0 = X`, and the
delta-submodule criterion fails: on `M = 𝔽_p⟦ϖ⟧⟦X⟧ ⧸ (X)`, `ω_0 = X` annihilates `M_δ = M`, while
`M ⧸ ξ_1 M = M` is infinite.

## Main results

* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`: all
  `M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite iff `Res(F_M, ξ_j) ≠ 0` for all `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero`
  — in characteristic zero, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite iff `Res(F_M, ξ_j) ≠ 0` for all
  `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_quotient_growthTransition_iff`: in characteristic zero, all
  `M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite iff `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite.
* `TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`: in characteristic zero, every
  finitely generated torsion module has a cutoff `n₀` above which all `M ⧸ ν_{k,n₀} M` are finite.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition (5.3.17).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public noncomputable section

open IsLocalRing PowerSeries Submodule
open scoped Pointwise Polynomial PowerSeries

namespace TauCeti.Iwasawa

/-- The supremum of the kernels `M[ν_{m,0}]` is `deltaSubmodule p O M`. -/
theorem iSup_torsionBy_growthTransition_zero (p : ℕ) (O M : Type*) [CommRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] :
    (⨆ m, torsionBy O⟦X⟧ M (growthTransition p O 0 m)) = deltaSubmodule p O M := by
  simp_rw [growthTransition_zero_left, deltaSubmodule_def]

section Blocks

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]

private theorem smul_quotient_mk {R : Type*} [CommRing R] (I : Ideal R) (r s : R) :
    r • Ideal.Quotient.mk I s = Ideal.Quotient.mk I (r * s) := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Ideal.Quotient.mk_eq_mk]

variable [IsAdicComplete (maximalIdeal O) O]

/-- On a horizontal block `O⟦X⟧ ⧸ (F ^ n)`, if `Res(F ^ n, ξ_j) ≠ 0` for all `j ≥ n₀`, then
`∏_{j < n₀} ν_{j,j}` annihilates the delta submodule. -/
private theorem smul_deltaSubmodule_quotient_span_pow_eq_bot {F : O[X]}
    (hF : F.IsDistinguishedAt (maximalIdeal O)) (n n₀ : ℕ)
    (hres : ∀ j, n₀ ≤ j →
      (F ^ n).resultant ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0) :
    (∏ j ∈ Finset.range n₀, growthTransition p O j j) •
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm⟩ := (mem_deltaSubmodule p O _ x).mp hx
  rw [← growthTransition_zero_left] at hm
  let k := max m n₀
  obtain ⟨q, hq⟩ := growthTransition_dvd_of_le p O 0 (le_max_left m n₀)
  have hxk : growthTransition p O 0 k • x = 0 := by
    rw [hq, mul_comm, mul_smul, hm, smul_zero]
  have hkres : (F ^ n).resultant (growthTransitionPoly p O n₀ k) ≠ 0 := by
    rw [growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one,
      (hF.pow n).monic.resultant_prod_right, Finset.prod_ne_zero_iff]
    exact fun j hj ↦ hres j (Finset.mem_Ico.mp hj).1
  have H := (hF.pow n).isWeierstrassFactorizationAt
  have hbot : torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})
      (growthTransitionPoly p O n₀ k : O⟦X⟧) = ⊥ :=
    H.torsionBy_eq_bot_iff _ |>.mpr (H.norm_mk_coe_eq_resultant _ ▸ hkres)
  have hmem : (∏ j ∈ Finset.range n₀, growthTransition p O j j) • x ∈
      torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})
        (growthTransitionPoly p O n₀ k : O⟦X⟧) := by
    rw [mem_torsionBy_iff, coe_growthTransitionPoly, smul_smul, mul_comm,
      prod_range_growthTransition_mul p O (le_trans (le_max_right m n₀) (Nat.le_succ k)), hxk]
  rwa [hbot, mem_bot] at hmem

/-- On a horizontal block `O⟦X⟧ ⧸ (F ^ n)` (`n ≠ 0`) in characteristic zero, if `F ∣ ξ_{j₀}` for
some `j₀ ≥ n₀`, then `(∏_{j < n₀} ν_{j,j}) • M_δ` is infinite. -/
private theorem infinite_smul_deltaSubmodule_quotient_span_pow_of_dvd [CharZero O] {F : O[X]}
    (hF : F.IsDistinguishedAt (maximalIdeal O)) (hirr : Irreducible F) {n n₀ j₀ : ℕ}
    (hn : n ≠ 0) (hj₀ : n₀ ≤ j₀)
    (hdvd : F ∣ (Polynomial.cyclotomic (p ^ j₀) O).comp (Polynomial.X + 1)) :
    Infinite ↥((∏ j ∈ Finset.range n₀, growthTransition p O j j) •
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Polynomial.coe_pow, pow_succ]
  set W : O[X] := ∏ j ∈ Finset.range n₀, growthTransitionPoly p O j j
  have hWres : F.resultant W ≠ 0 := by
    rw [hF.monic.resultant_prod_right, Finset.prod_ne_zero_iff]
    intro j hj
    rw [growthTransitionPoly_self_eq_cyclotomic_comp_X_add_one, Ne,
      hF.monic.resultant_eq_zero_iff_dvd hirr]
    have hne : j ≠ j₀ := by have := Finset.mem_range.mp hj; omega
    exact Polynomial.not_dvd_cyclotomic_comp_X_add_one_of_dvd hirr.not_isUnit
      ((Nat.pow_right_injective (Fact.out : p.Prime).one_lt).ne hne) hdvd
  have hQtor : torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) (W : O⟦X⟧) = ⊥ :=
    hF.isWeierstrassFactorizationAt.torsionBy_eq_bot_iff _ |>.mpr
      (hF.isWeierstrassFactorizationAt.norm_mk_coe_eq_resultant _ ▸ hWres)
  have hFm_ne : (F : O⟦X⟧) ^ m ≠ 0 :=
    pow_ne_zero m ((Polynomial.coe_eq_zero_iff).not.mpr hF.monic.ne_zero)
  let ι := Ideal.mulLeftQuotientSpanSingleton ((F : O⟦X⟧) ^ m) (F : O⟦X⟧)
  let ψ := ι ∘ₗ LinearMap.lsmul O⟦X⟧ _ (W : O⟦X⟧)
  have hψ_inj : Function.Injective ψ :=
    (Ideal.mulLeftQuotientSpanSingleton_injective (isRegular_iff_ne_zero.mpr hFm_ne).left _).comp
      ((isSMulRegular_iff_torsionBy_eq_bot _ _).mpr hQtor)
  have hw : (W : O⟦X⟧) = ∏ j ∈ Finset.range n₀, growthTransition p O j j := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp [Polynomial.coeToPowerSeries.ringHom_apply]
  obtain ⟨u, hu⟩ : F ∣ (1 + Polynomial.X) ^ p ^ j₀ - 1 := by
    rw [← growthTransitionPoly_zero_left p O j₀,
      growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one]
    exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩))
  have hcoe : ((1 + X) ^ p ^ j₀ - 1 : O⟦X⟧) = (F : O⟦X⟧) * (u : O⟦X⟧) := by
    simpa using congr_arg (Polynomial.coeToPowerSeries.ringHom (R := O)) hu
  have hι_delta (q : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) : ι q ∈ deltaSubmodule p O _ := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine (mem_deltaSubmodule p O _ _).mpr ⟨j₀, ?_⟩
    rw [Ideal.mulLeftQuotientSpanSingleton_mk, smul_quotient_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, hcoe]
    exact ⟨(u : O⟦X⟧) * s, by ring⟩
  have hψ_mem (q : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) :
      ψ q ∈ (∏ j ∈ Finset.range n₀, growthTransition p O j j) • deltaSubmodule p O _ := by
    simpa only [ψ, LinearMap.comp_apply, LinearMap.lsmul_apply, map_smul, hw] using
      Submodule.smul_mem_pointwise_smul (ι q) (W : O⟦X⟧) _ (hι_delta q)
  have hdeg : 0 < F.natDegree := Nat.pos_of_ne_zero fun h0 ↦
    hirr.not_isUnit (Polynomial.eq_one_of_monic_natDegree_zero hF.monic h0 ▸ isUnit_one)
  have := hF.isWeierstrassFactorizationAt.infinite_quotient hdeg
  exact Infinite.of_injective (fun q ↦ (⟨ψ q, hψ_mem q⟩ : _)) fun q₁ q₂ h ↦
    hψ_inj (congr_arg Subtype.val h)

/-- On an elementary module `E = Elementary O ϖ r m F n` with distinguished `Fᵢ`, if
`Res(∏ᵢ Fᵢ ^ nᵢ, ξ_j) ≠ 0` for all `j ≥ n₀`, then `(∏_{j < n₀} ν_{j,j}) • M_δ = ⊥`. -/
private theorem smul_deltaSubmodule_elementary_eq_bot {ϖ : O} (hϖ : Irreducible ϖ) {r a b : ℕ}
    (m : Fin a → ℕ) {F : Fin b → O[X]} (hF : ∀ i, (F i).IsDistinguishedAt (maximalIdeal O))
    (n : Fin b → ℕ) (n₀ : ℕ)
    (hres : ∀ j, n₀ ≤ j →
      (∏ i, F i ^ n i).resultant
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0) :
    (∏ j ∈ Finset.range n₀, growthTransition p O j j) •
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
    rw [deltaSubmodule_quotient_span_C_pow hϖ.prime (m i), mem_bot] at hx₁
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
    have hmem : (∏ j ∈ Finset.range n₀, growthTransition p O j j) • x₂ i ∈
        (∏ j ∈ Finset.range n₀, growthTransition p O j j) • deltaSubmodule p O _ := ⟨x₂ i, hx₂, rfl⟩
    rwa [smul_deltaSubmodule_quotient_span_pow_eq_bot (hF i) (n i) n₀ hires, mem_bot] at hmem

/-- On an elementary module `E = Elementary O ϖ r m F n` with irreducible distinguished `Fᵢ` and
`nᵢ ≠ 0` over a characteristic-zero ring `O`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite iff
`Res(∏ᵢ Fᵢ ^ nᵢ, ξ_j) ≠ 0` for all `j ≥ n₀`. -/
private theorem finite_smul_deltaSubmodule_elementary_iff [CharZero O] {ϖ : O}
    (hϖ : Irreducible ϖ) {r a b : ℕ} (m : Fin a → ℕ) {F : Fin b → O[X]}
    (hF : ∀ i, (F i).IsDistinguishedAt (maximalIdeal O)) (hirr : ∀ i, Irreducible (F i))
    {n : Fin b → ℕ} (hn : ∀ i, n i ≠ 0) (n₀ : ℕ) :
    Finite ↥((∏ j ∈ Finset.range n₀, growthTransition p O j j) •
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
      simpa [ι] using congr_fun (congr_arg (Prod.snd ∘ Prod.snd) hxy) i
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
quotients `M ⧸ ν_{k,n₀} M` for all `k ≥ n₀` if and only if `Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all
`j ≥ n₀`. -/
private theorem finite_quotSMulTop_growthTransition_iff_of_notMem {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M)
    (hpO : (p : O) ∉ maximalIdeal O) (n₀ : ℕ) :
    (∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M)) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  have hpu : IsUnit (p : O) := notMem_maximalIdeal.mp hpO
  have hunit_gt {m k : ℕ} (hm : 0 < m) : IsUnit (growthTransition p O m k) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, growthTransition_constantCoeff p O m k hm]
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
    have hsmul (k : ℕ) :
        growthTransition p O 0 k • (⊤ : Submodule O⟦X⟧ M) =
          ((Polynomial.X : O[X]) : O⟦X⟧) • ⊤ := by
      rw [← growthTransition_mul_of_le p O (Nat.zero_le 1) (Nat.zero_le k),
        growthTransition_zero_zero, mul_smul,
        Submodule.smul_eq_self_of_isUnit (hunit_gt Nat.one_pos), Polynomial.coe_X]
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
`O⟦X⟧`-module `M` (with no characteristic assumption on `O`), the quotients `M ⧸ ν_{k,n₀} M` are
finite for all `k ≥ n₀` if and only if `Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero {M : Type*}
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M)
    (n₀ : ℕ) :
    (∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M)) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  by_cases hpO : (p : O) ∈ maximalIdeal O
  · refine ⟨fun hfin j hj ↦ ?_, fun hres k _ ↦ ?_⟩
    · have h := resultant_charPoly_ne_zero_of_finite_quotSMulTop
        (coe_growthTransitionPoly p O n₀ j ▸ hfin j hj)
      rw [growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one,
        monic_charPoly.resultant_prod_right, Finset.prod_ne_zero_iff] at h
      exact h j (Finset.mem_Ico.mpr ⟨hj, Nat.lt_succ_self j⟩)
    · rw [← coe_growthTransitionPoly,
        finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM
          (isDistinguishedAt_growthTransitionPoly hpO n₀ k),
        growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one,
        monic_charPoly.resultant_prod_right, Finset.prod_ne_zero_iff]
      exact fun j hj ↦ hres j (Finset.mem_Ico.mp hj).1
  · exact finite_quotSMulTop_growthTransition_iff_of_notMem hM hpO n₀

/-- **Resultant criterion for the delta submodule.** Over a characteristic-zero ring `O`, for a
finitely generated `O⟦X⟧`-module `M`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite if and only if
`Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero
    [CharZero O] {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (n₀ : ℕ) :
    Finite ↥((∏ j ∈ Finset.range n₀, growthTransition p O j j) • deltaSubmodule p O M) ↔
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
quotients by the transitions `ν_{k,n₀}` (`k ≥ n₀`) are all finite if and only if
`∏_{j < n₀} ν_{j,j}` carries `M_δ = ⨆_m M[ν_{m,0}]` to a finite submodule. -/
theorem finite_quotient_growthTransition_iff (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [CharZero O] (M : Type*) [AddCommGroup M]
    [Module (PowerSeries O) M] [Module.Finite (PowerSeries O) M]
    (hM : Module.IsTorsion (PowerSeries O) M) (n₀ : ℕ) :
    (∀ k, n₀ ≤ k →
      Finite (M ⧸ (growthTransition p O n₀ k • (⊤ : Submodule (PowerSeries O) M)))) ↔
      Finite ↥((∏ j ∈ Finset.range n₀, growthTransition p O j j) •
        (⨆ m, Submodule.torsionBy (PowerSeries O) M (growthTransition p O 0 m) :
          Submodule (PowerSeries O) M)) := by
  rw [iSup_torsionBy_growthTransition_zero,
    finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero,
    ← finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero hM]

/-- Every finitely generated torsion `O⟦X⟧`-module over a characteristic-zero complete discrete
valuation ring with finite residue field admits a cutoff `n₀` above which all transition quotients
`M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite. -/
theorem exists_finite_quotSMulTop_growthTransition (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CharZero O] {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M) := by
  obtain ⟨m, hm⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  refine ⟨m + 1, (finite_quotient_growthTransition_iff p O M hM (m + 1)).mpr ?_⟩
  have hprod : ∏ j ∈ Finset.range (m + 1), growthTransition p O j j =
      (1 + X) ^ p ^ m - 1 := by
    rw [prod_range_growthTransition_eq p O (Nat.succ_pos m), Nat.succ_sub_one,
      growthTransition_zero_left]
  suffices (∏ j ∈ Finset.range (m + 1), growthTransition p O j j) •
      (⨆ l, torsionBy O⟦X⟧ M (growthTransition p O 0 l)) = ⊥ by
    rw [this]
    infer_instance
  rw [iSup_torsionBy_growthTransition_zero, hm, hprod, eq_bot_iff]
  intro y hy
  rw [Submodule.mem_smul_pointwise_iff_exists] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (mem_torsionBy_iff _ _).mp hx

-- Equal characteristic: over `O = 𝔽_p⟦ϖ⟧` and `M = O⟦X⟧ ⧸ (X)`, `ω_0 = X` kills `M_δ = M`, yet
-- `M ⧸ ξ_1 M = M` is infinite, since `ξ_1 = X ^ (p - 1)`: the cutoff criterion needs
-- characteristic zero.
example (p : ℕ) [Fact p.Prime] :
    let O := PowerSeries (ZMod p)
    let M := PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}
    growthTransition p O 0 0 •
        (⨆ m, Submodule.torsionBy (PowerSeries O) M (growthTransition p O 0 m)) = ⊥ ∧
      ¬ Finite (M ⧸ (growthTransition p O 1 1 • (⊤ : Submodule (PowerSeries O) M))) := by
  intro O M
  have hXsmul : (X : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ M) = ⊥ := by
    simp [M, Ideal.Quotient.smul_top]
  refine ⟨eq_bot_iff.mpr ((smul_mono_right _ le_top).trans_eq
    (by rw [growthTransition_zero_zero, hXsmul])), ?_⟩
  have : CharP O p := charP_of_injective_ringHom C_injective p
  have hξ : growthTransition p O 1 1 = X ^ (p ^ 1).totient := by
    rw [← coe_growthTransitionPoly, growthTransitionPoly_self_eq_cyclotomic_comp_X_add_one,
      Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_X_pow]
    simp
  have hpos : 0 < (p ^ 1).totient :=
    Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos 1)
  have hsmul₁ : growthTransition p O 1 1 • (⊤ : Submodule O⟦X⟧ M) = ⊥ := by
    rw [hξ, ← Nat.sub_add_cancel hpos, pow_succ, mul_smul, hXsmul]
    simp
  refine not_finite_iff_infinite.mpr
    (Infinite.of_injective
      (fun b : O ↦ Submodule.Quotient.mk (Ideal.Quotient.mk _ (C b))) fun b₁ b₂ hb ↦ ?_)
  rw [Submodule.Quotient.eq, hsmul₁, mem_bot, sub_eq_zero, Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at hb
  simpa [PowerSeries.X_dvd_iff, sub_eq_zero] using hb

end TauCeti.Iwasawa
