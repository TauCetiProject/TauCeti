/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.Filter.AtTopBot.Defs
public import TauCeti.RingTheory.Iwasawa.EulerQuotient
public import TauCeti.RingTheory.Iwasawa.Growth.Transition

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Iwasawa.Growth.Cutoff
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Iwasawa's growth formula

Let `O` be a complete discrete valuation ring of mixed characteristic `(0, p)` with uniformiser `ϖ`,
ramification index `e > 0` (`p = u ϖ ^ e` for a unit `u`), and finite residue field of cardinality
`q`, and let `Λ = O⟦X⟧`. For a finitely generated `Λ`-module `M` and a level `n₀ : ℕ` such that the
cyclotomic transition quotients `M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are all finite, this file proves
Iwasawa's asymptotic formula for their orders: there exists `ν : ℤ` such that for all sufficiently
large `k`,

`#(M ⧸ ν_{k,n₀} M) = q ^ (μ(M) p ^ k + e λ(M) k + ν)`,

where `μ(M)` and `λ(M)` are the `ϖ`-normalised `μ`-invariant and the `λ`-invariant of `M`
(`TauCeti.Iwasawa.muInvariant`, `TauCeti.Iwasawa.lambdaInvariant`). When `q = p ^ f`, this reads
`#(M ⧸ ν_{k,n₀} M) = p ^ (f μ p ^ k + e f λ k + ν)`, and over `ℤ_[p]` (`ϖ = p`, `e = f = 1`),
`#(M ⧸ ν_{k,n₀} M) = p ^ (μ p ^ k + λ k + ν)`. Combined with the cyclotomic cutoff
(`TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`), every finitely generated torsion
`O⟦X⟧`-module over such `O` admits a cutoff `n₀` for which this formula holds.

The proof combines three ingredients at level `k`:

* **Stabilisation of kernels:** the kernels `M[ν_{k,n₀}]` form an ascending chain of submodules of
  the Noetherian `Λ`-module `M`, so they stabilise to a single finite `O`-module of order `q ^ s`.
* **Euler quotient on an elementary module:** a pseudo-isomorphism
  `M → Elementary O ϖ 0 m F n` identifies `#(M ⧸ ν_{k,n₀} M) / #M[ν_{k,n₀}]` with
  `q ^ ((∑ mᵢ) deg ν_{k,n₀}) · #(O ⧸ Res(∏ Fⱼ ^ nⱼ, ν_{k,n₀}))`, and
  `deg ν_{k,n₀}` differs from `p ^ k` by a constant depending only on `n₀`.
* **Resultant growth above the ramification threshold:** once `k > e · ∑ nⱼ deg Fⱼ`, each step from
  `k` to `k + 1` multiplies `Res(∏ Fⱼ ^ nⱼ, ν_{k,n₀})` up to a unit of `O` by `p ^ (∑ nⱼ deg Fⱼ)`
  (`TauCeti.Iwasawa.associated_resultant_growthTransitionPoly`), increasing the `ϖ`-adic valuation
  by `e · ∑ nⱼ deg Fⱼ`.

Two worked examples at the end illustrate the necessity of the hypotheses: in equal characteristic
`p` (`O = 𝔽_p⟦ϖ⟧`, `M = O⟦X⟧ ⧸ (X - ϖ)`), `μ = 0` and `λ = 1` yet `#(M ⧸ ω_n M) = p ^ p ^ n`; in
ramified characteristic `(0, 2)` with `π ^ 2 = 2`, the level-one factor `(1 + π) ^ 2 - 1` has
quotient cardinality `4` before the linear growth regime begins.

## Main results

* `TauCeti.Iwasawa.eventually_natCard_quotSMulTop_growthTransition_of_isPseudoIsomorphism`: growth
  formula in base `q = #(ResidueField O)` from a pseudo-isomorphism to a torsion elementary module.
* `TauCeti.Iwasawa.eventually_natCard_quotSMulTop_growthTransition`: intrinsic growth formula in
  terms of `muInvariant O M` and `lambdaInvariant O M`.
* `TauCeti.Iwasawa.card_quotient_growthTransition_general`: mixed-characteristic growth formula in
  base `p` when `#(ResidueField O) = p ^ f`.
* `TauCeti.Iwasawa.card_quotient_growthTransition`: growth formula over `ℤ_[p]`.
* `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition`: unconditional existence
  of a cutoff `n₀` and constant `ν` for any finitely generated torsion `O⟦X⟧`-module.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition 5.3.17 and Theorem 5.3.18.
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, Theorem 13.13.
-/

public noncomputable section

open Filter IsLocalRing PowerSeries Submodule
open scoped Pointwise Polynomial PowerSeries

namespace TauCeti.Iwasawa

section Helpers

/-- Along a transition tower with finite cokernels on a Noetherian `O⟦X⟧`-module `M`, the kernels
`M[ν_{k,n₀}]` stabilise for `k ≥ K₁` to a finite `O`-module of cardinality `q ^ s`. -/
private theorem exists_eventually_natCard_torsionBy_growthTransition_eq_pow {p : ℕ} [Fact p.Prime]
    {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (n₀ : ℕ)
    (hfin : ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M)) :
    ∃ K₁ s : ℕ, ∀ k, K₁ ≤ k →
      Nat.card (torsionBy O⟦X⟧ M (growthTransition p O n₀ k)) =
        Nat.card (ResidueField O) ^ s := by
  let T : ℕ →o Submodule O⟦X⟧ M :=
    ⟨fun d ↦ torsionBy O⟦X⟧ M (growthTransition p O n₀ (n₀ + d)), fun d₁ d₂ hd x hx ↦ by
      obtain ⟨q, hq⟩ := growthTransition_dvd_of_le p O (n₀ := n₀) (Nat.add_le_add_left hd n₀)
      rw [mem_torsionBy_iff] at hx ⊢
      rw [hq, mul_comm, mul_smul, hx, smul_zero]⟩
  obtain ⟨d₀, hd₀⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance T
  have hT (d : ℕ) : T d = torsionBy O⟦X⟧ M (growthTransition p O n₀ (n₀ + d)) := rfl
  have hfinT : Finite (T d₀) := by
    rw [hT, ← coe_growthTransitionPoly]
    exact finite_torsionBy_of_finite_quotSMulTop (monic_growthTransitionPoly p O n₀ (n₀ + d₀))
      (coe_growthTransitionPoly p O n₀ (n₀ + d₀) ▸ hfin (n₀ + d₀) (Nat.le_add_right n₀ d₀))
  obtain ⟨s, hs⟩ := @TauCeti.IsDiscreteValuationRing.exists_natCard_eq_pow O _ _ _ (T d₀) _
    (Module.compHom (T d₀) (C : O →+* O⟦X⟧)) hfinT
  refine ⟨n₀ + d₀, s, fun k hk ↦ ?_⟩
  have hkeq : torsionBy O⟦X⟧ M (growthTransition p O n₀ k) = T d₀ := by
    rw [hd₀ (k - n₀) (by omega), hT, Nat.add_sub_of_le (le_trans (Nat.le_add_right n₀ d₀) hk)]
  rw [hkeq, hs]

/-- In a discrete valuation ring `O` with `(p : O) = u * ϖ ^ e`, the quotient `O ⧸ (x * p ^ d)` for
`x ≠ 0` has cardinality `q ^ (c + e * d)`, where `c` is the `ϖ`-adic valuation of `x`. -/
private theorem exists_natCard_quotient_span_mul_pow {p : ℕ} {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {u : Oˣ}
    (hpe : (p : O) = u * ϖ ^ e) {x : O} (hx : x ≠ 0) :
    ∃ c : ℕ, ∀ d : ℕ,
      Nat.card (O ⧸ Ideal.span {x * (p : O) ^ d}) =
        Nat.card (ResidueField O) ^ (c + e * d) := by
  have hpspan : Ideal.span {(p : O)} = maximalIdeal O ^ e := by
    rw [hpe, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (mt Ideal.span_singleton_eq_bot.mp hx) hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hc
  refine ⟨c, fun d ↦ ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hc, hpspan,
    ← pow_mul, ← pow_add, TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]

/-- At any single level `k` with `M ⧸ ν_{k,n₀} M` finite and `(p : O) ∈ maximalIdeal O`, a
pseudo-isomorphism `g : M → Elementary O ϖ 0 m F n` expresses `#(M ⧸ ν_{k,n₀} M)` as the product of
`#M[ν_{k,n₀}]`, the vertical factor `q ^ ((∑ mᵢ) deg ν_{k,n₀})`, and the horizontal resultant
quotient `#(O ⧸ Res(∏ Fⱼ ^ nⱼ, ν_{k,n₀}))`. -/
private theorem natCard_quotSMulTop_growthTransition_eq {p : ℕ} [Fact p.Prime] {O M : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) (hpO : (p : O) ∈ maximalIdeal O)
    {a b : ℕ} (m : Fin a → ℕ) {F : Fin b → O[X]}
    (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (n : Fin b → ℕ) [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] {g : M →ₗ[O⟦X⟧] Elementary O ϖ 0 m F n}
    (hg : IsPseudoIsomorphism g) {n₀ k : ℕ}
    (hfin : Finite (QuotSMulTop (growthTransition p O n₀ k) M)) :
    (∏ j, F j ^ n j).resultant (growthTransitionPoly p O n₀ k) ≠ 0 ∧
      (Nat.card (QuotSMulTop (growthTransition p O n₀ k) M) : ℚ) =
        Nat.card (torsionBy O⟦X⟧ M (growthTransition p O n₀ k)) *
          (Nat.card (ResidueField O) ^
              ((∑ i, m i) * (growthTransitionPoly p O n₀ k).natDegree) *
            Nat.card (O ⧸ Ideal.span
              {(∏ j, F j ^ n j).resultant (growthTransitionPoly p O n₀ k)})) := by
  set G := growthTransitionPoly p O n₀ k
  have hcoe : (G : O⟦X⟧) = growthTransition p O n₀ k := coe_growthTransitionPoly p O n₀ k
  rw [← hcoe] at hfin ⊢
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  have hE := (hg.finite_quotSMulTop_iff hdim (G : O⟦X⟧)).mp hfin
  have hres := resultant_ne_zero_of_finite_quotSMulTop_elementary 0 m hF n hE
  refine ⟨hres, ?_⟩
  have htor : Finite (torsionBy O⟦X⟧ M (G : O⟦X⟧)) :=
    finite_torsionBy_of_finite_quotSMulTop (monic_growthTransitionPoly p O n₀ k) hfin
  have hne : (Nat.card (torsionBy O⟦X⟧ M (G : O⟦X⟧)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdiv := hg.natCard_quotSMulTop_div_natCard_torsionBy_eq hdim (G : O⟦X⟧)
  rw [torsionBy_elementary_eq_bot hϖ 0 m hF n (monic_growthTransitionPoly p O n₀ k) hres,
    natCard_quotSMulTop_elementary hϖ m hF n (isDistinguishedAt_growthTransitionPoly hpO n₀ k)
      hres] at hdiv
  simp only [Nat.card_unique, Nat.cast_one, div_one, Nat.cast_mul, Nat.cast_pow] at hdiv
  rw [div_eq_iff hne] at hdiv
  linarith

/-- If a polynomial `G` distinguished at `maximalIdeal O` has positive degree and finite cokernel on
an elementary module `Elementary O ϖ r m F n`, then the free rank `r` is zero. -/
private theorem eq_zero_of_finite_quotSMulTop_elementary {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {ϖ : O} {r a b : ℕ}
    {m : Fin a → ℕ} {F : Fin b → O[X]} {n : Fin b → ℕ} {G : O[X]}
    (hG : G.IsDistinguishedAt (maximalIdeal O)) (hd : 0 < G.natDegree)
    (hfin : Finite (QuotSMulTop (G : O⟦X⟧) (Elementary O ϖ r m F n))) : r = 0 := by
  by_contra hr
  let i₀ : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  let π : Elementary O ϖ r m F n →ₗ[O⟦X⟧] O⟦X⟧ :=
    (LinearMap.proj i₀).comp (LinearMap.fst O⟦X⟧ _ _)
  have hsurj : Function.Surjective π := fun y ↦ ⟨(Pi.single i₀ y, 0), by simp [π]⟩
  have hspan : (G : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ O⟦X⟧) = Ideal.span {(G : O⟦X⟧)} := by
    rw [← ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  have hinf := hG.isWeierstrassFactorizationAt.infinite_quotient hd
  rw [← hspan] at hinf
  exact not_finite_iff_infinite.mpr hinf
    (Finite.of_surjective _ (QuotSMulTop.map_surjective _ hsurj))

/-- A local domain in which a rational prime `p` is a nonzero nonunit has characteristic zero. -/
private theorem charZero_of_mem_maximalIdeal_of_ne_zero {p : ℕ} [Fact p.Prime] {O : Type*}
    [CommRing O] [IsDomain O] [IsLocalRing O] (hp_mem : (p : O) ∈ maximalIdeal O)
    (hp_ne : (p : O) ≠ 0) : CharZero O := by
  rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | h0
  · exfalso
    rcases eq_or_ne (ringChar O) p with heq | hne
    · exact hp_ne (heq ▸ ringChar.Nat.cast_ringChar)
    · obtain ⟨a, b, hab⟩ := (hq.coprime_iff_not_dvd.mpr fun hdvd ↦
        hne ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hdvd)).isCoprime
      have h1 : (1 : O) ∈ maximalIdeal O := by
        have hcast := congr_arg (Int.cast : ℤ → O) hab
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
          ringChar.Nat.cast_ringChar, mul_zero, zero_add] at hcast
        rw [← hcast]
        exact Ideal.mul_mem_left _ _ hp_mem
      exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · have := ringChar.of_eq h0
    exact CharP.charP_to_charZero O

end Helpers

section GrowthFormula

/-- **Iwasawa's growth formula for a pseudo-isomorphism onto an elementary module.** Let `O` be a
complete discrete valuation ring of mixed characteristic `(0, p)` with `(p : O) = u * ϖ ^ e`
(`0 < e`) and finite residue field of cardinality `q`. If `M` is pseudo-isomorphic to
`Elementary O ϖ 0 m F n` with distinguished `Fⱼ` and `M ⧸ ν_{k,n₀} M` is finite for every `k ≥ n₀`,
then `#(M ⧸ ν_{k,n₀} M) = q ^ ((∑ mᵢ) p ^ k + e (∑ nⱼ deg Fⱼ) k + ν)` for all sufficiently large
`k`. -/
theorem eventually_natCard_quotSMulTop_growthTransition_of_isPseudoIsomorphism {p : ℕ}
    [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {e : ℕ} (he : 0 < e) {u : Oˣ} (hpe : (p : O) = u * ϖ ^ e) {a b : ℕ} (m : Fin a → ℕ)
    {F : Fin b → O[X]} (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (n : Fin b → ℕ)
    {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (g : M →ₗ[O⟦X⟧] Elementary O ϖ 0 m F n) (hg : IsPseudoIsomorphism g) (n₀ : ℕ)
    (hfin : ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M)) :
    ∃ ν : ℤ, ∀ᶠ k in atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ k) M) : ℚ) =
        (Nat.card (ResidueField O) : ℚ) ^
          ((((∑ i, m i) * p ^ k + e * (∑ j, n j * (F j).natDegree) * k : ℕ) : ℤ) + ν) := by
  have hpO : (p : O) ∈ maximalIdeal O := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hpe, ← Nat.sub_add_cancel he, pow_succ]
    exact ⟨↑u * ϖ ^ (e - 1), by ring⟩
  have hmax_le : maximalIdeal O ^ e ≤ Ideal.span {(p : O)} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hpe,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  set P : O[X] := ∏ j, F j ^ n j
  have hP : P.IsDistinguishedAt (maximalIdeal O) :=
    Polynomial.isDistinguishedAt_prod fun j _ ↦ (hF j).pow (n j)
  have hPdeg : P.natDegree = ∑ j, n j * (F j).natDegree := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ ↦ (hF j).monic.pow _]
    exact Finset.sum_congr rfl fun j _ ↦ (hF j).monic.natDegree_pow (n j)
  obtain ⟨K₁, s, hs⟩ := exists_eventually_natCard_torsionBy_growthTransition_eq_pow n₀ hfin
  let K₂ := max n₀ (P.natDegree * e + 1)
  have hresK₂ := (natCard_quotSMulTop_growthTransition_eq hϖ hpO m hF n hg
    (hfin K₂ (le_max_left _ _))).1
  obtain ⟨c, hc⟩ := exists_natCard_quotient_span_mul_pow hϖ hpe hresK₂
  let d₀ := if n₀ = 0 then 0 else p ^ (n₀ - 1)
  refine ⟨(s + c : ℤ) - (∑ i, m i) * d₀ - e * P.natDegree * K₂,
    eventually_atTop.mpr ⟨max K₁ K₂, fun k hk ↦ ?_⟩⟩
  have hk₁ : K₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : K₂ ≤ k := (le_max_right _ _).trans hk
  have hn₀k : n₀ ≤ k := (le_max_left _ _).trans hk₂
  have heq := (natCard_quotSMulTop_growthTransition_eq hϖ hpO m hF n hg (hfin k hn₀k)).2
  have hassoc := associated_resultant_growthTransitionPoly (p := p) hP hmax_le
    ((Ideal.jacobson_bot (R := O)).symm ▸ IsAdicComplete.le_jacobson (maximalIdeal O) hpO)
    ((le_max_left _ _).trans (Nat.le_succ K₂))
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) hk₂
  rw [hs k hk₁, Ideal.span_singleton_eq_span_singleton.mpr hassoc, hc (P.natDegree * (k - K₂))]
    at heq
  push_cast at heq
  rw [← pow_add, ← pow_add] at heq
  rw [heq, ← zpow_natCast]
  congr 1
  have hdeg := natDegree_growthTransitionPoly p O (Nat.le_trans hn₀k (Nat.le_succ k))
  change (growthTransitionPoly p O n₀ k).natDegree + d₀ = p ^ k at hdeg
  have hdegZ : ((growthTransitionPoly p O n₀ k).natDegree : ℤ) = (p : ℤ) ^ k - d₀ := by
    rw [← Nat.cast_pow]
    omega
  have hsubZ : ((k - K₂ : ℕ) : ℤ) = (k : ℤ) - K₂ := Int.ofNat_sub hk₂
  push_cast [hPdeg]
  rw [hdegZ, hsubZ]
  ring

/-- **Iwasawa's growth formula (intrinsic form).** Let `O` be a complete discrete valuation ring of
mixed characteristic `(0, p)` with `(p : O) = u * ϖ ^ e` (`0 < e`) and finite residue field of
cardinality `q`. For any finitely generated `O⟦X⟧`-module `M` and level `n₀` such that
`M ⧸ ν_{k,n₀} M` is finite for all `k ≥ n₀`, there exists `ν : ℤ` such that
`#(M ⧸ ν_{k,n₀} M) = q ^ (μ(M) p ^ k + e λ(M) k + ν)` for all sufficiently large `k`. -/
theorem eventually_natCard_quotSMulTop_growthTransition {p : ℕ} [Fact p.Prime] {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : 0 < e) {u : Oˣ}
    (hpe : (p : O) = u * ϖ ^ e) {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (n₀ : ℕ) (hfin : ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M)) :
    ∃ ν : ℤ, ∀ᶠ k in atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ k) M) : ℚ) =
        (Nat.card (ResidueField O) : ℚ) ^
          (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) := by
  have hpO : (p : O) ∈ maximalIdeal O := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hpe, ← Nat.sub_add_cancel he, pow_succ]
    exact ⟨↑u * ϖ ^ (e - 1), by ring⟩
  obtain ⟨r, a, b, m, F, n, -, hFn, g, hg⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  have hF (j : Fin b) := (hFn j).1
  have hirr (j : Fin b) := (hFn j).2.1
  have hdeg_pos : 0 < (growthTransitionPoly p O n₀ (n₀ + 1)).natDegree := by
    have hdeg := natDegree_growthTransitionPoly p O (n₀ := n₀) (n := n₀ + 1) (by omega)
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
    · simp only [↓reduceIte, add_zero, zero_add, pow_one] at hdeg
      rw [zero_add, hdeg]
      omega
    · rw [ite_eq_right hn₀.ne'] at hdeg
      have hlt : p ^ (n₀ - 1) < p ^ (n₀ + 1) := Nat.pow_lt_pow_right hp1 (by omega)
      omega
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  have hE := (hg.finite_quotSMulTop_iff hdim _).mp
    (coe_growthTransitionPoly p O n₀ (n₀ + 1) ▸ hfin (n₀ + 1) (Nat.le_succ n₀))
  obtain rfl : r = 0 := eq_zero_of_finite_quotSMulTop_elementary
    (isDistinguishedAt_growthTransitionPoly hpO n₀ (n₀ + 1)) hdeg_pos hE
  rw [hg.muInvariant_eq_sum hϖ fun j ↦ (hF j).monic, hg.lambdaInvariant_eq_sum hϖ hF hirr]
  exact eventually_natCard_quotSMulTop_growthTransition_of_isPseudoIsomorphism hϖ he hpe m hF n g
    hg n₀ hfin

/-- **Iwasawa's growth formula over a mixed-characteristic coefficient ring**
(Neukirch–Schmidt–Wingberg, Proposition 5.3.17): with `(p : O) = u * ϖ ^ e` (`0 < e`), residue field
of order `p ^ f`, and a pseudo-isomorphism from `M` onto `Elementary O ϖ 0 m F n` with `μ = ∑ mᵢ`
and `λ = ∑ nⱼ deg Fⱼ`, if the quotients `M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite, then
`#(M ⧸ ν_{k,n₀} M) = p ^ (f μ p ^ k + e f λ k + ν)` for all sufficiently large `k`. -/
theorem card_quotient_growthTransition_general (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (ϖ : O) (hϖ : Irreducible ϖ) (e f : ℕ) (he : 0 < e)
    (u : Oˣ) (hpe : (p : O) = u * ϖ ^ e) (hres : Nat.card (IsLocalRing.ResidueField O) = p ^ f)
    {a b : ℕ} (m : Fin a → ℕ) (F : Fin b → O[X]) (n : Fin b → ℕ)
    (hF : ∀ j, (F j).IsDistinguishedAt (IsLocalRing.maximalIdeal O)) (M : Type*)
    [AddCommGroup M] [Module (PowerSeries O) M] [Module.Finite (PowerSeries O) M]
    (g : M →ₗ[PowerSeries O] Elementary O ϖ 0 m F n) (hg : IsPseudoIsomorphism g) (n₀ : ℕ)
    (hfin : ∀ k, n₀ ≤ k →
      Finite (M ⧸ (growthTransition p O n₀ k • (⊤ : Submodule (PowerSeries O) M)))) :
    ∃ ν : ℤ, ∀ᶠ k in atTop,
      (Nat.card (M ⧸ (growthTransition p O n₀ k • (⊤ : Submodule (PowerSeries O) M))) : ℚ) =
        (p : ℚ) ^ (((f * (∑ i, m i) * p ^ k + e * f * (∑ j, n j * (F j).natDegree) * k : ℕ) : ℤ)
          + ν) := by
  obtain ⟨ν₀, hν₀⟩ := eventually_natCard_quotSMulTop_growthTransition_of_isPseudoIsomorphism
    hϖ he hpe m hF n g hg n₀ hfin
  refine ⟨f * ν₀, hν₀.mono fun k hk ↦ ?_⟩
  change (Nat.card (QuotSMulTop (growthTransition p O n₀ k) M) : ℚ) = _
  rw [hk, hres, Nat.cast_pow, ← zpow_natCast (p : ℚ) f, ← zpow_mul]
  congr 1
  push_cast
  ring

/-- **Iwasawa's growth formula over `ℤ_[p]`** (Neukirch–Schmidt–Wingberg, Proposition 5.3.17): if
`M` is pseudo-isomorphic to the torsion elementary module `Elementary ℤ_[p] p 0 m F n` with
`μ = ∑ mᵢ` and `λ = ∑ nⱼ deg Fⱼ`, and the quotients `M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite, then
`#(M ⧸ ν_{k,n₀} M) = p ^ (μ p ^ k + λ k + ν)` for all sufficiently large `k`. -/
theorem card_quotient_growthTransition (p : ℕ) [Fact p.Prime] {a b : ℕ} (m : Fin a → ℕ)
    (F : Fin b → ℤ_[p][X]) (n : Fin b → ℕ)
    (hF : ∀ j, (F j).IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p])) (M : Type*)
    [AddCommGroup M] [Module (PowerSeries ℤ_[p]) M] [Module.Finite (PowerSeries ℤ_[p]) M]
    (f : M →ₗ[PowerSeries ℤ_[p]] Elementary ℤ_[p] (p : ℤ_[p]) 0 m F n)
    (hf : IsPseudoIsomorphism f)
    (n₀ : ℕ) (hfin : ∀ k, n₀ ≤ k →
      Finite (M ⧸ (growthTransition p ℤ_[p] n₀ k • (⊤ : Submodule (PowerSeries ℤ_[p]) M)))) :
    ∃ ν : ℤ, ∀ᶠ k in atTop,
      (Nat.card (M ⧸ (growthTransition p ℤ_[p] n₀ k •
          (⊤ : Submodule (PowerSeries ℤ_[p]) M))) : ℚ) =
        (p : ℚ) ^ ((((∑ i, m i) * p ^ k + (∑ j, n j * (F j).natDegree) * k : ℕ) : ℤ) + ν) := by
  have hpe : (p : ℤ_[p]) = (1 : ℤ_[p]ˣ) * (p : ℤ_[p]) ^ 1 := by simp
  have hres : Nat.card (ResidueField ℤ_[p]) = p ^ 1 := by
    rw [PadicInt.card_residueField, pow_one]
  obtain ⟨ν, hν⟩ := card_quotient_growthTransition_general p ℤ_[p] (p : ℤ_[p])
    PadicInt.irreducible_p 1 1 Nat.one_pos 1 hpe hres m F n hF M f hf n₀ hfin
  exact ⟨ν, by simpa only [one_mul] using hν⟩

/-- **Unconditional existence of a cutoff and Iwasawa growth.** Over a complete discrete valuation
ring `O` of mixed characteristic `(0, p)` with `(p : O) = u * ϖ ^ e` (`0 < e`) and finite residue
field of cardinality `q`, every finitely generated torsion `O⟦X⟧`-module `M` admits a cutoff `n₀`
and an integer `ν` such that `M ⧸ ν_{k,n₀} M` is finite for all `k ≥ n₀` and has cardinality
`q ^ (μ(M) p ^ k + e λ(M) k + ν)` for all sufficiently large `k`. -/
theorem exists_eventually_natCard_quotSMulTop_growthTransition {p : ℕ} [Fact p.Prime] {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : 0 < e) {u : Oˣ}
    (hpe : (p : O) = u * ϖ ^ e) {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, (∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M)) ∧
      ∃ ν : ℤ, ∀ᶠ k in atTop,
        (Nat.card (QuotSMulTop (growthTransition p O n₀ k) M) : ℚ) =
          (Nat.card (ResidueField O) : ℚ) ^
            (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) := by
  have hpO : (p : O) ∈ maximalIdeal O := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hpe, ← Nat.sub_add_cancel he, pow_succ]
    exact ⟨↑u * ϖ ^ (e - 1), by ring⟩
  have hp_ne : (p : O) ≠ 0 := by
    rw [hpe]
    exact mul_ne_zero u.ne_zero (pow_ne_zero e hϖ.ne_zero)
  have : CharZero O := charZero_of_mem_maximalIdeal_of_ne_zero hpO hp_ne
  obtain ⟨n₀, hfin⟩ := exists_finite_quotSMulTop_growthTransition (p := p) hM
  exact ⟨n₀, hfin, eventually_natCard_quotSMulTop_growthTransition hϖ he hpe n₀ hfin⟩

end GrowthFormula

-- Equal characteristic: `O = 𝔽_p⟦ϖ⟧` and `M = O⟦X⟧ ⧸ (X - ϖ)` have `μ = 0` and `λ = 1`, yet
-- `ω_n = ϖ ^ p ^ n` on `M ≅ O` and `#(M ⧸ ω_n M) = p ^ p ^ n`.
example (p : ℕ) [Fact p.Prime] :
    let O := PowerSeries (ZMod p)
    let M := PowerSeries O ⧸
      Ideal.span {(PowerSeries.X - PowerSeries.C (PowerSeries.X : O) : PowerSeries O)}
    ∀ n : ℕ, Nat.card (M ⧸ (growthTransition p O 0 n • (⊤ : Submodule (PowerSeries O) M))) =
      p ^ (p ^ n) := by
  intro O M n
  have : IsAdicComplete (maximalIdeal (ZMod p)) (ZMod p) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let F : O[X] := Polynomial.X - Polynomial.C (X : O)
  have hF : F.IsDistinguishedAt (maximalIdeal O) := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, Polynomial.monic_X_sub_C _⟩
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hk
    subst hk
    simp only [F, Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff]
    exact (PowerSeries.irreducible_X (R := ZMod p)).not_isUnit
  have hFcoe : (F : O⟦X⟧) = X - C (X : O) := by simp [F]
  have : CharP O p := charP_of_injective_ringHom C_injective p
  have : CharP O[X] p := Polynomial.charP
  have hG : growthTransitionPoly p O 0 n = Polynomial.X ^ p ^ n := by
    rw [growthTransitionPoly_zero_left, add_pow_char_pow, one_pow, add_sub_cancel_left]
  have H : (X - C (X : O) : O⟦X⟧).IsWeierstrassFactorizationAt F 1 (maximalIdeal O) :=
    hFcoe ▸ hF.isWeierstrassFactorizationAt
  have hres : F.resultant (growthTransitionPoly p O 0 n) = (X : O) ^ p ^ n := by
    dsimp only [F]
    rw [hG, Polynomial.natDegree_X_sub_C, Polynomial.resultant_X_sub_C_left _ _ _ le_rfl]
    simp
  have hnorm := (H.norm_mk_coe_eq_resultant (growthTransitionPoly p O 0 n)).trans hres
  have hne : (X : O) ^ p ^ n ≠ 0 := pow_ne_zero _ (PowerSeries.irreducible_X (R := ZMod p)).ne_zero
  change Nat.card (QuotSMulTop (growthTransition p O 0 n) M) = p ^ (p ^ n)
  rw [← coe_growthTransitionPoly, H.natCard_quotSMulTop (hnorm.symm ▸ hne), hnorm,
    ← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    Nat.card_congr PowerSeries.residueFieldOfPowerSeries.toEquiv, Nat.card_zmod]

-- For `p = 2`, `π ^ 2 = 2` and residue field `𝔽₂`, the level-one order `#(O ⧸ ((1 + π) ^ 2 - 1))`
-- is `4` before the ramification threshold is passed.
example (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (π : O) (hπ : Irreducible π)
    (hπ2 : π ^ 2 = (2 : O)) (hk : Nat.card (IsLocalRing.ResidueField O) = 2) :
    (1 + π) ^ 2 - 1 = π ^ 2 * (1 + π) ∧ IsUnit (1 + π) ∧
      Nat.card (O ⧸ Ideal.span {(1 + π) ^ 2 - 1}) = 4 := by
  have h1 : (1 + π) ^ 2 - 1 = π ^ 2 * (1 + π) := by
    calc
      (1 + π) ^ 2 - 1 = π ^ 2 + 2 * π := by ring
      _ = π ^ 2 + π ^ 2 * π := by rw [hπ2]
      _ = π ^ 2 * (1 + π) := by ring
  have hπ_mem : π ∈ maximalIdeal O := hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hu : IsUnit (1 + π) := by
    rw [← notMem_maximalIdeal]
    intro hmem
    have h1mem : (1 : O) ∈ maximalIdeal O := by
      simpa using sub_mem hmem hπ_mem
    exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1mem isUnit_one)
  refine ⟨h1, hu, ?_⟩
  rw [h1, mul_comm, Ideal.span_singleton_mul_left_unit hu, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq, TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, hk]
  norm_num

end TauCeti.Iwasawa
