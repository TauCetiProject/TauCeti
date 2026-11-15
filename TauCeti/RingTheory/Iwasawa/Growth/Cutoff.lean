/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.Delta
public import TauCeti.RingTheory.Iwasawa.EulerQuotient
public import TauCeti.RingTheory.Iwasawa.Growth.Transition

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.LinearAlgebra.LinearMap.Cardinality
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.Iwasawa.CyclotomicGrowth
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
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
   divides `ξ_j` for some `j ≥ n₀` if and only if it divides none of the factors of
   `ω_{n₀ - 1} = ∏_{j < n₀} ξ_j` while dividing `ω_{j₀}`, which happens exactly when
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

* `TauCeti.Iwasawa.IsPseudoIsomorphism.finite_smul_deltaSubmodule_iff`: over `O⟦X⟧`, a
  pseudo-isomorphism onto a finitely generated torsion module preserves the finiteness of
  `a • deltaSubmodule p O M`.
* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`: all
  `M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite iff `Res(F_M, ξ_j) ≠ 0` for all `j ≥ n₀`.
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

/-- For prime `p`, the supremum of the kernels `M[ν_{m,0}]` is `deltaSubmodule p O M`. -/
theorem iSup_torsionBy_growthTransition_zero (p : ℕ) [Fact p.Prime] (O M : Type*) [CommRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] :
    (⨆ m, torsionBy O⟦X⟧ M (growthTransition p O 0 m)) = deltaSubmodule p O M := by
  simp_rw [growthTransition_zero_left, deltaSubmodule_def]

section Transport

/-- A linear map with finite kernel reflects the finiteness of `a • deltaSubmodule p O _`. -/
theorem finite_smul_deltaSubmodule_of_finite_ker {p : ℕ} {O M N : Type*} [CommRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [AddCommGroup N] [Module O⟦X⟧ N] {f : M →ₗ[O⟦X⟧] N}
    (hker : Finite (LinearMap.ker f)) (a : O⟦X⟧)
    (hN : Finite ↥(a • deltaSubmodule p O N)) :
    Finite ↥(a • deltaSubmodule p O M) := by
  have hmap (x : M) (hx : x ∈ a • deltaSubmodule p O M) : f x ∈ a • deltaSubmodule p O N := by
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨f y, f.map_deltaSubmodule_le p ⟨y, hy, rfl⟩, (map_smul f a y).symm⟩
  let g := f.restrict hmap
  have hgker : Finite (LinearMap.ker g) := by
    refine Finite.of_injective (fun x : LinearMap.ker g ↦
      (⟨x.1.1, congr_arg Subtype.val x.2⟩ : LinearMap.ker f)) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj hxy))
  refine Nat.finite_of_card_ne_zero ?_
  rw [g.card_eq_card_range_mul_card_ker]
  exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- Over `O⟦X⟧`, a pseudo-isomorphism onto a finitely generated torsion module preserves the
finiteness of `a • deltaSubmodule p O _`. -/
theorem IsPseudoIsomorphism.finite_smul_deltaSubmodule_iff {p : ℕ} {O M N : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [AddCommGroup M]
    [Module O⟦X⟧ M] [AddCommGroup N] [Module O⟦X⟧ N] [Module.Finite O⟦X⟧ N]
    (hN : Module.IsTorsion O⟦X⟧ N) {f : M →ₗ[O⟦X⟧] N} (hf : IsPseudoIsomorphism f) (a : O⟦X⟧) :
    Finite ↥(a • deltaSubmodule p O M) ↔ Finite ↥(a • deltaSubmodule p O N) := by
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  obtain ⟨g, hg⟩ := hf.exists_reverse hN
  exact ⟨finite_smul_deltaSubmodule_of_finite_ker
      ((isPseudoIsomorphism_iff_finite hdim).mp hg).1 a,
    finite_smul_deltaSubmodule_of_finite_ker ((isPseudoIsomorphism_iff_finite hdim).mp hf).1 a⟩

end Transport

section Blocks

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]

/-- The cyclotomic delta submodule of a vertical block `O⟦X⟧ ⧸ (ϖ ^ m)` vanishes. -/
@[simp]
theorem deltaSubmodule_quotient_span_C_pow {ϖ : O} (hϖ : Irreducible ϖ) (m : ℕ) :
    deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)}) = ⊥ := by
  refine eq_bot_iff.mpr (deltaSubmodule_le_iff _ _ _ |>.mpr fun k ↦ ?_)
  rw [torsionBy_quotient_span_C_pow_one_add_X_pow_sub_one_eq_bot hϖ.prime
    (pow_ne_zero k (Fact.out : p.Prime).ne_zero) m]

/-- Over a characteristic-zero domain, a monic irreducible polynomial dividing `ξ_{j₀}` divides no
`ξ_j` with `j ≠ j₀`. -/
private theorem not_dvd_cyclotomic_of_dvd [CharZero O] {F : O[X]} (hF : F.Monic)
    (hirr : Irreducible F) {j j₀ : ℕ} (hne : j ≠ j₀)
    (hdvd : F ∣ (Polynomial.cyclotomic (p ^ j₀) O).comp (Polynomial.X + 1)) :
    ¬ F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) := by
  intro hdj
  let φ := algebraMap O (FractionRing O)
  have hpne : p ^ j ≠ p ^ j₀ :=
    (Nat.pow_right_injective (Fact.out : p.Prime).one_lt).ne hne
  have hcop : IsCoprime
      (((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)).map φ)
      (((Polynomial.cyclotomic (p ^ j₀) O).comp (Polynomial.X + 1)).map φ) := by
    simpa [Polynomial.map_comp] using
      Polynomial.isCoprime_cyclotomic_comp_X_add_one (R := FractionRing O) hpne
  have hu : IsUnit (F.map φ) :=
    hcop.isUnit_of_dvd' (Polynomial.map_dvd φ hdj) (Polynomial.map_dvd φ hdvd)
  have hdeg : F.natDegree = 0 := by
    rw [← hF.natDegree_map φ]
    exact Polynomial.natDegree_eq_zero_of_isUnit hu
  exact hirr.not_isUnit (Polynomial.eq_one_of_monic_natDegree_zero hF hdeg ▸ isUnit_one)

/-- If `F` is monic, `n ≠ 0`, and `torsionBy O⟦X⟧ (O⟦X⟧ ⧸ (F)) a = ⊥`, then multiplication by
`a * F ^ (n - 1)` embeds `O⟦X⟧ ⧸ (F)` injectively into `O⟦X⟧ ⧸ (F ^ n)`. -/
private theorem exists_injective_quotient_span_pow {F : O[X]} (hF : F.Monic) {n : ℕ} (hn : n ≠ 0)
    {a : O⟦X⟧} (ha : torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) a = ⊥) :
    ∃ ψ : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)} →ₗ[O⟦X⟧]
        O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)},
      Function.Injective ψ ∧
        ∀ s : O⟦X⟧, ψ (Ideal.Quotient.mk _ s) =
          Ideal.Quotient.mk _ (a * ((F ^ (n - 1) : O[X]) : O⟦X⟧) * s) := by
  set Fn1 : O⟦X⟧ := ((F ^ (n - 1) : O[X]) : O⟦X⟧)
  have hFn : ((F ^ n : O[X]) : O⟦X⟧) = Fn1 * (F : O⟦X⟧) := by
    rw [← Polynomial.coe_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
  have hFn1_ne : Fn1 ≠ 0 := (Polynomial.coe_eq_zero_iff).not.mpr (hF.pow _).ne_zero
  let ψ : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)} →ₗ[O⟦X⟧]
      O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)} :=
    Submodule.liftQ _ ((Ideal.Quotient.mkₐ O⟦X⟧ _).toLinearMap ∘ₗ
      LinearMap.lsmul O⟦X⟧ O⟦X⟧ (a * Fn1)) fun s hs ↦ by
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply, smul_eq_mul,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, LinearMap.mem_ker,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hFn]
      exact ⟨a * t, by ring⟩
  refine ⟨ψ, ?_, fun _ ↦ rfl⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro q hq
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [LinearMap.mem_ker] at hq
  have hq' : Ideal.Quotient.mk (Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) (a * Fn1 * s) = 0 := hq
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hFn,
    show a * Fn1 * s = Fn1 * (a * s) by ring, mul_dvd_mul_iff_left hFn1_ne,
    ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem] at hq'
  have hmem : Ideal.Quotient.mk (Ideal.span {(F : O⟦X⟧)}) s ∈
      torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) a := by
    rw [mem_torsionBy_iff, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Ideal.Quotient.mk_eq_mk]
    exact hq'
  rwa [ha, mem_bot] at hmem

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
  obtain ⟨q, hq⟩ := growthTransition_dvd_of_le p O (n₀ := 0) (le_max_left m n₀)
  have hxk : growthTransition p O 0 k • x = 0 := by
    rw [hq, mul_comm, mul_smul, hm, smul_zero]
  have hkres : (F ^ n).resultant (growthTransitionPoly p O n₀ k) ≠ 0 := by
    rw [growthTransitionPoly_eq_prod_cyclotomic, (hF.pow n).monic.resultant_prod_right,
      Finset.prod_ne_zero_iff]
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
  set W : O[X] := ∏ j ∈ Finset.range n₀, growthTransitionPoly p O j j
  have hWres : F.resultant W ≠ 0 := by
    rw [hF.monic.resultant_prod_right, Finset.prod_ne_zero_iff]
    intro j hj
    rw [growthTransitionPoly_self_eq_cyclotomic, Ne, hF.monic.resultant_eq_zero_iff_dvd hirr]
    exact not_dvd_cyclotomic_of_dvd hF.monic hirr (by have := Finset.mem_range.mp hj; omega) hdvd
  have hQtor : torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) (W : O⟦X⟧) = ⊥ :=
    hF.isWeierstrassFactorizationAt.torsionBy_eq_bot_iff _ |>.mpr
      (hF.isWeierstrassFactorizationAt.norm_mk_coe_eq_resultant _ ▸ hWres)
  obtain ⟨ψ, hψ_inj, hψ_mk⟩ := exists_injective_quotient_span_pow hF.monic hn hQtor
  have hψ_mem (q : O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)}) :
      ψ q ∈ (∏ j ∈ Finset.range n₀, growthTransition p O j j) •
        deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hw : (W : O⟦X⟧) = ∏ j ∈ Finset.range n₀, growthTransition p O j j := by
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
      simp [Polynomial.coeToPowerSeries.ringHom_apply]
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨Ideal.Quotient.mk _ (((F ^ (n - 1) : O[X]) : O⟦X⟧) * s),
      (mem_deltaSubmodule p O _ _).mpr ⟨j₀, ?_⟩, ?_⟩
    · obtain ⟨u, hu⟩ : F ∣ (1 + Polynomial.X) ^ p ^ j₀ - 1 := by
        rw [← growthTransitionPoly_zero_left p O j₀, growthTransitionPoly_eq_prod_cyclotomic]
        exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩))
      have hcoe : ((1 + X) ^ p ^ j₀ - 1 : O⟦X⟧) = (F : O⟦X⟧) * (u : O⟦X⟧) := by
        simpa using congr_arg (Polynomial.coeToPowerSeries.ringHom (R := O)) hu
      have hFn : ((F ^ n : O[X]) : O⟦X⟧) = (F : O⟦X⟧) * ((F ^ (n - 1) : O[X]) : O⟦X⟧) := by
        rw [← Polynomial.coe_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hFn,
        hcoe]
      exact ⟨(u : O⟦X⟧) * s, by ring⟩
    · rw [← hw, hψ_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        Ideal.Quotient.mk_eq_mk, mul_assoc]
  have hdeg : 0 < F.natDegree := Nat.pos_of_ne_zero fun h0 ↦
    hirr.not_isUnit (Polynomial.eq_one_of_monic_natDegree_zero hF.monic h0 ▸ isUnit_one)
  have := hF.isWeierstrassFactorizationAt.infinite_quotient hdeg
  exact Infinite.of_injective (fun q ↦ (⟨ψ q, hψ_mem q⟩ : _)) fun q₁ q₂ h ↦
    hψ_inj (congr_arg Subtype.val h)

/-- On a torsion elementary module `E = Elementary O ϖ 0 m F n` with distinguished `Fᵢ`, if
`Res(∏ᵢ Fᵢ ^ nᵢ, ξ_j) ≠ 0` for all `j ≥ n₀`, then `(∏_{j < n₀} ν_{j,j}) • M_δ = ⊥`. -/
private theorem smul_deltaSubmodule_elementary_eq_bot {ϖ : O} (hϖ : Irreducible ϖ) {a b : ℕ}
    (m : Fin a → ℕ) {F : Fin b → O[X]} (hF : ∀ i, (F i).IsDistinguishedAt (maximalIdeal O))
    (n : Fin b → ℕ) (n₀ : ℕ)
    (hres : ∀ j, n₀ ≤ j →
      (∏ i, F i ^ n i).resultant
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0) :
    (∏ j ∈ Finset.range n₀, growthTransition p O j j) •
      deltaSubmodule p O (Elementary O ϖ 0 m F n) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨x₀, x₁, x₂⟩, hx, rfl⟩
  refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_))
  · let π₁ : Elementary O ϖ 0 m F n →ₗ[O⟦X⟧] O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m i)} :=
      (LinearMap.proj i).comp ((LinearMap.fst O⟦X⟧ _ _).comp (LinearMap.snd O⟦X⟧ _ _))
    have hx₁ : x₁ i ∈ deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m i)}) :=
      π₁.map_deltaSubmodule_le p ⟨(x₀, x₁, x₂), hx, rfl⟩
    rw [deltaSubmodule_quotient_span_C_pow hϖ (m i), mem_bot] at hx₁
    simp [hx₁]
  · let π₂ : Elementary O ϖ 0 m F n →ₗ[O⟦X⟧] O⟦X⟧ ⧸ Ideal.span {((F i ^ n i : O[X]) : O⟦X⟧)} :=
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

/-- On a torsion elementary module `E = Elementary O ϖ 0 m F n` with irreducible distinguished
`Fᵢ` and `nᵢ ≠ 0` over a characteristic-zero ring `O`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite iff
`Res(∏ᵢ Fᵢ ^ nᵢ, ξ_j) ≠ 0` for all `j ≥ n₀`. -/
private theorem finite_smul_deltaSubmodule_elementary_iff [CharZero O] {ϖ : O}
    (hϖ : Irreducible ϖ) {a b : ℕ} (m : Fin a → ℕ) {F : Fin b → O[X]}
    (hF : ∀ i, (F i).IsDistinguishedAt (maximalIdeal O)) (hirr : ∀ i, Irreducible (F i))
    {n : Fin b → ℕ} (hn : ∀ i, n i ≠ 0) (n₀ : ℕ) :
    Finite ↥((∏ j ∈ Finset.range n₀, growthTransition p O j j) •
        deltaSubmodule p O (Elementary O ϖ 0 m F n)) ↔
      ∀ j, n₀ ≤ j →
        (∏ i, F i ^ n i).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  have hpow_res (i : Fin b) (G : O[X]) :
      (F i ^ n i).resultant G = (F i).resultant G ^ n i := by
    have hpow : F i ^ n i = ∏ _ ∈ Finset.range (n i), F i := by simp
    rw [hpow, Polynomial.resultant_prod_left_of_monic _ fun _ _ ↦ (hF i).monic,
      Finset.prod_const, Finset.card_range]
  refine ⟨fun hfin j hj hzero ↦ ?_, fun hres ↦ ?_⟩
  · rw [Polynomial.resultant_prod_left_of_monic _ fun i _ ↦ (hF i).monic.pow _,
      Finset.prod_eq_zero_iff] at hzero
    obtain ⟨i, -, hi⟩ := hzero
    rw [hpow_res, pow_eq_zero_iff (hn i), (hF i).monic.resultant_eq_zero_iff_dvd (hirr i)] at hi
    let H (j : Fin b) := O⟦X⟧ ⧸ Ideal.span {((F j ^ n j : O[X]) : O⟦X⟧)}
    let ι : H i →ₗ[O⟦X⟧] Elementary O ϖ 0 m F n :=
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

/-- Over a local ring, a polynomial distinguished at the maximal ideal has unit resultant with
every polynomial whose constant coefficient is a unit. -/
private theorem isUnit_resultant_of_isUnit_coeff_zero {R : Type*} [CommRing R] [IsLocalRing R]
    {P Q : R[X]} (hP : P.IsDistinguishedAt (maximalIdeal R)) (hQ : IsUnit (Q.coeff 0)) :
    IsUnit (P.resultant Q) := by
  nontriviality R
  rw [Polynomial.isUnit_resultant_iff_isCoprime hP.monic]
  refine Polynomial.isCoprime_of_isCoprime_map (ringJacobson_eq_maximalIdeal (R := R)).ge
    hP.monic ?_
  rw [hP.map_eq_X_pow]
  have heval : IsUnit ((Q.map (Ideal.Quotient.mk (maximalIdeal R))).eval 0) := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    exact hQ.map _
  simpa using (Polynomial.isCoprime_X_sub_C_of_isUnit_eval (a := 0) heval).pow_left

/-- When `G` is distinguished at `maximalIdeal O`, a finitely generated torsion `O⟦X⟧`-module `M`
has finite cokernel `M ⧸ GM` iff `Res(F_M, G) ≠ 0`. -/
private theorem finite_quotSMulTop_iff_resultant_charPoly_ne_zero {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M) {G : O[X]}
    (hG : G.IsDistinguishedAt (maximalIdeal O)) :
    Finite (QuotSMulTop (G : O⟦X⟧) M) ↔ (charPoly O M).resultant G ≠ 0 := by
  refine ⟨resultant_charPoly_ne_zero_of_finite_quotSMulTop, fun hres ↦ ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  obtain rfl : r = 0 := eq_zero_of_isTorsion_elementary (hf.isTorsion_iff.mp hM)
  have hF (j : Fin b) := (hFn j).1
  rw [hf.charPoly_eq_prod hϖ hF fun j ↦ (hFn j).2.1] at hres
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  rw [hf.finite_quotSMulTop_iff hdim]
  refine Nat.finite_of_card_ne_zero ?_
  rw [natCard_quotSMulTop_elementary hϖ m hF n hG hres]
  have hq : Finite (O ⧸ Ideal.span {(∏ j, F j ^ n j).resultant G}) :=
    Ring.HasFiniteQuotients.finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hres)
  exact mul_ne_zero (pow_ne_zero _ Nat.card_pos.ne') Nat.card_pos.ne'

/-- When `(p : O) ∉ maximalIdeal O`, `p` is a unit of `O`, so `ν_{k,n₀}` is a unit for `n₀ ≥ 1`
and `X` times a unit for `n₀ = 0`, while `Res(F_M, ξ_j)` is a unit for every `j ≥ 1`. -/
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
  have hsmul_top {r : O⟦X⟧} (hr : IsUnit r) : r • (⊤ : Submodule O⟦X⟧ M) = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ ⟨(↑hr.unit⁻¹ : O⟦X⟧) • x, trivial, by simp [smul_smul]⟩
  have hres_pos {j : ℕ} (hj : 0 < j) :
      (charPoly O M).resultant
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact (isUnit_resultant_of_isUnit_coeff_zero isDistinguishedAt_charPoly (by simpa)).ne_zero
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
        growthTransition_zero_zero, mul_smul, hsmul_top (hunit_gt Nat.one_pos), Polynomial.coe_X]
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
    have : Subsingleton (QuotSMulTop (growthTransition p O n₀ k) M) := by
      rw [QuotSMulTop, hsmul_top (hunit_gt hn₀), Submodule.Quotient.subsingleton_iff]
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
      rw [growthTransitionPoly_eq_prod_cyclotomic, monic_charPoly.resultant_prod_right,
        Finset.prod_ne_zero_iff] at h
      exact h j (Finset.mem_Ico.mpr ⟨hj, Nat.lt_succ_self j⟩)
    · rw [← coe_growthTransitionPoly,
        finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM
          (isDistinguishedAt_growthTransitionPoly hpO n₀ k),
        growthTransitionPoly_eq_prod_cyclotomic, monic_charPoly.resultant_prod_right,
        Finset.prod_ne_zero_iff]
      exact fun j hj ↦ hres j (Finset.mem_Ico.mp hj).1
  · exact finite_quotSMulTop_growthTransition_iff_of_notMem hM hpO n₀

/-- **Resultant criterion for the delta submodule.** Over a characteristic-zero ring `O`, for a
finitely generated torsion `O⟦X⟧`-module `M`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite if and only if
`Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero [CharZero O] {M : Type*}
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M)
    (n₀ : ℕ) :
    Finite ↥((∏ j ∈ Finset.range n₀, growthTransition p O j j) • deltaSubmodule p O M) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  obtain rfl : r = 0 := eq_zero_of_isTorsion_elementary (hf.isTorsion_iff.mp hM)
  have hF (i : Fin b) := (hFn i).1
  have hirr (i : Fin b) := (hFn i).2.1
  have hn (i : Fin b) := (hFn i).2.2
  have hEtor := isTorsion_elementary hϖ.ne_zero m (fun i ↦ (hF i).monic) n
  rw [hf.finite_smul_deltaSubmodule_iff hEtor, hf.charPoly_eq_prod hϖ hF hirr]
  exact finite_smul_deltaSubmodule_elementary_iff hϖ m hF hirr hn n₀

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
    finite_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero hM,
    ← finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero hM]

/-- Every finitely generated torsion `O⟦X⟧`-module over a characteristic-zero complete discrete
valuation ring with finite residue field admits a cutoff `n₀` above which all transition quotients
`M ⧸ ν_{k,n₀} M` (`k ≥ n₀`) are finite. -/
theorem exists_finite_quotSMulTop_growthTransition [CharZero O] {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k) M) := by
  obtain ⟨m, hm⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  refine ⟨m + 1, (finite_quotient_growthTransition_iff p O M hM (m + 1)).mpr ?_⟩
  have hpos : 0 < m + 1 := Nat.succ_pos m
  have hprod : ∏ j ∈ Finset.range (m + 1), growthTransition p O j j =
      (1 + X) ^ p ^ m - 1 := by
    have h := congr_arg (Polynomial.coeToPowerSeries.ringHom (R := O))
      (prod_range_growthTransitionPoly_eq p O hpos)
    simpa only [map_prod, Polynomial.coeToPowerSeries.ringHom_apply, coe_growthTransitionPoly,
      Nat.add_sub_cancel, growthTransition_zero_left] using h
  suffices (∏ j ∈ Finset.range (m + 1), growthTransition p O j j) •
      (⨆ l, torsionBy O⟦X⟧ M (growthTransition p O 0 l)) = ⊥ by
    rw [this]
    infer_instance
  rw [iSup_torsionBy_growthTransition_zero, hm, hprod, eq_bot_iff]
  intro y hy
  rw [Submodule.mem_smul_pointwise_iff_exists] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (mem_torsionBy_iff _ _).mp hx

end Cutoff

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
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    rcases hz with ⟨y, -, rfl⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Ideal.Quotient.mk_eq_mk, mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact dvd_mul_right X f
  refine ⟨eq_bot_iff.mpr fun z hz ↦ ?_, ?_⟩
  · rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    rcases hz with ⟨x, _, rfl⟩
    rw [growthTransition_zero_zero, ← hXsmul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨x, trivial, rfl⟩
  · have : CharP O p := charP_of_injective_ringHom C_injective p
    have hξ : growthTransition p O 1 1 = X ^ (p ^ 1).totient := by
      rw [← coe_growthTransitionPoly, growthTransitionPoly_self_eq_cyclotomic,
        Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_X_pow]
      simp
    have hpos : 0 < (p ^ 1).totient :=
      Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos 1)
    have hsmul₁ : growthTransition p O 1 1 • (⊤ : Submodule O⟦X⟧ M) = ⊥ := by
      rw [hξ, ← Nat.sub_add_cancel hpos, pow_succ, mul_smul, hXsmul]
      simp
    have hOinf : Infinite O := by
      refine Infinite.of_injective (fun k : ℕ ↦ (X : O) ^ k) fun k₁ k₂ hk ↦ ?_
      by_contra hne
      have hc := congr_arg (PowerSeries.coeff k₁) hk
      simp [PowerSeries.coeff_X_pow, hne] at hc
    refine not_finite_iff_infinite.mpr
      (Infinite.of_injective
        (fun b : O ↦ Submodule.Quotient.mk (Ideal.Quotient.mk _ (C b))) fun b₁ b₂ hb ↦ ?_)
    rw [Submodule.Quotient.eq, hsmul₁, mem_bot, sub_eq_zero, Ideal.Quotient.eq,
      Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, constantCoeff_C,
      constantCoeff_C] at hb
    exact sub_eq_zero.mp hb

end TauCeti.Iwasawa
