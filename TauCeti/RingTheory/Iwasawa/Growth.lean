/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.EulerQuotient
public import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
public import Mathlib.NumberTheory.Padics.PadicIntegers

import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.Algebra.Module.Torsion.PGroup
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Iwasawa.CyclotomicGrowth
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm

/-!
# Iwasawa's growth formula

Let `p` be a prime and `O` a commutative ring. Write `ω_n = (1 + T) ^ pⁿ - 1` and
`ξ_j = Φ_{p ^ j}(1 + T)`, so that `ξ_0 = T` and `ω_n = ξ_0 ξ_1 ⋯ ξ_n`. The *growth transition*
`ν_{n, n₀} = ξ_{n₀} ξ_{n₀+1} ⋯ ξ_n` (`TauCeti.Iwasawa.growthTransition`) is the quotient
`ω_n / ω_{n₀ - 1}`, with the convention `ω_{-1} = 1`: so `ν_{n, 0} = ω_n`, and
`ω_c ν_{n, c + 1} = ω_n` for `c ≤ n`. It is a monic polynomial, distinguished at every ideal
containing `p`, of degree `pⁿ - p ^ c` when `n₀ = c + 1`.

Now let `O` be a discrete valuation ring, complete for its maximal ideal, with uniformizer `ϖ`,
residue field of order `p ^ f`, and `p = u ϖ ^ e` for a unit `u` (so `O` has characteristic zero),
and let `M` be a finitely generated `O⟦T⟧`-module with invariants `μ = μ(M)` and `λ = λ(M)`
(`TauCeti.Iwasawa.muInvariant`, `TauCeti.Iwasawa.lambdaInvariant`). If the quotients
`M ⧸ ν_{n, n₀} M` are finite for every `n ≥ n₀`, then there is an integer `ν` with

`#(M ⧸ ν_{n, n₀} M) = p ^ (f μ pⁿ + e f λ n + ν)` for all large `n`.

For `O = ℤ_p` this is Iwasawa's formula `p ^ (μ pⁿ + λ n + ν)`. By NSW, Proposition 5.3.17, the
finiteness hypothesis holds once `n₀` exceeds the cyclotomic cutoff of `M`, the largest `j` for
which `ξ_j` shares a prime factor with the characteristic polynomial of `M`; for `n₀ = 0` it is
the finiteness of the coinvariants `M ⧸ ω_n M`.

The proof combines three inputs. The Euler quotient
(`TauCeti.Iwasawa.natCard_quotSMulTop_div_natCard_torsionBy`) gives
`#(M ⧸ ν M) = #M[ν] · #k ^ (μ deg ν) · #(O ⧸ Res(F_M, ν))` for `ν = ν_{n, n₀}`. The kernels
`M[ν_{n, n₀}]` increase with `n`, so they are eventually constant since `M` is noetherian. Finally,
once `n > e deg F`, the factor `ξ_{n+1}` acts on `O⟦T⟧ ⧸ (F)` as `p` times a unit
(`Polynomial.IsDistinguishedAt.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one`), so the
resultant `Res(F_M, ν_{n, n₀})` gains a factor associated to `p ^ λ` per level
(`Polynomial.IsDistinguishedAt.associated_resultant_growthTransition`). The constant factors are
powers of `p` because finite modules over a ring with `p` in its Jacobson radical are `p`-groups
(`IsAddPGroup.of_natCast_mem_jacobson`).

## Main results

* `TauCeti.Iwasawa.growthTransition`: the transition polynomial `ν_{n, n₀} = ω_n / ω_{n₀ - 1}`.
* `TauCeti.Iwasawa.one_add_X_pow_sub_one_mul_growthTransition`: `ω_c ν_{n, c + 1} = ω_n`.
* `Polynomial.IsDistinguishedAt.associated_resultant_growthTransition`: the resultant
  `Res(F, ν_{n, n₀})` grows by a factor associated to `p ^ deg F` per level.
* `TauCeti.Iwasawa.natCard_quotient_resultant_growthTransition`: over a discrete valuation ring
  with `p` associated to `ϖ ^ e`, the order of `O ⧸ Res(F, ν_{n, n₀})` grows by `#k ^ (e deg F)`
  per level.
* `TauCeti.Iwasawa.exists_natCard_quotSMulTop_growthTransition_eq`: Iwasawa's growth formula
  `#(M ⧸ ν_{n, n₀} M) = p ^ (f μ pⁿ + e f λ n + ν)` for all large `n`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition 5.3.17 and Lemma 5.3.18.
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, Theorem 13.13.
-/

public section

open IsLocalRing Polynomial Submodule
open scoped PowerSeries

namespace TauCeti.Iwasawa

section Transition

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The *growth transition* `ν_{n, n₀} = ξ_{n₀} ξ_{n₀+1} ⋯ ξ_n`, where `ξ_j = Φ_{p ^ j}(1 + T)`.
Since `ω_n = (1 + T) ^ pⁿ - 1 = ξ_0 ξ_1 ⋯ ξ_n`, it is the quotient `ω_n / ω_{n₀ - 1}`, with
`ω_{-1} = 1`: `ν_{n, 0} = ω_n` (`growthTransition_zero_left`) and `ω_c ν_{n, c + 1} = ω_n` for
`c ≤ n` (`one_add_X_pow_sub_one_mul_growthTransition`). For `n < n₀` it is the empty product `1`.
-/
noncomputable def growthTransition (n₀ n : ℕ) : O[X] :=
  ∏ j ∈ Finset.Ico n₀ (n + 1), (cyclotomic (p ^ j) O).comp (X + 1)

variable {p O}

theorem growthTransition_def (n₀ n : ℕ) :
    growthTransition p O n₀ n = ∏ j ∈ Finset.Ico n₀ (n + 1), (cyclotomic (p ^ j) O).comp (X + 1) :=
  (rfl)

/-- The growth transition is monic. -/
theorem monic_growthTransition (n₀ n : ℕ) : (growthTransition p O n₀ n).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_cyclotomic_comp_X_add_one _

/-- **Transitivity of growth transitions**: `ν_{m, n₀} ν_{n, m + 1} = ν_{n, n₀}` for
`n₀ ≤ m + 1` and `m ≤ n`. -/
theorem growthTransition_mul_growthTransition {n₀ m n : ℕ} (h₀ : n₀ ≤ m + 1) (h : m ≤ n) :
    growthTransition p O n₀ m * growthTransition p O (m + 1) n = growthTransition p O n₀ n :=
  Finset.prod_Ico_consecutive _ h₀ (Nat.succ_le_succ h)

/-- The growth transitions from a fixed level divide one another: `ν_{m, n₀} ∣ ν_{n, n₀}` for
`m ≤ n`. -/
theorem growthTransition_dvd_growthTransition (n₀ : ℕ) {m n : ℕ} (h : m ≤ n) :
    growthTransition p O n₀ m ∣ growthTransition p O n₀ n :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Ico_subset_Ico_right (Nat.succ_le_succ h))

variable [Fact p.Prime]

/-- `ν_{n, 0} = ω_n = (1 + T) ^ pⁿ - 1`. -/
@[simp]
theorem growthTransition_zero_left (n : ℕ) :
    growthTransition p O 0 n = (1 + X) ^ p ^ n - 1 := by
  rw [growthTransition_def, ← Finset.range_eq_Ico, prod_range_cyclotomic_prime_pow_comp_X_add_one]

/-- `ω_c ν_{n, c + 1} = ω_n` for `c ≤ n`: the growth transition is `ω_n / ω_c`. -/
theorem one_add_X_pow_sub_one_mul_growthTransition {c n : ℕ} (h : c ≤ n) :
    ((1 + X) ^ p ^ c - 1) * growthTransition p O (c + 1) n = (1 + X) ^ p ^ n - 1 := by
  rw [← growthTransition_zero_left, ← growthTransition_zero_left,
    growthTransition_mul_growthTransition (Nat.zero_le _) h]

/-- The growth transition is distinguished at every ideal containing `p`. -/
theorem isDistinguishedAt_growthTransition {I : Ideal O} (hI : (p : O) ∈ I) (n₀ n : ℕ) :
    (growthTransition p O n₀ n).IsDistinguishedAt I :=
  isDistinguishedAt_prod fun j _ ↦ cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt p hI j

/-- The constant coefficient of `ν_{n, n₀}` is `p ^ (n + 1 - n₀)` for `n₀ ≥ 1`: each factor `ξ_j`
with `j ≥ 1` has constant coefficient `p`. By contrast `ω_n` has constant coefficient `0`. -/
theorem coeff_zero_growthTransition {n₀ : ℕ} (h₀ : 0 < n₀) (n : ℕ) :
    (growthTransition p O n₀ n).coeff 0 = (p : O) ^ (n + 1 - n₀) := by
  rw [growthTransition_def, coeff_zero_prod, ← Nat.card_Ico, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (h₀.trans_le (Finset.mem_Ico.1 hj).1)
  simp

/-- `ν_{n, c + 1} = ω_n / ω_c` has degree `pⁿ - p ^ c` for `c ≤ n`. -/
theorem natDegree_growthTransition [Nontrivial O] {c n : ℕ} (h : c ≤ n) :
    (growthTransition p O (c + 1) n).natDegree = p ^ n - p ^ c := by
  have hdeg := congr_arg natDegree (one_add_X_pow_sub_one_mul_growthTransition (O := O) (p := p) h)
  have hω := TauCeti.Polynomial.monic_one_add_X_pow_sub_one (R := O)
    (pow_ne_zero c (Fact.out : p.Prime).ne_zero)
  rw [hω.natDegree_mul (monic_growthTransition _ _),
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one,
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one] at hdeg
  omega

end Transition

end TauCeti.Iwasawa

namespace Polynomial.IsDistinguishedAt

open TauCeti.Iwasawa

variable {O : Type*} [CommRing O] {I : Ideal O} {F : O[X]} {p e : ℕ} [Fact p.Prime]

/-- **The resultant of a growth transition grows by `p ^ deg F` per level.** Let `O` be
`I`-adically complete, `F` distinguished at `I`, `I ^ e ⊆ (p)` and `p` in the Jacobson radical of
`O`. If `n₀ ≤ K + 1` and `K > deg F * e`, then for `K ≤ n` the resultant `Res(F, ν_{n, n₀})` is
associated to `Res(F, ν_{K, n₀}) p ^ (deg F (n - K))`. Over a discrete valuation ring with
`p = u ϖ ^ e`, its `ϖ`-valuation grows by `e deg F` per level. -/
theorem associated_resultant_growthTransition [IsAdicComplete I O] (hF : F.IsDistinguishedAt I)
    (hI : I ^ e ≤ Ideal.span {(p : O)}) (hpO : (p : O) ∈ (⊥ : Ideal O).jacobson) {n₀ K : ℕ}
    (h₀ : n₀ ≤ K + 1) (hK : F.natDegree * e < K) {n : ℕ} (hn : K ≤ n) :
    Associated (F.resultant (growthTransition p O n₀ n))
      (F.resultant (growthTransition p O n₀ K) * (p : O) ^ (F.natDegree * (n - K))) := by
  have H := hF.isWeierstrassFactorizationAt
  rw [← H.norm_mk_coe_eq_resultant, ← H.norm_mk_coe_eq_resultant,
    ← growthTransition_mul_growthTransition h₀ hn, coe_mul, map_mul, map_mul]
  refine Associated.mul_left _ ?_
  -- `ν_{n, K + 1} = ξ_{K + 1} ⋯ ξ_n` is the product of the cyclotomic factors `ξ_{j + 1}`,
  -- `K ≤ j < n`, each acting on `O⟦T⟧ ⧸ (F)` as `p` times a unit.
  have hprod : ((growthTransition p O (K + 1) n : O[X]) : O⟦X⟧) =
      ∏ j ∈ Finset.Ico K n, ((cyclotomic (p ^ (j + 1)) O).comp (X + 1) : O⟦X⟧) := by
    rw [growthTransition_def, ← Finset.prod_Ico_add' (c := 1)]
    exact map_prod Polynomial.coeToPowerSeries.ringHom _ _
  rw [hprod]
  exact hF.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one hI hpO hK n

end Polynomial.IsDistinguishedAt

namespace TauCeti.Iwasawa

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **The cyclotomic growth step.** Let `O` be a discrete valuation ring, complete for its maximal
ideal, with uniformizer `ϖ` and residue field `k` of characteristic `p`, with `p` associated to
`ϖ ^ e`, and let `F` be a distinguished polynomial. If `n₀ ≤ K + 1` and `K > deg F * e`, then for
`K ≤ n` the order of `O ⧸ Res(F, ν_{n, n₀})` is `#(O ⧸ Res(F, ν_{K, n₀})) · #k ^ (e deg F (n - K))`:
each further level contributes `e deg F` to the `ϖ`-valuation of the resultant. -/
theorem natCard_quotient_resultant_growthTransition {p : ℕ} [Fact p.Prime] {ϖ : O}
    (hϖ : Irreducible ϖ) {e : ℕ} (hpe : Associated (p : O) (ϖ ^ e))
    (hpO : (p : O) ∈ maximalIdeal O) {F : O[X]} (hF : F.IsDistinguishedAt (maximalIdeal O))
    {n₀ K : ℕ} (h₀ : n₀ ≤ K + 1) (hK : F.natDegree * e < K) {n : ℕ} (hn : K ≤ n) :
    Nat.card (O ⧸ Ideal.span {F.resultant (growthTransition p O n₀ n)}) =
      Nat.card (O ⧸ Ideal.span {F.resultant (growthTransition p O n₀ K)}) *
        Nat.card (ResidueField O) ^ (e * (F.natDegree * (n - K))) := by
  have hspan : Ideal.span {(p : O)} = maximalIdeal O ^ e := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton.2 hpe]
  have hpJ : (p : O) ∈ (⊥ : Ideal O).jacobson := by
    rwa [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  -- The order of a quotient of the Dedekind domain `O` is multiplicative in the ideal.
  rw [Ideal.span_singleton_eq_span_singleton.2
      (hF.associated_resultant_growthTransition hspan.ge hpJ h₀ hK hn),
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.absNorm_eq_natCard, map_mul,
    Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard, ← Ideal.span_singleton_pow, hspan,
    ← pow_mul, TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]

variable [Finite (ResidueField O)] {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
  [Module.Finite O⟦X⟧ M]

/-- **The invariants of the growth transitions stabilize.** Let `p` lie in the maximal ideal of
`O`. If the quotients `M ⧸ ν_{n, n₀} M` are finite for every `n ≥ n₀`, then from some level on the
kernels `M[ν_{n, n₀}]` all have the same order, a power of `p`. -/
theorem exists_natCard_torsionBy_growthTransition_eq_pow {p : ℕ} [Fact p.Prime]
    (hpO : (p : O) ∈ maximalIdeal O) (n₀ : ℕ)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ a N : ℕ, ∀ n, N ≤ n →
      Nat.card (torsionBy O⟦X⟧ M (growthTransition p O n₀ n : O⟦X⟧)) = p ^ a := by
  -- The kernels increase with `n`, so they stabilize since `M` is noetherian.
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance
    ⟨fun n ↦ torsionBy O⟦X⟧ M (growthTransition p O n₀ n : O⟦X⟧), fun m n h ↦
      torsionBy_le_torsionBy_of_dvd _ _
        (map_dvd Polynomial.coeToPowerSeries.ringHom (growthTransition_dvd_growthTransition n₀ h))⟩
  set K := max n₀ N
  have := finite_torsionBy_of_finite_quotSMulTop (monic_growthTransition n₀ K)
    (hfin K (le_max_left _ _))
  -- `p` lies in the maximal ideal of `O⟦T⟧`, so the finite module `M[ν_{K, n₀}]` is a `p`-group.
  have hpJ : (p : O⟦X⟧) ∈ Ring.jacobson O⟦X⟧ := by
    rw [ringJacobson_eq_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, map_natCast]
    exact hpO
  obtain ⟨a, ha⟩ := IsAddPGroup.iff_card.1 (IsAddPGroup.of_natCast_mem_jacobson
    (N := torsionBy O⟦X⟧ M (growthTransition p O n₀ K : O⟦X⟧)) hpJ)
  refine ⟨a, K, fun n hn ↦ ?_⟩
  have htor : torsionBy O⟦X⟧ M (growthTransition p O n₀ n : O⟦X⟧) =
      torsionBy O⟦X⟧ M (growthTransition p O n₀ K : O⟦X⟧) :=
    (hN n ((le_max_right _ _).trans hn)).symm.trans (hN K (le_max_right _ _))
  rw [htor, ha]

/-- **Iwasawa's growth formula.** Let `O` be a discrete valuation ring, complete for its maximal
ideal, with uniformizer `ϖ`, residue field of order `p ^ f` and `p` associated to `ϖ ^ e`, and let
`M` be a finitely generated `O⟦T⟧`-module. If the quotients `M ⧸ ν_{n, n₀} M` by the growth
transitions `ν_{n, n₀} = ω_n / ω_{n₀ - 1}` are finite for every `n ≥ n₀`, then there is an integer
`ν` such that `#(M ⧸ ν_{n, n₀} M) = p ^ (f μ pⁿ + e f λ n + ν)` for all large `n`, where `μ` and
`λ` are the Iwasawa invariants of `M`. For `n₀ = 0` these are the coinvariants `M ⧸ ω_n M`. -/
theorem exists_natCard_quotSMulTop_growthTransition_eq {p : ℕ} [Fact p.Prime] {ϖ : O}
    (hϖ : Irreducible ϖ) {e f : ℕ} (hpe : Associated (p : O) (ϖ ^ e))
    (hres : Nat.card (ResidueField O) = p ^ f) (n₀ : ℕ)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ ν : ℤ, ∀ᶠ n in Filter.atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M) : ℚ) =
        (p : ℚ) ^ (((f * muInvariant O M * p ^ n + e * f * lambdaInvariant O M * n : ℕ) : ℤ) +
          ν) := by
  have hp := (Fact.out : p.Prime)
  set F := charPoly O M
  set μ := muInvariant O M
  set ν := growthTransition p O n₀
  set d := lambdaInvariant O M
  -- The residue field has `p ^ f` elements, so `p` lies in the maximal ideal.
  have hpO : (p : O) ∈ maximalIdeal O := by
    have := Fintype.ofFinite (ResidueField O)
    have h := FiniteField.cast_card_eq_zero (ResidueField O)
    rw [← Nat.card_eq_fintype_card, hres, Nat.cast_pow] at h
    rw [← residue_eq_zero_iff, map_natCast]
    exact eq_zero_of_pow_eq_zero h
  obtain ⟨a, N, ha⟩ := exists_natCard_torsionBy_growthTransition_eq_pow hpO n₀ hfin
  set K := max (max n₀ N) (F.natDegree * e + 1)
  have hK₀ : n₀ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKN : N ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  -- The factor `#(O ⧸ Res(F_M, ν_{K, n₀}))` is a power of `p`.
  have := Ring.HasFiniteQuotients.finiteQuotient ((Ideal.span_singleton_eq_bot
    (x := F.resultant (ν K))).not.2 (resultant_charPoly_ne_zero_of_finite_quotSMulTop (hfin K hK₀)))
  obtain ⟨b, hb⟩ := IsAddPGroup.iff_card.1 (IsAddPGroup.of_natCast_mem_jacobson (p := p)
    (N := O ⧸ Ideal.span {F.resultant (ν K)})
    (show (p : O) ∈ Ring.jacobson O by rwa [ringJacobson_eq_maximalIdeal]))
  refine ⟨a + b + f * μ * (ν K).natDegree - f * μ * p ^ K - e * f * d * K,
    Filter.eventually_atTop.2 ⟨K, fun n hn ↦ ?_⟩⟩
  -- The Euler quotient at level `n`, in which the resultant grows by `#k ^ (e λ)` per level.
  have heuler := natCard_quotSMulTop_div_natCard_torsionBy
    (isDistinguishedAt_growthTransition (p := p) hpO n₀ n) (hfin n (hK₀.trans hn))
  rw [natCard_quotient_resultant_growthTransition hϖ hpe hpO (isDistinguishedAt_charPoly (M := M))
    (Nat.le_succ_of_le hK₀) (Nat.lt_of_succ_le (le_max_right _ _)) hn, ha n (hKN.trans hn), hb,
    hres, ← lambdaInvariant_def, div_eq_iff (by exact_mod_cast (pow_pos hp.pos a).ne')] at heuler
  -- The degree of `ν_{n, n₀} = ν_{K, n₀} ν_{n, K + 1}` is `deg ν_{K, n₀} + pⁿ - p ^ K`.
  have hdeg : (ν n).natDegree + p ^ K = (ν K).natDegree + p ^ n := by
    have := Nat.pow_le_pow_right hp.pos hn
    simp only [ν, ← growthTransition_mul_growthTransition (Nat.le_succ_of_le hK₀) hn,
      (monic_growthTransition _ _).natDegree_mul (monic_growthTransition _ _),
      natDegree_growthTransition hn]
    omega
  have hexp : (((f * μ * p ^ n + e * f * d * n : ℕ) : ℤ) +
      (a + b + f * μ * (ν K).natDegree - f * μ * p ^ K - e * f * d * K) : ℤ) =
      ((f * (μ * (ν n).natDegree) + (b + f * (e * (d * (n - K)))) + a : ℕ) : ℤ) := by
    have hdeg' : ((ν n).natDegree : ℤ) = (ν K).natDegree + p ^ n - p ^ K := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast hdeg
    push_cast [Nat.cast_sub hn, hdeg']
    ring
  rw [heuler, hexp, zpow_natCast]
  push_cast
  ring

/-- **Iwasawa's growth formula over `ℤ_p`.** Let `M` be a finitely generated `ℤ_p⟦T⟧`-module. If
the quotients `M ⧸ ν_{n, n₀} M` by the growth transitions `ν_{n, n₀} = ω_n / ω_{n₀ - 1}` are finite
for every `n ≥ n₀`, then there is an integer `ν` such that
`#(M ⧸ ν_{n, n₀} M) = p ^ (μ pⁿ + λ n + ν)` for all large `n`. -/
theorem exists_natCard_quotSMulTop_growthTransition_eq_padicInt {p : ℕ} [Fact p.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] (n₀ : ℕ)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop (growthTransition p ℤ_[p] n₀ n : ℤ_[p]⟦X⟧) M)) :
    ∃ ν : ℤ, ∀ᶠ n in Filter.atTop,
      (Nat.card (QuotSMulTop (growthTransition p ℤ_[p] n₀ n : ℤ_[p]⟦X⟧) M) : ℚ) =
        (p : ℚ) ^ (((muInvariant ℤ_[p] M * p ^ n + lambdaInvariant ℤ_[p] M * n : ℕ) : ℤ) + ν) := by
  simpa using exists_natCard_quotSMulTop_growthTransition_eq PadicInt.irreducible_p
    (e := 1) (f := 1) (by simp) (by simp [PadicInt.card_residueField]) n₀ hfin

end TauCeti.Iwasawa
