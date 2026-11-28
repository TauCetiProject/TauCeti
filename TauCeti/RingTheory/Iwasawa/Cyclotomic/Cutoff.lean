/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Iwasawa.Delta
public import TauCeti.RingTheory.Iwasawa.EulerQuotient
public import TauCeti.RingTheory.Iwasawa.GrowthFormula

import TauCeti.Algebra.Module.Submodule.Pointwise
import TauCeti.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Submodule.Prod.Basic
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Norm.Cokernel
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The cyclotomic cutoff for transition quotients of an Iwasawa module

Let `O` be a discrete valuation ring, complete for its maximal ideal, with finite residue field,
let `Λ = O⟦X⟧`, let `p : ℕ`, and let `M` be a finitely generated torsion `Λ`-module with
characteristic polynomial `F_M` (`TauCeti.Iwasawa.charPoly`). Write `ν_{n₀,k}`
(`TauCeti.Iwasawa.growthTransition`) for the cyclotomic transition polynomial
`∏_{n₀ ≤ j ≤ k} ξ_j`, where `ξ_j = Φ_{p ^ j}(X + 1)`.

This file characterizes the cutoff levels `n₀` above which every transition quotient
`M ⧸ ν_{n₀,k} M` (`k ≥ n₀`, equivalently for every `n`) is finite:

1. Over any such `O` (with no characteristic assumption on `O` and no primality assumption on `p`),
   `M ⧸ ν_{n₀,n} M` is finite for every `n` if and only if `Res(F_M, ξ_j) ≠ 0` for every `j ≥ n₀`
   (`TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`).
2. Whenever `p` is prime and `(p : O) ≠ 0`, a nonunit polynomial divides at most one shifted
   prime-power cyclotomic polynomial `ξ_j`. Passing along a pseudo-isomorphism to an elementary
   module yields the intrinsic *cyclotomic cutoff*
   (`TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff`): all quotients `M ⧸ ν_{n₀,n} M`
   are finite if and only if `(∏_{j < n₀} ξ_j) • M_δ` is finite, where
   `M_δ = ⨆_m M[ω_m]` is `TauCeti.Iwasawa.deltaSubmodule`. At `n₀ = 0`, `M ⧸ ω_n M` is finite
   for all `n` iff `M_δ` is finite (`TauCeti.Iwasawa.finite_quotSMulTop_one_add_X_pow_sub_one_iff`).
3. Since `M_δ = M[ω_m]` for some `m` on the noetherian module `M`, taking `n₀ = m + 1` makes
   `ω_m • M_δ = ω_m • M[ω_m] = 0`, so every finitely generated torsion module with `p` prime and
   `(p : O) ≠ 0` admits a cutoff `n₀`
   (`TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`). Combining this cutoff with
   Iwasawa's conditional growth formula
   (`TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq`) supplies a cutoff
   `n₀` and an integer constant `ν` for which the unconditional growth formula holds for all
   sufficiently large `k` whenever `p` is prime and `(p) = 𝔪 ^ e` with `e > 0`
   (`TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion`,
   `TauCeti.Iwasawa.exists_natCard_quotSMulTop_growthTransition_of_isTorsion`, and
   `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt_of_isTorsion`
   over `ℤ_p`).

The hypothesis `(p : O) ≠ 0` is sharp: in equal characteristic `p` (`O = 𝔽_p⟦t⟧`), every shifted
cyclotomic polynomial `Φ_{p ^ j}(X + 1)` is a power of `X`, so `X` kills the delta submodule of
`Λ ⧸ (X)` yet `Λ ⧸ (X, ν_{n₀, n})` is infinite for every `n₀` and `n ≥ n₀`.

## Main results

* `TauCeti.Iwasawa.iSup_torsionBy_growthTransition_zero`: `⨆ m, M[ν_{0,m}] = M_δ`.
* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero`: without
  assuming `p` is prime or `(p : O) ≠ 0`, all `M ⧸ ν_{n₀,n} M` are finite iff
  `Res(F_M, ξ_j) ≠ 0` for all `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero`:
  when `p` is prime and `(p : O) ≠ 0`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite iff
  `Res(F_M, ξ_j) ≠ 0` for all `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff`,
  `TauCeti.Iwasawa.finite_quotSMulTop_one_add_X_pow_sub_one_iff`,
  `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_succ_iff`: when `p` is prime and
  `(p : O) ≠ 0`, the cyclotomic cutoff equivalence.
* `TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`: when `p` is prime and
  `(p : O) ≠ 0`, every finitely generated torsion module has a cutoff `n₀` above which all
  `M ⧸ ν_{n₀,k} M` are finite.
* `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion`,
  `TauCeti.Iwasawa.exists_natCard_quotSMulTop_growthTransition_of_isTorsion`, and
  `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt_of_isTorsion`:
  for every finitely generated torsion module when `p` is prime and `(p) = 𝔪 ^ e` with `e > 0`
  (and over `ℤ_p`), these supply a cutoff `n₀` and an integer constant `ν` such that the
  unconditional growth formula `#(M ⧸ ν_{n₀,k} M) = q ^ (μ p ^ k + e λ k + ν)` holds for all
  sufficiently large `k`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition 5.3.17 and (5.3.17)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public noncomputable section

open IsLocalRing PowerSeries Submodule Filter
open scoped Pointwise Polynomial PowerSeries

namespace TauCeti.Iwasawa

section TransitionHelpers

/-- The supremum of the kernels `M[ν_{0,m}]` is `deltaSubmodule p O M`. -/
theorem iSup_torsionBy_growthTransition_zero (p : ℕ) [Fact p.Prime] (O M : Type*) [CommRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] :
    (⨆ m, torsionBy O⟦X⟧ M (growthTransition p O 0 m : O⟦X⟧)) = deltaSubmodule p O M := by
  simp_rw [growthTransition_zero_left, Polynomial.coe_sub, Polynomial.coe_pow,
    Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X, deltaSubmodule_def]

end TransitionHelpers

section Blocks

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- Helper: finiteness of `g • M_δ` on an elementary module `Elementary O ϖ r m F n`. -/
private theorem finite_smul_deltaSubmodule_elementary_iff {p : ℕ} (hp : p.Prime)
    (hp0 : (p : O) ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) {r a b : ℕ} (m : Fin a → ℕ)
    {F : Fin b → O[X]} {n : Fin b → ℕ}
    (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (hirr : ∀ j, Irreducible (F j))
    (hn : ∀ j, n j ≠ 0) (g : O[X]) :
    Finite ↥((g : O⟦X⟧) • deltaSubmodule p O (Elementary O ϖ r m F n)) ↔
      ∀ j : Fin b, ∀ k,
        F j ∣ (Polynomial.cyclotomic (p ^ k) O).comp (Polynomial.X + 1) → F j ∣ g := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Infinite O := TauCeti.IsDiscreteValuationRing.infinite
  have hfree : deltaSubmodule p O (Fin r → O⟦X⟧) = ⊥ := deltaSubmodule_eq_bot p O _
  dsimp only [Elementary]
  simp only [deltaSubmodule_prod, deltaSubmodule_pi, hfree,
    deltaSubmodule_quotient_span_C_pow_eq_bot (p := p) hϖ.prime, Submodule.smul_prod,
    Submodule.smul_pi_univ, Submodule.smul_bot', Submodule.finite_prod_iff,
    Submodule.finite_pi_univ_iff,
    finite_smul_deltaSubmodule_quotient_span_pow_iff hp hp0 (hF _) (hirr _).prime (hn _)]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨inferInstance, fun _ ↦ inferInstance, h⟩⟩

end Blocks

section Cutoff

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]

/-- **Resultant criterion for finite transition quotients.** For a finitely generated torsion
`O⟦X⟧`-module `M` (with no characteristic assumption on `O` and no primality assumption on `p`),
the quotients `M ⧸ ν_{n₀, n} M` are finite for every `n` if and only if
`Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero {p : ℕ}
    (hM : Module.IsTorsion O⟦X⟧ M) (n₀ : ℕ) :
    (∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  have hiff (k : ℕ) : Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) ↔
      ∏ j ∈ Finset.Icc n₀ k,
        (charPoly O M).resultant ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 :=
    by
    rw [finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM
        ((monic_growthTransition (p := p) (O := O) n₀ k).map _).ne_zero,
      growthTransition_def, monic_charPoly.resultant_prod_right]
  simp_rw [hiff, Finset.prod_ne_zero_iff, Finset.mem_Icc]
  exact ⟨fun h j hj ↦ h j j ⟨hj, le_rfl⟩, fun h n j hj ↦ h j hj.1⟩

/-- **Resultant criterion for the delta submodule.** When `p` is prime and `(p : O) ≠ 0`, for a
finitely generated `O⟦X⟧`-module `M`, `(∏_{j < n₀} ν_{j,j}) • M_δ` is finite if and only if
`Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`. -/
theorem finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero
    {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0) (n₀ : ℕ) :
    Finite ↥(((∏ j ∈ Finset.range n₀, growthTransition p O j j : O[X]) : O⟦X⟧) •
        deltaSubmodule p O M) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant
          ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set g : O[X] := ∏ j ∈ Finset.range n₀, growthTransition p O j j
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  have hF (j : Fin b) := (hFn j).1
  have hirr (j : Fin b) := (hFn j).2.1
  have hn (j : Fin b) := (hFn j).2.2
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  rw [hf.finite_smul_deltaSubmodule_iff hdim (g : O⟦X⟧), hf.charPoly_eq_prod hϖ hF hirr,
    finite_smul_deltaSubmodule_elementary_iff hp hp0 hϖ m hF hirr hn g]
  simp_rw [Polynomial.resultant_prod_pow_ne_zero_iff Finset.univ (fun j _ ↦ (hF j).monic)
    (fun j _ ↦ (hirr j).prime) (fun j _ ↦ hn j), Finset.mem_univ, true_implies]
  refine ⟨fun h k hk j hjk ↦ ?_, fun h j k hk ↦ ?_⟩
  · obtain ⟨i, hi, hij⟩ := (Prime.dvd_finsetProd_iff (hirr j).prime _).mp (h j k hjk)
    rw [growthTransition_self] at hij
    have heq := Polynomial.eq_of_dvd_cyclotomic_prime_pow_comp_X_add_one p hp0 (hirr j).not_isUnit
      hjk hij
    rw [heq] at hk
    exact (Finset.mem_range.mp hi).not_ge hk
  · have hklt : k < n₀ := by
      by_contra hge
      exact h k (not_lt.mp hge) j hk
    exact hk.trans ((growthTransition_self (p := p) (O := O) k).symm ▸
      Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hklt))

end Cutoff

section CyclotomicCutoff

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]

/-- **The cyclotomic cutoff criterion** (Neukirch–Schmidt–Wingberg, Proposition 5.3.17). Let `O` be
a complete discrete valuation ring with finite residue field, `p` a prime with `(p : O) ≠ 0`, and
`M` a finitely generated torsion `O⟦X⟧`-module. Then `M ⧸ ν_{n₀, n} M` is finite for every `n` if
and only if `(∏_{j < n₀} Φ_{p ^ j}(X + 1)) • M_δ` is finite. -/
theorem finite_quotSMulTop_growthTransition_iff {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) (n₀ : ℕ) :
    (∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) ↔
      Finite ↥(((∏ j ∈ Finset.range n₀,
        (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) : O[X]) : O⟦X⟧) •
          deltaSubmodule p O M) := by
  have : Fact p.Prime := ⟨hp⟩
  simp_rw [← growthTransition_self (p := p) (O := O)]
  rw [finite_quotSMulTop_growthTransition_iff_resultant_charPoly_ne_zero hM n₀]
  exact (finite_prod_growthTransition_smul_deltaSubmodule_iff_resultant_charPoly_ne_zero
    hp hp0 n₀).symm

/-- At `n₀ = 0`, for a prime `p` with `(p : O) ≠ 0` and a finitely generated torsion
`O⟦X⟧`-module `M`, `M ⧸ ω_n M` is finite for every `n` iff the delta submodule `M_δ` is finite. -/
theorem finite_quotSMulTop_one_add_X_pow_sub_one_iff {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) :
    (∀ n, Finite (QuotSMulTop ((1 + X) ^ p ^ n - 1 : O⟦X⟧) M)) ↔
      Finite (deltaSubmodule p O M) := by
  simpa only [coe_growthTransition_zero p O hp, Finset.range_zero, Finset.prod_empty,
    Polynomial.coe_one, one_smul] using finite_quotSMulTop_growthTransition_iff hp hp0 hM 0

/-- At `n₀ = m + 1`, for a prime `p` with `(p : O) ≠ 0` and a finitely generated torsion
`O⟦X⟧`-module `M`, `M ⧸ ν_{m + 1, n} M` is finite for every `n` iff `ω_m • M_δ` is finite. -/
theorem finite_quotSMulTop_growthTransition_succ_iff {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) (m : ℕ) :
    (∀ n, Finite (QuotSMulTop (growthTransition p O (m + 1) n : O⟦X⟧) M)) ↔
      Finite ↥(((1 + X) ^ p ^ m - 1 : O⟦X⟧) • deltaSubmodule p O M) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := finite_quotSMulTop_growthTransition_iff hp hp0 hM (m + 1)
  simpa only [Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one p m, Polynomial.coe_sub,
    Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X] using h

/-- **Existence of a cyclotomic cutoff.** For a prime `p` with `(p : O) ≠ 0`, every finitely
generated torsion `O⟦X⟧`-module over a complete discrete valuation ring with finite residue field
admits a level `n₀` from which all quotients `M ⧸ ν_{n₀, k} M` (`k ≥ n₀`) are finite. -/
theorem exists_finite_quotSMulTop_growthTransition (p : ℕ) [Fact p.Prime] (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∀ k, n₀ ≤ k → Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) := by
  have : IsNoetherian O⟦X⟧ M := isNoetherian_of_isNoetherianRing_of_finite O⟦X⟧ M
  obtain ⟨m, hm⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  refine ⟨m + 1, fun k _ ↦
    (finite_quotSMulTop_growthTransition_succ_iff Fact.out hp0 hM m).mpr ?_ k⟩
  have hbot : ((1 + X) ^ p ^ m - 1 : O⟦X⟧) • deltaSubmodule p O M = ⊥ := by
    rw [hm, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_torsionBy_iff _ _).mp hx
  rw [hbot]
  infer_instance

end CyclotomicCutoff

section TorsionGrowthFormula

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]

/-- **Unconditional Iwasawa growth formula.** Let `O` be a complete discrete valuation ring with
finite residue field of cardinality `q`, in which `(p) = 𝔪 ^ e` for a prime `p` and some `e > 0`,
and let `M` be a finitely generated torsion `O⟦X⟧`-module with Iwasawa invariants `μ = μ(M)` and
`λ = λ(M)`. Then there exist a cutoff level `n₀` and an integer `ν` such that
`#(M ⧸ ν_{n₀,k} M) = q ^ (μ p ^ k + e λ k + ν)` for all sufficiently large `k`. -/
theorem exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion {p e : ℕ}
    [Fact p.Prime] (he : 0 < e) (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e)
    (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∃ ν : ℤ, ∀ᶠ k in Filter.atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) : ℚ) =
        (Nat.card (ResidueField O) : ℚ) ^
          (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) := by
  have := TauCeti.IsDiscreteValuationRing.charZero_of_span_natCast_eq_maximalIdeal_pow he hpe
  obtain ⟨n₀, hn₀⟩ := exists_finite_quotSMulTop_growthTransition p (Nat.cast_ne_zero.mpr
    (Fact.out : p.Prime).ne_zero) hM
  exact ⟨n₀, exists_eventually_natCard_quotSMulTop_growthTransition_eq he hpe n₀
    (Filter.eventually_atTop.mpr ⟨n₀, hn₀⟩)⟩

/-- **Unconditional Iwasawa growth formula (natural-number cardinality form).**
Every finitely generated torsion `O⟦X⟧`-module over a complete discrete valuation ring with finite
residue field of cardinality `q`, in which `(p) = 𝔪 ^ e` for a prime `p` and some `e > 0`, admits
a cutoff `n₀`, an integer `ν`, and a threshold `N` such that for all `k ≥ N`,
`0 ≤ μ p ^ k + e λ k + ν` and `#(M ⧸ ν_{n₀, k} M) = q ^ (μ p ^ k + e λ k + ν)`. -/
theorem exists_natCard_quotSMulTop_growthTransition_of_isTorsion {p e : ℕ} [Fact p.Prime]
    (he : 0 < e) (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e)
    (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ (n₀ : ℕ) (ν : ℤ) (N : ℕ), ∀ k ≥ N,
      0 ≤ (muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν ∧
      Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) =
        Nat.card (ResidueField O) ^
          ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν).toNat := by
  obtain ⟨n₀, ν, hν⟩ := exists_eventually_natCard_quotSMulTop_growthTransition_eq_of_isTorsion
    (M := M) he hpe hM
  obtain ⟨N, hN⟩ := eventually_atTop.mp hν
  refine ⟨n₀, ν, N, fun k hk ↦ ?_⟩
  have hcard := hN k hk
  have hq : (1 : ℚ) < Nat.card (ResidueField O) := by
    have : Nontrivial (ResidueField O) := inferInstance
    exact_mod_cast Finite.one_lt_card
  have hge1 : (1 : ℚ) ≤ (Nat.card (ResidueField O) : ℚ) ^
      (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) := by
    rw [← hcard]
    rcases Nat.eq_zero_or_pos (Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M)) with
      h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero] at hcard
      exact (zpow_ne_zero _ (by positivity)) hcard.symm
    · exact_mod_cast hpos
  have hnn : 0 ≤ ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν := by
    by_contra hlt
    have hlt' : (Nat.card (ResidueField O) : ℚ) ^
        (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) < 1 :=
      (zpow_lt_one_iff_right₀ hq).mpr (not_le.mp hlt)
    exact hlt'.not_ge hge1
  refine ⟨by simpa using hnn, ?_⟩
  apply Nat.cast_injective (R := ℚ)
  rw [hcard, ← Int.toNat_of_nonneg hnn]
  push_cast
  rw [zpow_natCast]

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

end TorsionGrowthFormula

/-! ### Sharpness checks and concrete examples

1. **Equal characteristic breaks the cyclotomic cutoff.** Over `O = (ZMod p)⟦t⟧` and
   `M = O⟦X⟧ ⧸ (X)`, `ω_0 = X` kills `M_δ = M`, yet `ν_{1, 1} = X ^ (p - 1)` acts as `0` on `M`,
   so `M ⧸ ν_{1, 1} M ≃ O` is infinite.
2. **Equal characteristic breaks linear `λ`-growth.** Over `O = (ZMod p)⟦t⟧` and
   `M = O⟦X⟧ ⧸ (X - t)` (`μ = 0, λ = 1`), `ω_n = X ^ p ^ n` acts by `t ^ p ^ n`, giving
   `#(M ⧸ ω_n M) = p ^ (p ^ n)` instead of linear growth in `n`.
3. **Ramified `p = 2, π² = 2` small-index check.** In a discrete valuation ring with residue field
   of cardinality `2` and uniformiser `π` satisfying `π² = 2`, `(1 + π)² - 1 = π² (1 + π)` has
   unit factor `1 + π` and quotient cardinality `4 = 2 ^ 2`.
4. **Explicit `ℤ_p` cutoff.** On `M = ℤ_p⟦X⟧ ⧸ (X)` (`μ = 0, λ = 1`), `M ⧸ ω_k M` is infinite for
   every `k`, while stripping `ξ_0 = X` gives `#(M ⧸ ν_{1, k} M) = p ^ k` for all `k`. -/

section Examples

-- 1. Equal characteristic breaks the cyclotomic cutoff (`(p : O) = 0`).
example (p : ℕ) [Fact p.Prime] :
    let M := ((ZMod p)⟦X⟧)⟦X⟧ ⧸ Ideal.span {(X : ((ZMod p)⟦X⟧)⟦X⟧)}
    ((1 + X) ^ p ^ 0 - 1 : ((ZMod p)⟦X⟧)⟦X⟧) • deltaSubmodule p (ZMod p)⟦X⟧ M = ⊥ ∧
      Infinite (QuotSMulTop (growthTransition p (ZMod p)⟦X⟧ 1 1 : ((ZMod p)⟦X⟧)⟦X⟧) M) := by
  intro M
  have hp : p.Prime := Fact.out
  have : CharP (ZMod p)⟦X⟧ p :=
    charP_of_injective_ringHom (Function.LeftInverse.injective (constantCoeff_C (R := ZMod p))) p
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ _).mp hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [pow_zero, pow_one, add_sub_cancel_left]
    rw [Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · -- In char `p`, `ν_{1, 1} = Φ_p(X + 1) = X ^ (p - 1)` kills `M`, so `M ⧸ ν_{1, 1} M ≃ M`.
    have hν : (growthTransition p (ZMod p)⟦X⟧ 1 1 : ((ZMod p)⟦X⟧)⟦X⟧) = X ^ (p - 1) := by
      rw [growthTransition_self, Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_X_pow,
        pow_one, Nat.totient_prime hp, Polynomial.coe_pow, Polynomial.coe_X]
    have hsmul : (growthTransition p (ZMod p)⟦X⟧ 1 1 : ((ZMod p)⟦X⟧)⟦X⟧) •
        (⊤ : Submodule ((ZMod p)⟦X⟧)⟦X⟧ M) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ _).mp hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hν, Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton]
      exact (dvd_pow_self _ (Nat.sub_pos_of_lt hp.one_lt).ne').trans (dvd_mul_right _ _)
    have hO : Infinite (ZMod p)⟦X⟧ := TauCeti.IsDiscreteValuationRing.infinite
    have hM : Infinite M :=
      (Equiv.infinite_iff
        ((Ideal.quotEquivOfEq PowerSeries.ker_constantCoeff.symm).trans
          (RingHom.quotientKerEquivOfSurjective
            (f := (constantCoeff : ((ZMod p)⟦X⟧)⟦X⟧ →+* (ZMod p)⟦X⟧))
            fun r ↦ ⟨C r, constantCoeff_C r⟩)).toEquiv).mpr hO
    exact (Equiv.infinite_iff (Submodule.quotEquivOfEqBot _ hsmul).toEquiv).mpr hM

-- 2. Equal characteristic breaks linear `λ`-growth:
-- `M = O⟦X⟧ ⧸ (X - t)` has `#(M / ω_n M) = p ^ p ^ n`.
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let O := PowerSeries (ZMod p)
    let M := O⟦X⟧ ⧸ Ideal.span {((Polynomial.X - Polynomial.C (X : O) : O[X]) : O⟦X⟧)}
    Nat.card (QuotSMulTop ((1 + X) ^ p ^ n - 1 : O⟦X⟧) M) = p ^ p ^ n := by
  intro O M
  dsimp only [O, M]
  have : CharP (ZMod p)⟦X⟧ p :=
    charP_of_injective_ringHom (Function.LeftInverse.injective (constantCoeff_C (R := ZMod p))) p
  have : IsAdicComplete (maximalIdeal (ZMod p)) (ZMod p) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  have : IsAdicComplete (maximalIdeal (ZMod p)⟦X⟧) (ZMod p)⟦X⟧ :=
    PowerSeries.isAdicComplete_maximalIdeal
  have hF : (Polynomial.X - Polynomial.C (X : (ZMod p)⟦X⟧)).IsDistinguishedAt
      (maximalIdeal (ZMod p)⟦X⟧) := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, Polynomial.monic_X_sub_C _⟩
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hk
    subst hk
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_mem_iff]
    exact (PowerSeries.irreducible_X (R := ZMod p)).maximalIdeal_eq ▸
      Ideal.mem_span_singleton_self _
  have H := hF.isWeierstrassFactorizationAt
  have hcoe : (((1 + Polynomial.X) ^ p ^ n - 1 : ((ZMod p)⟦X⟧)[X]) : ((ZMod p)⟦X⟧)⟦X⟧) =
      (1 + X) ^ p ^ n - 1 := by simp
  have hnorm := H.norm_mk_coe_eq_resultant ((1 + Polynomial.X) ^ p ^ n - 1)
  rw [hcoe, Polynomial.natDegree_X_sub_C,
    Polynomial.resultant_X_sub_C_left _ _ (X : (ZMod p)⟦X⟧) le_rfl] at hnorm
  simp only [Polynomial.eval_pow, Polynomial.eval_X, add_pow_char_pow, one_pow,
    add_sub_cancel_left] at hnorm
  have hne : (X : (ZMod p)⟦X⟧) ^ p ^ n ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  rw [H.natCard_quotSMulTop (hnorm ▸ hne), hnorm, ← Ideal.span_singleton_pow,
    ← (PowerSeries.irreducible_X (R := ZMod p)).maximalIdeal_eq,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    Nat.card_congr (PowerSeries.residueFieldOfPowerSeries (k := ZMod p)).toEquiv, Nat.card_zmod]

-- 3. Ramified `p = 2, π² = 2` small-index check: `(1 + π)² - 1 = π² (1 + π)` has index `4`.
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hq : Nat.card (ResidueField O) = 2) {π : O} (hπ : Irreducible π) (h2 : π ^ 2 = 2) :
    (1 + π) ^ 2 - 1 = π ^ 2 * (1 + π) ∧ IsUnit (1 + π) ∧
      Nat.card (O ⧸ Ideal.span {(1 + π) ^ 2 - 1}) = 4 := by
  have heq : (1 + π) ^ 2 - 1 = π ^ 2 * (1 + π) := by
    calc (1 + π) ^ 2 - 1 = 2 * π + π ^ 2 := by ring
      _ = π ^ 2 * π + π ^ 2 := by rw [← h2]
      _ = π ^ 2 * (1 + π) := by ring
  have hu : IsUnit (1 + π) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, map_one,
      (IsLocalRing.residue_eq_zero_iff π).mpr
        (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π), add_zero]
    exact one_ne_zero
  refine ⟨heq, hu, ?_⟩
  rw [heq, Ideal.span_singleton_mul_right_unit hu, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, hq]
  norm_num

-- 4. Explicit `ℤ_p` cutoff on `M = ℤ_p⟦X⟧ ⧸ (X)`: `n₀ = 0` fails, while `n₀ = 1` gives `p ^ k`.
example (p : ℕ) [Fact p.Prime] (k : ℕ) :
    let M := ℤ_[p]⟦X⟧ ⧸ Ideal.span {(X : ℤ_[p]⟦X⟧)}
    Infinite (QuotSMulTop (growthTransition p ℤ_[p] 0 k : ℤ_[p]⟦X⟧) M) ∧
      Nat.card (QuotSMulTop (growthTransition p ℤ_[p] 1 k : ℤ_[p]⟦X⟧) M) = p ^ k := by
  intro M
  dsimp only [M]
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr (coeff_zero_growthTransition_zero p ℤ_[p] k)
    have hsmul : (growthTransition p ℤ_[p] 0 k : ℤ_[p]⟦X⟧) •
        (⊤ : Submodule ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {(X : ℤ_[p]⟦X⟧)})) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ _).mp hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul, hq, Polynomial.coe_mul, Polynomial.coe_X,
        mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    exact (Equiv.infinite_iff ((Submodule.quotEquivOfEqBot _ hsmul).toEquiv.trans
      (PowerSeries.quotientSpanXAlgEquiv ℤ_[p]).toEquiv)).mpr
      TauCeti.IsDiscreteValuationRing.infinite
  · have hX : (Polynomial.X : ℤ_[p][X]).IsDistinguishedAt (maximalIdeal ℤ_[p]) := by
      refine ⟨⟨fun {i} hi ↦ ?_⟩, Polynomial.monic_X⟩
      rw [Polynomial.natDegree_X, Nat.lt_one_iff] at hi
      simp [hi]
    have H := hX.isWeierstrassFactorizationAt
    have hres_eval (P : ℤ_[p][X]) : (Polynomial.X : ℤ_[p][X]).resultant P = P.coeff 0 := by
      have h := Polynomial.resultant_X_pow_left P 1 _ le_rfl
      rw [pow_one, pow_one] at h
      rwa [Polynomial.natDegree_X]
    have hXcoe : (X : ℤ_[p]⟦X⟧) = ((Polynomial.X : ℤ_[p][X]) : ℤ_[p]⟦X⟧) := Polynomial.coe_X.symm
    rw [hXcoe]
    have hnorm : Algebra.norm ℤ_[p]
        (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : ℤ_[p][X]) : ℤ_[p]⟦X⟧)})
          (growthTransition p ℤ_[p] 1 k : ℤ_[p]⟦X⟧)) = (p : ℤ_[p]) ^ k := by
      rw [H.norm_mk_coe_eq_resultant, hres_eval,
        coeff_zero_growthTransition Nat.one_pos, Nat.add_sub_cancel]
    have hne : ((p : ℤ_[p]) ^ k) ≠ 0 :=
      pow_ne_zero k (PadicInt.irreducible_p (p := p)).ne_zero
    rw [H.natCard_quotSMulTop (hnorm ▸ hne), hnorm, ← Ideal.span_singleton_pow,
      ← (PadicInt.irreducible_p (p := p)).maximalIdeal_eq,
      TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, PadicInt.card_residueField]

end Examples

end TauCeti.Iwasawa
