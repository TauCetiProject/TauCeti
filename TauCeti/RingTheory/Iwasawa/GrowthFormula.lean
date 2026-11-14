/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.EulerQuotient
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import TauCeti.RingTheory.Polynomial.Distinguished

import TauCeti.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Iwasawa.CyclotomicGrowth
import TauCeti.RingTheory.Jacobson.NilpotentAction
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm

/-!
# Iwasawa's growth formula

Let `p` be a prime and write `ξ_j = Φ_{p ^ j}(1 + X)` and `ω_n = (1 + X) ^ p ^ n - 1`, so that
`ξ_0 = X` and `ω_n = ξ_0 ξ_1 ⋯ ξ_n` (`Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one`).
The *transition polynomial*

  `ν_{n,n₀} = ξ_{n₀} ξ_{n₀+1} ⋯ ξ_n`

(`TauCeti.Iwasawa.growthTransition`) is `ω_n` for `n₀ = 0` and `ω_n / ω_c` for `n₀ = c + 1 ≤ n + 1`.

Let `O` be a complete discrete valuation ring with maximal ideal `𝔪` and residue field of order
`p ^ f`, in which `(p) = 𝔪 ^ e` (so `e ≥ 1`, `O` has characteristic zero and ramification index
`e`), and let `M` be a finitely generated module over `Λ = O⟦X⟧`, with `μ`-invariant `μ` and
`λ`-invariant `λ`. If the quotients `M ⧸ ν_{n,n₀} M` are
finite for all large `n`, then there is an integer `ν` with

  `#(M ⧸ ν_{n,n₀} M) = p ^ (f μ pⁿ + e f λ n + ν)`

for all large `n`. Over `O = ℤ_p` (`e = f = 1`) this is Iwasawa's formula
`#(M ⧸ ν_{n,n₀} M) = p ^ (μ pⁿ + λ n + ν)`; for `n₀ = 0` the quotients are the coinvariants
`M_{Γ_n} = M ⧸ ω_n M` of the subgroups `Γ_n = Γ ^ pⁿ` of `Γ ≅ ℤ_p`.

The proof combines three facts.

* The Euler quotient formula `#(M ⧸ GM) / #M[G] = q ^ (μ deg G) · #(O ⧸ Res(F_M, G))` for a
  distinguished polynomial `G` with `M ⧸ GM` finite, where `q = p ^ f` and `F_M` is the
  characteristic polynomial (`TauCeti.Iwasawa.natCard_quotSMulTop_div_natCard_torsionBy`). For
  `G = ν_{n,n₀}`, `deg G = pⁿ - D` with `D` independent of `n`.
* The kernels `M[ν_{n,n₀}]` increase with `n`, so they stabilize because `M` is noetherian; the
  stable kernel is a finite `Λ`-module, so its order is a power of `p`
  (`TauCeti.exists_natCard_eq_pow_of_natCast_mem_jacobson`).
* On `O⟦X⟧ ⧸ (F_M)`, the cyclotomic factor `ξ_{n+1}` acts as `p` times a unit once
  `n > e deg F_M`
  (`Polynomial.IsDistinguishedAt.associated_norm_mk_cyclotomic_prime_pow_comp_X_add_one`), so
  for `n₀ ≤ n + 1` the resultant `Res(F_M, ν_{n,n₀})` gains the factor `p ^ λ`, of valuation
  `e λ`, at each step.

The finiteness hypothesis is where the cyclotomic cutoff of the module enters: it fails for
`M = Λ ⧸ (ξ_j)` as soon as `n₀ ≤ j`. The assumption that `(p)` is a power of `𝔪`
excludes equal characteristic, where the formula is false.

## Main definitions

* `TauCeti.Iwasawa.growthTransition p O n₀ n`: the transition polynomial `ν_{n,n₀}`.

## Main results

* `TauCeti.Iwasawa.growthTransition_mul_growthTransition`: `ν_{k,n₀} ν_{n,k+1} = ν_{n,n₀}`.
* `TauCeti.Iwasawa.one_add_X_pow_sub_one_mul_growthTransition`: `ω_c ν_{n,c+1} = ω_n`.
* `TauCeti.Iwasawa.exists_forall_torsionBy_growthTransition_eq`: the kernels `M[ν_{n,n₀}]` of a
  noetherian module stabilize.
* `TauCeti.Iwasawa.associated_resultant_growthTransition`: `Res(F, ν_{m,n₀})` is associated to
  `Res(F, ν_{n,n₀}) p ^ (deg F (m - n))` for `n₀ ≤ n + 1`, `n > e deg F` and `m ≥ n`.
* `TauCeti.Iwasawa.exists_natCard_quotSMulTop_growthTransition_eq`: the growth formula
  `#(M ⧸ ν_{n,n₀} M) = p ^ (f μ pⁿ + e f λ n + ν)`.
* `TauCeti.Iwasawa.exists_natCard_quotSMulTop_growthTransition_eq_padicInt`: the growth formula
  `#(M ⧸ ν_{n,n₀} M) = p ^ (μ pⁿ + λ n + ν)` over `ℤ_p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition (5.3.17) and Lemma (5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, Theorem 13.13.
-/

public section

open IsLocalRing PowerSeries Submodule Filter
open scoped Polynomial PowerSeries

namespace TauCeti.Iwasawa

section Transition

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The *transition polynomial* `ν_{n,n₀} = ξ_{n₀} ξ_{n₀+1} ⋯ ξ_n`, where
`ξ_j = Φ_{p ^ j}(1 + X)`; it is `1` for `n + 1 ≤ n₀` (`growthTransition_eq_one_of_lt`). For prime
`p`, since `ξ_0 = X` and `ω_n = (1 + X) ^ p ^ n - 1 = ξ_0 ξ_1 ⋯ ξ_n`, it is `ω_n` for `n₀ = 0`
(`growthTransition_zero_left`) and `ω_n / ω_c` for `n₀ = c + 1 ≤ n + 1`
(`one_add_X_pow_sub_one_mul_growthTransition`). -/
noncomputable def growthTransition (n₀ n : ℕ) : O[X] :=
  ∏ j ∈ Finset.Ico n₀ (n + 1), (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)

theorem growthTransition_def (n₀ n : ℕ) : growthTransition p O n₀ n =
    ∏ j ∈ Finset.Ico n₀ (n + 1), (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) :=
  (rfl)

variable {p O}

/-- `ν_{n,n₀} = 1` for `n < n₀`: the product is empty. -/
@[simp]
theorem growthTransition_eq_one_of_lt {n₀ n : ℕ} (h : n < n₀) : growthTransition p O n₀ n = 1 := by
  rw [growthTransition_def, Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]

/-- `ν_{n,n} = ξ_n = Φ_{p ^ n}(1 + X)`. -/
theorem growthTransition_self (n : ℕ) :
    growthTransition p O n n = (Polynomial.cyclotomic (p ^ n) O).comp (Polynomial.X + 1) := by
  rw [growthTransition_def, Nat.Ico_succ_singleton, Finset.prod_singleton]

/-- The transition polynomials are compatible with ring homomorphisms of the coefficients. -/
@[simp]
theorem map_growthTransition {S : Type*} [CommRing S] (f : O →+* S) (n₀ n : ℕ) :
    (growthTransition p O n₀ n).map f = growthTransition p S n₀ n := by
  simp [growthTransition_def, Polynomial.map_prod, Polynomial.map_comp, Polynomial.map_cyclotomic]

/-- `ν_{n,n₁}` divides `ν_{m,n₀}` for `n₀ ≤ n₁` and `n ≤ m`. -/
theorem growthTransition_dvd {n₀ n₁ n m : ℕ} (h₀ : n₀ ≤ n₁) (h : n ≤ m) :
    growthTransition p O n₁ n ∣ growthTransition p O n₀ m :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Ico_subset_Ico h₀ (by omega))

/-- **The transition polynomials compose**: `ν_{k,n₀} ν_{n,k+1} = ν_{n,n₀}` for
`n₀ ≤ k + 1` and `k ≤ n`. -/
theorem growthTransition_mul_growthTransition {n₀ k n : ℕ} (h₀ : n₀ ≤ k + 1) (h : k ≤ n) :
    growthTransition p O n₀ k * growthTransition p O (k + 1) n = growthTransition p O n₀ n :=
  Finset.prod_Ico_consecutive _ h₀ (by omega)

/-- Passing from level `n` to level `m ≥ n` multiplies `ν_{n,n₀}` by `ξ_{n+1} ⋯ ξ_m`, for
`n₀ ≤ n + 1`. -/
private theorem growthTransition_mul_prod {n₀ n m : ℕ} (h₀ : n₀ ≤ n + 1) (h : n ≤ m) :
    growthTransition p O n₀ n *
        ∏ j ∈ Finset.Ico n m, (Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) =
      growthTransition p O n₀ m := by
  rw [← growthTransition_mul_growthTransition h₀ h, growthTransition_def p O (n + 1) m,
    Finset.prod_Ico_add' (fun j ↦ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1))]

/-- `ν_{n,n₀}` is monic. -/
theorem monic_growthTransition (n₀ n : ℕ) : (growthTransition p O n₀ n).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_cyclotomic_comp_X_add_one _

variable [Fact p.Prime]

/-- `ν_{n,0} = ω_n = (1 + X) ^ p ^ n - 1`. -/
@[simp]
theorem growthTransition_zero_left (n : ℕ) :
    growthTransition p O 0 n = (1 + Polynomial.X) ^ p ^ n - 1 := by
  rw [growthTransition_def, ← Finset.range_eq_Ico,
    Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one]

/-- **`ν_{n,c+1} = ω_n / ω_c`**: `ω_c ν_{n,c+1} = ω_n` for `c ≤ n`. -/
theorem one_add_X_pow_sub_one_mul_growthTransition {c n : ℕ} (h : c ≤ n) :
    ((1 + Polynomial.X) ^ p ^ c - 1) * growthTransition p O (c + 1) n =
      (1 + Polynomial.X) ^ p ^ n - 1 := by
  rw [← growthTransition_zero_left, ← growthTransition_zero_left,
    growthTransition_mul_growthTransition (Nat.zero_le _) h]

/-- `ν_{n,n₀}` is distinguished at every ideal containing `p`. -/
theorem isDistinguishedAt_growthTransition {I : Ideal O} (hI : (p : O) ∈ I) (n₀ n : ℕ) :
    (growthTransition p O n₀ n).IsDistinguishedAt I :=
  Polynomial.isDistinguishedAt_prod fun j _ ↦
    Polynomial.cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt p hI j

/-- The constant coefficient of `ν_{n,n₀}` is `p ^ (n + 1 - n₀)` for `n₀ ≥ 1`: each `ξ_j` with
`j ≥ 1` has constant coefficient `p`. In particular `ν_{n,n₀}` acts on `O⟦X⟧ ⧸ (X) = O` as
multiplication by `p ^ (n + 1 - n₀)`, whereas `ω_n` acts as zero. -/
@[simp]
theorem coeff_zero_growthTransition {n₀ : ℕ} (h₀ : 0 < n₀) (n : ℕ) :
    (growthTransition p O n₀ n).coeff 0 = (p : O) ^ (n + 1 - n₀) := by
  rw [growthTransition_def, Polynomial.coeff_zero_prod, ← Nat.card_Ico n₀ (n + 1),
    ← Finset.prod_const]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by grind⟩
  exact Polynomial.coeff_zero_cyclotomic_prime_pow_comp_X_add_one (R := O) p k

variable [Nontrivial O]

/-- `ν_{n,0} = ω_n` has degree `pⁿ`. -/
theorem natDegree_growthTransition_zero_left (n : ℕ) :
    (growthTransition p O 0 n).natDegree = p ^ n := by
  rw [growthTransition_zero_left, TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one]

/-- `ν_{n,c+1} = ω_n / ω_c` has degree `pⁿ - p ^ c`; both sides vanish for `n < c`. -/
@[simp]
theorem natDegree_growthTransition_succ_left (c n : ℕ) :
    (growthTransition p O (c + 1) n).natDegree = p ^ n - p ^ c := by
  rcases lt_or_ge n c with h | h
  · rw [growthTransition_eq_one_of_lt (by omega), Polynomial.natDegree_one,
      Nat.sub_eq_zero_of_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos h.le)]
  have hω : ((1 + Polynomial.X : O[X]) ^ p ^ c - 1).Monic :=
    TauCeti.Polynomial.monic_one_add_X_pow_sub_one (pow_ne_zero c (Fact.out : p.Prime).ne_zero)
  have hdeg := congrArg Polynomial.natDegree
    (one_add_X_pow_sub_one_mul_growthTransition (O := O) (p := p) h)
  rw [hω.natDegree_mul (monic_growthTransition _ _),
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one,
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one] at hdeg
  omega

variable (p O) in
/-- The degree of `ν_{n,n₀}` is `pⁿ` minus a constant independent of `n ≥ n₀`. -/
private theorem exists_natDegree_growthTransition_add_eq (n₀ : ℕ) :
    ∃ D : ℕ, ∀ n, n₀ ≤ n → (growthTransition p O n₀ n).natDegree + D = p ^ n := by
  rcases n₀ with _ | c
  · exact ⟨0, fun n _ ↦ by rw [natDegree_growthTransition_zero_left, add_zero]⟩
  · refine ⟨p ^ c, fun n hn ↦ ?_⟩
    rw [natDegree_growthTransition_succ_left,
      Nat.sub_add_cancel (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega))]

end Transition

section Growth

variable {O : Type*} [CommRing O]

/-- **The kernels of the transition polynomials stabilize.** For a noetherian `O⟦X⟧`-module `M`,
the kernels `M[ν_{n,n₀}]` increase with `n`, so they are eventually constant. -/
theorem exists_forall_torsionBy_growthTransition_eq (p n₀ : ℕ) (M : Type*)
    [AddCommMonoid M] [Module O⟦X⟧ M] [IsNoetherian O⟦X⟧ M] :
    ∃ N, ∀ n, N ≤ n → torsionBy O⟦X⟧ M (growthTransition p O n₀ n : O⟦X⟧) =
      torsionBy O⟦X⟧ M (growthTransition p O n₀ N : O⟦X⟧) := by
  let f : ℕ →o Submodule O⟦X⟧ M :=
    ⟨fun n ↦ torsionBy O⟦X⟧ M (growthTransition p O n₀ n : O⟦X⟧), fun _ _ h ↦
      torsionBy_le_torsionBy_of_dvd _ _
        (map_dvd Polynomial.coeToPowerSeries.ringHom (growthTransition_dvd le_rfl h))⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance f
  exact ⟨N, fun n hn ↦ (hN n hn).symm⟩

/-- **The resultants with the transition polynomials grow by `p ^ deg F` per level.** Let `O` be
`I`-adically complete with `I ^ e ⊆ (p)` and `p` in the Jacobson radical, and let `F` be
distinguished at `I`. For `n₀ ≤ n + 1`, `n > e deg F` and `m ≥ n`, `Res(F, ν_{m,n₀})` is
associated to `Res(F, ν_{n,n₀}) p ^ (deg F (m - n))`. -/
theorem associated_resultant_growthTransition {p : ℕ} [Fact p.Prime] {I : Ideal O}
    [IsAdicComplete I O] {F : O[X]} (hF : F.IsDistinguishedAt I) {e : ℕ}
    (hI : I ^ e ≤ Ideal.span {(p : O)}) (hpO : (p : O) ∈ (⊥ : Ideal O).jacobson) {n₀ n m : ℕ}
    (h₀ : n₀ ≤ n + 1) (hn : F.natDegree * e < n) (hm : n ≤ m) :
    Associated (F.resultant (growthTransition p O n₀ m))
      (F.resultant (growthTransition p O n₀ n) * (p : O) ^ (F.natDegree * (m - n))) := by
  have H := hF.isWeierstrassFactorizationAt
  have hcoe : ((∏ j ∈ Finset.Ico n m,
      (Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) : O[X]) : O⟦X⟧) =
      ∏ j ∈ Finset.Ico n m,
        ((Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) : O⟦X⟧) :=
    map_prod Polynomial.coeToPowerSeries.ringHom _ _
  rw [← H.norm_mk_coe_eq_resultant, ← H.norm_mk_coe_eq_resultant,
    ← growthTransition_mul_prod h₀ hm, Polynomial.coe_mul, map_mul, map_mul, hcoe]
  exact (hF.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one hI hpO hn m).mul_left _

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

/-- **The invariants under the transitions have eventually constant `p`-power order.** Let `O` be
a complete discrete valuation ring with finite residue field, in whose maximal ideal the prime
`p` lies, and let `M` be a finitely generated `O⟦X⟧`-module. If the quotients `M ⧸ ν_{n,n₀} M` are
finite for all large `n`, then there is `κ` with `#M[ν_{n,n₀}] = p ^ κ` for all large `n`. -/
theorem exists_natCard_torsionBy_growthTransition_eq [Finite (ResidueField O)] {p : ℕ}
    [Fact p.Prime] (hp : (p : O) ∈ maximalIdeal O) {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] {n₀ : ℕ}
    (hfin : ∀ᶠ n in atTop, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ κ : ℕ, ∀ᶠ n in atTop,
      Nat.card (torsionBy O⟦X⟧ M (growthTransition p O n₀ n : O⟦X⟧)) = p ^ κ := by
  obtain ⟨N₁, hN₁⟩ := exists_forall_torsionBy_growthTransition_eq (O := O) p n₀ M
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hfin
  set N := max N₁ N₂
  -- `p` is a non-unit of the local ring `O⟦X⟧`, so it lies in its Jacobson radical.
  have hpΛ : ((p : ℕ) : O⟦X⟧) ∈ Ring.jacobson O⟦X⟧ := by
    rw [← Ideal.jacobson_bot]
    refine maximalIdeal_le_jacobson _ ((mem_maximalIdeal _).2 fun hu ↦ ?_)
    rw [isUnit_iff_constantCoeff, map_natCast] at hu
    exact (mem_maximalIdeal _).1 hp hu
  -- The stable kernel `M[ν_{N,n₀}]` is a finite `O⟦X⟧`-module, so its order is a power of `p`.
  have := finite_torsionBy_of_finite_quotSMulTop (monic_growthTransition n₀ N)
    (hN₂ N (le_max_right _ _))
  obtain ⟨κ, hκ⟩ := exists_natCard_eq_pow_of_natCast_mem_jacobson
    (N := torsionBy O⟦X⟧ M (growthTransition p O n₀ N : O⟦X⟧)) hpΛ
  refine ⟨κ, (eventually_ge_atTop N).mono fun n hn ↦ ?_⟩
  rw [(hN₁ n (le_of_max_le_left hn)).trans (hN₁ N (le_max_left _ _)).symm, hκ]

/-- **The order of `O ⧸ Res(F, ν_{n,n₀})` grows by `q ^ (e deg F)` per level.** Let `O` be a
complete discrete valuation ring with maximal ideal `𝔪` and residue field of order `q`, in which
`(p) = 𝔪 ^ e` with `e ≥ 1` for the prime `p`, and let `F` be distinguished. If `n₀ ≤ N + 1` and
`N > e deg F`, then `#(O ⧸ Res(F, ν_{n,n₀})) = #(O ⧸ Res(F, ν_{N,n₀})) q ^ (e deg F (n - N))` for
every `n ≥ N`. -/
theorem natCard_quotient_resultant_growthTransition {p : ℕ} [Fact p.Prime] {e : ℕ} (he : 0 < e)
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) {F : O[X]}
    (hF : F.IsDistinguishedAt (maximalIdeal O)) {n₀ N : ℕ} (h₀ : n₀ ≤ N + 1)
    (hN : F.natDegree * e < N) {n : ℕ} (hn : N ≤ n) :
    Nat.card (O ⧸ Ideal.span {F.resultant (growthTransition p O n₀ n)}) =
      Nat.card (O ⧸ Ideal.span {F.resultant (growthTransition p O n₀ N)}) *
        Nat.card (ResidueField O) ^ (e * F.natDegree * (n - N)) := by
  have hpm : (p : O) ∈ maximalIdeal O :=
    Ideal.pow_le_self he.ne' (hpe ▸ Ideal.mem_span_singleton_self _)
  have hres := associated_resultant_growthTransition hF hpe.ge (maximalIdeal_le_jacobson _ hpm) h₀
    hN hn
  rw [Ideal.span_singleton_eq_span_singleton.2 hres, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_pow, hpe, ← pow_mul, ← Submodule.cardQuot_apply, cardQuot_mul,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, mul_assoc]

/-- **Iwasawa's growth formula.** Let `O` be a complete discrete valuation ring with maximal ideal
`𝔪` and residue field of order `p ^ f`, in which `(p) = 𝔪 ^ e` for the prime `p`, and let `M`
be a finitely generated `O⟦X⟧`-module with `μ`-invariant `μ` and `λ`-invariant `λ`. If the
quotients `M ⧸ ν_{n,n₀} M` by the transition polynomials are finite for all large `n`, then there
is an integer `ν` such that `#(M ⧸ ν_{n,n₀} M) = p ^ (f μ pⁿ + e f λ n + ν)` for all large `n`. -/
theorem exists_natCard_quotSMulTop_growthTransition_eq {p : ℕ} [Fact p.Prime] {e f : ℕ}
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) (hq : Nat.card (ResidueField O) = p ^ f)
    {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] {n₀ : ℕ}
    (hfin : ∀ᶠ n in atTop, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ ν : ℤ, ∀ᶠ n in atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M) : ℚ) =
        (p : ℚ) ^ (((f * muInvariant O M * p ^ n + e * f * lambdaInvariant O M * n : ℕ) : ℤ) +
          ν) := by
  have hp := (Fact.out : p.Prime)
  have : Finite (ResidueField O) := Nat.finite_of_card_ne_zero (hq ▸ (pow_pos hp.pos f).ne')
  -- The residue field has order `p ^ f`, so it has characteristic `p`: `p` lies in `𝔪`.
  have hpm : (p : O) ∈ maximalIdeal O := by
    have h : ((p : ResidueField O)) ^ f = 0 := by
      simpa [hq] using card_nsmul_eq_zero' (x := (1 : ResidueField O))
    rw [← residue_eq_zero_iff, map_natCast]
    exact eq_zero_of_pow_eq_zero h
  have he : 0 < e := Nat.pos_of_ne_zero fun h ↦ by
    rw [h, pow_zero, Ideal.one_eq_top, Ideal.span_singleton_eq_top] at hpe
    exact (mem_maximalIdeal _).1 hpm hpe
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set l := lambdaInvariant O M
  -- Past some level `N`, the kernels have order `p ^ κ`, the quotients are finite and the
  -- cyclotomic factors act on `O⟦X⟧ ⧸ (F_M)` as `p` times units; then `Res(F_M, ν_{N,n₀})` is
  -- nonzero, associated to `ϖ ^ v` for a uniformizer `ϖ`.
  obtain ⟨κ, hκ⟩ := exists_natCard_torsionBy_growthTransition_eq hpm hfin
  obtain ⟨D, hD⟩ := exists_natDegree_growthTransition_add_eq p O n₀
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hκ.and hfin)
  obtain ⟨N, hN₁N, hn₀N, hlN⟩ : ∃ N, N₁ ≤ N ∧ n₀ ≤ N ∧ l * e < N :=
    ⟨max N₁ (max n₀ (l * e + 1)), by omega⟩
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (resultant_charPoly_ne_zero_of_finite_quotSMulTop (hN₁ N hN₁N).2) hϖ
  refine ⟨κ + f * v - f * muInvariant O M * D - e * f * l * N, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  -- The Euler quotient formula at level `n`, with every factor a power of `p`.
  have heuler := natCard_quotSMulTop_div_natCard_torsionBy
    (isDistinguishedAt_growthTransition hpm n₀ n) (hN₁ n (by omega)).2
  rw [(hN₁ n (by omega)).1, natCard_quotient_resultant_growthTransition he hpe
      isDistinguishedAt_charPoly (by omega) (by rwa [← lambdaInvariant_def]) hn,
    Ideal.span_singleton_eq_span_singleton.2 hv, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    ← pow_add, hq,
    div_eq_iff (by exact_mod_cast (pow_pos hp.pos κ).ne')] at heuler
  rw [heuler]
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← zpow_natCast]
  congr 1
  -- Compare the exponents, using `deg ν_{n,n₀} = pⁿ - D`.
  have hdeg : ((growthTransition p O n₀ n).natDegree : ℤ) = p ^ n - D := by
    have := congrArg (Nat.cast : ℕ → ℤ) (hD n (by omega))
    push_cast at this
    linarith
  have hnN : ((n - N : ℕ) : ℤ) = n - N := by omega
  push_cast [hnN, hdeg, ← lambdaInvariant_def]
  ring

/-- **Iwasawa's growth formula over `ℤ_p`.** Let `M` be a finitely generated `ℤ_p⟦X⟧`-module with
`μ`-invariant `μ` and `λ`-invariant `λ`. If the quotients `M ⧸ ν_{n,n₀} M` by the transition
polynomials are finite for all large `n`, then there is an integer `ν` such that
`#(M ⧸ ν_{n,n₀} M) = p ^ (μ pⁿ + λ n + ν)` for all large `n`. -/
theorem exists_natCard_quotSMulTop_growthTransition_eq_padicInt {p : ℕ} [Fact p.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] {n₀ : ℕ}
    (hfin : ∀ᶠ n in atTop, Finite (QuotSMulTop (growthTransition p ℤ_[p] n₀ n : ℤ_[p]⟦X⟧) M)) :
    ∃ ν : ℤ, ∀ᶠ n in atTop,
      (Nat.card (QuotSMulTop (growthTransition p ℤ_[p] n₀ n : ℤ_[p]⟦X⟧) M) : ℚ) =
        (p : ℚ) ^ (((muInvariant ℤ_[p] M * p ^ n + lambdaInvariant ℤ_[p] M * n : ℕ) : ℤ) + ν) := by
  simpa only [one_mul] using exists_natCard_quotSMulTop_growthTransition_eq (e := 1) (f := 1)
    (by rw [pow_one, PadicInt.maximalIdeal_eq_span_p])
    (by rw [PadicInt.card_residueField, pow_one])
    hfin

end Growth

/-! ### Checks -/

-- On `ℤ_p⟦X⟧ ⧸ (X) = ℤ_p`, the transition `ν_{n,1} = ω_n / ω_0` acts as `pⁿ`, while `ω_n` acts as
-- zero: the growth of a horizontal factor `X` is only visible through the transition.
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (growthTransition p ℤ_[p] 1 n).coeff 0 = (p : ℤ_[p]) ^ n ∧
      (growthTransition p ℤ_[p] 0 n).coeff 0 = 0 := by
  refine ⟨by simp, ?_⟩
  simp [Polynomial.coeff_zero_eq_eval_zero]

end TauCeti.Iwasawa
