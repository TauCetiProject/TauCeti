/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.RingTheory.Iwasawa.LambdaInvariant
public import TauCeti.RingTheory.Iwasawa.MuInvariant

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Iwasawa.CyclotomicGrowth
import TauCeti.RingTheory.Iwasawa.EulerQuotient
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Iwasawa's growth formula

Let `p` be a prime and `O` a complete discrete valuation ring of characteristic zero with finite
residue field of cardinality `q` and absolute ramification index `e`, so that `(p) = 𝔪 ^ e`. Let
`Λ = O⟦X⟧`, where `1 + X` plays the role of a topological generator `γ` of `Γ ≅ ℤ_p`, and write

```text
ξ_j = Φ_{p ^ j}(1 + X),    ω_n = (1 + X) ^ pⁿ - 1 = ξ_0 ξ_1 ⋯ ξ_n,
```

so that `ξ_0 = X`. The *transition polynomial* `ν_{n₀,n} = ξ_{n₀} ξ_{n₀+1} ⋯ ξ_n`
(`TauCeti.Iwasawa.growthTransition`) is `ω_n / ω_{n₀-1}`; for `n₀ = 0` it is `ω_n` itself, and for
`n₀ ≥ 1` its constant coefficient is a power of `p`.

The main theorem is Iwasawa's formula for the orders of the quotients of a finitely generated
`Λ`-module `M` by the transitions: if `M ⧸ ν_{n₀,n} M` is finite for all large `n`, then there is
an integer `ν` with

`#(M ⧸ ν_{n₀,n} M) = q ^ (μ pⁿ + e λ n + ν)`

for all large `n`, where `μ = μ(M)` and `λ = λ(M)` are the Iwasawa invariants of `M`
(`TauCeti.Iwasawa.muInvariant`, `TauCeti.Iwasawa.lambdaInvariant`). For `n₀ = 0` these quotients
are the coinvariants `M_{Γ_n} = M ⧸ ω_n M` of the subgroup `Γ_n = Γ ^ pⁿ`. Allowing `n₀ > 0` is
what makes the formula apply when `F_M` shares a factor with some `ξ_j`, `j < n₀`: then
`M ⧸ ω_n M` is infinite, while the quotients by the transitions stay finite. Over `ℤ_p`, where
`q = p` and `e = 1`, the formula reads `#(M ⧸ ν_{n₀,n} M) = p ^ (μ pⁿ + λ n + ν)`
(`TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt`).

The proof combines three inputs. The Euler quotient at finite level
(`TauCeti.Iwasawa.natCard_quotSMulTop_div_natCard_torsionBy`) gives, whenever `M ⧸ ν M` is finite,

`#(M ⧸ ν M) = #M[ν] · q ^ (μ deg ν) · #(O ⧸ Res(F_M, ν))`,

with `F_M` the characteristic polynomial of `M`. The kernels `M[ν_{n₀,n}]` increase with `n`, so
they stabilize since `M` is noetherian; they are finite, so their orders are a constant power of
`q` (`TauCeti.natCard_eq_pow_of_length_eq`). Finally, once `n > λ e`, each further cyclotomic
factor `ξ_{n+1}` acts on `O⟦X⟧ ⧸ (F_M)` as `p` times an automorphism
(`Polynomial.IsDistinguishedAt.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one`), so the
resultant `Res(F_M, ν_{n₀,n})` gains a factor associated to `p ^ λ`, of index `q ^ (e λ)`, at each
step. The degree `deg ν_{n₀,n} = pⁿ - deg ω_{n₀-1}` contributes `μ pⁿ` up to a constant.

In characteristic `p` the formula is false: then `ξ_j = X ^ φ(p ^ j)`, and for `O = 𝔽_p⟦ϖ⟧` the
module `Λ ⧸ (X - ϖ)` has `μ = 0` and `λ = 1`, but `#(M ⧸ ω_n M) = p ^ pⁿ`. The hypothesis
`(p) = 𝔪 ^ e` with `e > 0` excludes this case, as it forces `p ≠ 0`.

## Main definitions

* `TauCeti.Iwasawa.growthTransition p O n₀ n`: the transition polynomial `ξ_{n₀} ⋯ ξ_n`.

## Main results

* `TauCeti.Iwasawa.growthTransition_self`, `TauCeti.Iwasawa.growthTransition_succ` and
  `TauCeti.Iwasawa.monic_growthTransition`: `ν_{j,j} = ξ_j`, `ν_{n₀,n+1} = ν_{n₀,n} ξ_{n+1}`, and
  `ν_{n₀,n}` is monic.
* `TauCeti.Iwasawa.prod_range_mul_growthTransition`: `ω_{n₀-1} · ν_{n₀,n} = ω_n`, and
  `TauCeti.Iwasawa.natDegree_prod_range_add_natDegree_growthTransition`: the degrees add up to
  `pⁿ`.
* `TauCeti.Iwasawa.isDistinguishedAt_growthTransition`: `ν_{n₀,n}` is distinguished at every
  ideal containing `p`.
* `TauCeti.Iwasawa.coeff_zero_growthTransition`: for `n₀ ≥ 1` the constant coefficient of
  `ν_{n₀,n}` is `p ^ (n + 1 - n₀)`.
* `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq`: Iwasawa's growth
  formula `#(M ⧸ ν_{n₀,n} M) = q ^ (μ pⁿ + e λ n + ν)` for all large `n`.
* `TauCeti.Iwasawa.exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt`: the
  case `O = ℤ_p`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, Proposition 5.3.17 and (5.3.17)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, Theorem 13.13.
-/

public section

open IsLocalRing PowerSeries Filter
open scoped Polynomial PowerSeries

namespace TauCeti.Iwasawa

section Transition

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The *transition polynomial* `ν_{n₀,n} = ξ_{n₀} ξ_{n₀+1} ⋯ ξ_n`, where `ξ_j = Φ_{p ^ j}(1 + X)`
is the `j`-th cyclotomic factor of `ω_n = (1 + X) ^ pⁿ - 1 = ξ_0 ⋯ ξ_n`. It is the quotient
`ω_n / ω_{n₀-1}` (`prod_range_mul_growthTransition`), equal to `ω_n` for `n₀ = 0`, and to `1`
for `n < n₀`. -/
noncomputable def growthTransition (n₀ n : ℕ) : O[X] :=
  ∏ j ∈ Finset.Icc n₀ n, (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)

theorem growthTransition_def (n₀ n : ℕ) :
    growthTransition p O n₀ n =
      ∏ j ∈ Finset.Icc n₀ n, (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) :=
  (rfl)

variable {p O}

/-- Below the bottom level the transition is the empty product `1`. -/
@[simp]
theorem growthTransition_of_lt {n₀ n : ℕ} (h : n < n₀) : growthTransition p O n₀ n = 1 := by
  rw [growthTransition_def, Finset.Icc_eq_empty_of_lt h, Finset.prod_empty]

/-- The transition from level `j` to itself is the single cyclotomic factor `ξ_j`. -/
theorem growthTransition_self (j : ℕ) :
    growthTransition p O j j = (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) := by
  rw [growthTransition_def, Finset.Icc_self, Finset.prod_singleton]

/-- Raising the top level by one multiplies the transition by the next cyclotomic factor. -/
theorem growthTransition_succ {n₀ n : ℕ} (h : n₀ ≤ n + 1) :
    growthTransition p O n₀ (n + 1) =
      growthTransition p O n₀ n * (Polynomial.cyclotomic (p ^ (n + 1)) O).comp (Polynomial.X + 1) :=
  Finset.prod_Icc_succ_top h _

/-- The transition polynomial is monic. -/
theorem monic_growthTransition (n₀ n : ℕ) : (growthTransition p O n₀ n).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_cyclotomic_comp_X_add_one _

/-- Raising the top level from `a` to `k` multiplies the transition by `ξ_{a+1} ⋯ ξ_k`. -/
theorem growthTransition_mul_prod_Ico {n₀ a k : ℕ} (h₀ : n₀ ≤ a + 1) (hak : a ≤ k) :
    growthTransition p O n₀ a *
        ∏ j ∈ Finset.Ico a k, (Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) =
      growthTransition p O n₀ k := by
  rw [growthTransition_def, growthTransition_def, ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_add' (fun j ↦ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) a k 1,
    Finset.prod_Ico_consecutive _ h₀ (by omega)]

/-- The transitions divide each other as the top level increases. -/
theorem growthTransition_dvd_growthTransition (n₀ : ℕ) {n k : ℕ} (h : n ≤ k) :
    growthTransition p O n₀ n ∣ growthTransition p O n₀ k :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Icc_subset_Icc_right h)

variable [Fact p.Prime]

/-- `ω_{n₀-1} · ν_{n₀,n} = ω_n`: the transition `ν_{n₀,n}` is the quotient of
`ω_n = (1 + X) ^ pⁿ - 1` by the product `ω_{n₀-1} = ξ_0 ⋯ ξ_{n₀-1}` of the lower cyclotomic
factors, for `n₀ ≤ n + 1`. -/
theorem prod_range_mul_growthTransition {n₀ n : ℕ} (h : n₀ ≤ n + 1) :
    (∏ j ∈ Finset.range n₀, growthTransition p O j j) * growthTransition p O n₀ n =
      (1 + Polynomial.X) ^ p ^ n - 1 := by
  simp only [growthTransition_self]
  rw [growthTransition_def, ← Finset.Ico_add_one_right_eq_Icc, Finset.range_eq_Ico,
    Finset.prod_Ico_consecutive _ (Nat.zero_le n₀) h, ← Finset.range_eq_Ico,
    Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one]

/-- For `n₀ = 0` the transition is `ω_n = (1 + X) ^ pⁿ - 1`. -/
@[simp]
theorem growthTransition_zero_left (n : ℕ) :
    growthTransition p O 0 n = (1 + Polynomial.X) ^ p ^ n - 1 := by
  simpa using prod_range_mul_growthTransition (p := p) (O := O) (Nat.zero_le (n + 1))

/-- The transition polynomial is distinguished at every ideal containing `p`. -/
theorem isDistinguishedAt_growthTransition {I : Ideal O} (hI : (p : O) ∈ I) (n₀ n : ℕ) :
    (growthTransition p O n₀ n).IsDistinguishedAt I :=
  Polynomial.isDistinguishedAt_prod fun j _ ↦
    Polynomial.cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt p hI j

/-- For `n₀ ≥ 1` the constant coefficient of `ν_{n₀,n}` is `p ^ (n + 1 - n₀)`: each factor `ξ_j`
with `j ≥ 1` has constant coefficient `p`. By contrast `ω_n` has constant coefficient `0`. -/
theorem coeff_zero_growthTransition {n₀ : ℕ} (h₀ : 0 < n₀) (n : ℕ) :
    (growthTransition p O n₀ n).coeff 0 = (p : O) ^ (n + 1 - n₀) := by
  rw [growthTransition_def, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod,
    ← Nat.card_Icc, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := Nat.exists_eq_add_one_of_ne_zero (by grind)
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_zero_cyclotomic_prime_pow_comp_X_add_one]

/-- The degrees of `ω_{n₀-1}` and of `ν_{n₀,n}` add up to `deg ω_n = pⁿ`, for `n₀ ≤ n + 1`. -/
theorem natDegree_prod_range_add_natDegree_growthTransition [Nontrivial O] {n₀ n : ℕ}
    (h : n₀ ≤ n + 1) :
    (∏ j ∈ Finset.range n₀, growthTransition p O j j).natDegree +
        (growthTransition p O n₀ n).natDegree =
      p ^ n := by
  rw [← Polynomial.Monic.natDegree_mul
    (Polynomial.monic_prod_of_monic _ _ fun j _ ↦ monic_growthTransition j j)
    (monic_growthTransition n₀ n), prod_range_mul_growthTransition h,
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one]

end Transition

section Growth

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
  {p : ℕ} [Fact p.Prime]

omit [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [Module.Finite O⟦X⟧ M]
  [Fact p.Prime] in
/-- If `(p) = 𝔪 ^ e` with `e > 0`, then `p` lies in the maximal ideal. -/
private theorem natCast_mem_maximalIdeal {e : ℕ} (he : 0 < e)
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) : (p : O) ∈ maximalIdeal O :=
  Ideal.pow_le_self he.ne' (hpe ▸ Ideal.mem_span_singleton_self _)

omit [Finite (ResidueField O)] [Module.Finite O⟦X⟧ M] in
/-- **The resultant along the transitions.** If `(p) = 𝔪 ^ e` and `a > λ(M) e`, then for `k ≥ a`
the quotient of `O` by `Res(F_M, ν_{n₀,k})` has `#(O ⧸ Res(F_M, ν_{n₀,a})) · q ^ (e λ(M) (k - a))`
elements: each cyclotomic factor `ξ_{j+1}`, `a ≤ j < k`, contributes a factor associated to
`p ^ λ(M)`. -/
private theorem natCard_quotient_resultant_growthTransition {e : ℕ} (he : 0 < e)
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) {n₀ a k : ℕ} (h₀ : n₀ ≤ a + 1)
    (ha : lambdaInvariant O M * e < a) (hak : a ≤ k) :
    Nat.card (O ⧸ Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ k)}) =
      Nat.card (O ⧸ Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ a)}) *
        Nat.card (ResidueField O) ^ (e * lambdaInvariant O M * (k - a)) := by
  have hF := isDistinguishedAt_charPoly (O := O) (M := M)
  have H := hF.isWeierstrassFactorizationAt
  have hpJ : (p : O) ∈ (⊥ : Ideal O).jacobson := by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact natCast_mem_maximalIdeal he hpe
  -- The norm of `ξ_{a+1} ⋯ ξ_k` on `O⟦X⟧ ⧸ (F_M)` is associated to `p ^ (λ (k - a))`.
  rw [lambdaInvariant_def] at ha
  have hassoc := hF.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one hpe.ge hpJ ha k
  have hcoe : ((∏ j ∈ Finset.Ico a k,
      (Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) : O[X]) : O⟦X⟧) =
      ∏ j ∈ Finset.Ico a k, ((Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) :
        O⟦X⟧) :=
    map_prod Polynomial.coeToPowerSeries.ringHom _ _
  -- The resultant is multiplicative along `ν_{n₀,k} = ν_{n₀,a} · ξ_{a+1} ⋯ ξ_k`.
  have hres : Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ k)} =
      Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ a)} *
        Ideal.span {(p : O) ^ ((charPoly O M).natDegree * (k - a))} := by
    rw [← growthTransition_mul_prod_Ico (p := p) (O := O) h₀ hak, ← H.norm_mk_coe_eq_resultant,
      Polynomial.coe_mul, map_mul, map_mul, H.norm_mk_coe_eq_resultant, hcoe,
      ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton.mpr hassoc]
  -- The ideal `(p ^ (λ (k - a))) = 𝔪 ^ (e λ (k - a))` has index `q ^ (e λ (k - a))`.
  have hidx : Nat.card (O ⧸ Ideal.span {(p : O) ^ ((charPoly O M).natDegree * (k - a))}) =
      Nat.card (ResidueField O) ^ (e * lambdaInvariant O M * (k - a)) := by
    rw [← Ideal.span_singleton_pow, hpe, ← pow_mul,
      TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, lambdaInvariant_def]
    ring_nf
  -- Conclude by multiplicativity of the ideal norm.
  rw [hres, ← Ideal.absNorm_eq_natCard, map_mul, Ideal.absNorm_eq_natCard,
    Ideal.absNorm_eq_natCard, hidx]

/-- **The order of a quotient by a transition, at a deep level.** Let `(p) = 𝔪 ^ e` with `e > 0`,
let `a ≥ n₀ - 1` with `a > λ(M) e`, and let `k ≥ a` be a level at which `M ⧸ ν_{n₀,k} M` is
finite and the kernel `M[ν_{n₀,k}]` equals `M[ν_{n₀,a}]`. Then `#(M ⧸ ν_{n₀,k} M)` is
`#M[ν_{n₀,a}] · q ^ (μ deg ν_{n₀,k}) · #(O ⧸ Res(F_M, ν_{n₀,a})) · q ^ (e λ (k - a))`. -/
private theorem natCard_quotSMulTop_growthTransition_eq_mul {e : ℕ} (he : 0 < e)
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) {n₀ a k : ℕ} (h₀ : n₀ ≤ a + 1)
    (ha : lambdaInvariant O M * e < a) (hak : a ≤ k)
    (hfin : Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M))
    (hker : Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ k : O⟦X⟧) =
      Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ a : O⟦X⟧)) :
    Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) =
      Nat.card (Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ a : O⟦X⟧)) *
        Nat.card (ResidueField O) ^ (muInvariant O M * (growthTransition p O n₀ k).natDegree) *
        Nat.card (O ⧸ Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ a)}) *
        Nat.card (ResidueField O) ^ (e * lambdaInvariant O M * (k - a)) := by
  have hD := isDistinguishedAt_growthTransition (p := p) (natCast_mem_maximalIdeal he hpe) n₀ k
  have := finite_torsionBy_of_finite_quotSMulTop hD.monic hfin
  have hE := natCard_quotSMulTop_div_natCard_torsionBy hD hfin
  rw [natCard_quotient_resultant_growthTransition he hpe h₀ ha hak,
    div_eq_iff (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), hker] at hE
  apply Nat.cast_injective (R := ℚ)
  rw [hE]
  push_cast
  ring

/-- **Iwasawa's growth formula.** Let `O` be a complete discrete valuation ring with finite residue
field of cardinality `q`, in which `(p) = 𝔪 ^ e` for a prime `p` and some `e > 0`, and let `M` be a
finitely generated `O⟦X⟧`-module with Iwasawa invariants `μ = μ(M)` and `λ = λ(M)`. If the
quotients `M ⧸ ν_{n₀,n} M` by the transition polynomials `ν_{n₀,n} = ω_n / ω_{n₀-1}` are finite for
all large `n`, then there is an integer `ν` such that `#(M ⧸ ν_{n₀,n} M) = q ^ (μ pⁿ + e λ n + ν)`
for all large `n`. -/
theorem exists_eventually_natCard_quotSMulTop_growthTransition_eq {e : ℕ} (he : 0 < e)
    (hpe : Ideal.span {(p : O)} = maximalIdeal O ^ e) (n₀ : ℕ)
    (hfin : ∀ᶠ k in atTop, Finite (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M)) :
    ∃ ν : ℤ, ∀ᶠ k in atTop,
      (Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) : ℚ) =
        (Nat.card (ResidueField O) : ℚ) ^
          (((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) + ν) := by
  -- The kernels `M[ν_{n₀,k}]` increase with `k`, so they stabilize from some level `K` on.
  obtain ⟨K, hK⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
    ⟨fun k ↦ Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ k : O⟦X⟧), fun _ _ hkl ↦
      Submodule.torsionBy_le_torsionBy_of_dvd _ _ (map_dvd Polynomial.coeToPowerSeries.ringHom
        (growthTransition_dvd_growthTransition n₀ hkl))⟩
  replace hK : ∀ k, K ≤ k → Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ k : O⟦X⟧) =
      Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ K : O⟦X⟧) := fun k hk ↦ (hK k hk).symm
  obtain ⟨K', hK'⟩ := eventually_atTop.mp hfin
  -- Fix a base level `a` past `K`, `K'`, `n₀` and `λ e`.
  set a := max (max K K') (max n₀ (lambdaInvariant O M * e + 1))
  have hfa := hK' a (by omega)
  -- `M[ν_{n₀,a}]` and `O ⧸ Res(F_M, ν_{n₀,a})` are finite, of orders powers `q ^ t` and `q ^ v`;
  -- the residue field of `O⟦X⟧` is that of `O`.
  have := finite_torsionBy_of_finite_quotSMulTop (monic_growthTransition n₀ a) hfa
  have ht := natCard_eq_pow_length_toNat (A := O⟦X⟧)
    (M := Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ a : O⟦X⟧))
  rw [Nat.card_congr TauCeti.PowerSeries.residueFieldEquiv.toEquiv] at ht
  have := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr (resultant_charPoly_ne_zero_of_finite_quotSMulTop hfa))
  have hv := natCard_eq_pow_length_toNat (A := O)
    (M := O ⧸ Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ a)})
  set t := (Module.length O⟦X⟧
    (Submodule.torsionBy O⟦X⟧ M (growthTransition p O n₀ a : O⟦X⟧))).toNat
  set v := (Module.length O
    (O ⧸ Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ a)})).toNat
  set c := (∏ j ∈ Finset.range n₀, growthTransition p O j j).natDegree
  refine ⟨t + v - muInvariant O M * c - e * lambdaInvariant O M * a, ?_⟩
  filter_upwards [eventually_ge_atTop a] with k hk
  -- Compare the exponent of `q` at level `k` with `μ pᵏ + e λ k`, using `deg ν_{n₀,k} = pᵏ - c`.
  have hdeg' : ((growthTransition p O n₀ k).natDegree : ℤ) = (p : ℤ) ^ k - c := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast natDegree_prod_range_add_natDegree_growthTransition (by omega)
  have hexp : ((t + muInvariant O M * (growthTransition p O n₀ k).natDegree + v +
      e * lambdaInvariant O M * (k - a) : ℕ) : ℤ) =
      ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℕ) : ℤ) +
        (t + v - muInvariant O M * c - e * lambdaInvariant O M * a) := by
    push_cast [hk, hdeg']
    ring
  rw [natCard_quotSMulTop_growthTransition_eq_mul he hpe (by omega) (by omega) hk (hK' k (by omega))
    ((hK k (by omega)).trans (hK a (by omega)).symm), ht, hv, ← hexp, zpow_natCast]
  push_cast
  ring

end Growth

/-- **Iwasawa's growth formula over `ℤ_p`.** Let `M` be a finitely generated `ℤ_p⟦X⟧`-module with
Iwasawa invariants `μ = μ(M)` and `λ = λ(M)`. If the quotients `M ⧸ ν_{n₀,n} M` by the transition
polynomials are finite for all large `n`, then there is an integer `ν` such that
`#(M ⧸ ν_{n₀,n} M) = p ^ (μ pⁿ + λ n + ν)` for all large `n`. -/
theorem exists_eventually_natCard_quotSMulTop_growthTransition_eq_padicInt (p : ℕ)
    [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (n₀ : ℕ)
    (hfin : ∀ᶠ k in atTop, Finite (QuotSMulTop (growthTransition p ℤ_[p] n₀ k : ℤ_[p]⟦X⟧) M)) :
    ∃ ν : ℤ, ∀ᶠ k in atTop,
      (Nat.card (QuotSMulTop (growthTransition p ℤ_[p] n₀ k : ℤ_[p]⟦X⟧) M) : ℚ) =
        (p : ℚ) ^ (((muInvariant ℤ_[p] M * p ^ k + lambdaInvariant ℤ_[p] M * k : ℕ) : ℤ) + ν) := by
  have : Finite (ResidueField ℤ_[p]) := .of_equiv _ PadicInt.residueField.symm.toEquiv
  have hq : Nat.card (ResidueField ℤ_[p]) = p :=
    (Nat.card_congr PadicInt.residueField.toEquiv).trans (Nat.card_zmod p)
  simpa [hq] using exists_eventually_natCard_quotSMulTop_growthTransition_eq (M := M) one_pos
    (by rw [pow_one, PadicInt.maximalIdeal_eq_span_p]) n₀ hfin

end TauCeti.Iwasawa
