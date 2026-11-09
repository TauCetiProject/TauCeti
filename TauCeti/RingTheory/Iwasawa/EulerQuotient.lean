/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.Elementary
public import TauCeti.RingTheory.Iwasawa.LambdaInvariant
public import TauCeti.RingTheory.Iwasawa.MuInvariant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.QuotSMulTop

import Mathlib.Algebra.Regular.Pi
import Mathlib.Algebra.Regular.Prod
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.Algebra.Module.Torsion.EulerQuotient
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Iwasawa.VerticalBlock
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The Euler quotient of an Iwasawa module at finite level

Let `O` be a discrete valuation ring, complete for its maximal ideal, with finite residue field of
cardinality `q`, let `Λ = O⟦X⟧`, and let `M` be a finitely generated `Λ`-module with `μ`-invariant
`μ = μ(M)` and characteristic polynomial `F_M` (`TauCeti.Iwasawa.muInvariant`,
`TauCeti.Iwasawa.charPoly`). For a polynomial `G` distinguished at the maximal ideal of `O`, write
`M[G]` and `M ⧸ GM` for the kernel and the cokernel of multiplication by `G` on `M`. This file
proves that if `M ⧸ GM` is finite, then `M[G]` is finite, the resultant `Res(F_M, G)` is nonzero,
and the Euler quotient is

`#(M ⧸ GM) / #M[G] = q ^ (μ deg G) · #(O ⧸ Res(F_M, G))`.

For `G = ω_n = (1 + X) ^ pⁿ - 1`, where `p` is the residue characteristic, `M ⧸ ω_n M` and
`M[ω_n]` are the coinvariants and the invariants of the subgroup of index `pⁿ` of `Γ ≅ ℤ_p` acting
on `M`, and the formula reads `#M_{Γ_n} / #M^{Γ_n} = q ^ (μ pⁿ) · #(O ⧸ Res(F_M, ω_n))`. It is an
identity at each finite level and depends on `F_M`, not only on `μ` and the `λ`-invariant. No
assumption on the characteristic of `O` is needed.

The proof passes through a pseudo-isomorphism onto an elementary module
`Λʳ × ∏ᵢ Λ ⧸ (ϖ ^ mᵢ) × ∏ⱼ Λ ⧸ (Fⱼ ^ nⱼ)` (`TauCeti.Iwasawa.exists_isPseudoIsomorphism_elementary`),
which preserves the Euler quotient and the finiteness of `M ⧸ GM` and of `M[G]`
(`TauCeti.Iwasawa.IsPseudoIsomorphism.natCard_quotSMulTop_div_natCard_torsionBy_eq`), and computes
the Euler quotient block by block:

* `G` acts injectively on a vertical block `Λ ⧸ (ϖ ^ m)`, with cokernel of order `q ^ (m deg G)`
  (`TauCeti.Iwasawa.natCard_quotSMulTop_quotient_span_C_pow`);
* on a horizontal block `Λ ⧸ (Fⱼ ^ nⱼ)`, free of rank `nⱼ deg Fⱼ` over `O`, the determinant of
  multiplication by `G` is the resultant `Res(Fⱼ ^ nⱼ, G)`; the cokernel is finite exactly when this
  resultant is nonzero, and then `G` acts injectively with cokernel of order
  `#(O ⧸ Res(Fⱼ ^ nⱼ, G))`;
* the free part `Λʳ` has infinite cokernel unless `r = 0` or `G = 1`.

The resultant is multiplicative in its monic first argument
(`Polynomial.resultant_prod_left_of_monic`) and the order of a quotient of the Dedekind domain `O`
is multiplicative in the ideal, so the horizontal blocks together contribute
`#(O ⧸ Res(∏ⱼ Fⱼ ^ nⱼ, G)) = #(O ⧸ Res(F_M, G))`.

## Main results

* `TauCeti.Iwasawa.torsionBy_elementary_eq_bot`,
  `TauCeti.Iwasawa.resultant_ne_zero_of_finite_quotSMulTop_elementary` and
  `TauCeti.Iwasawa.natCard_quotSMulTop_elementary`: the kernel and the cokernel of multiplication
  by `G` on an elementary module.
* `TauCeti.Iwasawa.resultant_charPoly_ne_zero_of_finite_quotSMulTop`: if `M ⧸ GM` is finite, then
  `Res(F_M, G) ≠ 0`.
* `TauCeti.Iwasawa.finite_torsionBy_of_finite_quotSMulTop`: if `M ⧸ GM` is finite, then so is
  `M[G]`.
* `TauCeti.Iwasawa.natCard_quotSMulTop_div_natCard_torsionBy`: the Euler quotient
  `#(M ⧸ GM) / #M[G] = q ^ (μ deg G) · #(O ⧸ Res(F_M, G))`.
* `TauCeti.Iwasawa.natCard_quotSMulTop_one_add_X_pow_sub_one_div_natCard_torsionBy`: the case
  `G = ω_n`, `#(M ⧸ ω_n M) / #M[ω_n] = q ^ (μ pⁿ) · #(O ⧸ Res(F_M, ω_n))`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, (5.3.11)–(5.3.16).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public section

open IsLocalRing PowerSeries Submodule
open scoped Pointwise Polynomial PowerSeries

namespace TauCeti.Iwasawa

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] {G : O[X]}

section Elementary

/-- **The kernel of a distinguished polynomial on an elementary module.** Let `G` be a polynomial
distinguished at the maximal ideal, and let the `Fⱼ` be distinguished with
`Res(∏ⱼ Fⱼ ^ nⱼ, G) ≠ 0`. Then `G` acts injectively on the elementary module
`O⟦X⟧ʳ × ∏ᵢ O⟦X⟧ ⧸ (ϖ ^ mᵢ) × ∏ⱼ O⟦X⟧ ⧸ (Fⱼ ^ nⱼ)`. -/
theorem torsionBy_elementary_eq_bot {ϖ : O} (hϖ : Irreducible ϖ) (r : ℕ) {a b : ℕ} (m : Fin a → ℕ)
    {F : Fin b → O[X]} (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (n : Fin b → ℕ)
    (hG : G.IsDistinguishedAt (maximalIdeal O)) (hres : (∏ j, F j ^ n j).resultant G ≠ 0) :
    torsionBy O⟦X⟧ (Elementary O ϖ r m F n) (G : O⟦X⟧) = ⊥ := by
  rw [Polynomial.resultant_prod_left_of_monic _ fun j _ ↦ (hF j).monic.pow _,
    Finset.prod_ne_zero_iff] at hres
  rw [← isSMulRegular_iff_torsionBy_eq_bot, Prod.isSMulRegular_iff, Prod.isSMulRegular_iff,
    Pi.isSMulRegular_iff, Pi.isSMulRegular_iff, Pi.isSMulRegular_iff]
  refine ⟨fun _ ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
  · -- The free part: `O⟦X⟧` is a domain and `G ≠ 0`.
    refine (isRegular_iff_ne_zero.2 ?_).left.isSMulRegular
    exact (Polynomial.coe_eq_zero_iff).not.2 hG.monic.ne_zero
  · rw [isSMulRegular_iff_torsionBy_eq_bot]
    refine torsionBy_quotient_span_C_pow_eq_bot hϖ.prime ?_ (m i)
    -- The reduction of the monic polynomial `G` to the residue field is nonzero.
    rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]
    exact (hG.monic.map _).ne_zero
  · have H := ((hF j).pow (n j)).isWeierstrassFactorizationAt
    rw [isSMulRegular_iff_torsionBy_eq_bot, H.torsionBy_eq_bot_iff, H.norm_mk_coe_eq_resultant]
    exact hres j (Finset.mem_univ j)

/-- **A finite cokernel on an elementary module has nonzero resultant.** Let `O` have finite residue
field and let the `Fⱼ` be distinguished. If `G` has finite cokernel on the elementary module
`O⟦X⟧ʳ × ∏ᵢ O⟦X⟧ ⧸ (ϖ ^ mᵢ) × ∏ⱼ O⟦X⟧ ⧸ (Fⱼ ^ nⱼ)`, then `Res(∏ⱼ Fⱼ ^ nⱼ, G) ≠ 0`. -/
theorem resultant_ne_zero_of_finite_quotSMulTop_elementary [Finite (ResidueField O)] {ϖ : O}
    (r : ℕ) {a b : ℕ} (m : Fin a → ℕ) {F : Fin b → O[X]}
    (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (n : Fin b → ℕ)
    (hfin : Finite (QuotSMulTop (G : O⟦X⟧) (Elementary O ϖ r m F n))) :
    (∏ j, F j ^ n j).resultant G ≠ 0 := by
  rw [Polynomial.resultant_prod_left_of_monic _ fun j _ ↦ (hF j).monic.pow _,
    Finset.prod_ne_zero_iff]
  intro j _
  have H := ((hF j).pow (n j)).isWeierstrassFactorizationAt
  rw [← H.norm_mk_coe_eq_resultant, ← H.finite_quotSMulTop_iff]
  -- The cokernel on the horizontal block `j` is a quotient of the cokernel on the whole module.
  let π : Elementary O ϖ r m F n →ₗ[O⟦X⟧] O⟦X⟧ ⧸ Ideal.span {((F j ^ n j : O[X]) : O⟦X⟧)} :=
    (LinearMap.proj j).comp ((LinearMap.snd O⟦X⟧ _ _).comp (LinearMap.snd O⟦X⟧ _ _))
  have hsurj : Function.Surjective π := fun y ↦ ⟨(0, 0, Pi.single j y), by simp [π]⟩
  exact Finite.of_surjective _ (QuotSMulTop.map_surjective _ hsurj)

/-- **The cokernel of a distinguished polynomial on a torsion elementary module.** Let `G` be a
polynomial distinguished at the maximal ideal, and let the `Fⱼ` be distinguished with
`Res(∏ⱼ Fⱼ ^ nⱼ, G) ≠ 0`. Then the cokernel of `G` on
`∏ᵢ O⟦X⟧ ⧸ (ϖ ^ mᵢ) × ∏ⱼ O⟦X⟧ ⧸ (Fⱼ ^ nⱼ)` has `q ^ ((Σ mᵢ) deg G) · #(O ⧸ Res(∏ⱼ Fⱼ ^ nⱼ, G))`
elements, where `q` is the cardinality of the residue field. -/
theorem natCard_quotSMulTop_elementary {ϖ : O} (hϖ : Irreducible ϖ) {a b : ℕ} (m : Fin a → ℕ)
    {F : Fin b → O[X]} (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (n : Fin b → ℕ)
    (hG : G.IsDistinguishedAt (maximalIdeal O)) (hres : (∏ j, F j ^ n j).resultant G ≠ 0) :
    Nat.card (QuotSMulTop (G : O⟦X⟧) (Elementary O ϖ 0 m F n)) =
      Nat.card (ResidueField O) ^ ((∑ i, m i) * G.natDegree) *
        Nat.card (O ⧸ Ideal.span {(∏ j, F j ^ n j).resultant G}) := by
  rw [Polynomial.resultant_prod_left_of_monic _ fun j _ ↦ (hF j).monic.pow _] at hres ⊢
  rw [Finset.prod_ne_zero_iff] at hres
  rw [natCard_quotSMulTop_prod, natCard_quotSMulTop_prod, natCard_quotSMulTop_pi,
    natCard_quotSMulTop_pi, natCard_quotSMulTop_pi, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul]
  congr 1
  · rw [Finset.sum_mul, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ ↦
      natCard_quotSMulTop_quotient_span_C_pow hϖ hG.isWeierstrassFactorizationAt (m i)
  · -- The order of a quotient of the Dedekind domain `O` is multiplicative in the ideal.
    have hmul (s : Finset (Fin b)) : cardQuot (∏ j ∈ s, Ideal.span {(F j ^ n j).resultant G}) =
        ∏ j ∈ s, cardQuot (Ideal.span {(F j ^ n j).resultant G}) := by
      induction s using Finset.cons_induction with
      | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, cardQuot_top]
      | cons j s hj ih => rw [Finset.prod_cons, Finset.prod_cons, cardQuot_mul, ih]
    rw [← Ideal.prod_span_singleton, ← cardQuot_apply, hmul]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have H := ((hF j).pow (n j)).isWeierstrassFactorizationAt
    have hnorm := H.norm_mk_coe_eq_resultant G
    rw [H.natCard_quotSMulTop (hnorm ▸ hres j (Finset.mem_univ j)), hnorm, cardQuot_apply]

end Elementary

section Module

variable [Finite (ResidueField O)] {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
  [Module.Finite O⟦X⟧ M]

/-- **The resultant of the characteristic polynomial.** If `M ⧸ GM` is finite for a polynomial `G`,
then the resultant `Res(F_M, G)` of the characteristic polynomial of `M` and `G` is nonzero. -/
theorem resultant_charPoly_ne_zero_of_finite_quotSMulTop
    (hfin : Finite (QuotSMulTop (G : O⟦X⟧) M)) : (charPoly O M).resultant G ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  rw [hf.charPoly_eq_prod hϖ (fun j ↦ (hFn j).1) fun j ↦ (hFn j).2.1]
  exact resultant_ne_zero_of_finite_quotSMulTop_elementary r m (fun j ↦ (hFn j).1) n
    ((hf.finite_quotSMulTop_iff TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing _).1
      hfin)

/-- **Finite invariants.** Let `G` be a polynomial distinguished at the maximal ideal. If `M ⧸ GM`
is finite, then so is `M[G]`. -/
theorem finite_torsionBy_of_finite_quotSMulTop (hG : G.IsDistinguishedAt (maximalIdeal O))
    (hfin : Finite (QuotSMulTop (G : O⟦X⟧) M)) : Finite (torsionBy O⟦X⟧ M (G : O⟦X⟧)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  have hE := (hf.finite_quotSMulTop_iff hdim _).1 hfin
  rw [hf.finite_torsionBy_iff hdim, torsionBy_elementary_eq_bot hϖ r m (fun j ↦ (hFn j).1) n hG
    (resultant_ne_zero_of_finite_quotSMulTop_elementary r m (fun j ↦ (hFn j).1) n hE)]
  infer_instance

/-- **The Euler quotient of an Iwasawa module.** Let `O` be a discrete valuation ring, complete for
its maximal ideal, with finite residue field of cardinality `q`, let `M` be a finitely generated
`O⟦X⟧`-module, and let `G` be a polynomial distinguished at the maximal ideal. If `M ⧸ GM` is
finite, then `#(M ⧸ GM) / #M[G] = q ^ (μ(M) deg G) · #(O ⧸ Res(F_M, G))`, where `F_M` is the
characteristic polynomial of `M`. -/
theorem natCard_quotSMulTop_div_natCard_torsionBy (hG : G.IsDistinguishedAt (maximalIdeal O))
    (hfin : Finite (QuotSMulTop (G : O⟦X⟧) M)) :
    (Nat.card (QuotSMulTop (G : O⟦X⟧) M) : ℚ) / Nat.card (torsionBy O⟦X⟧ M (G : O⟦X⟧)) =
      Nat.card (ResidueField O) ^ (muInvariant O M * G.natDegree) *
        Nat.card (O ⧸ Ideal.span {(charPoly O M).resultant G}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  have hF (j : Fin b) := (hFn j).1
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  have hE := (hf.finite_quotSMulTop_iff hdim _).1 hfin
  have hres := resultant_ne_zero_of_finite_quotSMulTop_elementary r m hF n hE
  rw [hf.natCard_quotSMulTop_div_natCard_torsionBy_eq hdim,
    torsionBy_elementary_eq_bot hϖ r m hF n hG hres, hf.muInvariant_eq_sum hϖ fun j ↦ (hF j).monic,
    hf.charPoly_eq_prod hϖ hF fun j ↦ (hFn j).2.1]
  rcases Nat.eq_zero_or_pos G.natDegree with hd | hd
  · -- If `deg G = 0` then `G = 1`, which acts bijectively, and both sides are `1`.
    obtain rfl := Polynomial.eq_one_of_monic_natDegree_zero hG.monic hd
    have : Subsingleton (QuotSMulTop ((1 : O[X]) : O⟦X⟧) (Elementary O ϖ r m F n)) := by
      rw [Polynomial.coe_one, QuotSMulTop, one_smul, Submodule.Quotient.subsingleton_iff]
    simp
  · -- If `deg G > 0` then the free part `O⟦X⟧ʳ` has infinite cokernel, so `r = 0`.
    obtain rfl : r = 0 := by
      by_contra hr
      let i₀ : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
      let π : Elementary O ϖ r m F n →ₗ[O⟦X⟧] O⟦X⟧ :=
        (LinearMap.proj i₀).comp (LinearMap.fst O⟦X⟧ _ _)
      have hsurj : Function.Surjective π := fun y ↦ ⟨(Pi.single i₀ y, 0), by simp [π]⟩
      have hspan : (G : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ O⟦X⟧) = Ideal.span {(G : O⟦X⟧)} := by
        rw [← ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
      have := hG.isWeierstrassFactorizationAt.infinite_quotient hd
      rw [← hspan] at this
      exact not_finite_iff_infinite.2 this
        (Finite.of_surjective _ (QuotSMulTop.map_surjective _ hsurj))
    rw [natCard_quotSMulTop_elementary hϖ m hF n hG hres]
    simp

/-- **The Euler quotient at finite level.** Let `O` be a discrete valuation ring, complete for its
maximal ideal, whose residue field is finite of cardinality `q` and characteristic `p`, and let `M`
be a finitely generated `O⟦X⟧`-module. Write `ω_k = (1 + X) ^ pᵏ - 1`. If the coinvariants
`M ⧸ ω_k M` are finite, then `#(M ⧸ ω_k M) / #M[ω_k] = q ^ (μ(M) pᵏ) · #(O ⧸ Res(F_M, ω_k))`,
where `F_M` is the characteristic polynomial of `M`. -/
theorem natCard_quotSMulTop_one_add_X_pow_sub_one_div_natCard_torsionBy {p : ℕ} (hp : p.Prime)
    (hpO : (p : O) ∈ maximalIdeal O) (k : ℕ)
    (hfin : Finite (QuotSMulTop ((1 + X) ^ p ^ k - 1 : O⟦X⟧) M)) :
    (Nat.card (QuotSMulTop ((1 + X) ^ p ^ k - 1 : O⟦X⟧) M) : ℚ) /
        Nat.card (torsionBy O⟦X⟧ M ((1 + X) ^ p ^ k - 1 : O⟦X⟧)) =
      Nat.card (ResidueField O) ^ (muInvariant O M * p ^ k) *
        Nat.card (O ⧸ Ideal.span {(charPoly O M).resultant ((1 + Polynomial.X) ^ p ^ k - 1)}) := by
  have hcoe : (((1 + Polynomial.X) ^ p ^ k - 1 : O[X]) : O⟦X⟧) = (1 + X) ^ p ^ k - 1 := by
    simp
  rw [← hcoe] at hfin ⊢
  rw [natCard_quotSMulTop_div_natCard_torsionBy
      (TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one hp hpO k) hfin,
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one]

end Module

end TauCeti.Iwasawa
