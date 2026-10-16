/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Multiplicativity of ideal Dirichlet convolution

Dirichlet convolution preserves multiplicativity on relatively prime nonzero ideals.
Factorizations of a relatively prime product are obtained uniquely by multiplying
factorizations of its two factors. This supplies the multiplicativity needed to form
products of ideal Euler products.

## References

* The factorization reindexing follows Mathlib’s `ArithmeticFunction.IsMultiplicative.mul`,
  with divisor decomposition in the ideal monoid replacing the natural-number gcd argument.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti.IdealArithmeticFunction

open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem divisorsAntidiagonal_mul_map_injective
    {A B : (Ideal (𝓞 K))⁰} (hAB : IsRelPrime (A : Ideal (𝓞 K)) B)
    (p p' : ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) ×
      ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰))
    (hp : p ∈ (TauCeti.Ideal.divisorsAntidiagonal A).product
      (TauCeti.Ideal.divisorsAntidiagonal B))
    (hp' : p' ∈ (TauCeti.Ideal.divisorsAntidiagonal A).product
      (TauCeti.Ideal.divisorsAntidiagonal B))
    (heq : (p.1.1 * p.2.1, p.1.2 * p.2.2) = (p'.1.1 * p'.2.1, p'.1.2 * p'.2.2)) :
    p = p' := by
  have hpA := (Finset.mem_product.mp hp).1
  have hpB := (Finset.mem_product.mp hp).2
  have hpA' := (Finset.mem_product.mp hp').1
  have hpB' := (Finset.mem_product.mp hp').2
  have hab : p.1.1 * p.2.1 = p'.1.1 * p'.2.1 := congrArg Prod.fst heq
  have hab_val : (p.1.1 : Ideal (𝓞 K)) * p.2.1 = (p'.1.1 : Ideal (𝓞 K)) * p'.2.1 :=
    congrArg Subtype.val hab
  have ha : p.1.1 = p'.1.1 := by
    apply Subtype.ext
    apply le_antisymm <;> apply _root_.Ideal.dvd_iff_le.mp
    · exact ((hAB.of_dvd_left
        (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hpA')).of_dvd_right
        (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hpB)).dvd_of_dvd_mul_right
        (hab_val ▸ dvd_mul_right _ _)
    · exact ((hAB.of_dvd_left
        (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hpA)).of_dvd_right
        (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hpB')).dvd_of_dvd_mul_right
        (hab_val.symm ▸ dvd_mul_right _ _)
  have hb : p.2.1 = p'.2.1 := by
    apply Subtype.ext
    apply mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero p'.1.1)
    exact congrArg Subtype.val (ha ▸ hab)
  have hc : p.1.2 = p'.1.2 := by
    apply Subtype.ext
    apply mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero p'.1.1)
    exact congrArg Subtype.val ((ha ▸ (TauCeti.Ideal.mem_divisorsAntidiagonal.mp hpA)).trans
      (TauCeti.Ideal.mem_divisorsAntidiagonal.mp hpA').symm)
  have hd : p.2.2 = p'.2.2 := by
    apply Subtype.ext
    apply mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero p'.2.1)
    exact congrArg Subtype.val ((hb ▸ (TauCeti.Ideal.mem_divisorsAntidiagonal.mp hpB)).trans
      (TauCeti.Ideal.mem_divisorsAntidiagonal.mp hpB').symm)
  exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd)

private theorem divisorsAntidiagonal_mul_map_surjective
    {A B : (Ideal (𝓞 K))⁰} {q : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰}
    (hq : q ∈ TauCeti.Ideal.divisorsAntidiagonal (A * B)) :
    ∃ p ∈ (TauCeti.Ideal.divisorsAntidiagonal A).product
        (TauCeti.Ideal.divisorsAntidiagonal B),
      (p.1.1 * p.2.1, p.1.2 * p.2.2) = q := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_dvd_and_dvd_of_dvd_mul
    (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hq)
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  have hA : a * c ≠ 0 := hc ▸ nonZeroDivisors.coe_ne_zero A
  have hB : b * d ≠ 0 := hd ▸ nonZeroDivisors.coe_ne_zero B
  let a₀ : (Ideal (𝓞 K))⁰ := ⟨a, mem_nonZeroDivisors_of_ne_zero (left_ne_zero_of_mul hA)⟩
  let b₀ : (Ideal (𝓞 K))⁰ := ⟨b, mem_nonZeroDivisors_of_ne_zero (left_ne_zero_of_mul hB)⟩
  let c₀ : (Ideal (𝓞 K))⁰ := ⟨c, mem_nonZeroDivisors_of_ne_zero (right_ne_zero_of_mul hA)⟩
  let d₀ : (Ideal (𝓞 K))⁰ := ⟨d, mem_nonZeroDivisors_of_ne_zero (right_ne_zero_of_mul hB)⟩
  have hac : a₀ * c₀ = A := Subtype.ext hc.symm
  have hbd : b₀ * d₀ = B := Subtype.ext hd.symm
  have hab₀ : a₀ * b₀ = q.1 := Subtype.ext hab.symm
  have hcd : c₀ * d₀ = q.2 := by
    apply Subtype.ext
    apply mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero (a₀ * b₀))
    have h : (a₀ * b₀) * (c₀ * d₀) = (a₀ * b₀) * q.2 := by
      rw [mul_mul_mul_comm, hac, hbd, hab₀, TauCeti.Ideal.mem_divisorsAntidiagonal.mp hq]
    exact congrArg Subtype.val h
  exact ⟨((a₀, c₀), (b₀, d₀)), by simp [hac, hbd], by simp [hab₀, hcd]⟩

/-- Dirichlet convolution of two coprime-multiplicative ideal arithmetic functions is
coprime-multiplicative. -/
theorem IsMultiplicative.convolution {f g : IdealArithmeticFunction K}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    (convolution f g).IsMultiplicative := by
  refine ⟨by simp [hf.map_one, hg.map_one], fun {A B} hAB ↦ ?_⟩
  rw [convolution_apply, convolution_apply, convolution_apply, Finset.sum_mul_sum]
  rw [← Finset.sum_product (f := fun p : ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) ×
    ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) ↦ f p.1.1 * g p.1.2 * (f p.2.1 * g p.2.2))]
  symm
  refine Finset.sum_nbij (fun p ↦ (p.1.1 * p.2.1, p.1.2 * p.2.2)) ?_
    (fun p hp p' hp' ↦ divisorsAntidiagonal_mul_map_injective hAB p p' hp hp')
    (fun q hq ↦ divisorsAntidiagonal_mul_map_surjective hq) ?_
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [TauCeti.Ideal.mem_divisorsAntidiagonal, mul_mul_mul_comm,
      TauCeti.Ideal.mem_divisorsAntidiagonal.mp hp.1,
      TauCeti.Ideal.mem_divisorsAntidiagonal.mp hp.2]
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [hf.map_mul_of_isRelPrime <| (hAB.of_dvd_left
      (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hp.1)).of_dvd_right
      (TauCeti.Ideal.fst_dvd_of_mem_divisorsAntidiagonal hp.2),
      hg.map_mul_of_isRelPrime <| (hAB.of_dvd_left
      (TauCeti.Ideal.snd_dvd_of_mem_divisorsAntidiagonal hp.1)).of_dvd_right
      (TauCeti.Ideal.snd_dvd_of_mem_divisorsAntidiagonal hp.2)]
    ring

end TauCeti.IdealArithmeticFunction
