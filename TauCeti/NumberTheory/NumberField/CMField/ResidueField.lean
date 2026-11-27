/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.RingTheory.Frobenius.Involution

/-!
# Residue fields of a CM field at the primes fixed by complex conjugation

Let `K` be a CM field with maximal real subfield `K⁺`, and `w` a maximal ideal of `𝓞 K` fixed by
complex conjugation, lying over the prime `v` of `𝓞 K⁺`, whose residue field has `q` elements.

Complex conjugation is an involution of `𝓞 K` over `𝓞 K⁺` with fixed ring `𝓞 K⁺`, so it acts on
the residue field `𝓞 K ⧸ w` as the `q`-power Frobenius: `conj x ≡ x ^ q` modulo `w`
(`NumberField.IsCMField.isArithFrobAt_ringOfIntegersComplexConj`). If it acts nontrivially there,
that is, if `w` is inert over `v`, then `𝓞 K ⧸ w` has `q ^ 2` elements
(`NumberField.IsCMField.natCard_quotient_eq_sq`).

If `K` contains a square root `i` of `-1` and an algebraic integer `α` with `α + conj α = 1` and
`α * conj α = 2`, such as `α = (1 + √-7) / 2`, the two facts combine into a congruence on `q`. A
prime fixed by conjugation does not lie over `2`, since otherwise it would contain `α` or
`conj α`, hence both, hence `α + conj α = 1`. So conjugation, which sends `i` to `-i`, acts
nontrivially on `𝓞 K ⧸ w`, and `i ^ q = -i` there. As `i` has order four in the residue field,
`q ≡ 3 (mod 4)`. Both elements exist when `K` contains a primitive fourth and a primitive seventh
root of unity `ζ₇`, with `α = -(ζ₇ + ζ₇ ^ 2 + ζ₇ ^ 4)`, for instance when `K` contains a primitive
`5040`-th root of unity. Then every residue field of `K` at a prime fixed by conjugation has
cardinality `r ^ 2` with `r ≡ 3 (mod 4)`
(`NumberField.IsCMField.exists_natCard_quotient_eq_sq_and_mod_four_eq_three`).

## Main results

* `NumberField.IsCMField.isArithFrobAt_ringOfIntegersComplexConj`: complex conjugation is an
  arithmetic Frobenius at every maximal ideal of `𝓞 K` that it fixes.
* `NumberField.IsCMField.natCard_quotient_eq_sq`: if conjugation fixes `w` and acts nontrivially
  modulo `w`, then `#(𝓞 K ⧸ w) = #(𝓞 K⁺ ⧸ w ∩ 𝓞 K⁺) ^ 2`.
* `NumberField.IsCMField.two_notMem_of_add_eq_one_of_mul_eq_two`: if `α + conj α = 1` and
  `α * conj α = 2`, no prime fixed by conjugation contains `2`.
* `NumberField.IsCMField.natCard_quotient_under_mod_four_eq_three`: if `i ^ 2 = -1` and `2 ∉ w`,
  then `#(𝓞 K⁺ ⧸ w ∩ 𝓞 K⁺) ≡ 3 (mod 4)`.
* `NumberField.IsCMField.exists_natCard_quotient_eq_sq_and_mod_four_eq_three`: if `K` contains a
  primitive fourth and a primitive seventh root of unity, the residue field at a prime fixed by
  conjugation has `r ^ 2` elements with `r ≡ 3 (mod 4)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 (decomposition and inertia groups, the
  Frobenius automorphism).
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2 (the Gauss period
  `ζ₇ + ζ₇ ^ 2 + ζ₇ ^ 4`).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/General/NumberTheory/FrobeniusOrbits.lean` (declaration
  `New.HasPrimitiveRoot5040.exists_sq_eq_q_of_inert`); Apache 2.0, Copyright 2026 Anthropic, PBC.
  The route (a prime fixed by conjugation does not lie over `2`, and conjugation induces an
  automorphism of order two of its residue field that moves `√-1`) follows the method of that
  declaration; the congruence `r ≡ 3 (mod 4)` is read off here from the action of conjugation as
  the `r`-power Frobenius.
-/

public section

open NumberField

namespace NumberField.IsCMField

section General

variable {K : Type*} [Field K] [CharZero K] [IsCMField K] [Algebra.IsIntegral ℚ K]

/-- **A prime fixed by conjugation does not lie over `2`** when `K` contains an algebraic integer
`α` of trace `α + conj α = 1` and norm `α * conj α = 2` over `K⁺`. -/
theorem two_notMem_of_add_eq_one_of_mul_eq_two (w : Ideal (𝓞 K)) [w.IsPrime]
    (hw : w.map (ringOfIntegersComplexConj K) = w) {α : 𝓞 K}
    (h₁ : α + ringOfIntegersComplexConj K α = 1) (h₂ : α * ringOfIntegersComplexConj K α = 2) :
    (2 : 𝓞 K) ∉ w := by
  intro h2
  have hconj {x : 𝓞 K} (hx : x ∈ w) : ringOfIntegersComplexConj K x ∈ w :=
    hw ▸ Ideal.mem_map_of_mem _ hx
  have hα : α ∈ w := by
    rcases Ideal.IsPrime.mem_or_mem ‹_› (h₂ ▸ h2) with h | h
    · exact h
    · simpa using hconj h
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr (h₁ ▸ add_mem hα (hconj hα)))

end General

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- **Complex conjugation is the Frobenius at the primes it fixes.** If `w` is a maximal ideal of
the ring of integers of a CM field `K` with `conj w = w`, then `conj x ≡ x ^ q` modulo `w` for
every `x ∈ 𝓞 K`, where `q` is the cardinality of the residue field of `𝓞 K⁺` below `w`. -/
theorem isArithFrobAt_ringOfIntegersComplexConj (w : Ideal (𝓞 K)) [w.IsMaximal]
    (hw : w.map (ringOfIntegersComplexConj K) = w) :
    (ringOfIntegersComplexConj K : 𝓞 K →ₐ[𝓞 K⁺] 𝓞 K).IsArithFrobAt w := by
  have : Finite (𝓞 K ⧸ w) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.IsMaximal.ne_bot_of_isIntegral_int w)
  have : Finite (𝓞 K⁺ ⧸ w.under (𝓞 K⁺)) := .of_injective _ Ideal.algebraMap_quotient_injective
  exact AlgHom.IsArithFrobAt.of_involutive (ringOfIntegersComplexConj_apply_apply K)
    (fun x ↦ (ringOfIntegersComplexConj_eq_self_iff K x).mp) (Ideal.map_le_iff_le_comap.mp hw.le)

/-- **The residue field of an inert prime of a CM field has square order.** If complex
conjugation fixes the maximal ideal `w` of `𝓞 K` and acts nontrivially on `𝓞 K ⧸ w`, then
`#(𝓞 K ⧸ w) = q ^ 2`, where `q` is the cardinality of the residue field of `𝓞 K⁺` below `w`. -/
theorem natCard_quotient_eq_sq (w : Ideal (𝓞 K)) [w.IsMaximal]
    (hw : w.map (ringOfIntegersComplexConj K) = w)
    (hne : ∃ x, ringOfIntegersComplexConj K x - x ∉ w) :
    Nat.card (𝓞 K ⧸ w) = Nat.card (𝓞 K⁺ ⧸ w.under (𝓞 K⁺)) ^ 2 :=
  (isArithFrobAt_ringOfIntegersComplexConj w hw).natCard_quotient_eq_sq
    (ringOfIntegersComplexConj_apply_apply K) hne

/-- **The residue field below a prime fixed by conjugation has `q ≡ 3 (mod 4)` elements** when
`K` contains a square root `i` of `-1` and the prime does not lie over `2`: if `w` is a maximal
ideal of `𝓞 K` with `conj w = w` and `2 ∉ w`, the residue field of `𝓞 K⁺` below `w` has `q`
elements with `q ≡ 3 (mod 4)`. -/
theorem natCard_quotient_under_mod_four_eq_three (w : Ideal (𝓞 K)) [w.IsMaximal]
    (hw : w.map (ringOfIntegersComplexConj K) = w) {i : 𝓞 K} (hi : i ^ 2 = -1)
    (h2 : (2 : 𝓞 K) ∉ w) : Nat.card (𝓞 K⁺ ⧸ w.under (𝓞 K⁺)) % 4 = 3 := by
  have h := (isArithFrobAt_ringOfIntegersComplexConj w hw).mk_apply i
  simp only [AlgEquiv.coe_toAlgHom, ringOfIntegersComplexConj_eq_neg_of_sq_eq_neg_one hi,
    map_neg] at h
  set θ := Ideal.Quotient.mk w i
  have hθ2 : θ ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
  -- `θ` has order four, since `-1 ≠ 1` in the residue field
  have horder : orderOf θ = 4 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) (fun h1 ↦ h2 ?_) ?_
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
      linear_combination hθ2 - h1
    · linear_combination (θ ^ 2 - 1) * hθ2
  have hfin : IsOfFinOrder θ := orderOf_pos_iff.mp (by rw [horder]; norm_num)
  have := hfin.pow_inj_mod.mp (show θ ^ Nat.card (𝓞 K⁺ ⧸ w.under (𝓞 K⁺)) = θ ^ 3 by
    linear_combination -h - θ * hθ2)
  rwa [horder] at this

/-- **The residue fields of a CM field with fourth and seventh roots of unity at the primes fixed
by conjugation.** Let `K` be a CM field containing a primitive fourth and a primitive seventh root
of unity, for instance a CM field containing a primitive `5040`-th root of unity. Then the residue
field `𝓞 K ⧸ w` at every maximal ideal `w` fixed by complex conjugation has `r ^ 2` elements for an
integer `r ≡ 3 (mod 4)`. One can take for `r` the cardinality of the residue field of `𝓞 K⁺`
below `w` (`natCard_quotient_eq_sq`, `natCard_quotient_under_mod_four_eq_three`). -/
theorem exists_natCard_quotient_eq_sq_and_mod_four_eq_three {ζ₄ ζ₇ : K}
    (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7) (w : Ideal (𝓞 K)) [w.IsMaximal]
    (hw : w.map (ringOfIntegersComplexConj K) = w) :
    ∃ r : ℕ, Nat.card (𝓞 K ⧸ w) = r ^ 2 ∧ r % 4 = 3 := by
  -- the roots of unity lie in `𝓞 K`
  obtain ⟨i, rfl⟩ : ∃ i : 𝓞 K, (i : K) = ζ₄ := ⟨⟨ζ₄, h₄.isIntegral (by norm_num)⟩, rfl⟩
  obtain ⟨η, rfl⟩ : ∃ η : 𝓞 K, (η : K) = ζ₇ := ⟨⟨ζ₇, h₇.isIntegral (by norm_num)⟩, rfl⟩
  replace h₄ := h₄.of_map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  replace h₇ := h₇.of_map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hi : i ^ 2 = -1 := (h₄.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right
  -- the Gauss period `α = -(η + η ^ 2 + η ^ 4)` has `α + conj α = 1` and `α * conj α = 2`
  have h7 := h₇.pow_eq_one
  have hsum := h₇.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hsum
  have hc : ringOfIntegersComplexConj K η = η ^ 6 := by
    linear_combination (-ringOfIntegersComplexConj K η) * h7 +
      η ^ 6 * mul_ringOfIntegersComplexConj_eq_one_of_pow_eq_one (by norm_num) h7
  have hc2 : ringOfIntegersComplexConj K η ^ 2 = η ^ 5 := by
    linear_combination (ringOfIntegersComplexConj K η + η ^ 6) * hc + η ^ 5 * h7
  have hc4 : ringOfIntegersComplexConj K η ^ 4 = η ^ 3 := by
    linear_combination (ringOfIntegersComplexConj K η ^ 2 + η ^ 5) * hc2 + η ^ 3 * h7
  have h2 : (2 : 𝓞 K) ∉ w := by
    refine two_notMem_of_add_eq_one_of_mul_eq_two w hw (α := -(η + η ^ 2 + η ^ 4)) ?_ ?_ <;>
      rw [map_neg, map_add, map_add, map_pow, map_pow, hc2, hc4, hc]
    · linear_combination -hsum
    · linear_combination hsum + (3 + η + η ^ 2 + η ^ 3) * h7
  -- conjugation moves `i` modulo `w`
  have hne : ringOfIntegersComplexConj K i - i ∉ w := by
    rw [ringOfIntegersComplexConj_eq_neg_of_sq_eq_neg_one hi, show -i - i = -(2 * i) by ring,
      neg_mem_iff]
    refine fun h ↦ (Ideal.IsPrime.mem_or_mem inferInstance h).elim h2 fun hiw ↦ ?_
    refine Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one w).mpr ?_)
    convert w.mul_mem_left (-i) hiw using 1
    linear_combination hi
  exact ⟨_, natCard_quotient_eq_sq w hw ⟨i, hne⟩,
    natCard_quotient_under_mod_four_eq_three w hw hi h2⟩

end NumberField.IsCMField
