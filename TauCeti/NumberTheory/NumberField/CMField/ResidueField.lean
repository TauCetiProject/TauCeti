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
import TauCeti.RingTheory.RootsOfUnity.FourthAndSixth
import TauCeti.RingTheory.RootsOfUnity.Seventh

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
nontrivially on `𝓞 K ⧸ w`. As a Frobenius at a prime not containing `4` it also sends the fourth
root of unity `i` to `i ^ q` (`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`), so `i ^ q = -i = i ^ 3`
and, as `i` has order four, `q ≡ 3 (mod 4)`. Both elements exist when `K` contains a primitive
fourth and a primitive seventh root of unity `ζ₇`, with `α = -(ζ₇ + ζ₇ ^ 2 + ζ₇ ^ 4)`
(`NumberField.IsCMField.add_eq_one_and_mul_eq_two_of_isPrimitiveRoot_seven`), for instance when
`K` contains a primitive `5040`-th root of unity. Then every residue field of `K` at a prime fixed
by conjugation has cardinality `r ^ 2` with `r ≡ 3 (mod 4)`
(`NumberField.IsCMField.exists_natCard_quotient_eq_sq_and_mod_four_eq_three`).

## Main results

* `NumberField.IsCMField.isArithFrobAt_ringOfIntegersComplexConj`: complex conjugation is an
  arithmetic Frobenius at every maximal ideal of `𝓞 K` that it fixes.
* `NumberField.IsCMField.natCard_quotient_eq_sq`: if conjugation fixes `w` and acts nontrivially
  modulo `w`, then `#(𝓞 K ⧸ w) = #(𝓞 K⁺ ⧸ w ∩ 𝓞 K⁺) ^ 2`.
* `Ideal.mul_conj_notMem_of_add_conj_eq_one`: no prime fixed by conjugation contains the
  relative norm of an algebraic integer of relative trace `1`.
* `NumberField.IsCMField.add_eq_one_and_mul_eq_two_of_isPrimitiveRoot_seven`: for a primitive
  seventh root of unity `η`, the Gauss period `α = -(η + η ^ 2 + η ^ 4)` has `α + conj α = 1` and
  `α * conj α = 2`.
* `Ideal.natCast_card_quotient_under_eq_neg_one`: if `K` contains a primitive `n`-th root of
  unity and `n ∉ w`, then `#(𝓞 K⁺ ⧸ w ∩ 𝓞 K⁺) ≡ -1 (mod n)`.
* `NumberField.IsCMField.natCard_quotient_under_mod_four_eq_three`: if `i ^ 2 = -1` and `2 ∉ w`,
  then `#(𝓞 K⁺ ⧸ w ∩ 𝓞 K⁺) ≡ 3 (mod 4)`.
* `NumberField.IsCMField.two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot`: if `K` contains a
  primitive fourth and a primitive seventh root of unity, a prime fixed by conjugation does not lie
  over `2`, and conjugation acts nontrivially modulo it.
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

open NumberField IsCMField

namespace Ideal

/-- The norm of an algebraic integer of relative trace `1` is outside every prime of a CM
field fixed by complex conjugation. -/
theorem mul_conj_notMem_of_add_conj_eq_one
    {K : Type*} [Field K] [CharZero K] [IsCMField K] [Algebra.IsIntegral ℚ K]
    (w : Ideal (𝓞 K)) [w.IsPrime] (hw : w.map (ringOfIntegersComplexConj K) = w) {α : 𝓞 K}
    (hα : α + ringOfIntegersComplexConj K α = 1) : α * ringOfIntegersComplexConj K α ∉ w := by
  intro h
  have hconj {x : 𝓞 K} (hx : x ∈ w) : ringOfIntegersComplexConj K x ∈ w :=
    hw ▸ Ideal.mem_map_of_mem _ hx
  have ha : α ∈ w := (Ideal.IsPrime.mem_or_mem ‹_› h).elim id fun hc ↦ by simpa using hconj hc
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr (hα ▸ add_mem ha (hconj ha)))

end Ideal

namespace NumberField.IsCMField

section General

variable {K : Type*} [Field K] [CharZero K] [IsCMField K] [Algebra.IsIntegral ℚ K]

/-- **The Gauss period of a seventh root of unity has trace `1` and norm `2` over `K⁺`.** If `η`
is a primitive seventh root of unity in `𝓞 K`, then `α = -(η + η ^ 2 + η ^ 4)` satisfies
`α + conj α = 1` and `α * conj α = 2`. -/
theorem add_eq_one_and_mul_eq_two_of_isPrimitiveRoot_seven {η : 𝓞 K} (hη : IsPrimitiveRoot η 7) :
    -(η + η ^ 2 + η ^ 4) + ringOfIntegersComplexConj K (-(η + η ^ 2 + η ^ 4)) = 1 ∧
      -(η + η ^ 2 + η ^ 4) * ringOfIntegersComplexConj K (-(η + η ^ 2 + η ^ 4)) = 2 := by
  -- `conj η = η⁻¹ = η ^ 6`, so conjugation sends `η ^ k` to `η ^ (6 * k % 7)`
  have hc : ringOfIntegersComplexConj K η = η ^ 6 := by
    linear_combination (-ringOfIntegersComplexConj K η) * hη.pow_eq_one +
      η ^ 6 * mul_ringOfIntegersComplexConj_eq_one_of_pow_eq_one (by norm_num) hη.pow_eq_one
  have hconj : ringOfIntegersComplexConj K (-(η + η ^ 2 + η ^ 4)) = -(η ^ 6 + η ^ 5 + η ^ 3) := by
    rw [map_neg, map_add, map_add, map_pow, map_pow, hc, ← pow_mul, ← pow_mul,
      pow_eq_pow_mod (6 * 2) hη.pow_eq_one, pow_eq_pow_mod (6 * 4) hη.pow_eq_one]
  -- the trace is `-(η + ⋯ + η ^ 6) = 1`
  have hadd : -(η + η ^ 2 + η ^ 4) + ringOfIntegersComplexConj K (-(η + η ^ 2 + η ^ 4)) = 1 := by
    rw [hconj]
    linear_combination -hη.geom_sum_eq_zero_of_seven
  -- and `(1 - 2 * α) ^ 2 = -7` gives `4 * α * conj α = 4 * α * (1 - α) = 8`
  refine ⟨hadd, mul_left_cancel₀ (by norm_num : (4 : 𝓞 K) ≠ 0) ?_⟩
  linear_combination 4 * -(η + η ^ 2 + η ^ 4) * hadd -
    hη.one_add_two_mul_add_sq_add_pow_four_sq_of_seven

/-- **The primes fixed by conjugation of a CM field with fourth and seventh roots of unity.** Let
`K` be a CM field containing a primitive fourth and a primitive seventh root of unity, for instance
a CM field containing a primitive `5040`-th root of unity. Then every prime `w` of `𝓞 K` fixed by
complex conjugation does not lie over `2`, and conjugation acts nontrivially on `𝓞 K ⧸ w`: it moves
the fourth root of unity `i` modulo `w`, since `conj i - i = -2 i`. -/
theorem two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot {ζ₄ ζ₇ : K}
    (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7) (w : Ideal (𝓞 K)) [w.IsPrime]
    (hw : w.map (ringOfIntegersComplexConj K) = w) :
    (2 : 𝓞 K) ∉ w ∧ ∃ x, ringOfIntegersComplexConj K x - x ∉ w := by
  -- the roots of unity lie in `𝓞 K`
  obtain ⟨i, rfl⟩ : ∃ i : 𝓞 K, (i : K) = ζ₄ := ⟨⟨ζ₄, h₄.isIntegral (by norm_num)⟩, rfl⟩
  obtain ⟨η, rfl⟩ : ∃ η : 𝓞 K, (η : K) = ζ₇ := ⟨⟨ζ₇, h₇.isIntegral (by norm_num)⟩, rfl⟩
  replace h₄ := h₄.of_map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  replace h₇ := h₇.of_map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hi : i ^ 2 = -1 := (h₄.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right
  -- the Gauss period `α = -(η + η ^ 2 + η ^ 4)` has `α + conj α = 1` and `α * conj α = 2`
  obtain ⟨hadd, hmul⟩ := add_eq_one_and_mul_eq_two_of_isPrimitiveRoot_seven h₇
  have h2 : (2 : 𝓞 K) ∉ w := hmul ▸ w.mul_conj_notMem_of_add_conj_eq_one hw hadd
  -- conjugation moves `i` modulo `w`
  refine ⟨h2, i, ?_⟩
  have hneg : -i - i = -(2 * i) := by ring
  rw [ringOfIntegersComplexConj_eq_neg_of_sq_eq_neg_one hi, hneg, neg_mem_iff]
  refine fun h ↦ (Ideal.IsPrime.mem_or_mem inferInstance h).elim h2 fun hiw ↦ ?_
  refine Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one w).mpr ?_)
  convert w.mul_mem_left (-i) hiw using 1
  linear_combination hi

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

/-- If a CM field contains a primitive `n`-th root of unity and a conjugation-fixed maximal
ideal does not contain `n`, the residue cardinality of the prime below in the maximal real
subfield is `-1` modulo `n`. -/
theorem _root_.Ideal.natCast_card_quotient_under_eq_neg_one (w : Ideal (𝓞 K)) [w.IsMaximal]
    (hw : w.map (ringOfIntegersComplexConj K) = w) {n : ℕ} {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ζ n) (hn : (n : 𝓞 K) ∉ w) :
    (Nat.card (𝓞 K⁺ ⧸ w.under (𝓞 K⁺)) : ZMod n) = -1 := by
  have hn₀ : n ≠ 0 := fun h ↦ hn (by simp [h])
  have hnpos := Nat.pos_of_ne_zero hn₀
  have hconj := mul_ringOfIntegersComplexConj_eq_one_of_pow_eq_one hn₀ hζ.pow_eq_one
  have he : ringOfIntegersComplexConj K ζ = ζ ^ (n - 1) := by
    have hlast : ζ * ζ ^ (n - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hnpos, hζ.pow_eq_one]
    calc
      ringOfIntegersComplexConj K ζ = (ζ * ζ ^ (n - 1)) * ringOfIntegersComplexConj K ζ := by
        rw [hlast, one_mul]
      _ = ζ ^ (n - 1) := by rw [mul_comm ζ, mul_assoc, hconj, mul_one]
  have hpow := (isArithFrobAt_ringOfIntegersComplexConj w hw).apply_of_pow_eq_one hζ.pow_eq_one hn
  rw [AlgEquiv.coe_toAlgHom, he, (hζ.isOfFinOrder hn₀).pow_inj_mod, ← hζ.eq_orderOf] at hpow
  calc
    _ = ((n - 1 : ℕ) : ZMod n) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpow.symm
    _ = -1 := by rw [Nat.cast_sub hnpos]; simp

/-- **The residue field below a prime fixed by conjugation has `q ≡ 3 (mod 4)` elements** when
`K` contains a square root `i` of `-1` and the prime does not lie over `2`: if `w` is a maximal
ideal of `𝓞 K` with `conj w = w` and `2 ∉ w`, the residue field of `𝓞 K⁺` below `w` has `q`
elements with `q ≡ 3 (mod 4)`. -/
theorem natCard_quotient_under_mod_four_eq_three (w : Ideal (𝓞 K)) [w.IsMaximal]
    (hw : w.map (ringOfIntegersComplexConj K) = w) {i : 𝓞 K} (hi : i ^ 2 = -1)
    (h2 : (2 : 𝓞 K) ∉ w) : Nat.card (𝓞 K⁺ ⧸ w.under (𝓞 K⁺)) % 4 = 3 := by
  -- `i` is a primitive fourth root of unity, and `4 = 2 * 2 ∉ w`
  have hi4 : IsPrimitiveRoot i 4 :=
    (TauCeti.isPrimitiveRoot_four_of_sq_eq_neg_one (θ := (i : K)) (by exact_mod_cast hi))
      |>.of_map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have h4 : ((4 : ℕ) : 𝓞 K) ∉ w := fun h ↦
    h2 (Ideal.IsPrime.mem_of_pow_mem inferInstance 2 (by norm_num at h ⊢; exact h))
  have h := w.natCast_card_quotient_under_eq_neg_one hw hi4 h4
  have hthree : ((3 : ℕ) : ZMod 4) = -1 := by decide
  rwa [← hthree, ZMod.natCast_eq_natCast_iff] at h

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
  obtain ⟨h2, hne⟩ := two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w hw
  -- the fourth root of unity lies in `𝓞 K` and squares to `-1`
  obtain ⟨i, rfl⟩ : ∃ i : 𝓞 K, (i : K) = ζ₄ := ⟨⟨ζ₄, h₄.isIntegral (by norm_num)⟩, rfl⟩
  replace h₄ := h₄.of_map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hi : i ^ 2 = -1 := (h₄.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right
  exact ⟨_, natCard_quotient_eq_sq w hw hne, natCard_quotient_under_mod_four_eq_three w hw hi h2⟩

end NumberField.IsCMField
