/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.RepresentationTheory.Character.CyclotomicPolynomial
import TauCeti.RepresentationTheory.Character.QuotientInvariants
import TauCeti.RepresentationTheory.CharacterTable.CoefficientAction
import TauCeti.RingTheory.Polynomial.Cyclotomic.Specialization

/-!
# Divisibility of character pairings from coset orthogonality

For a finite normal subgroup of prime index, orthogonality of two virtual characters on a
coset forces divisibility of their restricted pairing by the index. Apply the coset average to
the product with the dual character. The average is the trace of the quotient action on
invariants, so the coset value and the dimension at the identity are evaluations of the same
integer polynomial at a root of unity and at `1`.
-/

public section

open Polynomial

namespace TauCeti

variable {k G : Type*} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] [Fintype N]

/-- For a virtual character, the mean over `gN` is the evaluation of an integer polynomial
at a primitive root of order `d` whenever `(gN)^d = 1`. The evaluation at `1` gives the mean over
`N`. -/
theorem exists_aeval_eq_coset_mean_and_eval_one_eq_subgroup_mean
    [Invertible (Fintype.card N : k)] {X : G → k} (hX : X ∈ virtualCharacters k G)
    {g : G} {d : ℕ} [NeZero d] {ζ : k} (hζ : IsPrimitiveRoot ζ d)
    (hg : QuotientGroup.mk' N g ^ d = 1) :
    ∃ P : ℤ[X], aeval ζ P = (Nat.card N : k)⁻¹ * ∑ n : N, X (g * n) ∧
      ((P.eval 1 : ℤ) : k) = (Nat.card N : k)⁻¹ * ∑ n : N, X n := by
  have h (V : FDRep k G) :
      ∃ P : ℤ[X], aeval ζ P = (Nat.card N : k)⁻¹ * ∑ n : N, V.character (g * n) ∧
        ((P.eval 1 : ℤ) : k) = (Nat.card N : k)⁻¹ * ∑ n : N, V.character n := by
    let ρ := Representation.quotientToInvariants V.ρ N
    obtain ⟨P, hP, h₁⟩ := Representation.exists_aeval_eq_character_and_eval_one_eq_finrank
      ρ hζ hg
    refine ⟨P, hP.trans ?_, ?_⟩
    · exact Representation.character_quotientToInvariants_mk V.ρ N g
    · rw [h₁, Int.cast_natCast, ← Representation.char_one ρ]
      simpa only [ρ, map_one, one_mul, FDRep.character_ρ] using
        Representation.character_quotientToInvariants_mk V.ρ N 1
  obtain ⟨V, W, rfl⟩ := exists_eq_character_sub_character hX
  obtain ⟨P, hP, hP₁⟩ := h V
  obtain ⟨Q, hQ, hQ₁⟩ := h W
  refine ⟨P - Q, ?_, ?_⟩
  · simp only [map_sub, hP, hQ, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
  · simp only [eval_sub, Int.cast_sub, hP₁, hQ₁, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]

/-- If the order of the quotient image of `g` divides the prime `p`, and the mean of a virtual
character on `gN` is an integer `m`, its mean on `N` is an integer congruent to `m` modulo `p`. -/
theorem exists_int_modEq_of_coset_mean_eq_intCast [CharZero k] {X : G → k}
    (hX : X ∈ virtualCharacters k G) {g : G} {p : ℕ} (hp : p.Prime)
    (hg : QuotientGroup.mk' N g ^ p = 1) {m : ℤ}
    (hm : (Nat.card N : k)⁻¹ * ∑ n : N, X (g * n) = m) :
    ∃ b : ℤ, (Nat.card N : k)⁻¹ * ∑ n : N, X n = b ∧ b ≡ m [ZMOD (p : ℤ)] := by
  let L := AlgebraicClosure k
  let i := algebraMap k L
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (p : L) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let := invertibleOfNonzero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card N ≠ 0) :
    (Fintype.card N : L) ≠ 0)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L p
  obtain ⟨P, hP, h₁⟩ := exists_aeval_eq_coset_mean_and_eval_one_eq_subgroup_mean
    (i.comp_mem_virtualCharacters hX) hζ hg
  refine ⟨P.eval 1, i.injective ?_, ?_⟩
  · simpa only [map_mul, map_inv₀, map_natCast, map_sum, map_intCast, Function.comp_apply] using
      h₁.symm
  have hmL : (Nat.card N : L)⁻¹ * ∑ n : N, i (X (g * n)) = m := by
    simpa only [map_mul, map_inv₀, map_natCast, map_sum, map_intCast] using congrArg i hm
  have h : aeval ζ P = aeval ζ (C m) := by
    rw [aeval_C]
    exact hP.trans (hmL.trans (map_intCast (algebraMap ℤ L) m).symm)
  simpa only [eval_C] using P.eval_one_modEq_of_aeval_eq_of_pow_eq_one (C m) hp hζ.pow_eq_one h

/-- If two virtual characters are orthogonal on a coset of a finite normal subgroup of prime
index, their restrictions pair to an integer divisible by the index. Over `ℂ` the values at
inverses can equivalently be written as conjugate values. -/
theorem index_dvd_pairing_of_coset_pairing_eq_zero [CharZero k] (hp : N.index.Prime)
    {X Y : G → k} (hX : X ∈ virtualCharacters k G) (hY : Y ∈ virtualCharacters k G) (g : G)
    (h : ∑ n : N, X (g * n) * Y (g * n)⁻¹ = 0) :
    ∃ b : ℤ, (N.index : ℤ) ∣ b ∧ (Nat.card N : k)⁻¹ * ∑ n : N, X n * Y (n⁻¹ : N) = b := by
  have hYi : (fun x ↦ Y x⁻¹) ∈ virtualCharacters k G := by
    obtain ⟨V, W, rfl⟩ := exists_eq_character_sub_character hY
    refine (mem_virtualCharacters_iff_exists_eq_character_sub_character).2
      ⟨FDRep.of (Representation.dual V.ρ), FDRep.of (Representation.dual W.ρ), ?_⟩
    funext x
    simp only [Pi.sub_apply, FDRep.char_dual]
  have := exists_int_modEq_of_coset_mean_eq_intCast (mul_mem_virtualCharacters hX hYi) hp
    (pow_card_eq_one' (x := QuotientGroup.mk' N g)) (m := 0)
    (by simp only [Pi.mul_apply, Int.cast_zero, h, mul_zero])
  obtain ⟨b, hb, hmod⟩ := this
  exact ⟨b, Int.modEq_zero_iff_dvd.mp hmod, hb⟩

end TauCeti
