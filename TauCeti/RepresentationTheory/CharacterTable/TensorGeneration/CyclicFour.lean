/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Character
public import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# Tensor powers of the faithful two-dimensional representation of `C₄`

This file works out the faithful-tensor-generation theory of
`TauCeti.RepresentationTheory.CharacterTable.TensorGeneration` completely for the cyclic group
`C₄ = Multiplicative (ZMod 4)` and its faithful representation `U = χ₁ ⊕ χ₃`, where
`χⱼ (g ^ a) = i ^ (j a)`. The character of `U` is `(2, 0, -2, 0)` on `1, g, g², g³`, so it has
three values while `C₄` has four conjugacy classes. Every multiplicity
`mₙ = dim Hom(χⱼ, U^⊗n)` is computed: `m₀` is `1` for `χ₀` and `0` otherwise, and
`m_{n+1} = 2ⁿ` when `n + j` is odd and `0` otherwise. The multiplicities of every representation
`X` satisfy the recurrence `m_{n+3} = 4 m_{n+1}`, whose characteristic polynomial `T³ - 4T` has the
character values as roots, and the four tensor-multiplicity series are rational functions with
the denominator `1 - 4z²`.

The example shows two phenomena of the general theory. Every irreducible representation occurs
in some `U^⊗n` with `n ≤ 2`, below the number of character values. The characters of the tensor
powers span only the three-dimensional space of functions with `f (g³) = f g`, although all four
irreducible characters occur: spanning by characters and occurrence of summands are different
statements.

## Main definitions

* `TauCeti.cyclicFourChar j`: the character of `C₄` sending the generator to `i ^ j`.
* `TauCeti.cyclicFourFaithfulRep`: the faithful representation `U = χ₁ ⊕ χ₃`.

## Main statements

* `TauCeti.characterValues_cyclicFourFaithfulRep`: the character values of `U` are `2, 0, -2`.
* `TauCeti.finrank_hom_tensorPower_add_three_cyclicFourFaithfulRep`: `m_{n+3} = 4 m_{n+1}`.
* `TauCeti.finrank_hom_tensorPower_zero_cyclicFourChar`,
  `TauCeti.finrank_hom_tensorPower_succ_cyclicFourChar`: the multiplicities of `χⱼ`.
* `TauCeti.tensorMultiplicitySeries_cyclicFourChar_zero` and its siblings: the series
  `F₀ = (1 - 2z²)/(1 - 4z²)`, `F₁ = F₃ = z/(1 - 4z²)` and `F₂ = 2z²/(1 - 4z²)`.
* `TauCeti.nonempty_iso_tensorPower_two_cyclicFourFaithfulRep`: `U^⊗2 ≅ χ₀ ⊕ χ₀ ⊕ χ₂ ⊕ χ₂`.
* `TauCeti.mem_span_range_char_tensorPower_cyclicFourFaithfulRep_iff`: the span of the
  characters of the tensor powers.

## References

* B. Steinberg, *On the Burnside–Brauer–Steinberg theorem*, arXiv:1409.7632, Introduction and
  Remark 1.
-/

public section

open CategoryTheory Complex

namespace TauCeti

/-- The character `χⱼ` of the cyclic group `C₄ = Multiplicative (ZMod 4)` sending the generator
`ofAdd 1` to `i ^ j`. -/
noncomputable def cyclicFourChar (j : ZMod 4) : Multiplicative (ZMod 4) →* ℂˣ :=
  (MulEquiv.refl _).zmodCoordChar (ζ := Units.mk0 I I_ne_zero ^ j.val) (by
    rw [← pow_mul, mul_comm, pow_mul, show Units.mk0 I I_ne_zero ^ 4 = 1 from Units.ext (by simp),
      one_pow])

/-- The value of `χⱼ` at `ofAdd a` is `i ^ (j a)`, with exponents the representatives in
`{0, 1, 2, 3}`. -/
@[simp]
theorem coe_cyclicFourChar_ofAdd (j a : ZMod 4) :
    (cyclicFourChar j (.ofAdd a) : ℂ) = I ^ (j.val * a.val) := by
  simp [cyclicFourChar, ← pow_mul]

/-- The faithful two-dimensional representation `U = χ₁ ⊕ χ₃` of `C₄`, on which the generator
acts by `diag(i, -i)`. -/
noncomputable def cyclicFourFaithfulRep : FDRep ℂ (Multiplicative (ZMod 4)) :=
  FDRep.ofLinearCharacter (cyclicFourChar 1) ⊞ FDRep.ofLinearCharacter (cyclicFourChar 3)

/-- The character of `U` at `ofAdd a` is `i ^ a + (-i) ^ a`. -/
@[simp]
theorem char_cyclicFourFaithfulRep_ofAdd (a : ZMod 4) :
    cyclicFourFaithfulRep.character (.ofAdd a) = I ^ a.val + (-I) ^ a.val := by
  rw [cyclicFourFaithfulRep, FDRep.char_biprod, Pi.add_apply, FDRep.char_ofLinearCharacter,
    FDRep.char_ofLinearCharacter, coe_cyclicFourChar_ofAdd, coe_cyclicFourChar_ofAdd]
  simp [ZMod.val_ofNat, ZMod.val_one_eq_one_mod, pow_mul, pow_succ]

private theorem zmod_four_cases (a : ZMod 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  revert a
  decide

private theorem forall_cyclicFour {P : Multiplicative (ZMod 4) → Prop} (h₀ : P (.ofAdd 0))
    (h₁ : P (.ofAdd 1)) (h₂ : P (.ofAdd 2)) (h₃ : P (.ofAdd 3)) (g : Multiplicative (ZMod 4)) :
    P g := by
  rw [← ofAdd_toAdd g]
  rcases zmod_four_cases (Multiplicative.toAdd g) with h | h | h | h <;> rw [h] <;> assumption

/-- The character values of `U` are `2`, `0` and `-2`. -/
theorem characterValues_cyclicFourFaithfulRep :
    cyclicFourFaithfulRep.characterValues = {2, 0, -2} := by
  ext z
  simp only [FDRep.mem_characterValues, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    revert g
    refine forall_cyclicFour ?_ ?_ ?_ ?_ <;> rw [char_cyclicFourFaithfulRep_ofAdd] <;>
      norm_num [ZMod.val_one_eq_one_mod, ZMod.val_ofNat, pow_succ]
  · rintro (rfl | rfl | rfl)
    · exact ⟨.ofAdd 0, by rw [char_cyclicFourFaithfulRep_ofAdd]; norm_num⟩
    · exact ⟨.ofAdd 1, by simp [char_cyclicFourFaithfulRep_ofAdd, ZMod.val_one_eq_one_mod]⟩
    · exact ⟨.ofAdd 2, by simp [char_cyclicFourFaithfulRep_ofAdd, ZMod.val_ofNat]; norm_num⟩

/-- `U` has three distinct character values. -/
theorem characterValueCount_cyclicFourFaithfulRep :
    cyclicFourFaithfulRep.characterValueCount = 3 := by
  rw [← FDRep.card_characterValues, characterValues_cyclicFourFaithfulRep]
  norm_num

/-- `U` is faithful. -/
theorem cyclicFourFaithfulRep_ρ_injective : Function.Injective cyclicFourFaithfulRep.ρ := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  have h : cyclicFourFaithfulRep.character g = cyclicFourFaithfulRep.character 1 := by
    simp [FDRep.character, hg]
  rw [← ofAdd_zero, char_cyclicFourFaithfulRep_ofAdd] at h
  revert g
  refine forall_cyclicFour ?_ ?_ ?_ ?_ <;> intro _ h <;> [rfl; skip; skip; skip] <;>
    rw [char_cyclicFourFaithfulRep_ofAdd] at h <;>
    norm_num [ZMod.val_one_eq_one_mod, ZMod.val_ofNat, pow_succ] at h

/-- The denominator `Q(z) = ∏ₐ (1 - a z)` of the tensor-multiplicity series of `U` is `1 - 4 z²`. -/
theorem tensorMultiplicityDenominator_cyclicFourFaithfulRep :
    cyclicFourFaithfulRep.tensorMultiplicityDenominator =
      1 - Polynomial.C 4 * Polynomial.X ^ 2 := by
  rw [FDRep.tensorMultiplicityDenominator_def, characterValues_cyclicFourFaithfulRep]
  rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_singleton]
  simp only [map_neg, map_zero, zero_mul, sub_zero, one_mul, Polynomial.C_ofNat]
  ring

/-- The polynomial `R(T) = ∏ₐ (T - a)` over the character values of `U` is `T³ - 4T`. -/
theorem nodal_characterValues_cyclicFourFaithfulRep :
    Lagrange.nodal cyclicFourFaithfulRep.characterValues id =
      Polynomial.X ^ 3 - Polynomial.C 4 * Polynomial.X := by
  rw [characterValues_cyclicFourFaithfulRep, Lagrange.nodal,
    Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_singleton]
  simp only [id, map_neg, map_zero, sub_zero, sub_neg_eq_add, Polynomial.C_ofNat]
  ring

/-- **The recurrence of tensor multiplicities for `U`.** For every `X`, the multiplicities
`mₙ = dim Hom(X, U^⊗n)` satisfy `m_{n+3} = 4 m_{n+1}`, the recurrence with characteristic
polynomial `T³ - 4T`. -/
theorem finrank_hom_tensorPower_add_three_cyclicFourFaithfulRep
    (X : FDRep ℂ (Multiplicative (ZMod 4))) (n : ℕ) :
    Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower (n + 3)) =
      4 * Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower (n + 1)) := by
  have h := FDRep.sum_coeff_nodal_mul_finrank_hom_tensorPower_add_eq_zero cyclicFourFaithfulRep X n
  rw [characterValueCount_cyclicFourFaithfulRep, nodal_characterValues_cyclicFourFaithfulRep] at h
  have c₀ : (Polynomial.X ^ 3 - Polynomial.C (4 : ℂ) * Polynomial.X).coeff 0 = 0 := by simp
  have c₁ : (Polynomial.X ^ 3 - Polynomial.C (4 : ℂ) * Polynomial.X).coeff 1 = -4 := by
    simp [Polynomial.coeff_X_pow]
  have c₂ : (Polynomial.X ^ 3 - Polynomial.C (4 : ℂ) * Polynomial.X).coeff 2 = 0 := by
    simp [Polynomial.coeff_X_pow]
  have c₃ : (Polynomial.X ^ 3 - Polynomial.C (4 : ℂ) * Polynomial.X).coeff 3 = 1 := by
    simp
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    c₀, c₁, c₂, c₃] at h
  exact_mod_cast (by linear_combination h :
    (Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower (n + 3)) : ℂ) =
      4 * Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower (n + 1)))

/-- The tensor multiplicities of the characters of `C₄` in the powers of `U`, read in `ℂ`:
`dim Hom(χⱼ, U^⊗n) = (2ⁿ + (-1)ʲ (-2)ⁿ + 0ⁿ (iʲ + (-i)ʲ)) / 4`, with `0⁰ = 1`. -/
private theorem finrank_hom_tensorPower_cyclicFourChar_eq (j : ZMod 4) (n : ℕ) :
    (Module.finrank ℂ (FDRep.ofLinearCharacter (cyclicFourChar j) ⟶
        cyclicFourFaithfulRep.tensorPower n) : ℂ) =
      (2 ^ n + (-1) ^ j.val * (-2) ^ n + 0 ^ n * (I ^ j.val + (-I) ^ j.val)) / 4 := by
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant,
    show (Finset.univ : Finset (Multiplicative (ZMod 4))) = {.ofAdd 0, .ofAdd 1, .ofAdd 2, .ofAdd 3}
      by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [FDRep.char_tensorPower, FDRep.char_ofLinearCharacter, char_cyclicFourFaithfulRep_ofAdd,
    ← ofAdd_neg, coe_cyclicFourChar_ofAdd, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card]
  rw [show (-(0 : ZMod 4)).val = 0 from rfl, show (-(1 : ZMod 4)).val = 3 from rfl,
    show (-(2 : ZMod 4)).val = 2 from rfl, show (-(3 : ZMod 4)).val = 1 from rfl,
    show (0 : ZMod 4).val = 0 from rfl, show (1 : ZMod 4).val = 1 from rfl,
    show (2 : ZMod 4).val = 2 from rfl, show (3 : ZMod 4).val = 3 from rfl]
  have h2 : I ^ (j.val * 2) = (-1) ^ j.val := by rw [pow_mul', I_sq]
  have h3 : I ^ (j.val * 3) = (-I) ^ j.val := by rw [pow_mul', show I ^ 3 = -I by simp [pow_succ]]
  rw [h2, h3, mul_zero, mul_one]
  norm_num [pow_succ]
  ring

/-- **The tensor multiplicities of the characters of `C₄` in the zero-fold power of `U`**: the
trivial character occurs once and no other character occurs. -/
theorem finrank_hom_tensorPower_zero_cyclicFourChar (j : ZMod 4) :
    Module.finrank ℂ (FDRep.ofLinearCharacter (cyclicFourChar j) ⟶
      cyclicFourFaithfulRep.tensorPower 0) = if j = 0 then 1 else 0 := by
  have h := finrank_hom_tensorPower_cyclicFourChar_eq j 0
  split_ifs with hj
  · subst hj
    norm_num at h
    exact_mod_cast h
  · rcases zmod_four_cases j with rfl | rfl | rfl | rfl <;> [contradiction; skip; skip; skip] <;>
      norm_num [ZMod.val_one_eq_one_mod, ZMod.val_ofNat, pow_succ] at h <;> exact_mod_cast h

/-- **The tensor multiplicities of the characters of `C₄` in the positive powers of `U`**:
`χⱼ` occurs in `U^⊗(n+1)` with multiplicity `2ⁿ` if `n + j` is odd, and not at all otherwise. -/
theorem finrank_hom_tensorPower_succ_cyclicFourChar (j : ZMod 4) (n : ℕ) :
    Module.finrank ℂ (FDRep.ofLinearCharacter (cyclicFourChar j) ⟶
      cyclicFourFaithfulRep.tensorPower (n + 1)) = if Odd (n + j.val) then 2 ^ n else 0 := by
  have h := finrank_hom_tensorPower_cyclicFourChar_eq j (n + 1)
  rw [zero_pow n.succ_ne_zero, zero_mul, add_zero, neg_pow (2 : ℂ), ← mul_assoc, ← pow_add] at h
  split_ifs with hn
  · have he : Even (j.val + (n + 1)) := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k + 1, by omega⟩
    rw [he.neg_one_pow] at h
    exact_mod_cast (h.trans (by ring) : _ = (2 : ℂ) ^ n)
  · have ho : Odd (j.val + (n + 1)) := by
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hn
      exact ⟨k, by omega⟩
    rw [ho.neg_one_pow] at h
    exact_mod_cast (h.trans (by ring) : _ = (0 : ℂ))

open PowerSeries in
/-- Multiplying the tensor-multiplicity series of `X` by `1 - 4z²` leaves the polynomial
`m₀ + m₁ z + (m₂ - 4 m₀) z²`, by the recurrence `m_{n+3} = 4 m_{n+1}`. -/
private theorem tensorMultiplicitySeries_mul_one_sub_four_mul_X_sq
    (X : FDRep ℂ (Multiplicative (ZMod 4))) :
    cyclicFourFaithfulRep.tensorMultiplicitySeries X * (1 - 4 * PowerSeries.X ^ 2) =
      C (Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower 0) : ℂ) +
        C (Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower 1) : ℂ) * PowerSeries.X +
        C ((Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower 2) : ℂ) -
          4 * Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower 0)) * PowerSeries.X ^ 2 := by
  have h (n : ℕ) : (Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower (n + 1 + 1 + 1)) : ℂ) =
      4 * Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower (n + 1)) := by
    exact_mod_cast finrank_hom_tensorPower_add_three_cyclicFourFaithfulRep X n
  ext n
  rcases n with _ | _ | _ | n <;>
    simp [-map_natCast, -coeff_zero_eq_constantCoeff, mul_sub, ← mul_assoc,
      mul_comm _ (4 : ℂ⟦X⟧), coeff_mul_X_pow', coeff_C, h]

/-- The zero-fold tensor power of `U` is the trivial character `χ₀`. -/
theorem nonempty_iso_tensorPower_zero_cyclicFourFaithfulRep :
    Nonempty (cyclicFourFaithfulRep.tensorPower 0 ≅ FDRep.ofLinearCharacter (cyclicFourChar 0)) :=
  FDRep.nonempty_iso_of_character_eq _ _ (funext fun g ↦ by
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective g
    simp)

/-- The tensor square of `U` is `χ₀ ⊕ χ₀ ⊕ χ₂ ⊕ χ₂`. -/
theorem nonempty_iso_tensorPower_two_cyclicFourFaithfulRep :
    Nonempty (cyclicFourFaithfulRep.tensorPower 2 ≅
      FDRep.ofLinearCharacter (cyclicFourChar 0) ⊞ FDRep.ofLinearCharacter (cyclicFourChar 0) ⊞
        FDRep.ofLinearCharacter (cyclicFourChar 2) ⊞
          FDRep.ofLinearCharacter (cyclicFourChar 2)) := by
  refine FDRep.nonempty_iso_of_character_eq _ _ (funext (forall_cyclicFour ?_ ?_ ?_ ?_)) <;>
    simp only [FDRep.char_tensorPower, char_cyclicFourFaithfulRep_ofAdd, FDRep.char_biprod,
      Pi.add_apply, FDRep.char_ofLinearCharacter, coe_cyclicFourChar_ofAdd] <;>
    norm_num [ZMod.val_one_eq_one_mod, ZMod.val_ofNat, pow_succ]

/-- **Every irreducible representation of `C₄` occurs in `U^⊗n` for some `n ≤ 2`**: every nonzero
`X` has a nonzero map into such a tensor power, the exponent staying below the three character
values of `U`. The bound is attained by `χ₂`, which first occurs in `U^⊗2`. -/
theorem exists_le_two_pos_finrank_hom_tensorPower_cyclicFourFaithfulRep
    (X : FDRep ℂ (Multiplicative (ZMod 4))) (hX : 0 < Module.finrank ℂ X) :
    ∃ n ≤ 2, 0 < Module.finrank ℂ (X ⟶ cyclicFourFaithfulRep.tensorPower n) := by
  obtain ⟨n, hn, h⟩ := FDRep.exists_pos_finrank_hom_tensorPower _ X
    cyclicFourFaithfulRep_ρ_injective hX
  rw [characterValueCount_cyclicFourFaithfulRep] at hn
  exact ⟨n, by omega, h⟩

/-- **The span of the characters of the tensor powers of `U`** is the three-dimensional space
of functions with `f (g³) = f g`. It is a proper subspace of the class functions of `C₄`, although
every irreducible character occurs in some tensor power: spanning by characters and occurrence
of summands are different statements. -/
theorem mem_span_range_char_tensorPower_cyclicFourFaithfulRep_iff
    (f : Multiplicative (ZMod 4) → ℂ) :
    f ∈ Submodule.span ℂ (Set.range fun n ↦ (cyclicFourFaithfulRep.tensorPower n).character) ↔
      ∀ g, f (g ^ 3) = f g := by
  have hval (a : ZMod 4) := char_cyclicFourFaithfulRep_ofAdd a
  have h₀ : cyclicFourFaithfulRep.character (.ofAdd 0) = 2 := by rw [hval]; norm_num
  have h₁ : cyclicFourFaithfulRep.character (.ofAdd 1) = 0 := by
    rw [hval]; simp [ZMod.val_one_eq_one_mod]
  have h₂ : cyclicFourFaithfulRep.character (.ofAdd 2) = -2 := by
    rw [hval]; norm_num [ZMod.val_ofNat, pow_succ]
  have h₃ : cyclicFourFaithfulRep.character (.ofAdd 3) = 0 := by
    rw [hval]; norm_num [ZMod.val_ofNat, pow_succ]
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      refine forall_cyclicFour ?_ ?_ ?_ ?_ <;> simp only [FDRep.char_tensorPower]
      · rw [show (Multiplicative.ofAdd 0 : Multiplicative (ZMod 4)) ^ 3 = .ofAdd 0 by decide]
      · rw [show (Multiplicative.ofAdd 1 : Multiplicative (ZMod 4)) ^ 3 = .ofAdd 3 by decide,
          h₁, h₃]
      · rw [show (Multiplicative.ofAdd 2 : Multiplicative (ZMod 4)) ^ 3 = .ofAdd 2 by decide]
      · rw [show (Multiplicative.ofAdd 3 : Multiplicative (ZMod 4)) ^ 3 = .ofAdd 1 by decide,
          h₁, h₃]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  · intro hf
    have hf₃ : f (.ofAdd 3) = f (.ofAdd 1) :=
      (congrArg f (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 4)) ^ 3 =
        .ofAdd 3)).symm.trans (hf _)
    have e : f = f (.ofAdd 1) • (cyclicFourFaithfulRep.tensorPower 0).character +
        ((f (.ofAdd 0) - f (.ofAdd 2)) / 4) • (cyclicFourFaithfulRep.tensorPower 1).character +
        ((f (.ofAdd 0) + f (.ofAdd 2) - 2 * f (.ofAdd 1)) / 8) •
          (cyclicFourFaithfulRep.tensorPower 2).character := by
      refine funext (forall_cyclicFour ?_ ?_ ?_ ?_) <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, FDRep.char_tensorPower, h₀, h₁, h₂,
          h₃, hf₃] <;> ring
    rw [e]
    refine add_mem (add_mem ?_ ?_) ?_ <;> refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

open PowerSeries

/-- **The tensor-multiplicity series of the trivial character** is
`F₀ = (1 - 2z²) / (1 - 4z²)`. -/
theorem tensorMultiplicitySeries_cyclicFourChar_zero :
    cyclicFourFaithfulRep.tensorMultiplicitySeries (FDRep.ofLinearCharacter (cyclicFourChar 0)) =
      (1 - 2 * X ^ 2) * (1 - 4 * X ^ 2)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp), tensorMultiplicitySeries_mul_one_sub_four_mul_X_sq,
    finrank_hom_tensorPower_zero_cyclicFourChar, finrank_hom_tensorPower_succ_cyclicFourChar,
    finrank_hom_tensorPower_succ_cyclicFourChar]
  simp [map_ofNat C 2, map_ofNat C 4]
  ring

/-- **The tensor-multiplicity series of `χ₁`** is `F₁ = z / (1 - 4z²)`. -/
theorem tensorMultiplicitySeries_cyclicFourChar_one :
    cyclicFourFaithfulRep.tensorMultiplicitySeries (FDRep.ofLinearCharacter (cyclicFourChar 1)) =
      X * (1 - 4 * X ^ 2)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp), tensorMultiplicitySeries_mul_one_sub_four_mul_X_sq,
    finrank_hom_tensorPower_zero_cyclicFourChar, finrank_hom_tensorPower_succ_cyclicFourChar,
    finrank_hom_tensorPower_succ_cyclicFourChar]
  simp [ZMod.val_one_eq_one_mod, show (1 : ZMod 4) ≠ 0 by decide]

/-- **The tensor-multiplicity series of `χ₂`** is `F₂ = 2z² / (1 - 4z²)`. -/
theorem tensorMultiplicitySeries_cyclicFourChar_two :
    cyclicFourFaithfulRep.tensorMultiplicitySeries (FDRep.ofLinearCharacter (cyclicFourChar 2)) =
      2 * X ^ 2 * (1 - 4 * X ^ 2)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp), tensorMultiplicitySeries_mul_one_sub_four_mul_X_sq,
    finrank_hom_tensorPower_zero_cyclicFourChar, finrank_hom_tensorPower_succ_cyclicFourChar,
    finrank_hom_tensorPower_succ_cyclicFourChar]
  simp [ZMod.val_ofNat, show (2 : ZMod 4) ≠ 0 by decide, Nat.odd_iff, map_ofNat C 2]

/-- **The tensor-multiplicity series of `χ₃`** is `F₃ = z / (1 - 4z²)`, equal to `F₁`. -/
theorem tensorMultiplicitySeries_cyclicFourChar_three :
    cyclicFourFaithfulRep.tensorMultiplicitySeries (FDRep.ofLinearCharacter (cyclicFourChar 3)) =
      X * (1 - 4 * X ^ 2)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp), tensorMultiplicitySeries_mul_one_sub_four_mul_X_sq,
    finrank_hom_tensorPower_zero_cyclicFourChar, finrank_hom_tensorPower_succ_cyclicFourChar,
    finrank_hom_tensorPower_succ_cyclicFourChar]
  simp [ZMod.val_ofNat, show (3 : ZMod 4) ≠ 0 by decide, Nat.odd_iff]

end TauCeti
