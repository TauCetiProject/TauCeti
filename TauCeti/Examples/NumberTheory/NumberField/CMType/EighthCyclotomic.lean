/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import TauCeti.NumberTheory.NumberField.CMType.Primitive
public import TauCeti.NumberTheory.NumberField.CMType.ReflexField
import TauCeti.Analysis.Complex.Sqrt

/-!
# A non-primitive CM type on `ℚ(ζ₈)`

This file checks the primitivity and reflex-field API of `TauCeti.CMType` on the eighth
cyclotomic field `K = ℚ(ζ)`, `ζ` a primitive eighth root of unity, modelled as
`CyclotomicField 8 ℚ`.

The element `s = ζ + ζ³` satisfies `s² = -2` (`s_sq`), so `F = ℚ(s) ⊆ K` is `ℚ(√-2)`, of degree at
most two (`finrank_F_le`), while `[K : ℚ] = 4` (`finrank_K`). Every complex embedding sends `s`
to `±i√2` (`apply_eq_or_apply_eq_neg`), and the embeddings sending `s` to `i√2` form a CM type
`Φ` (`TauCeti.EighthCyclotomicCMType.sqrtNegTwoType`). They are the two embeddings
`ζ ↦ ζ₈` and `ζ ↦ ζ₈³`, for `ζ₈ = (1 + i)/√2` (`mem_Φ_iff`). Membership only depends on the value
at `s`, so `Φ` is induced from the corresponding type on `ℚ(√-2)` (`induced_Φ₀`) and is not
primitive (`not_isPrimitive_Φ`). An induced type has the reflex field of the type it is induced
from, so the reflex field of `Φ` is `ℚ(i√2) ⊆ ℂ` (`reflexField_Φ`), of degree two
(`finrank_reflexField_Φ`), not the degree-four field `K`.

## References

* J. S. Milne, *Complex Multiplication*, §1, p.11, Proposition 1.9, p.12, and Proposition 1.18,
  p.14.
-/

public section

open NumberField Polynomial IntermediateField Complex

namespace TauCeti.EighthCyclotomicCMType

/-! ### Square roots of `-2` -/

section SqrtNegTwo

variable {L : Type*} [Field L]

/-- `i√2` is a square root of `-2` in `ℂ`. -/
theorem I_mul_sqrt_two_sq : (I * √2) ^ 2 = -2 := by
  rw [mul_pow, I_sq, sq_ofReal_sqrt zero_le_two, ofReal_ofNat]
  ring

/-- A square root of `-2` is integral over `ℚ`: it is a root of `X ^ 2 + 2`. -/
theorem isIntegral_of_sq_eq_neg_two [Algebra ℚ L] {x : L} (hx : x ^ 2 = -2) : IsIntegral ℚ x :=
  ⟨X ^ 2 + C 2, monic_X_pow_add_C 2 two_ne_zero, by simp [hx]⟩

/-- **A square root of `-2` generates an extension of `ℚ` of degree at most two.** -/
theorem finrank_adjoin_le_two [Algebra ℚ L] {x : L} (hx : x ^ 2 = -2) :
    Module.finrank ℚ ℚ⟮x⟯ ≤ 2 := by
  have hp : aeval x (X ^ 2 + C 2 : ℚ[X]) = 0 := by simp [hx]
  rw [adjoin.finrank (isIntegral_of_sq_eq_neg_two hx)]
  refine (natDegree_le_of_dvd (minpoly.dvd ℚ x hp)
    (monic_X_pow_add_C 2 two_ne_zero).ne_zero).trans ?_
  rw [natDegree_X_pow_add_C]

/-- **Every complex embedding sends a square root of `-2` to `±i√2`.** -/
theorem apply_eq_or_apply_eq_neg {t : L} (ht : t ^ 2 = -2) (ψ : L →+* ℂ) :
    ψ t = I * √2 ∨ ψ t = -(I * √2) := by
  refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
  rw [← map_pow, ht, map_neg, map_ofNat, I_mul_sqrt_two_sq]

theorem I_mul_sqrt_two_ne_neg : I * √2 ≠ -(I * √2) := by
  intro h
  have := congrArg Complex.im h
  simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add,
    neg_im] at this
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 two_pos
  linarith

/-- The CM type of the embeddings sending a square root `t` of `-2` to `i√2`. -/
noncomputable def sqrtNegTwoType (t : L) (ht : t ^ 2 = -2) : CMType L where
  carrier := {ψ | ψ t = I * √2}
  star_mem_iff' ψ := by
    rcases apply_eq_or_apply_eq_neg ht ψ with h | h <;>
      simp [RingHom.star_apply, h, I_mul_sqrt_two_ne_neg.symm]

@[simp]
theorem mem_sqrtNegTwoType {t : L} {ht : t ^ 2 = -2} {ψ : L →+* ℂ} :
    ψ ∈ sqrtNegTwoType t ht ↔ ψ t = I * √2 :=
  Iff.rfl

end SqrtNegTwo

/-! ### The field `ℚ(ζ₈)` -/

/-- `ℚ(ζ₈)`, as the eighth cyclotomic field. -/
abbrev K : Type := CyclotomicField 8 ℚ

local instance instIsCyclotomicExtensionK : IsCyclotomicExtension {8} ℚ K :=
  have : NeZero ((8 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 8 ℚ

/-- The primitive eighth root of unity `ζ` of `ℚ(ζ₈)`. -/
noncomputable abbrev ζ : K := IsCyclotomicExtension.zeta 8 ℚ K

theorem isPrimitiveRoot_ζ : IsPrimitiveRoot ζ 8 := IsCyclotomicExtension.zeta_spec 8 ℚ K

/-- `[ℚ(ζ₈) : ℚ] = 4`. -/
theorem finrank_K : Module.finrank ℚ K = 4 := by
  rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (n := 8) (by norm_num))]
  decide

theorem ζ_pow_four : ζ ^ 4 = -1 :=
  (isPrimitiveRoot_ζ.pow_of_dvd (by norm_num) (by norm_num : 4 ∣ 8)).eq_neg_one_of_two_right

/-- The square root `s = ζ + ζ³` of `-2` in `ℚ(ζ₈)`. -/
noncomputable abbrev s : K := ζ + ζ ^ 3

theorem s_sq : s ^ 2 = -2 := by
  linear_combination (ζ ^ 2 + 2) * ζ_pow_four

/-- The CM type `Φ` of `ℚ(ζ₈)`: the embeddings sending `√-2 = ζ + ζ³` to `i√2`. -/
noncomputable def Φ : CMType K := sqrtNegTwoType s s_sq

theorem mem_Φ {φ : K →+* ℂ} : φ ∈ Φ ↔ φ s = I * √2 :=
  Iff.rfl

/-- The primitive eighth root of unity `ζ₈ = (1 + i)/√2` in `ℂ`. -/
noncomputable def ζ₈ : ℂ := (1 + I) / √2

theorem ζ₈_sq : ζ₈ ^ 2 = I := by
  rw [ζ₈, div_pow, sq_ofReal_sqrt zero_le_two, ofReal_ofNat]
  linear_combination (1 / 2 : ℂ) * I_sq

theorem ζ₈_add_ζ₈_pow_three : ζ₈ + ζ₈ ^ 3 = I * √2 := by
  have h : ζ₈ * √2 = 1 + I := by rw [ζ₈, div_mul_cancel₀ _ (ofReal_sqrt_ne_zero two_pos)]
  have h3 : ζ₈ ^ 3 = ζ₈ * I := by rw [pow_succ, ζ₈_sq, mul_comm]
  rw [h3]
  refine mul_right_cancel₀ (ofReal_sqrt_ne_zero two_pos) ?_
  linear_combination (1 + I) * h + I * I_mul_sqrt_two_sq - (I * (√2 : ℂ) ^ 2 - 1) * I_sq

theorem ζ₈_mul_ζ₈_pow_three : ζ₈ * ζ₈ ^ 3 = -1 := by
  linear_combination (ζ₈ ^ 2 + I) * ζ₈_sq + I_sq

/-- **`Φ = {ζ ↦ ζ₈, ζ ↦ ζ₈³}`.** An embedding of `ℚ(ζ₈)` sends `√-2 = ζ + ζ³` to `i√2` exactly
when it sends `ζ` to `ζ₈` or to `ζ₈³`. -/
theorem mem_Φ_iff {φ : K →+* ℂ} : φ ∈ Φ ↔ φ ζ = ζ₈ ∨ φ ζ = ζ₈ ^ 3 := by
  have hx4 : φ ζ ^ 4 = -1 := by rw [← map_pow, ζ_pow_four, map_neg, map_one]
  have hs : φ s = φ ζ + φ ζ ^ 3 := by rw [map_add, map_pow]
  -- `ζ₈` and `ζ₈³` are the roots of `X² - i√2 X - 1`.
  have hp : (φ ζ - ζ₈) * (φ ζ - ζ₈ ^ 3) = φ ζ ^ 2 - I * √2 * φ ζ - 1 := by
    linear_combination (-φ ζ) * ζ₈_add_ζ₈_pow_three + ζ₈_mul_ζ₈_pow_three
  rw [mem_Φ, hs, ← sub_eq_zero (a := φ ζ), ← sub_eq_zero (a := φ ζ), ← mul_eq_zero, hp]
  constructor
  · intro h
    have hpq : (φ ζ ^ 2 - I * √2 * φ ζ - 1) * (φ ζ ^ 2 + I * √2 * φ ζ - 1) = 0 := by
      linear_combination hx4 - φ ζ ^ 2 * I_mul_sqrt_two_sq
    refine (mul_eq_zero.1 hpq).resolve_right fun hq => I_mul_sqrt_two_ne_neg ?_
    linear_combination -h - (I * √2 - φ ζ) * hq + φ ζ * I_mul_sqrt_two_sq
  · intro h
    linear_combination (φ ζ + I * √2) * h + φ ζ * I_mul_sqrt_two_sq

/-! ### The subfield `ℚ(√-2)` and non-primitivity -/

/-- The subfield `ℚ(√-2) = ℚ(ζ + ζ³)` of `ℚ(ζ₈)`. -/
noncomputable abbrev F : IntermediateField ℚ K := ℚ⟮s⟯

/-- The generator `√-2` of `F`. -/
noncomputable abbrev t : F := AdjoinSimple.gen ℚ s

theorem t_sq : t ^ 2 = -2 :=
  (algebraMap F K).injective <| by
    rw [map_pow, AdjoinSimple.algebraMap_gen, s_sq, map_neg, map_ofNat]

/-- `[ℚ(√-2) : ℚ] ≤ 2`. -/
theorem finrank_F_le : Module.finrank ℚ F ≤ 2 :=
  finrank_adjoin_le_two s_sq

/-- The CM type of `ℚ(√-2)` sending `√-2` to `i√2`. -/
noncomputable def Φ₀ : CMType F := sqrtNegTwoType t t_sq

/-- **`Φ` is induced from `ℚ(√-2)`**: both of its embeddings send `√-2` to `i√2`. -/
theorem induced_Φ₀ : Φ₀.induced (algebraMap F K) = Φ := by
  ext φ
  simp [Φ₀, Φ]

/-- **`Φ` is not primitive**: it is induced from the proper subfield `ℚ(√-2)`. -/
theorem not_isPrimitive_Φ : ¬ Φ.IsPrimitive := fun h => by
  have hF := (CMType.isPrimitive_iff Φ).1 h F ⟨Φ₀, induced_Φ₀⟩
  have h2 := finrank_F_le
  rw [hF, IntermediateField.finrank_top', finrank_K] at h2
  omega

/-! ### The reflex field -/

theorem typeTrace_Φ_s : Φ.typeTrace s = 2 * (I * √2) := by
  classical
  have hcard : Nat.card Φ = 2 := by
    have := Φ.two_mul_card_eq_finrank
    rw [finrank_K] at this
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
  rw [CMType.typeTrace_eq_sum, Finset.sum_congr rfl fun φ hφ => mem_Φ.1 (Finset.mem_filter.1 hφ).2,
    Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_ofNat]

theorem apply_mem_of_mem_Φ₀ {ψ : F →+* ℂ} (hψ : ψ ∈ Φ₀) (a : F) : ψ a ∈ ℚ⟮I * √2⟯ := by
  have ha : a ∈ Algebra.adjoin ℚ {t} := by
    have h := PowerBasis.adjoin_gen_eq_top (adjoin.powerBasis (IsIntegral.of_finite ℚ s))
    rw [adjoin.powerBasis_gen] at h
    rw [h]
    trivial
  have hψa : ψ.toRatAlgHom a ∈ (Algebra.adjoin ℚ {t}).map ψ.toRatAlgHom :=
    Subalgebra.mem_map.2 ⟨a, ha, rfl⟩
  rw [AlgHom.map_adjoin, Set.image_singleton, RingHom.toRatAlgHom_apply,
    mem_sqrtNegTwoType.1 hψ] at hψa
  exact algebra_adjoin_le_adjoin ℚ _ hψa

/-- **The reflex field of `Φ` is `ℚ(i√2) ⊆ ℂ`.** -/
theorem reflexField_Φ : Φ.reflexField = ℚ⟮I * √2⟯ := by
  refine le_antisymm ?_ (adjoin_simple_le_iff.2 ?_)
  · rw [← induced_Φ₀, CMType.reflexField_induced, CMType.reflexField_le_iff]
    intro a
    rw [CMType.typeTrace_apply]
    exact finsum_mem_induction (· ∈ ℚ⟮I * √2⟯) (zero_mem _) (fun _ _ => add_mem)
      fun ψ hψ => apply_mem_of_mem_Φ₀ hψ a
  · have h := Φ.typeTrace_mem_reflexField s
    rw [typeTrace_Φ_s] at h
    have h2 : (2 : ℂ)⁻¹ ∈ Φ.reflexField := inv_mem (ofNat_mem _ 2)
    simpa using mul_mem h2 h

/-- **The reflex field of `Φ` has degree two**, whereas `[ℚ(ζ₈) : ℚ] = 4` (`finrank_K`). -/
theorem finrank_reflexField_Φ : Module.finrank ℚ Φ.reflexField = 2 := by
  rw [reflexField_Φ]
  have hle := finrank_adjoin_le_two I_mul_sqrt_two_sq
  have hne : Module.finrank ℚ ℚ⟮I * √2⟯ ≠ 1 := by
    intro h1
    rw [IntermediateField.finrank_eq_one_iff, adjoin_simple_eq_bot_iff, mem_bot] at h1
    obtain ⟨q, hq⟩ := h1
    have h0 : (0 : ℝ) = √2 := by simpa using congrArg Complex.im hq
    exact Real.sqrt_ne_zero'.2 two_pos h0.symm
  have := adjoin.finiteDimensional (isIntegral_of_sq_eq_neg_two I_mul_sqrt_two_sq)
  have hpos : 0 < Module.finrank ℚ ℚ⟮I * √2⟯ := Module.finrank_pos
  omega

end TauCeti.EighthCyclotomicCMType
