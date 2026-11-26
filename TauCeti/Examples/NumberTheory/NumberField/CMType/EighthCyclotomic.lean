/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import TauCeti.NumberTheory.NumberField.CMType.Primitive.Basic
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IntermediateField.Quadratic

/-!
# A non-primitive CM type on `ℚ(ζ₈)`

This file checks the primitivity and reflex-field API of `TauCeti.CMType` on the eighth
cyclotomic field `K = ℚ(ζ)`, `ζ` a primitive eighth root of unity, modelled as
`CyclotomicField 8 ℚ`.

The element `s = ζ + ζ³` satisfies `s² = -2` (`s_sq`), so `F = ℚ(s) ⊆ K` is `ℚ(√-2)`, of degree
two (`finrank_F`), while `[K : ℚ] = 4` (`finrank_K`). Every complex embedding sends `s`
to `±i√2` (`apply_eq_or_apply_eq_neg`), and the embeddings sending `s` to `i√2` form a CM type
`Φ` (`TauCeti.EighthCyclotomicCMType.sqrtNegTwoType`). They are the two embeddings
`ζ ↦ ζ₈` and `ζ ↦ ζ₈³`, for the primitive eighth root of unity `ζ₈ = (1 + i)/√2`
(`isPrimitiveRoot_ζ₈`, `mem_Φ_iff`). Membership only depends on the value
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

/-! ### Square roots of `-2`

The CM type `sqrtNegTwoType` is stated for any field with a square root of `-2` so that the same
construction gives both the type `Φ` on `ℚ(ζ₈)` and the type `Φ₀` on `ℚ(√-2)` it is induced
from; it is kept in this example because its only uses are these two types. -/

section SqrtNegTwo

variable {L : Type*} [Field L]

/-- **A square root of `-2` generates a quadratic extension of `ℚ`.** -/
private theorem finrank_adjoin_eq_two [Algebra ℚ L] {x : L} (hx : x ^ 2 = -2) :
    Module.finrank ℚ ℚ⟮x⟯ = 2 :=
  TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare (a := -2)
    (by rw [hx, map_neg, map_ofNat]) fun h => by linarith [h.nonneg]

/-- `Complex.I_mul_ofReal_sqrt_sq` at `x = 2`, with the cast of `2` normalised for
`linear_combination`. -/
private theorem I_mul_sqrt_two_sq : (I * √2) ^ 2 = -2 := by
  rw [I_mul_ofReal_sqrt_sq zero_le_two, ofReal_ofNat]

/-- **Every complex embedding sends a square root of `-2` to `±i√2`.** -/
private theorem apply_eq_or_apply_eq_neg {t : L} (ht : t ^ 2 = -2) (ψ : L →+* ℂ) :
    ψ t = I * √2 ∨ ψ t = -(I * √2) := by
  refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
  rw [← map_pow, ht, map_neg, map_ofNat, I_mul_sqrt_two_sq]

private theorem I_mul_sqrt_two_ne_neg : I * √2 ≠ -(I * √2) :=
  self_ne_neg.2 (mul_ne_zero I_ne_zero (ofReal_sqrt_ne_zero two_pos))

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

theorem ζ₈_def : ζ₈ = (1 + I) / √2 :=
  (rfl)

theorem ζ₈_sq : ζ₈ ^ 2 = I := by
  rw [ζ₈_def, div_pow, sq_ofReal_sqrt zero_le_two, ofReal_ofNat]
  linear_combination (1 / 2 : ℂ) * I_sq

/-- `ζ₈` is a primitive eighth root of unity, since `ζ₈ ^ 4 = i ^ 2 = -1`. -/
theorem isPrimitiveRoot_ζ₈ : IsPrimitiveRoot ζ₈ 8 := by
  have h4 : ζ₈ ^ 4 = -1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, ζ₈_sq, I_sq]
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime_pow (p := 2) (n := 2) ?_ ?_
  · norm_num [h4]
  · norm_num [show ζ₈ ^ 8 = (ζ₈ ^ 4) ^ 2 by ring, h4]

theorem ζ₈_add_ζ₈_pow_three : ζ₈ + ζ₈ ^ 3 = I * √2 := by
  have h : ζ₈ * √2 = 1 + I := by rw [ζ₈_def, div_mul_cancel₀ _ (ofReal_sqrt_ne_zero two_pos)]
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

/-- `[ℚ(√-2) : ℚ] = 2`. -/
theorem finrank_F : Module.finrank ℚ F = 2 :=
  finrank_adjoin_eq_two s_sq

/-- The CM type of `ℚ(√-2)` sending `√-2` to `i√2`. -/
noncomputable def Φ₀ : CMType F := sqrtNegTwoType t t_sq

/-- **`Φ` is induced from `ℚ(√-2)`**: both of its embeddings send `√-2` to `i√2`. -/
theorem induced_Φ₀ : Φ₀.induced (algebraMap F K) = Φ := by
  ext φ
  simp [Φ₀, Φ]

/-- **`Φ` is not primitive**: it is induced from the proper subfield `ℚ(√-2)`. -/
theorem not_isPrimitive_Φ : ¬ Φ.IsPrimitive := fun h => by
  have hF := (CMType.isPrimitive_iff Φ).1 h F ⟨Φ₀, induced_Φ₀⟩
  have h2 := finrank_F
  rw [hF, IntermediateField.finrank_top', finrank_K] at h2
  omega

/-! ### The reflex field -/

/-- `Φ` has two embeddings, half of the four embeddings of `ℚ(ζ₈)`. -/
theorem card_Φ : Nat.card Φ = 2 := by
  have := Φ.two_mul_card_eq_finrank
  rw [finrank_K] at this
  omega

theorem typeTrace_Φ_s : Φ.typeTrace s = 2 * (I * √2) := by
  rw [CMType.typeTrace_apply, finsum_mem_congr rfl fun φ hφ => mem_Φ.1 hφ,
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_const,
    ← Nat.card_eq_card_finite_toFinset, SetLike.coe_sort_coe, card_Φ, nsmul_eq_mul, Nat.cast_ofNat]

/-- `t` generates `F = ℚ⟮s⟯`. -/
theorem adjoin_t_eq_top : ℚ⟮t⟯ = ⊤ :=
  lift_injective _ (by rw [lift_adjoin_simple, AdjoinSimple.coe_gen, lift_top])

theorem apply_mem_of_mem_Φ₀ {ψ : F →+* ℂ} (hψ : ψ ∈ Φ₀) (a : F) : ψ a ∈ ℚ⟮I * √2⟯ := by
  rw [← mem_sqrtNegTwoType.1 hψ]
  simpa using apply_mem_adjoin_image ψ.toRatAlgHom (S := {t}) (adjoin_t_eq_top ▸ mem_top)

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
  exact finrank_adjoin_eq_two I_mul_sqrt_two_sq

end TauCeti.EighthCyclotomicCMType
