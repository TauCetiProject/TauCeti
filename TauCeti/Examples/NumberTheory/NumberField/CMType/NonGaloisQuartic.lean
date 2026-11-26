/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.NumberTheory.NumberField.CMType.Primitive.Basic
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic
import Mathlib.Tactic.NormNum.IsSquare
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.IntermediateField.Quadratic

/-!
# A non-Galois quartic CM type and its reflex

Let `a = i √(3 + √2)` and `b = i √(3 - √2)`, the two roots of `X⁴ + 6 X² + 7` in the upper half
plane, so that `a² = -3 - √2`, `b² = -3 + √2` and `a b = -√7`. This file works out the quartic CM
field `E = ℚ(a) ⊆ ℂ` with the CM type `Φ` of the two embeddings sending the generator to `a` and to
`b`. It is the basic example in which the reflex field `E* = ℚ(a + b)` of a primitive CM type is
again a quartic field but is not `E`: `E / ℚ` is not Galois, `Φ` is primitive, and the real
quadratic subfields of `E` and `E*` are the distinct fields `ℚ(√2)` and `ℚ(√7)`. So a reflex field
cannot be identified with the original field by comparing degrees.

* **The roots.** `a_sq`, `b_sq` and `a_mul_b` give `a² = -3 - √2`, `b² = -3 + √2` and
  `a b = -√7`; `aeval_a` and `aeval_b` say that `a` and `b` are roots of `X⁴ + 6 X² + 7`, and
  `a_im_pos`, `b_im_pos` that they lie in the upper half plane. The lower-half-plane root `-b`
  has the same square and is again a root (`neg_b_sq`, `aeval_neg_b`), but `a · (-b) = √7`
  (`a_mul_neg_b`), so these identities alone do not select `b`.
* **The field `E`.** `[E : ℚ] = 4` (`finrank_E`), `a` has minimal polynomial `X⁴ + 6 X² + 7`
  (`minpoly_a`), and the real elements of `E` are those of `ℚ(√2)` (`mem_E_and_im_eq_zero_iff`).
  Since `√7` is real and not in `ℚ(√2)` (`sqrt_seven_notMem_adjoin_sqrt_two`), `b = -√7 / a`
  is not in `E` (`b_notMem_E`), so `E / ℚ` is not normal (`not_normal_E`, `not_isGalois_E`).
* **The embeddings.** Every embedding `E → ℂ` sends the generator to one of `±a`, `±b`
  (`apply_gen_mem`) and is determined by that value (`ringHom_ext`); the inclusion `E.val` and
  `ιb` are the `ℚ`-algebra embeddings with values `a` and `b`. The embeddings with value `a` or
  `b` form a CM type `Φ = {E.val, ιb}` (`Φ`, `coe_Φ`).
* **The reflex field.** The type trace of the generator is `a + b` (`typeTrace_Φ_gen`), and the
  reflex field of `Φ` is `E* = ℚ(a + b)` (`reflexField_Φ`), with `[E* : ℚ] = 4`
  (`finrank_reflexField_Φ`), minimal polynomial `X⁴ + 12 X² + 8` of `a + b`
  (`minpoly_a_add_b`) and real elements those of `ℚ(√7)` (`mem_Estar_and_im_eq_zero_iff`).
  Hence `E* ≠ E` (`Estar_ne_E`).
* **Primitivity.** `Φ` is induced from no proper subfield of `E` (`isPrimitive_Φ`): the reflex
  field of a CM type on a quadratic field has degree two
  (`TauCeti.CMType.finrank_reflexField_of_finrank_eq_two`).

## References

* J. S. Milne, *Complex Multiplication*, §1, pp. 11–19.
-/

public section

open Polynomial IntermediateField Complex Module

namespace TauCeti.NonGaloisQuarticCMType

/-! ### The complex numbers `a` and `b` -/

/-- `a = i √(3 + √2)`, a root of `X⁴ + 6 X² + 7` in the upper half plane. -/
noncomputable def a : ℂ := (√(3 + √2) : ℝ) * I

/-- `b = i √(3 - √2)`, a root of `X⁴ + 6 X² + 7` in the upper half plane. -/
noncomputable def b : ℂ := (√(3 - √2) : ℝ) * I

private theorem sqrt_two_lt_three : √2 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

private theorem sq_sqrt_three_add : √(3 + √2) ^ 2 = 3 + √2 :=
  Real.sq_sqrt (by positivity)

private theorem sq_sqrt_three_sub : √(3 - √2) ^ 2 = 3 - √2 :=
  Real.sq_sqrt (by linarith [sqrt_two_lt_three])

private theorem sqrt_three_add_mul_sqrt_three_sub : √(3 + √2) * √(3 - √2) = √7 := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private theorem ofReal_sqrt_two_sq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem ofReal_sqrt_seven_sq : ((√7 : ℝ) : ℂ) ^ 2 = 7 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

@[simp]
theorem a_re : a.re = 0 := by simp [a]

@[simp]
theorem a_im : a.im = √(3 + √2) := by simp [a]

@[simp]
theorem b_re : b.re = 0 := by simp [b]

@[simp]
theorem b_im : b.im = √(3 - √2) := by simp [b]

/-- `a` lies in the upper half plane. -/
theorem a_im_pos : 0 < a.im := by
  rw [a_im]
  exact Real.sqrt_pos.2 (by positivity)

/-- `b` lies in the upper half plane. -/
theorem b_im_pos : 0 < b.im := by
  rw [b_im]
  exact Real.sqrt_pos.2 (by linarith [sqrt_two_lt_three])

/-- `-b` lies in the lower half plane. -/
theorem neg_b_im_neg : (-b).im < 0 := by
  rw [neg_im]
  exact neg_neg_of_pos b_im_pos

/-- `a² = -3 - √2`. -/
theorem a_sq : a ^ 2 = -3 - (√2 : ℝ) := by
  rw [a, mul_pow, I_sq, ← ofReal_pow, sq_sqrt_three_add]
  push_cast
  ring

/-- `b² = -3 + √2`. -/
theorem b_sq : b ^ 2 = -3 + (√2 : ℝ) := by
  rw [b, mul_pow, I_sq, ← ofReal_pow, sq_sqrt_three_sub]
  push_cast
  ring

/-- The lower-half-plane root `-b` has the same square as `b`. -/
theorem neg_b_sq : (-b) ^ 2 = -3 + (√2 : ℝ) := by
  rw [neg_sq, b_sq]

/-- `a b = -√7`. -/
theorem a_mul_b : a * b = -(√7 : ℝ) := by
  rw [a, b, mul_mul_mul_comm, I_mul_I, ← ofReal_mul, sqrt_three_add_mul_sqrt_three_sub]
  ring

/-- Replacing `b` by the lower-half-plane root `-b` reverses the sign of the product. -/
theorem a_mul_neg_b : a * -b = (√7 : ℝ) := by
  rw [mul_neg, a_mul_b, neg_neg]

private theorem pow_four_of_sq_eq {z : ℂ} {s : ℝ} (hs : s ^ 2 = 2)
    (hz : z ^ 2 = -3 + (s : ℂ)) : z ^ 4 + 6 * z ^ 2 + 7 = 0 := by
  have hs' : (s : ℂ) ^ 2 = 2 := by exact_mod_cast hs
  linear_combination (z ^ 2 + 3 + (s : ℂ)) * hz + hs'

private theorem a_pow_four : a ^ 4 + 6 * a ^ 2 + 7 = 0 :=
  pow_four_of_sq_eq (s := -√2) (by rw [neg_sq, Real.sq_sqrt (by norm_num)])
    (by rw [a_sq]; push_cast; ring)

private theorem b_pow_four : b ^ 4 + 6 * b ^ 2 + 7 = 0 :=
  pow_four_of_sq_eq (Real.sq_sqrt (by norm_num)) b_sq

/-- `a` is a root of `X⁴ + 6 X² + 7`. -/
theorem aeval_a : aeval a (X ^ 4 + C 6 * X ^ 2 + C 7 : ℚ[X]) = 0 := by
  simpa using a_pow_four

/-- `b` is a root of `X⁴ + 6 X² + 7`. -/
theorem aeval_b : aeval b (X ^ 4 + C 6 * X ^ 2 + C 7 : ℚ[X]) = 0 := by
  simpa using b_pow_four

/-- The lower-half-plane root `-b` is also a root of `X⁴ + 6 X² + 7`. -/
theorem aeval_neg_b : aeval (-b) (X ^ 4 + C 6 * X ^ 2 + C 7 : ℚ[X]) = 0 := by
  simpa [neg_pow, Even.neg_pow (by decide : Even 4)] using b_pow_four

/-- `(a + b)² = -6 - 2√7`. -/
theorem a_add_b_sq : (a + b) ^ 2 = -6 - 2 * (√7 : ℝ) := by
  linear_combination a_sq + b_sq + 2 * a_mul_b

private theorem a_add_b_pow_four : (a + b) ^ 4 + 12 * (a + b) ^ 2 + 8 = 0 := by
  linear_combination ((a + b) ^ 2 + 6 - 2 * (√7 : ℝ)) * a_add_b_sq +
    4 * ofReal_sqrt_seven_sq

/-- `a + b` is a root of `X⁴ + 12 X² + 8`. -/
theorem aeval_a_add_b : aeval (a + b) (X ^ 4 + C 12 * X ^ 2 + C 8 : ℚ[X]) = 0 := by
  simpa using a_add_b_pow_four

/-! ### Real quadratic subfields of `ℂ` -/

/-- `ℝ`, as an intermediate field of `ℂ / ℚ`. -/
private noncomputable abbrev realField : IntermediateField ℚ ℂ :=
  (ofRealAm.restrictScalars ℚ).fieldRange

private theorem mem_realField_iff {x : ℂ} : x ∈ realField ↔ x.im = 0 := by
  refine ⟨?_, fun h ↦ ⟨x.re, Complex.ext (by simp) (by simp [h])⟩⟩
  rintro ⟨r, rfl⟩
  simp

private theorem ofReal_mem_realField (r : ℝ) : (r : ℂ) ∈ realField :=
  mem_realField_iff.2 (ofReal_im r)

private theorem finrank_adjoin_sqrt_two : finrank ℚ ℚ⟮((√2 : ℝ) : ℂ)⟯ = 2 :=
  TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
    (ofReal_sqrt_two_sq.trans (map_ofNat _ 2).symm) (by norm_num)

private theorem finrank_adjoin_sqrt_seven : finrank ℚ ℚ⟮((√7 : ℝ) : ℂ)⟯ = 2 :=
  TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
    (ofReal_sqrt_seven_sq.trans (map_ofNat _ 7).symm) (by norm_num)

/-- **The real quadratic fields `ℚ(√2)` and `ℚ(√7)` are distinct**, since `2 · 7` is not a
square. -/
theorem adjoin_sqrt_two_ne_adjoin_sqrt_seven :
    ℚ⟮((√2 : ℝ) : ℂ)⟯ ≠ ℚ⟮((√7 : ℝ) : ℂ)⟯ := fun h ↦ by
  have h14 := TauCeti.IntermediateField.isSquare_mul_of_adjoin_simple_eq
    (ofReal_sqrt_two_sq.trans (map_ofNat _ 2).symm)
    (ofReal_sqrt_seven_sq.trans (map_ofNat _ 7).symm) h
  norm_num at h14

/-- **`√7 ∉ ℚ(√2)`**, since `ℚ(√2)` and `ℚ(√7)` are distinct quadratic fields. -/
theorem sqrt_seven_notMem_adjoin_sqrt_two : ((√7 : ℝ) : ℂ) ∉ ℚ⟮((√2 : ℝ) : ℂ)⟯ := fun h ↦ by
  have : FiniteDimensional ℚ ℚ⟮((√2 : ℝ) : ℂ)⟯ :=
    .of_finrank_pos (finrank_adjoin_sqrt_two.symm ▸ two_pos)
  exact adjoin_sqrt_two_ne_adjoin_sqrt_seven (eq_of_le_of_finrank_eq (adjoin_simple_le_iff.2 h)
    (finrank_adjoin_sqrt_seven.trans finrank_adjoin_sqrt_two.symm)).symm

/-- Let `K ⊆ L ⊆ ℂ` with `K` real quadratic and `L` nonreal of degree at most four. Then `L` is
quartic and its real elements are those of `K`. -/
private theorem finrank_eq_four_and_inf_realField_eq {K L : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ L] (hKL : K ≤ L) (hK : finrank ℚ K = 2) (hKR : K ≤ realField)
    (hLR : ¬L ≤ realField) (hL : finrank ℚ L ≤ 4) :
    finrank ℚ L = 4 ∧ L ⊓ realField = K := by
  have hL4 : finrank ℚ L = 4 := by
    have h2 : 2 ∣ finrank ℚ L := hK ▸ finrank_dvd_of_le_right hKL
    have hne : finrank ℚ L ≠ 2 := fun h ↦ hLR (eq_of_le_of_finrank_eq hKL (hK.trans h.symm) ▸ hKR)
    have hpos : 0 < finrank ℚ L := finrank_pos
    omega
  refine ⟨hL4, (eq_of_le_of_finrank_eq (le_inf hKL hKR) ?_).symm⟩
  have hM : finrank ℚ ↥(L ⊓ realField) ∣ 4 := hL4 ▸ finrank_dvd_of_le_right inf_le_left
  have h2 : 2 ∣ finrank ℚ ↥(L ⊓ realField) := hK ▸ finrank_dvd_of_le_right (le_inf hKL hKR)
  have hne : finrank ℚ ↥(L ⊓ realField) ≠ 4 := fun h ↦
    hLR ((eq_of_le_of_finrank_eq inf_le_left (h.trans hL4.symm)) ▸ inf_le_right)
  have hle := Nat.le_of_dvd (by norm_num) hM
  have hpos : 0 < finrank ℚ ↥(L ⊓ realField) := Nat.pos_of_dvd_of_pos hM (by norm_num)
  omega

/-! ### The field `E = ℚ(a)` -/

/-- The quartic CM field `E = ℚ(a) ⊆ ℂ`. -/
noncomputable abbrev E : IntermediateField ℚ ℂ := ℚ⟮a⟯

private theorem monic_quartic_a : (X ^ 4 + C 6 * X ^ 2 + C 7 : ℚ[X]).Monic := by monicity!

private theorem natDegree_quartic_a : (X ^ 4 + C 6 * X ^ 2 + C 7 : ℚ[X]).natDegree = 4 := by
  compute_degree!

theorem isIntegral_a : IsIntegral ℚ a := ⟨_, monic_quartic_a, aeval_a⟩

instance : FiniteDimensional ℚ E := adjoin.finiteDimensional isIntegral_a

/-- `√2 = -3 - a² ∈ E`. -/
theorem sqrt_two_mem_E : ((√2 : ℝ) : ℂ) ∈ E := by
  rw [show ((√2 : ℝ) : ℂ) = -3 - a ^ 2 by rw [a_sq]; ring]
  exact sub_mem (by simp) (pow_mem (mem_adjoin_simple_self ℚ a) 2)

private theorem finrank_E_and_inf_realField :
    finrank ℚ E = 4 ∧ E ⊓ realField = ℚ⟮((√2 : ℝ) : ℂ)⟯ :=
  finrank_eq_four_and_inf_realField_eq (adjoin_simple_le_iff.2 sqrt_two_mem_E)
    finrank_adjoin_sqrt_two (adjoin_simple_le_iff.2 (ofReal_mem_realField _))
    (fun h ↦ a_im_pos.ne' (mem_realField_iff.1 (h (mem_adjoin_simple_self ℚ a))))
    ((TauCeti.IntermediateField.finrank_adjoin_simple_le_natDegree
      monic_quartic_a.ne_zero aeval_a).trans natDegree_quartic_a.le)

/-- **`[E : ℚ] = 4`.** -/
theorem finrank_E : finrank ℚ E = 4 :=
  finrank_E_and_inf_realField.1

/-- **The minimal polynomial of `a` is `X⁴ + 6 X² + 7`.** -/
theorem minpoly_a : minpoly ℚ a = X ^ 4 + C 6 * X ^ 2 + C 7 :=
  TauCeti.IntermediateField.minpoly_eq_of_natDegree_le_finrank_adjoin_simple monic_quartic_a
    aeval_a (natDegree_quartic_a.trans finrank_E.symm).le

/-- **The real elements of `E` are those of `ℚ(√2)`.** -/
theorem mem_E_and_im_eq_zero_iff {x : ℂ} : x ∈ E ∧ x.im = 0 ↔ x ∈ ℚ⟮((√2 : ℝ) : ℂ)⟯ := by
  rw [← finrank_E_and_inf_realField.2, mem_inf, mem_realField_iff]

/-- **`b ∉ E`**: otherwise the real number `√7 = -a b` would lie in the real subfield `ℚ(√2)`
of `E`. -/
theorem b_notMem_E : b ∉ E := fun hb ↦ by
  have h7 : ((√7 : ℝ) : ℂ) ∈ E := by
    rw [show ((√7 : ℝ) : ℂ) = -(a * b) by rw [a_mul_b, neg_neg]]
    exact neg_mem (mul_mem (mem_adjoin_simple_self ℚ a) hb)
  exact sqrt_seven_notMem_adjoin_sqrt_two (mem_E_and_im_eq_zero_iff.1 ⟨h7, ofReal_im _⟩)

/-! ### The field `E* = ℚ(a + b)` -/

/-- The quartic CM field `E* = ℚ(a + b) ⊆ ℂ`, the reflex field of `Φ` (`reflexField_Φ`). -/
noncomputable abbrev Estar : IntermediateField ℚ ℂ := ℚ⟮a + b⟯

private theorem monic_quartic_a_add_b : (X ^ 4 + C 12 * X ^ 2 + C 8 : ℚ[X]).Monic := by
  monicity!

private theorem natDegree_quartic_a_add_b :
    (X ^ 4 + C 12 * X ^ 2 + C 8 : ℚ[X]).natDegree = 4 := by
  compute_degree!

theorem isIntegral_a_add_b : IsIntegral ℚ (a + b) := ⟨_, monic_quartic_a_add_b, aeval_a_add_b⟩

instance : FiniteDimensional ℚ Estar := adjoin.finiteDimensional isIntegral_a_add_b

/-- `√7 = -((a + b)² + 6) / 2 ∈ E*`. -/
theorem sqrt_seven_mem_Estar : ((√7 : ℝ) : ℂ) ∈ Estar := by
  rw [show ((√7 : ℝ) : ℂ) = -((a + b) ^ 2 + 6) / 2 by rw [a_add_b_sq]; ring]
  exact div_mem (neg_mem (add_mem (pow_mem (mem_adjoin_simple_self ℚ _) 2) (by simp))) (by simp)

private theorem finrank_Estar_and_inf_realField :
    finrank ℚ Estar = 4 ∧ Estar ⊓ realField = ℚ⟮((√7 : ℝ) : ℂ)⟯ :=
  finrank_eq_four_and_inf_realField_eq (adjoin_simple_le_iff.2 sqrt_seven_mem_Estar)
    finrank_adjoin_sqrt_seven (adjoin_simple_le_iff.2 (ofReal_mem_realField _))
    (fun h ↦ (add_pos a_im_pos b_im_pos).ne'
      (by simpa using mem_realField_iff.1 (h (mem_adjoin_simple_self ℚ (a + b)))))
    ((TauCeti.IntermediateField.finrank_adjoin_simple_le_natDegree
      monic_quartic_a_add_b.ne_zero aeval_a_add_b).trans natDegree_quartic_a_add_b.le)

/-- **`[E* : ℚ] = 4`.** -/
theorem finrank_Estar : finrank ℚ Estar = 4 :=
  finrank_Estar_and_inf_realField.1

/-- **The minimal polynomial of `a + b` is `X⁴ + 12 X² + 8`.** -/
theorem minpoly_a_add_b : minpoly ℚ (a + b) = X ^ 4 + C 12 * X ^ 2 + C 8 :=
  TauCeti.IntermediateField.minpoly_eq_of_natDegree_le_finrank_adjoin_simple
    monic_quartic_a_add_b aeval_a_add_b (natDegree_quartic_a_add_b.trans finrank_Estar.symm).le

/-- **The real elements of `E*` are those of `ℚ(√7)`.** -/
theorem mem_Estar_and_im_eq_zero_iff {x : ℂ} :
    x ∈ Estar ∧ x.im = 0 ↔ x ∈ ℚ⟮((√7 : ℝ) : ℂ)⟯ := by
  rw [← finrank_Estar_and_inf_realField.2, mem_inf, mem_realField_iff]

/-- **`E* ≠ E`**: the real number `√7` lies in `E*` but not in `E`. -/
theorem Estar_ne_E : Estar ≠ E := fun h ↦
  sqrt_seven_notMem_adjoin_sqrt_two
    (mem_E_and_im_eq_zero_iff.1 ⟨h ▸ sqrt_seven_mem_Estar, ofReal_im _⟩)

/-! ### The complex embeddings of `E` -/

/-- The generator `a` of `E`. -/
noncomputable abbrev gen : E := AdjoinSimple.gen ℚ a

private theorem gen_pow_four : gen ^ 4 + 6 * gen ^ 2 + 7 = 0 :=
  (algebraMap E ℂ).injective (by
    simpa only [map_add, map_mul, map_pow, map_ofNat, AdjoinSimple.algebraMap_gen, map_zero]
      using a_pow_four)

/-- The embedding `E → ℂ` taking the generator to `b`. -/
noncomputable def ιb : E →ₐ[ℚ] ℂ :=
  (adjoin.powerBasis isIntegral_a).lift b (by
    rw [adjoin.powerBasis_gen, minpoly_gen, minpoly_a]
    exact aeval_b)

@[simp]
theorem ιb_gen : ιb gen = b :=
  PowerBasis.lift_gen _ _ _

/-- A complex embedding of `E` is determined by its value at the generator. -/
theorem ringHom_ext {ψ₁ ψ₂ : E →+* ℂ} (h : ψ₁ gen = ψ₂ gen) : ψ₁ = ψ₂ := by
  have := (adjoin.powerBasis isIntegral_a).algHom_ext (f := ψ₁.toRatAlgHom)
    (g := ψ₂.toRatAlgHom) h
  exact RingHom.ext fun x ↦ by
    rw [← RingHom.toRatAlgHom_apply, ← RingHom.toRatAlgHom_apply, this]

/-- **Every complex embedding of `E`** sends the generator to one of `a`, `-a`, `b`, `-b`. -/
theorem apply_gen_mem (ψ : E →+* ℂ) : ψ gen ∈ ({a, -a, b, -b} : Set ℂ) := by
  have h := congrArg ψ gen_pow_four
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
  have : (ψ gen - a) * (ψ gen + a) * ((ψ gen - b) * (ψ gen + b)) = 0 := by
    linear_combination h - ψ gen ^ 2 * (a_sq + b_sq) + (a * b - (√7 : ℝ)) * a_mul_b +
      ofReal_sqrt_seven_sq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_eq_zero.1 this with h | h <;> rcases mul_eq_zero.1 h with h | h
  · exact .inl (sub_eq_zero.1 h)
  · exact .inr (.inl (eq_neg_of_add_eq_zero_left h))
  · exact .inr (.inr (.inl (sub_eq_zero.1 h)))
  · exact .inr (.inr (.inr (eq_neg_of_add_eq_zero_left h)))

/-! ### Non-normality -/

/-- **`E / ℚ` is not normal**: the embedding `ιb` moves `E` off itself, since `b ∉ E`. -/
theorem not_normal_E : ¬Normal ℚ E := fun _ ↦
  b_notMem_E (AlgHom.fieldRange_of_normal ιb ▸ ⟨gen, ιb_gen⟩)

/-- **`E / ℚ` is not Galois.** -/
theorem not_isGalois_E : ¬IsGalois ℚ E := fun h ↦ not_normal_E h.to_normal

/-! ### The CM type `Φ` -/

private theorem a_ne_b : a ≠ b := fun h ↦ by
  have h' := a_sq
  rw [h, b_sq] at h'
  have h2 : ((√2 : ℝ) : ℂ) = 0 := by linear_combination h' / 2
  exact (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne' (ofReal_eq_zero.1 h2)

private theorem conj_a : (starRingEnd ℂ) a = -a := by simp [a]

private theorem conj_b : (starRingEnd ℂ) b = -b := by simp [b]

/-- **The CM type `Φ` of `E`**: the embeddings sending the generator to `a` or to `b`, the two
roots of `X⁴ + 6 X² + 7` in the upper half plane. -/
noncomputable def Φ : CMType E where
  carrier := {ψ | ψ gen = a ∨ ψ gen = b}
  star_mem_iff' ψ := by
    simp only [Set.mem_ofPred_eq, RingHom.star_apply]
    have hab := a_ne_b
    -- Negation swaps the half planes, so `-a` and `-b` differ from `a` and `b`.
    have him {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : -w ≠ z := fun h ↦ by
      have := congrArg im h
      rw [neg_im] at this
      linarith
    have h₁ := him a_im_pos a_im_pos
    have h₂ := him a_im_pos b_im_pos
    have h₃ := him b_im_pos a_im_pos
    have h₄ := him b_im_pos b_im_pos
    have h := apply_gen_mem ψ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h <;>
      simp [h, conj_a, conj_b, hab, hab.symm, h₁, h₂, h₃, h₄]

@[simp]
theorem mem_Φ_iff {ψ : E →+* ℂ} : ψ ∈ Φ ↔ ψ gen = a ∨ ψ gen = b :=
  Iff.rfl

/-- `Φ` consists of the inclusion `E.val` and the embedding `ιb`. -/
theorem coe_Φ : (Φ : Set (E →+* ℂ)) = {(E.val : E →+* ℂ), (ιb : E →+* ℂ)} := by
  ext ψ
  rw [SetLike.mem_coe, mem_Φ_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨Or.imp (fun h ↦ ringHom_ext (by simpa using h)) (fun h ↦ ringHom_ext (by simpa using h)),
    Or.imp (fun h ↦ by simp [h]) (fun h ↦ by simp [h])⟩

private theorem val_ne_ιb : (E.val : E →+* ℂ) ≠ ιb := fun h ↦
  a_ne_b (by simpa using congrArg (· gen) h)

/-- The type trace of `Φ` at `x ∈ E` is `x + ιb x`. -/
@[simp]
theorem typeTrace_Φ (x : E) : Φ.typeTrace x = x + ιb x := by
  rw [CMType.typeTrace_apply, coe_Φ, finsum_mem_pair val_ne_ιb, AlgHom.coe_toRingHom,
    AlgHom.coe_toRingHom, coe_val]

/-- The type trace of the `n`th power of the generator is `aⁿ + bⁿ`. -/
theorem typeTrace_Φ_gen_pow (n : ℕ) : Φ.typeTrace (gen ^ n) = a ^ n + b ^ n := by
  simp

/-- **The type trace of the generator is `a + b`.** -/
theorem typeTrace_Φ_gen : Φ.typeTrace gen = a + b := by
  simp

/-! ### The reflex field -/

/-- The power sums `aⁿ + bⁿ` lie in `ℚ(a + b)`, by the recursion
`aⁿ⁺² + bⁿ⁺² = (a + b)(aⁿ⁺¹ + bⁿ⁺¹) - a b (aⁿ + bⁿ)` with `a b = -√7 ∈ ℚ(a + b)`. -/
private theorem pow_add_pow_mem_Estar (n : ℕ) : a ^ n + b ^ n ∈ Estar := by
  have hs : a + b ∈ Estar := mem_adjoin_simple_self ℚ _
  have hab : a * b ∈ Estar := by
    rw [a_mul_b]
    exact neg_mem sqrt_seven_mem_Estar
  suffices ∀ n, a ^ n + b ^ n ∈ Estar ∧ a ^ (n + 1) + b ^ (n + 1) ∈ Estar from (this n).1
  intro n
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, zero_add, pow_one, pow_one]
    exact ⟨add_mem (one_mem _) (one_mem _), hs⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show a ^ (n + 1 + 1) + b ^ (n + 1 + 1) =
      (a + b) * (a ^ (n + 1) + b ^ (n + 1)) - a * b * (a ^ n + b ^ n) by ring]
    exact sub_mem (mul_mem hs ih.2) (mul_mem hab ih.1)

/-- **The reflex field of `Φ` is `E* = ℚ(a + b)`.** -/
theorem reflexField_Φ : Φ.reflexField = Estar := by
  have hspan : Submodule.span ℚ (Set.range (gen ^ · : ℕ → E)) = ⊤ := by
    refine top_unique ((adjoin.powerBasis isIntegral_a).basis.span_eq.ge.trans
      (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨i, by simp⟩
  rw [Φ.reflexField_eq_adjoin_of_span_eq_top hspan, ← Set.range_comp]
  refine le_antisymm (adjoin_le_iff.2 ?_) (adjoin_simple_le_iff.2 (subset_adjoin ℚ _ ⟨1, ?_⟩))
  · rintro _ ⟨n, rfl⟩
    simpa [typeTrace_Φ_gen_pow] using pow_add_pow_mem_Estar n
  · simp

/-- **The reflex field of `Φ` has degree four.** -/
theorem finrank_reflexField_Φ : finrank ℚ Φ.reflexField = 4 := by
  rw [reflexField_Φ, finrank_Estar]

/-! ### Primitivity -/

/-- `E` is a number field. -/
instance : NumberField E where

/-- **`Φ` is primitive**: it is not induced from any proper subfield of `E`. -/
theorem isPrimitive_Φ : Φ.IsPrimitive := by
  rw [CMType.isPrimitive_iff]
  rintro F ⟨Φ₀, hΦ₀⟩
  have hdvd : finrank ℚ F ∣ 4 := by
    have := finrank_dvd_of_le_right (le_top : F ≤ ⊤)
    rwa [finrank_top', finrank_E] at this
  by_cases h4 : finrank ℚ F = 4
  · exact eq_of_le_of_finrank_eq le_top (by rw [finrank_top', finrank_E, h4])
  exfalso
  -- `F` carries the CM type `Φ₀`, so it is quadratic, and then so is the reflex field of `Φ₀`,
  -- which is that of `Φ`.
  have hcard := Φ₀.two_mul_card_eq_finrank
  have hF : finrank ℚ F = 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases finrank ℚ F <;> omega
  have h := Φ₀.finrank_reflexField_of_finrank_eq_two hF
  rw [← CMType.reflexField_induced (L := E), hΦ₀, finrank_reflexField_Φ] at h
  omega

end TauCeti.NonGaloisQuarticCMType
