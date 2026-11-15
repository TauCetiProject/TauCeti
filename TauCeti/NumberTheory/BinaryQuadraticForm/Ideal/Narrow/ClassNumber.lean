/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Narrow.Equivalence
public import TauCeti.NumberTheory.BinaryQuadraticForm.IndefiniteReduction.Cycles
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.OrderOfConductor
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import TauCeti.Data.Int.Sqrt
import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.DiscriminantTwelve
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger
import TauCeti.NumberTheory.NumberField.Global.Orders.Functoriality
import TauCeti.NumberTheory.NumberField.Global.Orders.Maximal
import TauCeti.NumberTheory.NumberField.Global.Orders.NarrowPic.RayClass

/-!
# Narrow class numbers of real quadratic orders from Gauss cycles

For a positive nonsquare discriminant `D ≡ 0, 1 (mod 4)`, proper equivalence classes of primitive
binary quadratic forms of discriminant `D` are in canonical bijection both with the narrow Picard
group of the quadratic order of discriminant `D` (`properClassEquivNarrowPic`) and with the cycles
of Gauss's reduction operator `primitiveReductionPerm D`
(`primitiveGaussReducedCyclesEquivProperClasses`). Composing the two identifies
`PrimitiveGaussReducedCycle D` with `NarrowPic (QuadraticOrder.numberFieldOrder D hD)`, so the
order of the narrow Picard group equals the number of primitive Gauss cycles of discriminant `D`.

When `D` is a fundamental discriminant, `QuadraticOrder.numberFieldOrder D` is the maximal order of
`ℚ(√D)` (`QuadraticOrder.numberFieldOrder_eq_maximal_iff`), whose narrow Picard group is the narrow
class group `NumberField.NarrowClassGroup ℚ(√D)` (`GlobalNumberFields.maximalOrderNarrowPicEquiv`).
More generally, in any quadratic number field `K` with `f² discr K = D`, evaluation at
`f √(discr K)` identifies the order of discriminant `D` in `ℚ(√D)` with the order `ℤ + f 𝓞 K` of
conductor `f` in `K` (`QuadraticOrder.numberFieldOrderOfSqrt_eq_intAddMulOrder`), transporting the
narrow Picard count to `ℤ + f 𝓞 K` and, at `f = 1`, to `NarrowClassGroup K`.

As certified examples:
* At `D = 5`, the two primitive Gauss reduced forms `x² + x y - y²` and `-x² + x y + y²` form a
  single `2`-cycle, so `ℚ(√5)` has narrow class number `1` and wide class number `1`.
* At `D = 12`, the four primitive Gauss reduced forms split into two `2`-cycles,
  `x² + 2 x y - 2 y² ↔ -2 x² + 2 x y + y²` and `-x² + 2 x y + 2 y² ↔ 2 x² + 2 x y - y²`, so
  `ℚ(√12) = ℚ(√3)` has narrow class number `2`, while the nontrivial narrow principal class of
  `√12` forces its wide class number to be `1`.

## Main definitions and results

* `TauCeti.BinaryQuadraticForm.primitiveGaussReducedCyclesEquivNarrowPic`: bijection between
  `PrimitiveGaussReducedCycle D` and `NarrowPic (QuadraticOrder.numberFieldOrder D hD)`.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowPic`: the narrow Picard group of the quadratic order
  of discriminant `D` has `Fintype.card (PrimitiveGaussReducedCycle D)` elements.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup_eq_card_primitiveGaussReducedCycle`: for a
  positive nonsquare fundamental discriminant `D`, `Nat.card (NarrowClassGroup ℚ(√D))` equals
  `Fintype.card (PrimitiveGaussReducedCycle D)`.
* `TauCeti.BinaryQuadraticForm.card_narrowPic_intAddMulOrder_eq_card_primitiveGaussReducedCycle`:
  if `f² discr K = D > 0` in a quadratic field `K`, then `Nat.card (NarrowPic (ℤ + f 𝓞 K))` equals
  `Fintype.card (PrimitiveGaussReducedCycle D)`.
* `card_narrowClassGroup_eq_card_primitiveGaussReducedCycle_of_discr_eq`:
  the narrow class number of any quadratic field of positive discriminant `D` equals
  `Fintype.card (PrimitiveGaussReducedCycle D)`.
* `TauCeti.BinaryQuadraticForm.classNumber_eq_one_of_card_primitiveGaussReducedCycle_eq_one`: a
  single primitive Gauss cycle at discriminant `D = discr K` forces
  `NumberField.classNumber K = 1`.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup_five_eq_one`,
  `TauCeti.BinaryQuadraticForm.classNumber_five_eq_one`: `ℚ(√5)` has narrow and wide class number
  `1`.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup_twelve_eq_two`,
  `TauCeti.BinaryQuadraticForm.classNumber_twelve_eq_one`: `ℚ(√12)` has narrow class number `2` and
  wide class number `1`.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 183–197.
* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.6–5.7.
-/

public section
noncomputable section

open scoped NumberField

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

section Order

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)]

/-- **Cycles of primitive Gauss reduced forms classify the narrow Picard group.** For a positive
nonsquare discriminant `D ≡ 0, 1 (mod 4)`, the cycles of `primitiveReductionPerm D` are in
canonical bijection with the narrow Picard group of the quadratic order of discriminant `D`. -/
def primitiveGaussReducedCyclesEquivNarrowPic (hpos : 0 < D) :
    PrimitiveGaussReducedCycle D ≃ NarrowPic (QuadraticOrder.numberFieldOrder D hD) :=
  (primitiveGaussReducedCyclesEquivProperClasses D hpos).trans
    (properClassEquivNarrowPic D hD hpos)

/-- Applying `primitiveGaussReducedCyclesEquivNarrowPic` sends a cycle to the narrow Picard class
of its proper equivalence class. -/
@[simp] theorem primitiveGaussReducedCyclesEquivNarrowPic_apply (hpos : 0 < D)
    (c : PrimitiveGaussReducedCycle D) :
    primitiveGaussReducedCyclesEquivNarrowPic D hD hpos c =
      properClassToNarrowPic D hD (primitiveGaussReducedCycleToProperClass D c) := by
  simp [primitiveGaussReducedCyclesEquivNarrowPic]

/-- On the cycle of a primitive Gauss reduced form `f`,
`primitiveGaussReducedCyclesEquivNarrowPic` evaluates to the oriented narrow class of `f`. -/
theorem primitiveGaussReducedCyclesEquivNarrowPic_mk (hpos : 0 < D)
    (f : primitiveGaussReducedForms D) :
    primitiveGaussReducedCyclesEquivNarrowPic D hD hpos (Quotient.mk _ f) =
      f.1.narrowPicClass D (mem_primitiveGaussReducedForms.mp f.2).1
        (mem_primitiveGaussReducedForms.mp f.2).2.2 := by
  simp

/-- **The order of the narrow Picard group** of the quadratic order of positive nonsquare
discriminant `D` equals the number of cycles of `primitiveReductionPerm D`. -/
theorem nat_card_narrowPic (hpos : 0 < D) :
    Nat.card (NarrowPic (QuadraticOrder.numberFieldOrder D hD)) =
      Fintype.card (PrimitiveGaussReducedCycle D) := by
  rw [Nat.card_congr (primitiveGaussReducedCyclesEquivNarrowPic D hD hpos).symm,
    Nat.card_eq_fintype_card]

end Order

section Fundamental

/-- **The narrow class number of a real quadratic model counts primitive Gauss cycles.** For a
positive nonsquare fundamental discriminant `D`, the narrow class group of `ℚ(√D)` has
`Fintype.card (PrimitiveGaussReducedCycle D)` elements. -/
theorem nat_card_narrowClassGroup_eq_card_primitiveGaussReducedCycle
    {D : ℤ} [Fact (¬ IsSquare D)] (hfund : Int.IsFundamentalDiscr D) (hpos : 0 < D) :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ (D : ℚ) 0)) =
      Fintype.card (PrimitiveGaussReducedCycle D) := by
  rw [← Nat.card_congr (maximalOrderNarrowPicEquiv _).toEquiv,
    ← (QuadraticOrder.numberFieldOrder_eq_maximal_iff D hfund.emod_four_eq_zero_or_one).mpr hfund,
    nat_card_narrowPic D hfund.emod_four_eq_zero_or_one hpos]

end Fundamental

section Conductor

/-- An isomorphism of number fields identifying two orders induces an isomorphism of their narrow
Picard groups via `NumberFieldOrder.Hom.mapNarrowPic`. -/
private def narrowPicMulEquivOfRingEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] {O : NumberFieldOrder K} {O' : NumberFieldOrder L}
    (e : K ≃+* L) (h : ∀ x : K, e x ∈ O'.toSubalgebra ↔ x ∈ O.toSubalgebra) :
    NarrowPic O ≃* NarrowPic O' :=
  let φ : NumberFieldOrder.Hom O O' := ⟨e.toRingHom, fun {x} hx ↦ (h x).mpr hx⟩
  let ψ : NumberFieldOrder.Hom O' O :=
    ⟨e.symm.toRingHom, fun {y} hy ↦ (h (e.symm y)).mp (by simpa using hy)⟩
  MonoidHom.toMulEquiv φ.mapNarrowPic ψ.mapNarrowPic
    (by
      rw [← NumberFieldOrder.Hom.mapNarrowPic_comp]
      have hid : ψ.comp φ = NumberFieldOrder.Hom.id O :=
        NumberFieldOrder.Hom.ext fun x ↦ by simp [φ, ψ]
      rw [hid, NumberFieldOrder.Hom.mapNarrowPic_id])
    (by
      rw [← NumberFieldOrder.Hom.mapNarrowPic_comp]
      have hid : φ.comp ψ = NumberFieldOrder.Hom.id O' :=
        NumberFieldOrder.Hom.ext fun y ↦ by simp [φ, ψ]
      rw [hid, NumberFieldOrder.Hom.mapNarrowPic_id])

variable {K : Type*} [Field K] [NumberField K]

/-- **Narrow Picard numbers of real quadratic orders of conductor `f` from Gauss cycles.** Let `K`
be a quadratic field and `f ≥ 1` with `f² discr K = D > 0`. The narrow Picard group of the order
`ℤ + f 𝓞 K` of conductor `f` has `Fintype.card (PrimitiveGaussReducedCycle D)` elements. -/
theorem card_narrowPic_intAddMulOrder_eq_card_primitiveGaussReducedCycle
    (hK : Module.finrank ℚ K = 2) {f : ℕ} [NeZero f] {D : ℤ} [Fact (¬ IsSquare D)]
    (hpos : 0 < D) (hD : (f : ℤ) ^ 2 * NumberField.discr K = D) :
    Nat.card (NarrowPic (intAddMulOrder K f)) =
      Fintype.card (PrimitiveGaussReducedCycle D) := by
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := by
    rw [← hD, Int.mul_emod, Int.sq_emod_four]
    rcases TauCeti.NumberField.discr_emod_four_eq_zero_or_one K with h | h <;>
      rcases Int.emod_two_eq_zero_or_one (f : ℤ) with h' | h' <;> simp [h, h']
  obtain ⟨δ, hδ⟩ := Multiquadratic.exists_sq_eq_discr hK
  have hfδ : ((f : K) * δ) ^ 2 = (D : K) := by
    rw [mul_pow, hδ, ← hD]
    push_cast
    ring
  rw [← QuadraticOrder.numberFieldOrderOfSqrt_eq_intAddMulOrder hK hD4 hD.symm _ hfδ,
    ← nat_card_narrowPic D hD4 hpos]
  let e := QuadraticOrder.algEquivOfSqrt D ((f : K) * δ) hfδ hK
  refine (Nat.card_congr (narrowPicMulEquivOfRingEquiv e.toRingEquiv fun x ↦ ?_).toEquiv).symm
  rw [QuadraticOrder.numberFieldOrderOfSqrt_toSubalgebra,
    QuadraticOrder.numberFieldOrder_toSubalgebra, Subalgebra.mem_map]
  exact ⟨fun ⟨z, hz, hzx⟩ ↦ e.injective hzx ▸ hz, fun hx ↦ ⟨x, hx, rfl⟩⟩

/-- **Narrow class numbers of real quadratic fields from Gauss cycles.** Any quadratic number field
`K` of positive discriminant `D` has narrow class number
`Fintype.card (PrimitiveGaussReducedCycle D)`. -/
theorem card_narrowClassGroup_eq_card_primitiveGaussReducedCycle_of_discr_eq
    (hK : Module.finrank ℚ K = 2) {D : ℤ} [Fact (¬ IsSquare D)] (hpos : 0 < D)
    (hD : NumberField.discr K = D) :
    Nat.card (NumberField.NarrowClassGroup K) =
      Fintype.card (PrimitiveGaussReducedCycle D) := by
  rw [← Nat.card_congr (maximalOrderNarrowPicEquiv K).toEquiv,
    ← NumberFieldOrder.intAddMulOrder_one,
    card_narrowPic_intAddMulOrder_eq_card_primitiveGaussReducedCycle hK hpos
      (by simpa using hD)]

end Conductor

section Examples

private theorem isFundamentalDiscr_five : Int.IsFundamentalDiscr 5 := by
  rw [show (5 : ℤ) = 4 * 1 + 1 by norm_num, Int.isFundamentalDiscr_four_mul_add_one]
  exact Int.squarefree_natAbs.mp (by norm_num : Nat.Prime 5).squarefree

private theorem isFundamentalDiscr_twelve : Int.IsFundamentalDiscr 12 := by
  rw [show (12 : ℤ) = 4 * 3 by norm_num, Int.isFundamentalDiscr_four_mul]
  exact ⟨Int.squarefree_natAbs.mp (by norm_num : Nat.Prime 3).squarefree, by norm_num⟩

/-- `5` is not an integer square. -/
instance instFactNotIsSquareFive : Fact (¬ IsSquare (5 : ℤ)) :=
  ⟨fun h ↦ isFundamentalDiscr_five.not_isSquare_rat (by norm_num) (h.map (Int.castRingHom ℚ))⟩

/-- `12` is not an integer square. -/
instance instFactNotIsSquareTwelve : Fact (¬ IsSquare (12 : ℤ)) :=
  ⟨fun h ↦ isFundamentalDiscr_twelve.not_isSquare_rat (by norm_num) (h.map (Int.castRingHom ℚ))⟩

/-- Every Gauss reduced form of discriminant `5` is `x² + x y - y²` or `-x² + x y + y²`. -/
private theorem eq_of_mem_primitiveGaussReducedForms_five {f : BinaryQuadraticForm ℤ}
    (hf : f ∈ primitiveGaussReducedForms 5) :
    f = ⟨1, 1, -1⟩ ∨ f = ⟨-1, 1, 1⟩ := by
  obtain ⟨a, b, c⟩ := f
  obtain ⟨hd, hred, -⟩ := mem_primitiveGaussReducedForms.mp hf
  have hb : 0 < b := hred.b_pos
  have hac : a * c < 0 := (isGaussReduced_iff.mp hred).1
  have hsq : (|a| + |c|) ^ 2 < 5 := hd ▸ hred.sq_abs_add_abs_lt
  rw [discrim_def, discrim] at hd
  dsimp only at hb hac hsq hd
  have ha0 : 1 ≤ |a| := Int.one_le_abs (left_ne_zero_of_mul hac.ne)
  have hc0 : 1 ≤ |c| := Int.one_le_abs (right_ne_zero_of_mul hac.ne)
  obtain ⟨ha_lo, ha_hi⟩ := abs_le.mp (by nlinarith : |a| ≤ 1)
  obtain ⟨hc_lo, hc_hi⟩ := abs_le.mp (by nlinarith : |c| ≤ 1)
  interval_cases a <;> interval_cases c
  all_goals norm_num at hac
  · exact Or.inr (BinaryQuadraticForm.ext rfl (by nlinarith) rfl)
  · exact Or.inl (BinaryQuadraticForm.ext rfl (by nlinarith) rfl)

/-- The principal reduced form `x² + x y - y²` of discriminant `5`. -/
private def gaussFivePos : primitiveGaussReducedForms 5 :=
  ⟨⟨1, 1, -1⟩, mem_primitiveGaussReducedForms.mpr
    ⟨by norm_num [discrim_def, discrim],
      isGaussReduced_iff.mpr ⟨by norm_num, by norm_num⟩,
      by norm_num [isPrimitive_iff, content_def]⟩⟩

private theorem int_sqrt_five : Int.sqrt 5 = 2 := by
  have h1 : (2 : ℤ) ≤ Int.sqrt 5 := by
    simpa using (Int.abs_le_sqrt (a := 2) (by norm_num : (0 : ℤ) ≤ 5)).mpr (by norm_num)
  have h2 : Int.sqrt 5 * Int.sqrt 5 ≤ 5 :=
    (Int.abs_le_sqrt (by norm_num)).mp (abs_of_nonneg (Int.sqrt_nonneg 5)).le
  nlinarith

/-- One reduction step carries `x² + x y - y²` to `-x² + x y + y²`. -/
private theorem reductionStep_one_one_neg_one :
    reductionStep ⟨1, 1, -1⟩ = ⟨-1, 1, 1⟩ := by
  have hd : (⟨1, 1, -1⟩ : BinaryQuadraticForm ℤ).discrim = 5 := by norm_num [discrim_def, discrim]
  refine BinaryQuadraticForm.ext (by simp) ?_ ?_
  · rw [reductionStep_b, hd, int_sqrt_five]
    norm_num
  · rw [reductionStep_c, hd, int_sqrt_five]
    norm_num

/-- **Discriminant `5` has a single cycle of primitive Gauss reduced forms**, consisting of
`x² + x y - y²` and `-x² + x y + y²`. -/
theorem card_primitiveGaussReducedCycle_five :
    Fintype.card (PrimitiveGaussReducedCycle 5) = 1 := by
  refine Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ gaussFivePos, fun c ↦ ?_⟩
  refine Quotient.inductionOn c fun f ↦ eq_comm.mpr (Quotient.sound ?_)
  rcases eq_of_mem_primitiveGaussReducedForms_five f.2 with hf | hf
  · exact (Subtype.ext hf : f = gaussFivePos) ▸ Equiv.Perm.SameCycle.rfl
  · refine ⟨1, Subtype.ext ?_⟩
    rw [zpow_one, coe_primitiveReductionPerm_apply]
    exact reductionStep_one_one_neg_one.trans hf.symm

/-- **`ℚ(√5)` has narrow class number `1`**, certified by its single primitive Gauss cycle. -/
theorem nat_card_narrowClassGroup_five_eq_one :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0)) = 1 := by
  rw [nat_card_narrowClassGroup_eq_card_primitiveGaussReducedCycle isFundamentalDiscr_five
    (by norm_num), card_primitiveGaussReducedCycle_five]

/-- **`ℚ(√5)` has wide class number `1`.** -/
theorem classNumber_five_eq_one :
    NumberField.classNumber (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0) = 1 := by
  have : Subsingleton (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0)) :=
    (Nat.card_eq_one_iff_unique.mp nat_card_narrowClassGroup_five_eq_one).1
  have hsub : Subsingleton (ClassGroup (𝓞 (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0))) :=
    NumberField.NarrowClassGroup.toClassGroup_surjective.subsingleton
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩

/-- Every Gauss reduced form of discriminant `12` is one of `(1, 2, -2)`, `(-2, 2, 1)`,
`(-1, 2, 2)`, or `(2, 2, -1)`. -/
private theorem eq_of_mem_primitiveGaussReducedForms_twelve {f : BinaryQuadraticForm ℤ}
    (hf : f ∈ primitiveGaussReducedForms 12) :
    f = ⟨1, 2, -2⟩ ∨ f = ⟨-2, 2, 1⟩ ∨ f = ⟨-1, 2, 2⟩ ∨ f = ⟨2, 2, -1⟩ := by
  obtain ⟨a, b, c⟩ := f
  obtain ⟨hd, hred, -⟩ := mem_primitiveGaussReducedForms.mp hf
  have hb : 0 < b := hred.b_pos
  have hb2 : b ^ 2 < 12 := hd ▸ (isGaussReduced_iff_sq_lt.mp hred).2.1
  rw [discrim_def, discrim] at hd
  dsimp only at hb hb2 hd
  have hb3 : b ≤ 3 := by nlinarith
  have hd_mod : b ^ 2 % 4 = 0 := by
    have : b ^ 2 = 12 + 4 * (a * c) := by linarith
    rw [this]
    omega
  have hb_eq : b = 2 := by
    interval_cases b
    · norm_num at hd_mod
    · rfl
    · norm_num at hd_mod
  subst hb_eq
  have hac : a * c = -2 := by linarith
  have hc0 : 1 ≤ |c| := Int.one_le_abs (right_ne_zero_of_mul (by omega : a * c ≠ 0))
  have ha_abs : |a| ≤ 2 := by
    have : |a| * |c| = 2 := by rw [← abs_mul, hac]; norm_num
    nlinarith [abs_nonneg a]
  obtain ⟨ha_lo, ha_hi⟩ := abs_le.mp ha_abs
  interval_cases a
  · exact Or.inr (Or.inl (BinaryQuadraticForm.ext rfl rfl (by dsimp only; omega)))
  · exact Or.inr (Or.inr (Or.inl (BinaryQuadraticForm.ext rfl rfl (by dsimp only; omega))))
  · omega
  · exact Or.inl (BinaryQuadraticForm.ext rfl rfl (by dsimp only; omega))
  · exact Or.inr (Or.inr (Or.inr (BinaryQuadraticForm.ext rfl rfl (by dsimp only; omega))))

/-- The reduced form `x² + 2 x y - 2 y²` of discriminant `12`. -/
private def gaussTwelvePos : primitiveGaussReducedForms 12 :=
  ⟨⟨1, 2, -2⟩, mem_primitiveGaussReducedForms.mpr
    ⟨by norm_num [discrim_def, discrim],
      isGaussReduced_iff.mpr ⟨by norm_num, by norm_num⟩,
      by norm_num [isPrimitive_iff, content_def]⟩⟩

/-- The reduced form `-x² + 2 x y + 2 y²` of discriminant `12`. -/
private def gaussTwelveNeg : primitiveGaussReducedForms 12 :=
  ⟨⟨-1, 2, 2⟩, mem_primitiveGaussReducedForms.mpr
    ⟨by norm_num [discrim_def, discrim],
      isGaussReduced_iff.mpr ⟨by norm_num, by norm_num⟩,
      by norm_num [isPrimitive_iff, content_def]⟩⟩

private theorem int_sqrt_twelve : Int.sqrt 12 = 3 := by
  have h1 : (3 : ℤ) ≤ Int.sqrt 12 := by
    simpa using (Int.abs_le_sqrt (a := 3) (by norm_num : (0 : ℤ) ≤ 12)).mpr (by norm_num)
  have h2 : Int.sqrt 12 * Int.sqrt 12 ≤ 12 :=
    (Int.abs_le_sqrt (by norm_num)).mp (abs_of_nonneg (Int.sqrt_nonneg 12)).le
  nlinarith

private theorem reductionStep_one_two_neg_two :
    reductionStep ⟨1, 2, -2⟩ = ⟨-2, 2, 1⟩ := by
  have hd : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ).discrim = 12 := by norm_num [discrim_def, discrim]
  refine BinaryQuadraticForm.ext (by simp) ?_ ?_
  · rw [reductionStep_b, hd, int_sqrt_twelve]
    norm_num
  · rw [reductionStep_c, hd, int_sqrt_twelve]
    norm_num

private theorem reductionStep_neg_two_two_one :
    reductionStep ⟨-2, 2, 1⟩ = ⟨1, 2, -2⟩ := by
  have hd : (⟨-2, 2, 1⟩ : BinaryQuadraticForm ℤ).discrim = 12 := by norm_num [discrim_def, discrim]
  refine BinaryQuadraticForm.ext (by simp) ?_ ?_
  · rw [reductionStep_b, hd, int_sqrt_twelve]
    norm_num
  · rw [reductionStep_c, hd, int_sqrt_twelve]
    norm_num

private theorem reductionStep_neg_one_two_two :
    reductionStep ⟨-1, 2, 2⟩ = ⟨2, 2, -1⟩ := by
  have hd : (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ).discrim = 12 := by norm_num [discrim_def, discrim]
  refine BinaryQuadraticForm.ext (by simp) ?_ ?_
  · rw [reductionStep_b, hd, int_sqrt_twelve]
    norm_num
  · rw [reductionStep_c, hd, int_sqrt_twelve]
    norm_num

private theorem pow_primitiveReductionPerm_gaussTwelvePos (n : ℕ) :
    ((primitiveReductionPerm 12 ^ n) gaussTwelvePos).1 = ⟨1, 2, -2⟩ ∨
      ((primitiveReductionPerm 12 ^ n) gaussTwelvePos).1 = ⟨-2, 2, 1⟩ := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_primitiveReductionPerm_apply]
    rcases ih with h | h
    · exact Or.inr (by rw [h, reductionStep_one_two_neg_two])
    · exact Or.inl (by rw [h, reductionStep_neg_two_two_one])

/-- **Discriminant `12` has exactly two cycles of primitive Gauss reduced forms.** -/
theorem card_primitiveGaussReducedCycle_twelve :
    Fintype.card (PrimitiveGaussReducedCycle 12) = 2 := by
  have hne : (Quotient.mk _ gaussTwelvePos : PrimitiveGaussReducedCycle 12) ≠
      Quotient.mk _ gaussTwelveNeg := by
    intro h
    obtain ⟨n, hn⟩ := (Quotient.exact h).exists_nat_pow_eq
    rcases pow_primitiveReductionPerm_gaussTwelvePos n with h1 | h2
    · have ha : (-1 : ℤ) = 1 := by
        simpa [gaussTwelveNeg] using
          congrArg BinaryQuadraticForm.a ((congrArg Subtype.val hn).symm.trans h1)
      norm_num at ha
    · have ha : (-1 : ℤ) = -2 := by
        simpa [gaussTwelveNeg] using
          congrArg BinaryQuadraticForm.a ((congrArg Subtype.val hn).symm.trans h2)
      norm_num at ha
  have hbij : Function.Bijective
      (fun b : Bool ↦ cond b (Quotient.mk _ gaussTwelvePos : PrimitiveGaussReducedCycle 12)
        (Quotient.mk _ gaussTwelveNeg)) := by
    refine ⟨?_, fun c ↦ Quotient.inductionOn c fun f ↦ ?_⟩
    · intro b₁ b₂ hb
      cases b₁ <;> cases b₂ <;> simp_all
    · rcases eq_of_mem_primitiveGaussReducedForms_twelve f.2 with hf | hf | hf | hf
      · exact ⟨true, Quotient.sound ((Subtype.ext hf.symm : gaussTwelvePos = f) ▸
          Equiv.Perm.SameCycle.rfl)⟩
      · refine ⟨true, Quotient.sound ⟨1, Subtype.ext ?_⟩⟩
        rw [zpow_one, coe_primitiveReductionPerm_apply]
        exact reductionStep_one_two_neg_two.trans hf.symm
      · exact ⟨false, Quotient.sound ((Subtype.ext hf.symm : gaussTwelveNeg = f) ▸
          Equiv.Perm.SameCycle.rfl)⟩
      · refine ⟨false, Quotient.sound ⟨1, Subtype.ext ?_⟩⟩
        rw [zpow_one, coe_primitiveReductionPerm_apply]
        exact reductionStep_neg_one_two_two.trans hf.symm
  exact (Fintype.card_of_bijective hbij).symm.trans Fintype.card_bool

/-- **`ℚ(√12)` has narrow class number `2`**, certified by its two primitive Gauss cycles. -/
theorem nat_card_narrowClassGroup_twelve_eq_two :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0)) = 2 := by
  rw [nat_card_narrowClassGroup_eq_card_primitiveGaussReducedCycle isFundamentalDiscr_twelve
    (by norm_num), card_primitiveGaussReducedCycle_twelve]

/-- **`ℚ(√12)` has wide class number `1`**: its narrow class group of order `2` has a nontrivial
narrowly non-principal ideal class killed by forgetting positivity. -/
theorem classNumber_twelve_eq_one :
    NumberField.classNumber (QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0) = 1 := by
  let O := QuadraticOrder.numberFieldOrder 12 (Or.inl rfl)
  have hcard : Nat.card (NarrowPic O) = 2 :=
    (nat_card_narrowPic 12 (Or.inl rfl) (by norm_num)).trans card_primitiveGaussReducedCycle_twelve
  have hprod : Nat.card (NarrowPic O) =
      Nat.card (Pic O) * Nat.card (MonoidHom.ker O.narrowToPic) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker O.narrowToPic),
      Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective _ O.narrowToPic_surjective).toEquiv]
  let c := NarrowPic.mkPrincipal O (discrimTwelveNegativeLeading.val.idealSignFactor 12)
  have hc_ker : c ∈ MonoidHom.ker O.narrowToPic := O.narrowToPic_mkPrincipal _
  have hc_ne : c ≠ 1 := by
    have hce : c = discrimTwelveNegativeLeading.val.narrowPicClass 12
        ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).1
        ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).2 := by
      rw [narrowPicClass_def, orientedInvertibleFractionalIdeal_def,
        invertibleFractionalIdeal_discrimTwelveNegativeLeading_eq_one, mul_one,
        ← NarrowPic.mkPrincipal_apply]
    exact hce ▸ narrowPicClass_discrimTwelveNegativeLeading_ne_one
  have : Nontrivial (MonoidHom.ker O.narrowToPic) :=
    ⟨⟨1, one_mem _⟩, ⟨c, hc_ker⟩, fun h ↦ hc_ne (congrArg Subtype.val h).symm⟩
  have hk : 1 < Nat.card (MonoidHom.ker O.narrowToPic) := Finite.one_lt_card
  have hp : Nat.card (Pic O) = 1 := by nlinarith
  have hmax :=
    (QuadraticOrder.numberFieldOrder_eq_maximal_iff 12 (Or.inl rfl)).mpr isFundamentalDiscr_twelve
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (maximalOrderPicEquiv _).toEquiv, ← hmax]
  exact hp

end Examples

end TauCeti.BinaryQuadraticForm
