/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Class
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Narrow.Equivalence
public import TauCeti.NumberTheory.BinaryQuadraticForm.IndefiniteReduction.Cycles
public import TauCeti.NumberTheory.NumberField.Global.Orders.Maximal
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Narrow class numbers of real quadratic orders from cycles of reduced forms

Proper classes of primitive indefinite binary quadratic forms of nonsquare discriminant `D > 0`
(`D ≡ 0, 1 (mod 4)`) are in bijection with the narrow Picard group `NarrowPic O_D` of the quadratic
order `O_D` of discriminant `D` (`properClassEquivNarrowPic`), and by Gauss's theorem on reduced
cycles (`primitiveCycleEquivProperClass`) those proper classes are in bijection with the cycles of
`primitiveReductionPerm D` on the finite set `primitiveGaussReducedForms D`. Composing the two gives
a canonical bijection `primitiveCycleEquivNarrowPic` between cycles of primitive Gauss reduced forms
and `NarrowPic O_D`, expressing `#NarrowPic O_D` as the number of primitive reduction cycles
(`nat_card_narrowPic`).

Under the forgetful homomorphism `O_D.narrowToPic : NarrowPic O_D →* Pic O_D`, the oriented narrow
class `f.narrowPicClass` projects to the wide Picard class `picClass`
(`narrowToPic_narrowPicClass`), because the sign-correction factor `√D` generates a principal ideal.
When `D > 0` is a fundamental discriminant, `O_D` is the maximal order of `ℚ(√D)`
(`QuadraticOrder.numberFieldOrder_eq_maximal_iff`), so `maximalOrderNarrowPicEquiv` identifies
`NarrowPic O_D` with `NumberField.NarrowClassGroup` and counts the narrow class group by primitive
cycles (`nat_card_narrowClassGroup`).

The final section certifies the narrow and wide class numbers at the three canonical indefinite test
discriminants `D = 5`, `8`, and `12`:

* `D = 5` (`ℚ(√5)`): `primitiveGaussReducedForms 5 = {⟨1, 1, -1⟩, ⟨-1, 1, 1⟩}` forms a single
  2-cycle, so `#NarrowPic = #Cl⁺(ℚ(√5)) = 1`, `classNumber ℚ(√5) = 1`, and `𝓞 ℚ(√5)` is a UFD.
* `D = 8` (`ℚ(√2)`): `primitiveGaussReducedForms 8 = {⟨1, 2, -1⟩, ⟨-1, 2, 1⟩}` forms a single
  2-cycle, so `#NarrowPic = #Cl⁺(ℚ(√8)) = 1`, `classNumber ℚ(√8) = 1`, and `𝓞 ℚ(√8)` is a UFD.
* `D = 12` (`ℚ(√3)`): complementing
  `TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.DiscriminantTwelve` (which separates the unreduced
  forms `x² - 3 y²` and `-x² + 3 y²` via unit norms modulo `3`), we compute
  `primitiveGaussReducedForms 12 = {⟨1, 2, -2⟩, ⟨-2, 2, 1⟩, ⟨-1, 2, 2⟩, ⟨2, 2, -1⟩}` and decompose
  it into two 2-cycles, certifying directly from Gauss's theorem that `⟨1, 2, -2⟩` and `⟨-1, 2, 2⟩`
  are not properly equivalent (`not_exists_smul_eq_twelve`) and `#NarrowPic = #Cl⁺ = 2`, while both
  cycle representatives have unit leading coefficients `±1` and hence trivial wide Picard class,
  giving `#Pic = classNumber ℚ(√12) = 1` (the first narrow/wide split).

## Main definitions and results

* `TauCeti.BinaryQuadraticForm.primitiveCycleEquivNarrowPic`: bijection between cycles of
  `primitiveReductionPerm D` and `NarrowPic (QuadraticOrder.numberFieldOrder D hD)`.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowPic`: cycle-count formula for
  `NarrowPic (QuadraticOrder.numberFieldOrder D hD)`.
* `TauCeti.BinaryQuadraticForm.narrowToPic_narrowPicClass` and
  `TauCeti.BinaryQuadraticForm.picClass_eq_of_sameCycle`: projection from `narrowPicClass` to
  `picClass` and cycle-invariance of `picClass`.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup`: for a positive fundamental discriminant
  `D`, `#Cl⁺(ℚ(√D))` equals the number of cycles of `primitiveReductionPerm D`.
* `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup_five`,
  `TauCeti.BinaryQuadraticForm.classNumber_five`,
  `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup_eight`,
  `TauCeti.BinaryQuadraticForm.classNumber_eight`: narrow and wide class number `1` at `D = 5, 8`.
* `TauCeti.BinaryQuadraticForm.not_exists_smul_eq_twelve`,
  `TauCeti.BinaryQuadraticForm.nat_card_narrowClassGroup_twelve`,
  `TauCeti.BinaryQuadraticForm.classNumber_twelve`: the narrow/wide split `#Cl⁺ = 2`, `h = 1` at
  `D = 12`.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 183–195.
* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.6–5.7.
-/

public section
noncomputable section

open Finset MulAction
open scoped MatrixGroups NumberField

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

section Order

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)]

/-- Forgetting positivity maps the oriented narrow class of a primitive form to its wide Picard
class, because the orientation factor `idealSignFactor` generates a principal ideal. -/
@[simp] theorem narrowToPic_narrowPicClass {f : BinaryQuadraticForm ℤ} (hf : f.discrim = D)
    (hprim : f.IsPrimitive) :
    (QuadraticOrder.numberFieldOrder D hD).narrowToPic (f.narrowPicClass D hf hprim) =
      picClass D hD ⟨f, (mem_primitiveForms D f).mpr ⟨hf, hprim⟩⟩ := by
  rw [narrowPicClass_def, NumberFieldOrder.narrowToPic_mk, orientedInvertibleFractionalIdeal_def,
    map_mul, ClassGroup.mk_toPrincipalIdeal, one_mul, picClass_def]

/-- Forms in the same cycle of `primitiveReductionPerm D` represent the same wide Picard class. -/
theorem picClass_eq_of_sameCycle {f g : primitiveGaussReducedForms D}
    (h : (primitiveReductionPerm D).SameCycle f g) :
    picClass D hD ⟨f.1, (mem_primitiveForms D f.1).mpr
      ⟨(mem_primitiveGaussReducedForms.mp f.2).1,
        (mem_primitiveGaussReducedForms.mp f.2).2.2⟩⟩ =
    picClass D hD ⟨g.1, (mem_primitiveForms D g.1).mpr
      ⟨(mem_primitiveGaussReducedForms.mp g.2).1,
        (mem_primitiveGaussReducedForms.mp g.2).2.2⟩⟩ := by
  obtain ⟨γ, hγ⟩ := sameCycle_primitiveReductionPerm_iff.mp h
  have hsub : γ • (⟨f.1, (mem_primitiveForms D f.1).mpr
      ⟨(mem_primitiveGaussReducedForms.mp f.2).1,
        (mem_primitiveGaussReducedForms.mp f.2).2.2⟩⟩ : primitiveForms D) =
      ⟨g.1, (mem_primitiveForms D g.1).mpr
        ⟨(mem_primitiveGaussReducedForms.mp g.2).1,
          (mem_primitiveGaussReducedForms.mp g.2).2.2⟩⟩ :=
    Subtype.ext (by simpa only [SubMulAction.val_smul] using hγ)
  rw [← hsub, picClass_smul]

/-- **Cycles of primitive Gauss reduced forms classify the narrow Picard group.** For a positive
nonsquare discriminant `D ≡ 0, 1 (mod 4)`, the cycles of `primitiveReductionPerm D` are in
bijection with `NarrowPic` of the quadratic order of discriminant `D`. -/
def primitiveCycleEquivNarrowPic (hpos : 0 < D) :
    Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D)) ≃
      NarrowPic (QuadraticOrder.numberFieldOrder D hD) :=
  (primitiveCycleEquivProperClass D hpos).trans (properClassEquivNarrowPic D hD hpos)

/-- On a primitive Gauss reduced form `f`, `primitiveCycleEquivNarrowPic` evaluates to the oriented
narrow class `f.1.narrowPicClass`. -/
@[simp] theorem primitiveCycleEquivNarrowPic_mk (hpos : 0 < D) (f : primitiveGaussReducedForms D) :
    primitiveCycleEquivNarrowPic D hD hpos (Quotient.mk'' f) =
      f.1.narrowPicClass D (mem_primitiveGaussReducedForms.mp f.2).1
        (mem_primitiveGaussReducedForms.mp f.2).2.2 := by
  simp [primitiveCycleEquivNarrowPic]

/-- **The order of the narrow Picard group** of a real quadratic order of discriminant `D > 0` is
the number of cycles of `primitiveReductionPerm D`. -/
theorem nat_card_narrowPic (hpos : 0 < D) :
    Nat.card (NarrowPic (QuadraticOrder.numberFieldOrder D hD)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))) :=
  Nat.card_congr (primitiveCycleEquivNarrowPic D hD hpos).symm

/-- Every wide Picard class of a real quadratic order of discriminant `D > 0` is represented by a
primitive Gauss reduced form. -/
theorem exists_mem_primitiveGaussReducedForms_picClass_eq (hpos : 0 < D)
    (c : Pic (QuadraticOrder.numberFieldOrder D hD)) :
    ∃ f : primitiveGaussReducedForms D,
      picClass D hD ⟨f.1, (mem_primitiveForms D f.1).mpr
        ⟨(mem_primitiveGaussReducedForms.mp f.2).1,
          (mem_primitiveGaussReducedForms.mp f.2).2.2⟩⟩ = c := by
  obtain ⟨n, rfl⟩ := (QuadraticOrder.numberFieldOrder D hD).narrowToPic_surjective c
  obtain ⟨q, rfl⟩ := (primitiveCycleEquivNarrowPic D hD hpos).surjective n
  refine Quotient.inductionOn' q fun f ↦ ⟨f, ?_⟩
  rw [primitiveCycleEquivNarrowPic_mk, narrowToPic_narrowPicClass]

end Order

section Fundamental

/-- **The narrow class number of a real quadratic field counts primitive reduction cycles.** For a
positive fundamental discriminant `D`, the narrow class group of `ℚ(√D)` has cardinality equal to
the number of cycles of `primitiveReductionPerm D`. -/
theorem nat_card_narrowClassGroup (D : ℤ) [Fact (¬ IsSquare D)] (hpos : 0 < D)
    (hfund : Int.IsFundamentalDiscr D) :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ (D : ℚ) 0)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))) := by
  rw [← Nat.card_congr (maximalOrderNarrowPicEquiv _).toEquiv,
    ← (QuadraticOrder.numberFieldOrder_eq_maximal_iff D hfund.emod_four_eq_zero_or_one).2 hfund,
    nat_card_narrowPic D hfund.emod_four_eq_zero_or_one hpos]

end Fundamental

/-! ### Certified narrow and wide class numbers at `D = 5`, `8`, `12` -/

private theorem nat_card_narrowPic_eq_one_of_sameCycle {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) (f₀ : primitiveGaussReducedForms D)
    (h : ∀ g : primitiveGaussReducedForms D, (primitiveReductionPerm D).SameCycle f₀ g) :
    Nat.card (NarrowPic (QuadraticOrder.numberFieldOrder D hD)) = 1 := by
  rw [nat_card_narrowPic D hD hpos]
  have : Subsingleton (Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))) :=
    ⟨fun a b ↦ Quotient.inductionOn₂' a b fun y z ↦ Quotient.sound' ((h y).symm.trans (h z))⟩
  have : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))) :=
    ⟨Quotient.mk'' f₀⟩
  exact Nat.card_unique

section DiscriminantFive

private theorem isFundamentalDiscr_five : Int.IsFundamentalDiscr 5 :=
  Int.isFundamentalDiscr_iff_squarefree.mpr
    (Or.inl ⟨rfl, Int.squarefree_natAbs.mp Nat.prime_five.squarefree⟩)

local instance : Fact (¬ IsSquare (5 : ℤ)) :=
  ⟨fun h ↦ isFundamentalDiscr_five.not_isSquare_rat (by decide) (h.map (Int.castRingHom ℚ))⟩

private theorem nat_sqrt_five : Nat.sqrt 5 = 2 :=
  ((Nat.eq_sqrt (a := 2) (n := 5)).mpr (by norm_num)).symm

/-- The primitive Gauss reduced forms of discriminant `5` are `x² + x y - y²` and
`-x² + x y + y²`. -/
theorem primitiveGaussReducedForms_five :
    primitiveGaussReducedForms 5 = {⟨1, 1, -1⟩, ⟨-1, 1, 1⟩} := by
  ext f
  rw [mem_primitiveGaussReducedForms, mem_insert, mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨hD, hred, -⟩
    obtain ⟨a, b, c⟩ := f
    obtain ⟨hb, hb2, -, -⟩ := isGaussReduced_iff_sq_lt.mp hred
    simp only [discrim_def, _root_.discrim, mul_assoc] at hD hb hb2
    have : b ≤ 2 := by by_contra!; nlinarith
    have hb1 : b = 1 := by interval_cases b <;> omega
    subst hb1
    have hac : a * c = -1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hac with rfl | rfl
    · obtain rfl : c = -1 := by linarith
      left; rfl
    · obtain rfl : c = 1 := by linarith
      right; rfl
  · rintro (rfl | rfl) <;>
      norm_num [discrim_def, _root_.discrim, isGaussReduced_iff, isPrimitive_iff, content_def]

/-- **`NarrowPic` of the order of discriminant `5` is trivial.** -/
theorem nat_card_narrowPic_five :
    Nat.card (NarrowPic (QuadraticOrder.numberFieldOrder 5 (Or.inr rfl))) = 1 := by
  have hf₀ : (⟨1, 1, -1⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 5 := by
    rw [primitiveGaussReducedForms_five]; simp
  refine nat_card_narrowPic_eq_one_of_sameCycle (Or.inr rfl) (by decide) ⟨⟨1, 1, -1⟩, hf₀⟩
    fun g ↦ ?_
  have hg := (Finset.ext_iff.mp primitiveGaussReducedForms_five g.1).mp g.2
  simp only [mem_insert, mem_singleton] at hg
  rcases hg with hg | hg
  · exact (Subtype.ext hg.symm).sameCycle _
  · refine ⟨1, ?_⟩
    rw [zpow_one]
    apply Subtype.ext
    rw [coe_primitiveReductionPerm_apply, hg]
    ext <;>
      simp only [reductionStep_a, reductionStep_b, reductionStep_c, discrim_def, _root_.discrim] <;>
      norm_num [nat_sqrt_five]

/-- **`ℚ(√5)` has narrow class number `1`.** -/
theorem nat_card_narrowClassGroup_five :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0)) = 1 := by
  rw [nat_card_narrowClassGroup 5 (by decide) isFundamentalDiscr_five,
    ← nat_card_narrowPic 5 (Or.inr rfl) (by decide), nat_card_narrowPic_five]

/-- **`ℚ(√5)` has class number `1`.** -/
theorem classNumber_five :
    NumberField.classNumber (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0) = 1 := by
  have h := nat_card_narrowClassGroup_five
  rw [NumberField.NarrowClassGroup.card_eq_card_classGroup_mul_card_ker] at h
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact Nat.eq_one_of_mul_eq_one_right h

/-- **The ring of integers of `ℚ(√5)` is a unique factorization domain.** -/
theorem uniqueFactorizationMonoid_five :
    UniqueFactorizationMonoid (𝓞 (QuadraticAlgebra ℚ ((5 : ℤ) : ℚ) 0)) :=
  NumberField.classNumber_eq_one_iff_uniqueFactorizationMonoid.mp classNumber_five

end DiscriminantFive

section DiscriminantEight

private theorem isFundamentalDiscr_eight : Int.IsFundamentalDiscr 8 :=
  (Int.isFundamentalDiscr_four_mul (m := 2)).mpr
    ⟨Int.squarefree_natAbs.mp Nat.prime_two.squarefree, Or.inl rfl⟩

local instance : Fact (¬ IsSquare (8 : ℤ)) :=
  ⟨fun h ↦ isFundamentalDiscr_eight.not_isSquare_rat (by decide) (h.map (Int.castRingHom ℚ))⟩

private theorem nat_sqrt_eight : Nat.sqrt 8 = 2 :=
  ((Nat.eq_sqrt (a := 2) (n := 8)).mpr (by norm_num)).symm

/-- The primitive Gauss reduced forms of discriminant `8` are `x² + 2 x y - y²` and
`-x² + 2 x y + y²`. -/
theorem primitiveGaussReducedForms_eight :
    primitiveGaussReducedForms 8 = {⟨1, 2, -1⟩, ⟨-1, 2, 1⟩} := by
  ext f
  rw [mem_primitiveGaussReducedForms, mem_insert, mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨hD, hred, -⟩
    obtain ⟨a, b, c⟩ := f
    obtain ⟨hb, hb2, -, -⟩ := isGaussReduced_iff_sq_lt.mp hred
    simp only [discrim_def, _root_.discrim, mul_assoc] at hD hb hb2
    have : b ≤ 2 := by by_contra!; nlinarith
    have hb2' : b = 2 := by interval_cases b <;> omega
    subst hb2'
    have hac : a * c = -1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hac with rfl | rfl
    · obtain rfl : c = -1 := by linarith
      left; rfl
    · obtain rfl : c = 1 := by linarith
      right; rfl
  · rintro (rfl | rfl) <;>
      norm_num [discrim_def, _root_.discrim, isGaussReduced_iff, isPrimitive_iff, content_def]

/-- **`NarrowPic` of the order of discriminant `8` is trivial.** -/
theorem nat_card_narrowPic_eight :
    Nat.card (NarrowPic (QuadraticOrder.numberFieldOrder 8 (Or.inl rfl))) = 1 := by
  have hf₀ : (⟨1, 2, -1⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 8 := by
    rw [primitiveGaussReducedForms_eight]; simp
  refine nat_card_narrowPic_eq_one_of_sameCycle (Or.inl rfl) (by decide) ⟨⟨1, 2, -1⟩, hf₀⟩
    fun g ↦ ?_
  have hg := (Finset.ext_iff.mp primitiveGaussReducedForms_eight g.1).mp g.2
  simp only [mem_insert, mem_singleton] at hg
  rcases hg with hg | hg
  · exact (Subtype.ext hg.symm).sameCycle _
  · refine ⟨1, ?_⟩
    rw [zpow_one]
    apply Subtype.ext
    rw [coe_primitiveReductionPerm_apply, hg]
    ext <;>
      simp only [reductionStep_a, reductionStep_b, reductionStep_c, discrim_def, _root_.discrim] <;>
      norm_num [nat_sqrt_eight]

/-- **`ℚ(√8) = ℚ(√2)` has narrow class number `1`.** -/
theorem nat_card_narrowClassGroup_eight :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ ((8 : ℤ) : ℚ) 0)) = 1 := by
  rw [nat_card_narrowClassGroup 8 (by decide) isFundamentalDiscr_eight,
    ← nat_card_narrowPic 8 (Or.inl rfl) (by decide), nat_card_narrowPic_eight]

/-- **`ℚ(√8) = ℚ(√2)` has class number `1`.** -/
theorem classNumber_eight :
    NumberField.classNumber (QuadraticAlgebra ℚ ((8 : ℤ) : ℚ) 0) = 1 := by
  have h := nat_card_narrowClassGroup_eight
  rw [NumberField.NarrowClassGroup.card_eq_card_classGroup_mul_card_ker] at h
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact Nat.eq_one_of_mul_eq_one_right h

/-- **The ring of integers of `ℚ(√8)` is a unique factorization domain.** -/
theorem uniqueFactorizationMonoid_eight :
    UniqueFactorizationMonoid (𝓞 (QuadraticAlgebra ℚ ((8 : ℤ) : ℚ) 0)) :=
  NumberField.classNumber_eq_one_iff_uniqueFactorizationMonoid.mp classNumber_eight

end DiscriminantEight

section DiscriminantTwelve

private theorem isFundamentalDiscr_twelve : Int.IsFundamentalDiscr 12 :=
  (Int.isFundamentalDiscr_four_mul (m := 3)).mpr
    ⟨Int.squarefree_natAbs.mp Nat.prime_three.squarefree, Or.inr rfl⟩

local instance : Fact (¬ IsSquare (12 : ℤ)) :=
  ⟨fun h ↦ isFundamentalDiscr_twelve.not_isSquare_rat (by decide) (h.map (Int.castRingHom ℚ))⟩

private theorem nat_sqrt_twelve : Nat.sqrt 12 = 3 :=
  ((Nat.eq_sqrt (a := 3) (n := 12)).mpr (by norm_num)).symm

/-- The primitive Gauss reduced forms of discriminant `12` are `(1, 2, -2)`, `(-2, 2, 1)`,
`(-1, 2, 2)`, and `(2, 2, -1)`. -/
theorem primitiveGaussReducedForms_twelve :
    primitiveGaussReducedForms 12 = {⟨1, 2, -2⟩, ⟨-2, 2, 1⟩, ⟨-1, 2, 2⟩, ⟨2, 2, -1⟩} := by
  ext f
  rw [mem_primitiveGaussReducedForms]
  simp only [mem_insert, mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨hD, hred, -⟩
    obtain ⟨a, b, c⟩ := f
    obtain ⟨hb, hb2, -, -⟩ := isGaussReduced_iff_sq_lt.mp hred
    simp only [discrim_def, _root_.discrim, mul_assoc] at hD hb hb2
    have : b ≤ 3 := by by_contra!; nlinarith
    have hb_eq : b = 2 := by interval_cases b <;> omega
    subst hb_eq
    have hac : a * c = -2 := by linarith
    have ha_le : -2 ≤ a ∧ a ≤ 2 := by
      have hc0 : c ≠ 0 := fun hc0 ↦ by simp [hc0] at hac
      have : |a| ≤ 2 := by
        have := Int.one_le_abs hc0
        have : |a| * |c| = 2 := by rw [← abs_mul, hac]; rfl
        nlinarith [abs_nonneg a]
      exact abs_le.mp this
    obtain ⟨ha_lo, ha_hi⟩ := ha_le
    interval_cases a
    · obtain rfl : c = 1 := by linarith
      right; left; rfl
    · obtain rfl : c = 2 := by linarith
      right; right; left; rfl
    · exfalso; linarith
    · obtain rfl : c = -2 := by linarith
      left; rfl
    · obtain rfl : c = -1 := by linarith
      right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl) <;>
      norm_num [discrim_def, _root_.discrim, isGaussReduced_iff, isPrimitive_iff, content_def]

private theorem pow_primitiveReductionPerm_twelve_one_two_neg_two
    (h₀ : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12) (n : ℕ) :
    ((primitiveReductionPerm 12 ^ n) ⟨⟨1, 2, -2⟩, h₀⟩).1 = ⟨1, 2, -2⟩ ∨
      ((primitiveReductionPerm 12 ^ n) ⟨⟨1, 2, -2⟩, h₀⟩).1 = ⟨-2, 2, 1⟩ := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_primitiveReductionPerm_apply]
    rcases ih with h | h <;> rw [h]
    · right
      ext <;>
        simp only [reductionStep_a, reductionStep_b, reductionStep_c, discrim_def,
          _root_.discrim] <;>
        norm_num [nat_sqrt_twelve]
    · left
      ext <;>
        simp only [reductionStep_a, reductionStep_b, reductionStep_c, discrim_def,
          _root_.discrim] <;>
        norm_num [nat_sqrt_twelve]

private theorem not_sameCycle_twelve
    (h₀ : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12)
    (h₁ : (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12) :
    ¬ (primitiveReductionPerm 12).SameCycle ⟨⟨1, 2, -2⟩, h₀⟩ ⟨⟨-1, 2, 2⟩, h₁⟩ := by
  intro hsc
  obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
  have hn' := congrArg (fun f : primitiveGaussReducedForms 12 ↦ f.1.a) hn
  rcases pow_primitiveReductionPerm_twelve_one_two_neg_two h₀ n with h | h <;>
    rw [h] at hn' <;> norm_num at hn'

/-- **Cycle-theoretic non-equivalence at discriminant `12`**: `x² + 2 x y - 2 y²` and
`-x² + 2 x y + 2 y²` are not properly equivalent under `SL(2, ℤ)`, because they lie in distinct
cycles of `primitiveReductionPerm 12`. -/
theorem not_exists_smul_eq_twelve :
    ¬ ∃ γ : SL(2, ℤ), γ • (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) = ⟨-1, 2, 2⟩ := by
  have h₀ : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12 := by
    rw [primitiveGaussReducedForms_twelve]; simp
  have h₁ : (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12 := by
    rw [primitiveGaussReducedForms_twelve]; simp
  rw [← sameCycle_primitiveReductionPerm_iff (f := ⟨⟨1, 2, -2⟩, h₀⟩) (g := ⟨⟨-1, 2, 2⟩, h₁⟩)]
  exact not_sameCycle_twelve h₀ h₁

private theorem sameCycle_twelve_or
    (h₀ : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12)
    (h₁ : (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12)
    (g : primitiveGaussReducedForms 12) :
    (primitiveReductionPerm 12).SameCycle ⟨⟨1, 2, -2⟩, h₀⟩ g ∨
      (primitiveReductionPerm 12).SameCycle ⟨⟨-1, 2, 2⟩, h₁⟩ g := by
  have hg := (Finset.ext_iff.mp primitiveGaussReducedForms_twelve g.1).mp g.2
  simp only [mem_insert, mem_singleton] at hg
  rcases hg with hg | hg | hg | hg
  · exact Or.inl ((Subtype.ext hg.symm).sameCycle _)
  · refine Or.inl ⟨1, ?_⟩
    rw [zpow_one]
    apply Subtype.ext
    rw [coe_primitiveReductionPerm_apply, hg]
    ext <;>
      simp only [reductionStep_a, reductionStep_b, reductionStep_c, discrim_def, _root_.discrim] <;>
      norm_num [nat_sqrt_twelve]
  · exact Or.inr ((Subtype.ext hg.symm).sameCycle _)
  · refine Or.inr ⟨1, ?_⟩
    rw [zpow_one]
    apply Subtype.ext
    rw [coe_primitiveReductionPerm_apply, hg]
    ext <;>
      simp only [reductionStep_a, reductionStep_b, reductionStep_c, discrim_def, _root_.discrim] <;>
      norm_num [nat_sqrt_twelve]

/-- **`NarrowPic` of the order of discriminant `12` has order `2`**, corresponding to the two
2-cycles `{(1, 2, -2), (-2, 2, 1)}` and `{(-1, 2, 2), (2, 2, -1)}`. -/
theorem nat_card_narrowPic_twelve :
    Nat.card (NarrowPic (QuadraticOrder.numberFieldOrder 12 (Or.inl rfl))) = 2 := by
  rw [nat_card_narrowPic 12 (Or.inl rfl) (by decide)]
  have h₀ : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12 := by
    rw [primitiveGaussReducedForms_twelve]; simp
  have h₁ : (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12 := by
    rw [primitiveGaussReducedForms_twelve]; simp
  let φ : Bool → Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm 12)) := fun b ↦
    cond b (Quotient.mk'' ⟨⟨-1, 2, 2⟩, h₁⟩) (Quotient.mk'' ⟨⟨1, 2, -2⟩, h₀⟩)
  have hbij : Function.Bijective φ := by
    refine ⟨fun b₁ b₂ hb ↦ ?_, Quotient.ind' fun g ↦ ?_⟩
    · cases b₁ <;> cases b₂
      · rfl
      · exact absurd (Quotient.exact' hb) (not_sameCycle_twelve h₀ h₁)
      · exact absurd (Quotient.exact' hb).symm (not_sameCycle_twelve h₀ h₁)
      · rfl
    · rcases sameCycle_twelve_or h₀ h₁ g with hg | hg
      · exact ⟨false, Quotient.sound' hg⟩
      · exact ⟨true, Quotient.sound' hg⟩
  exact (Nat.card_eq_of_bijective φ hbij).symm.trans (by simp)

/-- **`ℚ(√12) = ℚ(√3)` has narrow class number `2`.** -/
theorem nat_card_narrowClassGroup_twelve :
    Nat.card (NumberField.NarrowClassGroup (QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0)) = 2 := by
  rw [nat_card_narrowClassGroup 12 (by decide) isFundamentalDiscr_twelve,
    ← nat_card_narrowPic 12 (Or.inl rfl) (by decide), nat_card_narrowPic_twelve]

/-- **The wide Picard group of the order of discriminant `12` is trivial**, because both narrow
cycle representatives `(1, 2, -2)` and `(-1, 2, 2)` have unit leading coefficients `±1`. -/
theorem nat_card_pic_twelve :
    Nat.card (Pic (QuadraticOrder.numberFieldOrder 12 (Or.inl rfl))) = 1 := by
  have h₀ : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12 := by
    rw [primitiveGaussReducedForms_twelve]; simp
  have h₁ : (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ) ∈ primitiveGaussReducedForms 12 := by
    rw [primitiveGaussReducedForms_twelve]; simp
  have : Subsingleton (Pic (QuadraticOrder.numberFieldOrder 12 (Or.inl rfl))) := by
    refine ⟨fun c₁ c₂ ↦ ?_⟩
    suffices ∀ c : Pic (QuadraticOrder.numberFieldOrder 12 (Or.inl rfl)), c = 1 by
      rw [this c₁, this c₂]
    intro c
    obtain ⟨g, rfl⟩ := exists_mem_primitiveGaussReducedForms_picClass_eq 12 (Or.inl rfl)
      (by decide) c
    rcases sameCycle_twelve_or h₀ h₁ g with hsc | hsc
    · rw [← picClass_eq_of_sameCycle 12 (Or.inl rfl) hsc]
      exact picClass_eq_one_of_isUnit_a 12 (Or.inl rfl) isUnit_one
    · rw [← picClass_eq_of_sameCycle 12 (Or.inl rfl) hsc]
      exact picClass_eq_one_of_isUnit_a 12 (Or.inl rfl) (IsUnit.neg isUnit_one)
  exact Nat.card_unique

/-- **`ℚ(√12) = ℚ(√3)` has wide class number `1`**, exhibiting the first narrow/wide split
(`#Cl⁺ = 2`, `h = 1`). -/
theorem classNumber_twelve :
    NumberField.classNumber (QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0) = 1 := by
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (maximalOrderPicEquiv _).toEquiv,
    ← (QuadraticOrder.numberFieldOrder_eq_maximal_iff 12 (Or.inl rfl)).2 isFundamentalDiscr_twelve,
    nat_card_pic_twelve]

/-- **The ring of integers of `ℚ(√12)` is a unique factorization domain.** -/
theorem uniqueFactorizationMonoid_twelve :
    UniqueFactorizationMonoid (𝓞 (QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0)) :=
  NumberField.classNumber_eq_one_iff_uniqueFactorizationMonoid.mp classNumber_twelve

end DiscriminantTwelve

end TauCeti.BinaryQuadraticForm
