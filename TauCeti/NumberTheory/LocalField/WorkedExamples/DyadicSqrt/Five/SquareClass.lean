/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.Basic
public import TauCeti.FieldTheory.SquareClassGroup.Basic
import TauCeti.NumberTheory.LocalField.FiniteExtension.SquareClass
import TauCeti.NumberTheory.Multiquadratic.SquareClass.Basic
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# Unit square classes of `ℚ₂(√5)`

The three units `-1`, `2 + √5` and `3 + 2√5` generate eight distinct square classes of
units in the unramified quadratic extension of `ℚ₂`. Together with the uniformizer `2`,
they represent all sixteen square classes. The eight unit classes are exactly the classes
of even valuation, which are the domain for computations of transferred lines.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, for dyadic square classes.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. 78 (1984), Théorème 2, for transferred-line computations.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.DyadicSqrtFive

/-- Three generators for the unit square classes of `ℚ₂(√5)`: `-1`, `2 + √5`, `3 + 2√5`. -/
def unitSquareClassGenerator (i : Fin 3) : DyadicSqrtFiveˣ :=
  ![-1, Units.mk0 (2 + sqrtFive) (by
    intro h
    have hx : sqrtFive = -2 := eq_neg_of_add_eq_zero_right h
    have hsq := sqrtFive_sq
    rw [hx] at hsq
    norm_num at hsq), Units.mk0 (3 + 2 * sqrtFive) (by
    intro h
    have hx : sqrtFive = -3 / 2 := by linear_combination h / 2
    have hsq := sqrtFive_sq
    rw [hx] at hsq
    norm_num at hsq)] i

@[simp]
theorem coe_unitSquareClassGenerator (i : Fin 3) :
    (unitSquareClassGenerator i : DyadicSqrtFive) = ![-1, 2 + sqrtFive, 3 + 2 * sqrtFive] i :=
  by fin_cases i <;> rfl

/-- The norms of the three unit-square-class generators are `1`, `-1`, `-11`. -/
@[simp↓] -- Compute before the coercion is expanded to an indexed tuple.
theorem norm_unitSquareClassGenerator (i : Fin 3) :
    Algebra.norm ℚ_[2] (unitSquareClassGenerator i : DyadicSqrtFive) = ![1, -1, -11] i := by
  rw [coe_unitSquareClassGenerator]
  fin_cases i
  · simpa [map_ofNat] using norm_add_mul_sqrtFive (-1) 0
  · convert norm_add_mul_sqrtFive 2 1 using 1 <;> norm_num [map_ofNat]
  · convert norm_add_mul_sqrtFive 3 2 using 1 <;> norm_num [map_ofNat]

/-- Each generator is a unit of the integer ring: its multiplicative normalized valuation is one
(equivalently, its additive valuation is zero). -/
@[simp]
theorem normalizedValuation_unitSquareClassGenerator (i : Fin 3) :
    normalizedValuation DyadicSqrtFive (unitSquareClassGenerator i) = 1 := by
  have h := toAdd_normalizedValuation_norm (K := ℚ_[2]) (unitSquareClassGenerator i)
  have hn : (normalizedValuation ℚ_[2]
      (Algebra.normUnits ℚ_[2] (unitSquareClassGenerator i))).toAdd = 0 := by
    rw [Padic.toAdd_normalizedValuation_eq_valuation, Algebra.coe_normUnits,
      norm_unitSquareClassGenerator]
    fin_cases i
    · simp
    · have ht := Padic.valuation_intCast (p := 2) (-1)
      norm_num [padicValInt] at ht
      exact ht
    · have ht := Padic.valuation_intCast (p := 2) (-11)
      norm_num [padicValInt, padicValNat.eq_zero_of_not_dvd] at ht
      exact ht
  rw [hn, inertiaDegree_eq_two] at h
  apply Multiplicative.toAdd.injective
  simp only [toAdd_one]
  omega

private theorem not_isSquare_neg_one : ¬IsSquare (-1 : DyadicSqrtFive) := by
  rintro ⟨y, hy⟩
  have hy2 : y ^ 2 = algebraMap ℚ_[2] DyadicSqrtFive (-1) := by
    simpa [sq] using hy.symm
  obtain ⟨T, hT, s, hs⟩ := Multiquadratic.squareClass_of_sq_mem_finset
    (fun _ : Fin 1 => (5 : ℚ_[2])) (fun _ => sqrtFive) {0}
    (by simp [map_ofNat]) hy2 (by simp [adjoin_sqrtFive_eq_top])
  have ht : T = ∅ ∨ T = {0} := Finset.subset_singleton_iff.mp hT
  rcases ht with rfl | rfl
  · have hsq : IsSquare (-1 : ℚ_[2]) := ⟨s, by simpa [sq] using hs⟩
    exact Padic.not_isSquare_intCast_of_not_isSquare_zmod
      (p := 2) (a := -1) (k := 3) (by decide) hsq
  · have hsq : IsSquare (-5 : ℚ_[2]) := ⟨5 * s, by
      simp only [Finset.prod_singleton] at hs
      linear_combination 5 * hs⟩
    exact Padic.not_isSquare_intCast_of_not_isSquare_zmod
      (p := 2) (a := -5) (k := 3) (by decide) hsq

/-- The eight products of the three unit generators, indexed by their binary exponents. -/
def unitSquareClassRep (c : Fin 3 → ZMod 2) : DyadicSqrtFiveˣ :=
  ∏ i, unitSquareClassGenerator i ^ (c i).val

/-- The product formula characterizing the unit representatives. -/
theorem unitSquareClassRep_def (c : Fin 3 → ZMod 2) :
    unitSquareClassRep c = ∏ i, unitSquareClassGenerator i ^ (c i).val := (rfl)

@[simp]
theorem unitSquareClassRep_zero : unitSquareClassRep 0 = 1 := by
  simp [unitSquareClassRep_def]

/-- Every representative is a unit of the integer ring. -/
@[simp]
theorem normalizedValuation_unitSquareClassRep (c : Fin 3 → ZMod 2) :
    normalizedValuation DyadicSqrtFive (unitSquareClassRep c) = 1 := by
  simp [unitSquareClassRep_def]

private def fullRep (c : Fin 4 → ZMod 2) : DyadicSqrtFiveˣ :=
  unitSquareClassRep (fun i => c i.castSucc) * Units.mk0 (2 : DyadicSqrtFive) (by norm_num) ^
    (c 3).val

private theorem valuation_fullRep (c : Fin 4 → ZMod 2) :
    (normalizedValuation DyadicSqrtFive (fullRep c)).toAdd = (c 3).val := by
  have htwo : (normalizedValuation DyadicSqrtFive
      (Units.mk0 (2 : DyadicSqrtFive) (by norm_num))).toAdd = 1 := by
    have h := IsUnramified.normalizedValuation_algebraMap (L := DyadicSqrtFive)
      (Units.mk0 (2 : ℚ_[2]) two_ne_zero)
    have hu : Units.map (algebraMap ℚ_[2] DyadicSqrtFive : ℚ_[2] →* DyadicSqrtFive)
        (Units.mk0 (2 : ℚ_[2]) two_ne_zero) = Units.mk0 2 (by norm_num) := by ext; simp [map_ofNat]
    rw [hu] at h
    rw [h, Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0,
      Padic.valuation_ofNat, padicValNat_self]
    norm_num
  simp [fullRep, htwo]

private theorem fullRep_isSquare_iff (c : Fin 4 → ZMod 2) :
    IsSquare (fullRep c) ↔ c = 0 := by
  constructor
  · intro hs
    have hev := even_toAdd_normalizedValuation_of_isSquare hs
    rw [valuation_fullRep] at hev
    have h3 : c 3 = 0 := by
      have hb := ZMod.val_lt (c 3)
      have hc : (c 3).val = 0 := by rcases hev with ⟨n, hn⟩; omega
      exact (ZMod.val_eq_zero _).mp hc
    have hn := hs.map (Algebra.normUnits ℚ_[2])
    have hnorm : (Algebra.normUnits ℚ_[2] (fullRep c) : ℚ_[2]) =
        (-1) ^ (c 1).val * (-11) ^ (c 2).val := by
      simp [fullRep, unitSquareClassRep_def, Fin.prod_univ_three, h3,
        Algebra.coe_normUnits, norm_unitSquareClassGenerator]
    have hsq : IsSquare ((-1 : ℚ_[2]) ^ (c 1).val * (-11) ^ (c 2).val) := by
      rw [← hnorm]
      exact isSquare_units_val_iff.mpr hn
    have cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide
    have h12 : c 1 = 0 ∧ c 2 = 0 := by
      rcases cases (c 1) with h1 | h1 <;> rcases cases (c 2) with h2 | h2
      · exact ⟨h1, h2⟩
      · exact False.elim (Padic.not_isSquare_intCast_of_not_isSquare_zmod
          (p := 2) (a := -11) (k := 3) (by decide)
          (by simpa [h1, h2, ZMod.val_one] using hsq))
      · exact False.elim (Padic.not_isSquare_intCast_of_not_isSquare_zmod
          (p := 2) (a := -1) (k := 3) (by decide)
          (by simpa [h1, h2, ZMod.val_one] using hsq))
      · exact False.elim (Padic.not_isSquare_intCast_of_not_isSquare_zmod
          (p := 2) (a := 11) (k := 3) (by decide)
          (by norm_num [h1, h2, ZMod.val_one] at hsq ⊢; exact hsq))
    have h0 : c 0 = 0 := by
      rcases cases (c 0) with h0 | h0
      · exact h0
      · apply False.elim
        apply not_isSquare_neg_one
        have heq : fullRep c = -1 := by
          apply Units.ext
          simp [fullRep, unitSquareClassRep_def, Fin.prod_univ_three,
            h0, h12.1, h12.2, h3, ZMod.val_one]
        exact isSquare_units_val_iff.mpr (heq ▸ hs)
    funext i
    fin_cases i <;> simp [h0, h12.1, h12.2, h3]
  · rintro rfl
    simp [fullRep, unitSquareClassRep_def]

private def fullGenerator : Fin 4 → DyadicSqrtFiveˣ :=
  Fin.snoc unitSquareClassGenerator (Units.mk0 2 (by norm_num))

private theorem squareClass_fullRep (c : Fin 4 → ZMod 2) :
    squareClass (fullRep c) = ∑ i, c i • squareClass (fullGenerator i) := by
  have hsmul (z : ZMod 2) (x : SquareClassGroup DyadicSqrtFive) : z.val • x = z • x := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) z.val x, ZMod.natCast_zmod_val]
  simp only [fullRep, squareClass_mul, unitSquareClassRep_def, squareClass_prod,
    squareClass_pow, hsmul, Fin.sum_univ_castSucc, fullGenerator,
    Fin.snoc_castSucc, Fin.snoc_last]
  rfl

private theorem fullRep_bijective :
    Function.Bijective fun c => squareClass (fullRep c) := by
  have hind : LinearIndependent (ZMod 2) (fun i => squareClass (fullGenerator i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [← squareClass_fullRep, squareClass_eq_zero_iff, fullRep_isSquare_iff] at hc
    simp [hc]
  have hinj : Function.Injective fun c => squareClass (fullRep c) := by
    intro c d h
    apply hind.fintypeLinearCombination_injective
    simpa only [Fintype.linearCombination_apply, ← squareClass_fullRep] using h
  have hcard : Nat.card (SquareClassGroup DyadicSqrtFive) = 16 := by
    rw [natCard_squareClassGroup_eq_four_mul_pow_finrank (K := ℚ_[2]) two_ne_zero,
      Padic.natCard_residueField, Padic.natCastValuation_self, finrank_eq_two]
    norm_num
  have : Finite (SquareClassGroup DyadicSqrtFive) := Nat.finite_of_card_ne_zero (by omega)
  exact hinj.bijective_of_nat_card_le (by simp [hcard])

/-- The eight unit representatives have pairwise distinct square classes. -/
theorem squareClass_unitSquareClassRep_injective :
    Function.Injective fun c => squareClass (unitSquareClassRep c) := by
  intro c d h
  have hfull : Fin.snoc c 0 = Fin.snoc d 0 := fullRep_bijective.injective (by
    simpa [fullRep, Fin.snoc] using h)
  funext i
  simpa using congrFun hfull i.castSucc

/-- A nonzero element has a unique unit-square-class representative exactly when its
normalized valuation is even. Thus the eight representatives exhaust the unit classes. -/
theorem existsUnique_unitSquareClassRep_iff_even (a : DyadicSqrtFiveˣ) :
    (∃! c : Fin 3 → ZMod 2, squareClass a = squareClass (unitSquareClassRep c)) ↔
      Even (normalizedValuation DyadicSqrtFive a).toAdd := by
  constructor
  · rintro ⟨c, hc, _⟩
    have hs := (squareClass_eq_iff_isSquare_mul _ _).mp hc
    have h := even_toAdd_normalizedValuation_of_isSquare hs
    simpa using h
  · intro ha
    obtain ⟨c, hc⟩ := fullRep_bijective.surjective (squareClass a)
    have hs := (squareClass_eq_iff_isSquare_mul _ _).mp hc.symm
    have hev := even_toAdd_normalizedValuation_of_isSquare hs
    simp only [map_mul, toAdd_mul, valuation_fullRep] at hev
    have h3 : c 3 = 0 := by
      have hb := ZMod.val_lt (c 3)
      have hc0 : (c 3).val = 0 := by
        rcases ha with ⟨n, hn⟩
        rcases hev with ⟨m, hm⟩
        omega
      exact (ZMod.val_eq_zero _).mp hc0
    have hrep : fullRep c = unitSquareClassRep (fun i => c i.castSucc) := by simp [fullRep, h3]
    have hc' : squareClass (unitSquareClassRep (fun i => c i.castSucc)) = squareClass a :=
      (congrArg squareClass hrep).symm.trans hc
    exact ⟨fun i => c i.castSucc, hc'.symm,
      fun d hd => squareClass_unitSquareClassRep_injective (hd.symm.trans hc'.symm)⟩

/-- Every unit of the integer ring of `ℚ₂(√5)` is represented by exactly one of the eight
products of `-1`, `2 + √5`, and `3 + 2√5`, modulo squares in the field. -/
theorem existsUnique_unitSquareClassRep (a : 𝒪[DyadicSqrtFive]ˣ) :
    ∃! c : Fin 3 → ZMod 2,
      squareClass (Units.map (𝒪[DyadicSqrtFive].subtype : 𝒪[DyadicSqrtFive] →* DyadicSqrtFive) a) =
        squareClass (unitSquareClassRep c) := by
  rw [existsUnique_unitSquareClassRep_iff_even, normalizedValuation_integerUnits]
  simp

end TauCeti.DyadicSqrtFive
