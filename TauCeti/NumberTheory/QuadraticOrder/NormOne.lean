/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.QuadraticOrder.Basic
public import TauCeti.NumberTheory.QuadraticOrder.Split.Basic
public import TauCeti.RingTheory.Norm.Units
public import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.Norm.Basic

/-!
# Norm-one units of quadratic orders

The norm-one subgroup is the kernel of the ordinary algebra norm on the units of the embedded
quadratic order. The existing integral quadratic-algebra model identifies this subgroup with
its unitary elements. This comparison supplies integral coordinates for the unit arithmetic
used by binary lattice automorphisms.

At negative discriminant every unit has norm one, with six units at minus three, four at
minus four, and two otherwise. At positive nonsquare discriminant the embedded Pell solutions
give infinitely many norm-one units. At nonzero square discriminant the product-order norm
calculation leaves exactly the diagonal units one and minus one.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Sections 2 and 7.
-/

public section

open QuadraticAlgebra

namespace TauCeti.QuadraticOrder

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)

/-- The norm-one subgroup of the units of the embedded quadratic order. -/
noncomputable def normOneUnits : Subgroup (toSubalgebra D hD)ˣ :=
  (Algebra.normUnits ℤ).ker

/-- A unit lies in the norm-one subgroup exactly when its ordinary algebra norm equals one. -/
@[simp] theorem mem_normOneUnits_iff (u : (toSubalgebra D hD)ˣ) :
    u ∈ normOneUnits D hD ↔ _root_.Algebra.norm ℤ (u : toSubalgebra D hD) = 1 := by
  rw [normOneUnits, MonoidHom.mem_ker]
  constructor
  · intro h
    simpa only [Algebra.coe_normUnits, Units.val_one] using congrArg Units.val h
  · intro h
    apply Units.ext
    simpa only [Algebra.coe_normUnits, Units.val_one] using h

/-- The integral-model equivalence identifies the algebra norm with the quadratic norm. -/
@[simp] theorem norm_equivToSubalgebra
    (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
    _root_.Algebra.norm ℤ (equivToSubalgebra D hD z) = z.norm := by
  rw [_root_.Algebra.norm_eq_of_algEquiv, _root_.Algebra.norm_quadraticAlgebra_apply]

private noncomputable def unitaryToNormOneUnits :
    unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) →* normOneUnits D hD :=
  (((Units.map (equivToSubalgebra D hD).toMonoidHom).comp Unitary.toUnits).codRestrict
    (normOneUnits D hD) fun z ↦ by
      rw [mem_normOneUnits_iff, MonoidHom.comp_apply, Units.coe_map,
        Unitary.val_toUnits_apply]
      -- `Units.map` views the algebra equivalence as a monoid homomorphism;
      -- this conversion exposes the same algebra map for the norm computation.
      change _root_.Algebra.norm ℤ (equivToSubalgebra D hD (z : _)) = 1
      rw [norm_equivToSubalgebra]
      exact QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mpr z.property)

private theorem unitaryToNormOneUnits_bijective :
    Function.Bijective (unitaryToNormOneUnits D hD) := by
  constructor
  · intro z w h
    apply Subtype.ext
    apply (equivToSubalgebra D hD).injective
    exact congrArg (fun u : normOneUnits D hD ↦ ((u : (toSubalgebra D hD)ˣ) :
      toSubalgebra D hD)) h
  · intro u
    let z := (equivToSubalgebra D hD).symm ((u : (toSubalgebra D hD)ˣ) : toSubalgebra D hD)
    have hz : z.norm = 1 := by
      rw [← norm_equivToSubalgebra D hD z, AlgEquiv.apply_symm_apply]
      exact (mem_normOneUnits_iff D hD _).mp u.property
    refine ⟨⟨z, QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mp hz⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact (equivToSubalgebra D hD).apply_symm_apply _

/-- Norm-one units of the actual embedded order are the unitary elements of its integral model. -/
noncomputable def normOneUnitsEquivUnitary :
    normOneUnits D hD ≃* unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :=
  (MulEquiv.ofBijective (unitaryToNormOneUnits D hD)
    (unitaryToNormOneUnits_bijective D hD)).symm

/-- The inverse comparison embeds a unitary integral-model element in the actual order. -/
@[simp] theorem coe_normOneUnitsEquivUnitary_symm
    (z : unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D)) :
    (((normOneUnitsEquivUnitary D hD).symm z : (toSubalgebra D hD)ˣ) : toSubalgebra D hD) =
      equivToSubalgebra D hD (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) := (rfl)

/-- The forward comparison recovers the integral coordinates of the underlying order element. -/
@[simp] theorem coe_normOneUnitsEquivUnitary_apply (u : normOneUnits D hD) :
    (normOneUnitsEquivUnitary D hD u : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) =
      (equivToSubalgebra D hD).symm ((u : (toSubalgebra D hD)ˣ) : toSubalgebra D hD) := by
  apply (equivToSubalgebra D hD).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun v : normOneUnits D hD ↦ ((v : (toSubalgebra D hD)ˣ) :
    toSubalgebra D hD)) ((normOneUnitsEquivUnitary D hD).symm_apply_apply u)
  simpa only [coe_normOneUnitsEquivUnitary_symm] using h

/-- The norm in the rational quadratic algebra is the integer norm of the embedded order. -/
theorem norm_coe (z : toSubalgebra D hD) :
    QuadraticAlgebra.norm (z : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (_root_.Algebra.norm ℤ z : ℚ) := by
  obtain ⟨w, rfl⟩ := (equivToSubalgebra D hD).surjective z
  rw [coe_equivToSubalgebra_apply, lift_apply, norm_equivToSubalgebra]
  have hp := parameter_discr D hD
  rw [QuadraticAlgebra.discr_def] at hp
  have hpQ : (D : ℚ) ^ 2 + 4 * (((D - D ^ 2) / 4 : ℤ) : ℚ) = D := by
    exact_mod_cast hp
  simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul,
    QuadraticAlgebra.im_one, generator_re, generator_im, Int.cast_add, Int.cast_mul,
    Int.cast_sub, zero_mul, add_zero]
  linear_combination (w.im : ℚ) ^ 2 / 4 * hpQ

/-- For negative discriminant every unit has norm one. -/
theorem norm_unit_eq_one_of_neg (hneg : D < 0) (u : (toSubalgebra D hD)ˣ) :
    _root_.Algebra.norm ℤ (u : toSubalgebra D hD) = 1 := by
  rcases Int.isUnit_iff.mp
      (u.isUnit.map (_root_.Algebra.norm ℤ : toSubalgebra D hD →* ℤ)) with h | h
  · exact h
  · have hn := norm_coe D hD (u : toSubalgebra D hD)
    rw [h, QuadraticAlgebra.norm_def] at hn
    norm_num only [Int.cast_neg, Int.cast_one, zero_mul, zero_add] at hn
    have hd : (D : ℚ) < 0 := by exact_mod_cast hneg
    have := mul_nonneg (neg_nonneg.mpr hd.le)
      (sq_nonneg (u : QuadraticAlgebra ℚ (D : ℚ) 0).im)
    exfalso
    nlinarith only [hn, this, sq_nonneg (u : QuadraticAlgebra ℚ (D : ℚ) 0).re]

/-- At negative discriminant the norm-one subgroup is the full unit group. -/
theorem normOneUnits_eq_top_of_neg (hneg : D < 0) : normOneUnits D hD = ⊤ := by
  apply top_unique
  intro u _
  exact (mem_normOneUnits_iff D hD u).mpr (norm_unit_eq_one_of_neg D hD hneg u)

/-- Minus one is a norm-one unit of every quadratic order. -/
theorem neg_one_mem_normOneUnits : (-1 : (toSubalgebra D hD)ˣ) ∈ normOneUnits D hD := by
  rw [mem_normOneUnits_iff]
  simpa using norm_equivToSubalgebra D hD
    (-1 : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D)

include hD in
private theorem model_norm_one_equation
    (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) (hz : z.norm = 1) :
    (2 * z.re + D * z.im) ^ 2 - D * z.im ^ 2 = 4 := by
  have hp := parameter_discr D hD
  rw [QuadraticAlgebra.discr_def] at hp
  rw [QuadraticAlgebra.norm_def] at hz
  linear_combination 4 * hz + z.im ^ 2 * hp

/-- Away from discriminants minus three and minus four, a negative-discriminant order has
only the units one and minus one. -/
theorem units_eq_one_or_neg_one_of_neg (hneg : D < 0) (h₃ : D ≠ -3) (h₄ : D ≠ -4)
    (u : (toSubalgebra D hD)ˣ) : u = 1 ∨ u = -1 := by
  let z := (equivToSubalgebra D hD).symm (u : toSubalgebra D hD)
  have hz : z.norm = 1 := by
    rw [← norm_equivToSubalgebra D hD z, AlgEquiv.apply_symm_apply]
    exact norm_unit_eq_one_of_neg D hD hneg u
  have he := model_norm_one_equation D hD z hz
  have hd : D ≤ -5 := by omega
  have him : z.im = 0 := by
    have hn : z.im ^ 2 < 1 := by
      nlinarith [sq_nonneg (2 * z.re + D * z.im), sq_nonneg z.im]
    have hn₀ : z.im ^ 2 = 0 := by have := sq_nonneg z.im; omega
    exact sq_eq_zero_iff.mp hn₀
  rw [QuadraticAlgebra.norm_def, him] at hz
  have hre : z.re ^ 2 = 1 := by nlinarith [hz]
  rcases sq_eq_one_iff.mp hre with h | h
  · left
    apply Units.ext
    apply (equivToSubalgebra D hD).symm.injective
    ext <;> simp [z, h, him]
  · right
    apply Units.ext
    apply (equivToSubalgebra D hD).symm.injective
    ext <;> simp [z, h, him]

/-- Apart from the two exceptional negative discriminants, the unit group has order two. -/
theorem card_units_of_neg_of_ne (hneg : D < 0) (h₃ : D ≠ -3) (h₄ : D ≠ -4) :
    Nat.card (toSubalgebra D hD)ˣ = 2 := by
  let f : Fin 2 → (toSubalgebra D hD)ˣ := ![1, -1]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl |
        (have h := congrArg (fun u : (toSubalgebra D hD)ˣ ↦
          (((u : toSubalgebra D hD) : QuadraticAlgebra ℚ (D : ℚ) 0).re)) hij
         norm_num [f] at h)
    · intro u
      rcases units_eq_one_or_neg_one_of_neg D hD hneg h₃ h₄ u with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  simpa using (Nat.card_eq_of_bijective f hf).symm

private def negFourUnitary (i : Fin 4) : unitary (QuadraticAlgebra ℤ (-5) (-4)) :=
  ⟨![⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩] i, by
    apply QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mp
    fin_cases i <;> norm_num [QuadraticAlgebra.norm_def]⟩

private theorem negFourUnitary_bijective : Function.Bijective negFourUnitary := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl |
      (have h := congrArg (fun z : unitary (QuadraticAlgebra ℤ (-5) (-4)) ↦
        ((z : QuadraticAlgebra ℤ (-5) (-4)).re, (z : QuadraticAlgebra ℤ (-5) (-4)).im)) hij
       norm_num [negFourUnitary] at h)
  · intro z
    have hz := QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mpr z.property
    norm_num [QuadraticAlgebra.norm_def] at hz
    have hi : (z : QuadraticAlgebra ℤ (-5) (-4)).im ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((z : QuadraticAlgebra ℤ (-5) (-4)).re - 2 * z.val.im)]
    have hb : -1 ≤ z.val.im ∧ z.val.im ≤ 1 := by constructor <;> nlinarith
    have hc : z.val.im = -1 ∨ z.val.im = 0 ∨ z.val.im = 1 := by omega
    rcases hc with h | h | h
    · have hr : z.val.re = -2 := by rw [h] at hz; nlinarith [hz]
      refine ⟨3, ?_⟩
      apply Subtype.ext
      ext <;> simp [negFourUnitary, h, hr]
    · have hr : z.val.re = 1 ∨ z.val.re = -1 := by
        rw [h] at hz
        apply sq_eq_one_iff.mp
        nlinarith [hz]
      rcases hr with hr | hr
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        ext <;> simp [negFourUnitary, h, hr]
      · refine ⟨1, ?_⟩
        apply Subtype.ext
        ext <;> simp [negFourUnitary, h, hr]
    · have hr : z.val.re = 2 := by rw [h] at hz; nlinarith [hz]
      refine ⟨2, ?_⟩
      apply Subtype.ext
      ext <;> simp [negFourUnitary, h, hr]

/-- The discriminant-minus-four order has four units. -/
theorem card_units_neg_four : Nat.card (toSubalgebra (-4) (by decide))ˣ = 4 := by
  have h := Nat.card_congr (normOneUnitsEquivUnitary (-4) (by decide)).toEquiv
  rw [normOneUnits_eq_top_of_neg _ _ (by decide), Subgroup.card_top] at h
  exact h.trans (by
    simpa using (Nat.card_eq_of_bijective negFourUnitary negFourUnitary_bijective).symm)

private def negThreeUnitary (i : Fin 6) : unitary (QuadraticAlgebra ℤ (-3) (-3)) :=
  ⟨![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩] i, by
    apply QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mp
    fin_cases i <;> norm_num [QuadraticAlgebra.norm_def]⟩

private theorem negThreeUnitary_bijective : Function.Bijective negThreeUnitary := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl |
      (have h := congrArg (fun z : unitary (QuadraticAlgebra ℤ (-3) (-3)) ↦
        ((z : QuadraticAlgebra ℤ (-3) (-3)).re, (z : QuadraticAlgebra ℤ (-3) (-3)).im)) hij
       norm_num [negThreeUnitary] at h)
  · intro z
    have hz := QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mpr z.property
    norm_num [QuadraticAlgebra.norm_def] at hz
    have hi : z.val.im ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (2 * z.val.re - 3 * z.val.im)]
    have hb : -1 ≤ z.val.im ∧ z.val.im ≤ 1 := by constructor <;> nlinarith
    have hc : z.val.im = -1 ∨ z.val.im = 0 ∨ z.val.im = 1 := by omega
    rcases hc with h | h | h
    · have hr : (z.val.re + 1) * (z.val.re + 2) = 0 := by rw [h] at hz; nlinarith [hz]
      rcases mul_eq_zero.mp hr with hr | hr
      · have hr' : z.val.re = -1 := by omega
        refine ⟨4, ?_⟩
        apply Subtype.ext
        ext <;> simp [negThreeUnitary, h, hr']
      · have hr' : z.val.re = -2 := by omega
        refine ⟨5, ?_⟩
        apply Subtype.ext
        ext <;> simp [negThreeUnitary, h, hr']
    · have hr : z.val.re = 1 ∨ z.val.re = -1 := by
        rw [h] at hz
        apply sq_eq_one_iff.mp
        nlinarith [hz]
      rcases hr with hr | hr
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        ext <;> simp [negThreeUnitary, h, hr]
      · refine ⟨1, ?_⟩
        apply Subtype.ext
        ext <;> simp [negThreeUnitary, h, hr]
    · have hr : (z.val.re - 1) * (z.val.re - 2) = 0 := by rw [h] at hz; nlinarith [hz]
      rcases mul_eq_zero.mp hr with hr | hr
      · have hr' : z.val.re = 1 := by omega
        refine ⟨2, ?_⟩
        apply Subtype.ext
        ext <;> simp [negThreeUnitary, h, hr']
      · have hr' : z.val.re = 2 := by omega
        refine ⟨3, ?_⟩
        apply Subtype.ext
        ext <;> simp [negThreeUnitary, h, hr']

/-- The discriminant-minus-three order has six units. -/
theorem card_units_neg_three : Nat.card (toSubalgebra (-3) (by decide))ˣ = 6 := by
  have h := Nat.card_congr (normOneUnitsEquivUnitary (-3) (by decide)).toEquiv
  rw [normOneUnits_eq_top_of_neg _ _ (by decide), Subgroup.card_top] at h
  exact h.trans (by
    simpa using (Nat.card_eq_of_bijective negThreeUnitary negThreeUnitary_bijective).symm)

/-- The unit count for every negative quadratic discriminant, including the two exceptions. -/
theorem card_units_of_neg (hneg : D < 0) :
    Nat.card (toSubalgebra D hD)ˣ = if D = -3 then 6 else if D = -4 then 4 else 2 := by
  by_cases h₃ : D = -3
  · subst D
    rw [ite_eq_left rfl]
    exact card_units_neg_three
  · by_cases h₄ : D = -4
    · subst D
      rw [ite_eq_right (by decide), ite_eq_left rfl]
      exact card_units_neg_four
    · simpa only [ite_eq_right h₃, ite_eq_right h₄] using card_units_of_neg_of_ne D hD hneg h₃ h₄

/-- The norm-one unit count at negative discriminant. -/
theorem card_normOneUnits_of_neg (hneg : D < 0) :
    Nat.card (normOneUnits D hD) = if D = -3 then 6 else if D = -4 then 4 else 2 := by
  rw [normOneUnits_eq_top_of_neg D hD hneg, Subgroup.card_top]
  exact card_units_of_neg D hD hneg

/-- Negative-discriminant quadratic orders have finite norm-one unit groups. -/
theorem finite_normOneUnits_of_neg (hneg : D < 0) : Finite (normOneUnits D hD) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_normOneUnits_of_neg D hD hneg]
  split_ifs <;> decide

/-- In the split branch, the integer norm is multiplication of the product coordinates. -/
theorem norm_eq_product_of_sq (s : ℤ) (hs : s ≠ 0)
    (z : toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega)) :
    _root_.Algebra.norm ℤ z =
      (equivProductOfSq s hs z : ℤ × ℤ).1 * (equivProductOfSq s hs z : ℤ × ℤ).2 := by
  apply Int.cast_injective (α := ℚ)
  rw [← norm_coe, Int.cast_mul]
  have h := equivProductOfSq_commutes s hs z
  rw [algEquivProdOfIntSq_apply] at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  rw [← h₁, ← h₂, QuadraticAlgebra.norm_def]
  simp only [Int.cast_pow, zero_mul]
  ring

/-- The norm-one units of a nonzero square-discriminant order are precisely one and minus one. -/
theorem normOneUnits_eq_one_or_neg_one_of_sq (s : ℤ) (hs : s ≠ 0)
    (u : normOneUnits (s ^ 2) (by rw [Int.sq_emod_four]; omega)) :
    (u : (toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega))ˣ) = 1 ∨
      (u : (toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega))ˣ) = -1 := by
  let w := equivProductOfSq s hs
    ((u : (toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega))ˣ) :
      toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega))
  have hw : w.val.1 * w.val.2 = 1 := by
    rw [← norm_eq_product_of_sq]
    exact (mem_normOneUnits_iff _ _ _).mp u.property
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    apply Units.ext
    apply (equivProductOfSq s hs).injective
    rw [Units.val_one, map_one]
    apply Subtype.ext
    exact Prod.ext h₁ h₂
  · right
    apply Units.ext
    apply (equivProductOfSq s hs).injective
    rw [Units.val_neg, Units.val_one, map_neg, map_one]
    apply Subtype.ext
    exact Prod.ext h₁ h₂

/-- A nonzero square-discriminant order has two norm-one units, computed in the product order. -/
theorem card_normOneUnits_sq (s : ℤ) (hs : s ≠ 0) :
    Nat.card (normOneUnits (s ^ 2) (by rw [Int.sq_emod_four]; omega)) = 2 := by
  let U := normOneUnits (s ^ 2) (by rw [Int.sq_emod_four]; omega)
  let f : Fin 2 → U := ![1, ⟨-1, neg_one_mem_normOneUnits _ _⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl |
        (have h := congrArg (fun u : U ↦
          ((((u : (toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega))ˣ) :
            toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega)) :
              QuadraticAlgebra ℚ ((s ^ 2 : ℤ) : ℚ) 0).re)) hij
         norm_num [f] at h)
    · intro u
      rcases normOneUnits_eq_one_or_neg_one_of_sq s hs u with h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
  simpa only [U] using (Nat.card_eq_of_bijective f hf).symm.trans (Nat.card_fin _)

/-- Nonzero square-discriminant quadratic orders have finite norm-one unit groups. -/
theorem finite_normOneUnits_sq (s : ℤ) (hs : s ≠ 0) :
    Finite (normOneUnits (s ^ 2) (by rw [Int.sq_emod_four]; omega)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_normOneUnits_sq s hs]
  decide

private def pellToUnitary :
    Pell.Solution₁ D →* unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) where
  toFun a := ⟨⟨a.x - D * a.y, 2 * a.y⟩, by
    apply QuadraticAlgebra.norm_eq_one_iff_mem_unitary.mp
    have hp := parameter_discr D hD
    rw [QuadraticAlgebra.discr_def] at hp
    simp only [QuadraticAlgebra.norm_def]
    linear_combination a.prop - a.y ^ 2 * hp⟩
  map_one' := by
    apply Subtype.ext
    ext <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext
    · have hp := parameter_discr D hD
      rw [QuadraticAlgebra.discr_def] at hp
      simp only [Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Submonoid.coe_mul,
        QuadraticAlgebra.re_mul]
      linear_combination -(a.y * b.y) * hp
    · simp only [Pell.Solution₁.y_mul, Submonoid.coe_mul, QuadraticAlgebra.im_mul]
      ring

/-- An ordinary Pell solution gives a norm-one unit of the actual quadratic order. -/
noncomputable def pellToNormOneUnits : Pell.Solution₁ D →* normOneUnits D hD :=
  (normOneUnitsEquivUnitary D hD).symm.toMonoidHom.comp (pellToUnitary D hD)

/-- The embedded unit attached to `(x, y)` is exactly `x + y√D`. -/
@[simp] theorem coe_pellToNormOneUnits (a : Pell.Solution₁ D) :
    (((pellToNormOneUnits D hD a : (toSubalgebra D hD)ˣ) : toSubalgebra D hD) :
      QuadraticAlgebra ℚ (D : ℚ) 0) = ⟨(a.x : ℚ), (a.y : ℚ)⟩ := by
  rw [pellToNormOneUnits, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    coe_normOneUnitsEquivUnitary_symm, coe_equivToSubalgebra_apply]
  dsimp only [pellToUnitary]
  rw [lift_apply]
  ext <;> simp <;> ring

/-- Distinct Pell solutions give distinct units in the order. -/
theorem pellToNormOneUnits_injective : Function.Injective (pellToNormOneUnits D hD) := by
  intro a b h
  have h' := congrArg (fun u : normOneUnits D hD ↦
    (((u : (toSubalgebra D hD)ˣ) : toSubalgebra D hD) : QuadraticAlgebra ℚ (D : ℚ) 0)) h
  rw [coe_pellToNormOneUnits, coe_pellToNormOneUnits] at h'
  apply Pell.Solution₁.ext
  · have := congrArg QuadraticAlgebra.re h'
    exact Int.cast_injective (α := ℚ) this
  · have := congrArg QuadraticAlgebra.im h'
    exact Int.cast_injective (α := ℚ) this

/-- Positive nonsquare discriminants have infinitely many integral norm-one units, by powers
of a fundamental Pell solution. -/
theorem infinite_normOneUnits_of_pos_of_not_isSquare (hpos : 0 < D) (hns : ¬ IsSquare D) :
    Infinite (normOneUnits D hD) := by
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hpos hns
  apply Infinite.of_injective (fun n : ℤ ↦ pellToNormOneUnits D hD (a ^ n))
  intro m n h
  have he := pellToNormOneUnits_injective D hD h
  exact ha.y_strictMono.injective (congrArg Pell.Solution₁.y he)

end TauCeti.QuadraticOrder
