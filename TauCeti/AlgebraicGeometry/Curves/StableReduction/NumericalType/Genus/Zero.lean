/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
import Mathlib.Tactic.Linarith

/-!
# Minimal numerical types of genus zero

This file classifies minimal numerical types of arithmetic genus zero. There is only one, up to
equivalence: it has one component, of multiplicity one, weight one, and component genus zero. Its
intersection matrix is necessarily zero.

The one-component genus formula is

`g(T) = 1 + mᵢwᵢ(gᵢ - 1)`.

Thus genus zero forces `gᵢ = 0` and `mᵢwᵢ = 1`, hence `mᵢ = wᵢ = 1`. Conversely these data have
genus zero. A minimal numerical type with more than one component has arithmetic genus at least
one, so the one-component calculation gives the full classification.

## Main definitions

* `TauCeti.NumericalType.genusZeroType`: the canonical one-component numerical type of genus zero.

## Main results

* `TauCeti.NumericalType.arithmeticGenus_eq_zero_iff_of_card_eq_one`: a one-component numerical
  type has genus zero exactly when its multiplicity and weight are one and its component genus is
  zero.
* `TauCeti.NumericalType.isMinimal_and_arithmeticGenus_eq_zero_iff`: the intrinsic classification
  of minimal numerical types of genus zero.
* `TauCeti.NumericalType.nonempty_equiv_genusZeroType_iff`: a numerical type is equivalent to the
  canonical genus-zero type exactly when it is minimal and has arithmetic genus zero.

## References

The classification is [Stacks, Lemma 55.6.1](https://stacks.math.columbia.edu/tag/0C8S) in the
chapter [*Semistable Reduction*](https://stacks.math.columbia.edu/tag/0C2P).
-/

public section

namespace TauCeti

namespace NumericalType

universe u

variable {T : NumericalType.{u}}

/-- The canonical minimal numerical type of arithmetic genus zero: one component, with
multiplicity and weight one, component genus zero, and zero intersection matrix. -/
def genusZeroType : NumericalType.{0} where
  Component := Unit
  multiplicity _ := 1
  weight _ := 1
  intersection := 0
  intersection_isSymm := Matrix.isSymm_zero
  offDiagonal_nonneg _ _ _ := le_rfl
  connected i j := by cases i; cases j; exact .refl
  fiber_relation _ := by simp
  weight_dvd _ _ := one_dvd _
  genus _ := 0

/-- The canonical genus-zero type has one component. -/
@[simp]
theorem card_genusZeroType_component : Fintype.card genusZeroType.Component = 1 := (rfl)

/-- The multiplicity of the component of the canonical genus-zero type is one. -/
@[simp]
theorem genusZeroType_multiplicity (i : genusZeroType.Component) :
    genusZeroType.multiplicity i = 1 := (rfl)

/-- The weight of the component of the canonical genus-zero type is one. -/
@[simp]
theorem genusZeroType_weight (i : genusZeroType.Component) : genusZeroType.weight i = 1 := (rfl)

/-- Every intersection number of the canonical genus-zero type is zero. -/
@[simp]
theorem genusZeroType_intersection (i j : genusZeroType.Component) :
    genusZeroType.intersection i j = 0 := (rfl)

/-- The component of the canonical genus-zero type has genus zero. -/
@[simp]
theorem genusZeroType_genus (i : genusZeroType.Component) : genusZeroType.genus i = 0 := (rfl)

/-- A numerical type with a single component `i` has arithmetic genus zero exactly when `i` has
multiplicity one, weight one, and component genus zero. -/
theorem arithmeticGenus_eq_zero_iff_of_card_eq_one (h : Fintype.card T.Component = 1)
    (i : T.Component) :
    T.arithmeticGenus = 0 ↔
      T.multiplicity i = 1 ∧ T.weight i = 1 ∧ T.genus i = 0 := by
  rw [T.arithmeticGenus_of_card_eq_one h i]
  constructor
  · intro hgenus
    have hg : T.genus i = 0 := by
      by_contra hne
      have hg1 : 1 ≤ T.genus i := Nat.one_le_iff_ne_zero.mpr hne
      have hnonneg : (0 : ℤ) ≤ (T.genus i : ℤ) - 1 := by omega
      have hm : (0 : ℤ) < T.multiplicity i := by
        exact_mod_cast (T.multiplicity i).pos
      have hw : (0 : ℤ) < T.weight i := by exact_mod_cast (T.weight i).pos
      have hterm : (0 : ℤ) ≤
          (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1) :=
        mul_nonneg (mul_nonneg hm.le hw.le) hnonneg
      linarith
    have hprodInt : (T.multiplicity i : ℤ) * (T.weight i : ℤ) = 1 := by
      rw [hg] at hgenus
      push_cast at hgenus
      linarith
    have hprod : (T.multiplicity i : ℕ) * T.weight i = 1 := by exact_mod_cast hprodInt
    have hm1 : 1 ≤ (T.multiplicity i : ℕ) := (T.multiplicity i).pos
    have hw1 : 1 ≤ (T.weight i : ℕ) := (T.weight i).pos
    obtain ⟨hm, hw⟩ := (mul_eq_one_iff_of_one_le hm1 hw1).mp hprod
    exact ⟨PNat.eq hm, PNat.eq hw, hg⟩
  · rintro ⟨hm, hw, hg⟩
    have hm' : (T.multiplicity i : ℤ) = 1 := by exact_mod_cast congrArg PNat.val hm
    have hw' : (T.weight i : ℤ) = 1 := by exact_mod_cast congrArg PNat.val hw
    simp [hm', hw', hg]

/-- **Classification of minimal numerical types of genus zero.** A numerical type is minimal and
has arithmetic genus zero exactly when it has one component, whose multiplicity and weight are one
and whose component genus is zero. -/
theorem isMinimal_and_arithmeticGenus_eq_zero_iff :
    T.IsMinimal ∧ T.arithmeticGenus = 0 ↔
      Fintype.card T.Component = 1 ∧
        ∀ i, T.multiplicity i = 1 ∧ T.weight i = 1 ∧ T.genus i = 0 := by
  constructor
  · rintro ⟨hminimal, hgenus⟩
    have hcard : Fintype.card T.Component = 1 := by
      have hpos : 0 < Fintype.card T.Component := Fintype.card_pos
      by_contra hne
      have htwo : 1 < Fintype.card T.Component := by omega
      have := hminimal.one_le_arithmeticGenus htwo
      omega
    exact ⟨hcard, fun i ↦
      (T.arithmeticGenus_eq_zero_iff_of_card_eq_one hcard i).mp hgenus⟩
  · rintro ⟨hcard, hdata⟩
    obtain ⟨i⟩ := (inferInstance : Nonempty T.Component)
    exact ⟨T.isMinimal_of_card_eq_one hcard,
      (T.arithmeticGenus_eq_zero_iff_of_card_eq_one hcard i).mpr (hdata i)⟩

/-- The canonical genus-zero numerical type is minimal. -/
@[simp]
theorem isMinimal_genusZeroType : genusZeroType.IsMinimal :=
  genusZeroType.isMinimal_of_card_eq_one card_genusZeroType_component

/-- The canonical genus-zero numerical type has arithmetic genus zero. -/
@[simp]
theorem genusZeroType_arithmeticGenus : genusZeroType.arithmeticGenus = 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty genusZeroType.Component)
  exact (genusZeroType.arithmeticGenus_eq_zero_iff_of_card_eq_one
    card_genusZeroType_component i).mpr (by simp)

/-- A numerical type is equivalent to the canonical genus-zero type exactly when it is minimal
and has arithmetic genus zero. This is the uniqueness-up-to-equivalence form of the genus-zero
classification. -/
theorem nonempty_equiv_genusZeroType_iff :
    Nonempty (T.Equiv genusZeroType) ↔ T.IsMinimal ∧ T.arithmeticGenus = 0 := by
  constructor
  · rintro ⟨e⟩
    have hcard : Fintype.card T.Component = 1 := by
      rw [Fintype.card_congr e.toEquiv]
      exact card_genusZeroType_component
    exact ⟨T.isMinimal_of_card_eq_one hcard, by
      rw [← e.arithmeticGenus_eq]
      exact genusZeroType_arithmeticGenus⟩
  · intro h
    obtain ⟨hcard, hdata⟩ := isMinimal_and_arithmeticGenus_eq_zero_iff.mp h
    let e : T.Component ≃ genusZeroType.Component :=
      Fintype.equivOfCardEq (hcard.trans card_genusZeroType_component.symm)
    refine ⟨{
      toEquiv := e
      multiplicity_apply := fun i ↦ by simpa using (hdata i).1.symm
      weight_apply := fun i ↦ by simpa using (hdata i).2.1.symm
      intersection_apply := fun i j ↦ by
        rw [genusZeroType_intersection, T.intersection_eq_zero_of_card_eq_one hcard]
      genus_apply := fun i ↦ by simpa using (hdata i).2.2.symm }⟩

end NumericalType

end TauCeti
