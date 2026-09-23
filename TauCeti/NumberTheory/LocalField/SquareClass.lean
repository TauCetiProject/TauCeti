/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.ElementaryTwoQuotient.KleinFour
public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.NumberTheory.LocalField.PowerSubgroup
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.LocalField.Squares

/-!
# The square classes of a nonarchimedean local field

Let `K` be a nonarchimedean local field with normalized valuation `v_K` and uniformizer `π`.
Writing an element as `π ^ m * w` with `v_K(w)` even splits the question of being a square into
two independent questions: the parity of `m`, and whether `w` is a square. That is
`TauCeti.isSquare_zpow_mul_iff`, and it holds in every residue characteristic. In particular a
square has even valuation, so an element of odd valuation is never a square.

Away from residue characteristic two the second question has exactly two answers: the
square-class group `Kˣ ⧸ (Kˣ)²` has four elements, and for a nonsquare `u` of even valuation the
four classes are represented by

`1`, `u`, `π`, `u π`.

The choice of `u` is part of the statement. Up to squares `u` is a unit of `𝒪[K]`, and by
`TauCeti.isSquare_unitsMap_subtype_iff` such a unit is a nonsquare exactly when its residue is a
nonsquare of `𝓀[K]`. The theorem
`TauCeti.exists_mem_unitFiltration_not_isSquare` supplies a nonsquare in the unit filtration
whenever `K` has characteristic different from two. This is the list of representatives used to
compute Hilbert symbols over `K` and to count its quadratic extensions.

## Main results

* `TauCeti.isSquare_zpow_mul_iff`: for `w` of even valuation, `π ^ m * w` is a square exactly
  when `m` is even and `w` is a square.
* `TauCeti.not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation`: a uniformizer
  times an element of even valuation is not a square.
* `TauCeti.not_isSquare_of_isUniformizer`: a uniformizer is not a square.
* `TauCeti.natCard_multiplicativeSquareClassGroup_of_isUnit_two`: away from residue
  characteristic two the literal quotient by squares has four elements.
* `TauCeti.natCard_squareClassGroup_of_isUnit_two`: away from residue characteristic two the
  square-class group has four elements.
* `TauCeti.isAddKleinFour_squareClassGroup_of_isUnit_two`: away from residue characteristic two
  the square-class group is a Klein four-group.
* `TauCeti.squareClass_ne_zero_and_ne_of_isUniformizer_of_not_isSquare`: the four specified
  square classes are pairwise distinct.
* `TauCeti.eq_zero_or_eq_squareClass_of_isUnit_two`: the four specified square classes
  exhaust the square-class group.
* `TauCeti.exists_isSquare_mul_of_isUnit_two`: every element of `Kˣ` agrees, up to a square,
  with one of `1`, `u`, `π`, `u π`.
* `TauCeti.exists_integerUnit_residue_not_isSquare_and_isSquare_mul_of_isUnit_two`: the unit `u`
  can be chosen with nonsquare residue, as required by the representative classification.
* `TauCeti.isSquare_or_isSquare_mul_of_isUnit_two`: an element of even valuation is a square or
  `u` times a square.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3, for `K = ℚ_p`.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Squares in a nonarchimedean local field.** Written against a uniformizer `π`, an element
`π ^ m * w` with `w` of even valuation is a square exactly when `m` is even and `w` is a square.
No hypothesis on the residue characteristic is needed. -/
theorem isSquare_zpow_mul_iff {π w : Kˣ} (hπ : IsUniformizer K π)
    (hw : Even (normalizedValuation K w).toAdd) (m : ℤ) :
    IsSquare (π ^ m * w) ↔ Even m ∧ IsSquare w := by
  have hπ' := (isUniformizer_def π).mp hπ
  refine ⟨fun hsq ↦ ?_, ?_⟩
  · -- The valuation of `π ^ m * w` is `m`, so `m` is even.
    have hm : Even m := by
      have hev := even_toAdd_normalizedValuation_of_isSquare hsq
      rw [map_mul, toAdd_mul, normalizedValuation_zpow_of_eq_ofAdd_one hπ', toAdd_ofAdd] at hev
      exact (Int.even_add.mp hev).mpr hw
    refine ⟨hm, ?_⟩
    have h := hsq.mul ((even_neg.mpr hm).isSquare_zpow π)
    rwa [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at h
  · rintro ⟨hm, hw'⟩
    exact (hm.isSquare_zpow π).mul hw'

/-- A uniformizer times an element of even valuation has odd valuation, so it is not a
square. -/
theorem not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation {π w : Kˣ}
    (hπ : IsUniformizer K π)
    (hw : Even (normalizedValuation K w).toAdd) : ¬IsSquare (π * w) := fun h ↦
  Int.not_even_one ((isSquare_zpow_mul_iff hπ hw 1).mp (by simpa using h)).1

/-- A uniformizer is not a square. -/
theorem not_isSquare_of_isUniformizer {π : Kˣ} (hπ : IsUniformizer K π) : ¬IsSquare π := by
  simpa using not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation
    hπ (w := 1) (by simp)

/-- **The multiplicative square-class group of a nonarchimedean local field away from residue
characteristic two has four elements.** This is the literal quotient `Kˣ ⧸ (Kˣ)²`;
`TauCeti.natCard_squareClassGroup_of_isUnit_two` restates it on the additive
`TauCeti.SquareClassGroup`. -/
theorem natCard_multiplicativeSquareClassGroup_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (MultiplicativeSquareClassGroup K) = 4 :=
  (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
    (square_eq_powMonoidHom_two_range (G := Kˣ))).toEquiv).trans
      (card_squareClasses_of_isUnit h2)

/-- **The square-class group of a nonarchimedean local field away from residue characteristic
two has four elements.** This is the count `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K)` of
`TauCeti.card_squareClasses_of_isUnit`, read on `TauCeti.SquareClassGroup`. -/
theorem natCard_squareClassGroup_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (SquareClassGroup K) = 4 := by
  rw [← natCard_multiplicativeSquareClassGroup]
  exact natCard_multiplicativeSquareClassGroup_of_isUnit_two h2

/-- Away from residue characteristic two, the square-class group of a nonarchimedean local field
is a Klein four-group. -/
theorem isAddKleinFour_squareClassGroup_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) :
    IsAddKleinFour (SquareClassGroup K) :=
  isAddKleinFour_of_natCard_eq_four (natCard_squareClassGroup_of_isUnit_two h2)

/-- For a nonsquare `u` of even valuation and a uniformizer `π`, the square classes of
`1`, `u`, `π`, and `u * π` are pairwise distinct. -/
theorem squareClass_ne_zero_and_ne_of_isUniformizer_of_not_isSquare
    {u π : Kˣ} (hπ : IsUniformizer K π)
    (hu : Even (normalizedValuation K u).toAdd) (hu' : ¬IsSquare u) :
    squareClass u ≠ 0 ∧ squareClass π ≠ 0 ∧ squareClass (u * π) ≠ 0 ∧
      squareClass u ≠ squareClass π ∧ squareClass u ≠ squareClass (u * π) ∧
      squareClass π ≠ squareClass (u * π) := by
  have h0u : squareClass u ≠ 0 := (squareClass_eq_zero_iff u).not.mpr hu'
  have h0π : squareClass π ≠ 0 :=
    (squareClass_eq_zero_iff π).not.mpr (not_isSquare_of_isUniformizer hπ)
  have hne : ¬IsSquare (u * π) := by
    simpa [mul_comm] using
      not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation hπ hu
  have huπ : squareClass u ≠ squareClass π :=
    (squareClass_eq_iff_isSquare_mul u π).not.mpr hne
  have h0uπ : squareClass (u * π) ≠ 0 :=
    (squareClass_eq_zero_iff (u * π)).not.mpr hne
  have hu_uπ : squareClass u ≠ squareClass (u * π) := by
    rw [squareClass_mul]
    exact left_ne_add.mpr h0π
  have hπ_uπ : squareClass π ≠ squareClass (u * π) := by
    rw [squareClass_mul]
    exact right_ne_add.mpr h0u
  exact ⟨h0u, h0π, h0uπ, huπ, hu_uπ, hπ_uπ⟩

/-- **The four square classes of a nonarchimedean local field of odd residue characteristic.**
For a nonsquare `u` of even valuation and a uniformizer `π`, their four classes exhaust the
square-class group. -/
theorem eq_zero_or_eq_squareClass_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) {π u : Kˣ}
    (hπ : IsUniformizer K π) (hu : Even (normalizedValuation K u).toAdd) (hu' : ¬IsSquare u) :
    ∀ x : SquareClassGroup K,
      x = 0 ∨ x = squareClass u ∨ x = squareClass π ∨ x = squareClass (u * π) := by
  let _ : IsAddKleinFour (SquareClassGroup K) :=
    isAddKleinFour_squareClassGroup_of_isUnit_two h2
  obtain ⟨h0u, h0π, _, huπ, _, _⟩ :=
    squareClass_ne_zero_and_ne_of_isUniformizer_of_not_isSquare hπ hu hu'
  intro x
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hxu : x = squareClass u
  · exact Or.inr (Or.inl hxu)
  by_cases hxπ : x = squareClass π
  · exact Or.inr (Or.inr (Or.inl hxπ))
  · exact Or.inr (Or.inr (Or.inr <| by
      rw [squareClass_mul]
      exact IsAddKleinFour.eq_add_of_ne_all h0u h0π huπ hx hxu hxπ))

/-- **The four square classes of a nonarchimedean local field of odd residue characteristic.**
For a uniformizer `π` and a nonsquare `u` of even valuation, every element of `Kˣ` becomes a
square after multiplication by one of `1`, `u`, `π`, `u π`. Together with
`TauCeti.natCard_squareClassGroup_of_isUnit_two` this says that the four listed elements
represent the four square classes. -/
theorem exists_isSquare_mul_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) {π u : Kˣ}
    (hπ : IsUniformizer K π) (hu : Even (normalizedValuation K u).toAdd) (hu' : ¬IsSquare u)
    (a : Kˣ) :
    ∃ r ∈ ({1, u, π, u * π} : Set Kˣ), IsSquare (a * r) := by
  classical
  rcases eq_zero_or_eq_squareClass_of_isUnit_two h2 hπ hu hu' (squareClass a) with
    h | h | h | h
  · exact ⟨1, by simp, by simpa using (squareClass_eq_zero_iff a).mp h⟩
  · exact ⟨u, by simp, (squareClass_eq_iff_isSquare_mul a u).mp h⟩
  · exact ⟨π, by simp, (squareClass_eq_iff_isSquare_mul a π).mp h⟩
  · exact ⟨u * π, by simp, (squareClass_eq_iff_isSquare_mul a (u * π)).mp h⟩

/-- **The four square classes with the unramified unit chosen explicitly.** Away from residue
characteristic two, for every uniformizer `π` there is a unit `u` of `𝒪[K]` whose residue is
a nonsquare, and `1`, `u`, `π`, `u π` represent all four square classes. -/
theorem exists_integerUnit_residue_not_isSquare_and_isSquare_mul_of_isUnit_two
    (h2 : IsUnit (2 : 𝒪[K])) {π : Kˣ} (hπ : IsUniformizer K π) :
    ∃ u : 𝒪[K]ˣ,
      ¬IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) ∧
      ∀ a : Kˣ, ∃ r ∈ ({1, Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u,
          π, Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u * π} : Set Kˣ),
        IsSquare (a * r) := by
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2.ne_zero
    exact Subtype.ext h
  obtain ⟨x, hx, hxsq⟩ := exists_mem_unitFiltration_not_isSquare h2K
  have hx0 : x ∈ unitFiltration K 0 := unitFiltration_antitone (Nat.zero_le _) hx
  let x0 : unitFiltration K 0 := ⟨x, hx0⟩
  let u : 𝒪[K]ˣ := unitFiltrationToIntegerUnits 0 x0
  have hu_map : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u = x := by
    simp [u, x0]
  refine ⟨u, ?_, fun a ↦ ?_⟩
  · rw [← not_congr (isSquare_unitsMap_subtype_iff h2 u), hu_map]
    exact hxsq
  · apply exists_isSquare_mul_of_isUnit_two h2 hπ
    · have hxval : (normalizedValuation K x).toAdd = 0 := by
        apply toAdd_eq_zero.mpr
        rw [normalizedValuation_eq_one_iff]
        exact (mem_unitFiltration_zero x).mp hx0
      rw [hu_map, hxval]
      exact ⟨0, by simp⟩
    · rwa [hu_map]

/-- **The even-valuation square classes away from residue characteristic two.** An element of
even valuation is a square, or `u` times a square, for any fixed nonsquare `u` of even
valuation. -/
theorem isSquare_or_isSquare_mul_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) {u w : Kˣ}
    (hu : Even (normalizedValuation K u).toAdd) (hu' : ¬IsSquare u)
    (hw : Even (normalizedValuation K w).toAdd) : IsSquare w ∨ IsSquare (w * u) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  obtain ⟨r, hr, hsq⟩ := exists_isSquare_mul_of_isUnit_two h2 hπ hu hu' w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl (by simpa using hsq)
  · exact Or.inr hsq
  · exact absurd (by simpa [mul_comm] using hsq)
      (not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation hπ hw (w := w))
  · exact absurd (by simpa [mul_assoc, mul_comm, mul_left_comm] using hsq)
      (not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation hπ
        (by rw [map_mul, toAdd_mul]; exact hw.add hu) (w := w * u))

end TauCeti
