/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.NumberTheory.LocalField.PowerSubgroup
public import TauCeti.NumberTheory.LocalField.Uniformizer

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
nonsquare of `𝓀[K]`. One exists: in odd residue characteristic
`TauCeti.not_unitFiltration_le_square` says that not every unit of `𝒪[K]` is a square. This is
the list of representatives used to compute Hilbert symbols over `K` and to count its quadratic
extensions.

## Main results

* `TauCeti.even_toAdd_normalizedValuation_of_isSquare`: a square has even valuation.
* `TauCeti.isSquare_zpow_mul_iff`: for `w` of even valuation, `π ^ m * w` is a square exactly
  when `m` is even and `w` is a square.
* `TauCeti.not_isSquare_mul_of_isUniformizer`: a uniformizer times an element of even valuation
  is not a square.
* `TauCeti.natCard_squareClassGroup_of_isUnit_two`: away from residue characteristic two the
  square-class group has four elements.
* `TauCeti.exists_isSquare_mul_of_isUnit_two`: every element of `Kˣ` agrees, up to a square,
  with one of `1`, `u`, `π`, `u π`.
* `TauCeti.isSquare_or_isSquare_mul_of_isUnit_two`: an element of even valuation is a square or
  `u` times a square.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3, for `K = ℚ_p`.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A square has even normalized valuation. -/
theorem even_toAdd_normalizedValuation_of_isSquare {a : Kˣ} (ha : IsSquare a) :
    Even (normalizedValuation K a).toAdd :=
  even_toAdd_iff.mpr (ha.map (normalizedValuation K))

/-- **Squares in a nonarchimedean local field.** Written against a uniformizer `π`, an element
`π ^ m * w` with `w` of even valuation is a square exactly when `m` is even and `w` is a square.
No hypothesis on the residue characteristic is needed. -/
theorem isSquare_zpow_mul_iff {π w : Kˣ} (hπ : IsUniformizer K π)
    (hw : Even (normalizedValuation K w).toAdd) (m : ℤ) :
    IsSquare (π ^ m * w) ↔ Even m ∧ IsSquare w := by
  have hπ' := (isUniformizer_def π).mp hπ
  refine ⟨fun hsq ↦ ?_, ?_⟩
  · -- The valuation of `π ^ m * w` is `m`, so `m` is even; halving it splits off a square root.
    obtain ⟨r, hr⟩ := hsq
    obtain ⟨k, rfl⟩ : Even m := by
      have hev := even_toAdd_normalizedValuation_of_isSquare ⟨r, hr⟩
      rw [map_mul, toAdd_mul, normalizedValuation_zpow_of_eq_ofAdd_one hπ', toAdd_ofAdd] at hev
      exact (Int.even_add.mp hev).mpr hw
    refine ⟨⟨k, rfl⟩, π ^ (-k) * r, ?_⟩
    have hexp : π ^ (-k) * r * (π ^ (-k) * r) = π ^ (-(k + k)) * (r * r) := by
      rw [mul_mul_mul_comm, ← zpow_add, ← neg_add]
    rw [hexp, ← hr, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  · rintro ⟨⟨k, rfl⟩, c, rfl⟩
    exact ⟨π ^ k * c, by rw [mul_mul_mul_comm, ← zpow_add]⟩

/-- A uniformizer times an element of even valuation has odd valuation, so it is not a
square. -/
theorem not_isSquare_mul_of_isUniformizer {π w : Kˣ} (hπ : IsUniformizer K π)
    (hw : Even (normalizedValuation K w).toAdd) : ¬IsSquare (w * π) := fun h ↦ by
  have hev := even_toAdd_normalizedValuation_of_isSquare h
  rw [map_mul, toAdd_mul, (isUniformizer_def π).mp hπ, toAdd_ofAdd] at hev
  exact (Int.not_even_iff_odd.mpr odd_one) ((Int.even_add.mp hev).mp hw)

/-- **The square-class group of a nonarchimedean local field away from residue characteristic
two has four elements.** This is the count `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K)` of
`TauCeti.card_squareClasses_of_isUnit`, read on `TauCeti.SquareClassGroup`. -/
theorem natCard_squareClassGroup_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (SquareClassGroup K) = 4 := by
  rw [← natCard_multiplicativeSquareClassGroup]
  exact (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
    (square_eq_powMonoidHom_two_range (G := Kˣ))).toEquiv).trans
      (card_squareClasses_of_isUnit h2)

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
  have hcard := natCard_squareClassGroup_of_isUnit_two h2
  have : Finite (SquareClassGroup K) := Nat.finite_of_card_ne_zero (by omega)
  have hfin : Fintype (SquareClassGroup K) := Fintype.ofFinite _
  -- The four listed classes are pairwise distinct.
  have hπ' : ¬IsSquare π := by simpa using not_isSquare_mul_of_isUniformizer hπ (w := 1) (by simp)
  have huπ : ¬IsSquare (u * π) := not_isSquare_mul_of_isUniformizer hπ hu
  have h0u : (0 : SquareClassGroup K) ≠ squareClass u :=
    fun h ↦ hu' ((squareClass_eq_zero_iff u).mp h.symm)
  have h0π : (0 : SquareClassGroup K) ≠ squareClass π :=
    fun h ↦ hπ' ((squareClass_eq_zero_iff π).mp h.symm)
  have h0uπ : (0 : SquareClassGroup K) ≠ squareClass (u * π) :=
    fun h ↦ huπ ((squareClass_eq_zero_iff (u * π)).mp h.symm)
  have huπ' : squareClass u ≠ squareClass π :=
    fun h ↦ huπ ((squareClass_eq_iff_isSquare_mul u π).mp h)
  have hu_uπ' : squareClass u ≠ squareClass (u * π) := by
    rw [squareClass_mul]
    exact fun h ↦ hπ' ((squareClass_eq_zero_iff π).mp (by simpa using sub_eq_zero.mpr h.symm))
  have hπ_uπ' : squareClass π ≠ squareClass (u * π) := by
    rw [squareClass_mul]
    exact fun h ↦ hu' ((squareClass_eq_zero_iff u).mp (by simpa using sub_eq_zero.mpr h.symm))
  -- A four-element subset of a four-element type is everything.
  have hS : ({0, squareClass u, squareClass π, squareClass (u * π)} :
      Finset (SquareClassGroup K)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h0u, h0π, h0uπ⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨huπ', hu_uπ'⟩),
      Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hπ_uπ'),
      Finset.card_singleton, ← Nat.card_eq_fintype_card, hcard]
  have hmem : squareClass a ∈ ({0, squareClass u, squareClass π, squareClass (u * π)} :
      Finset (SquareClassGroup K)) := hS ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact ⟨1, by simp, by simpa using (squareClass_eq_zero_iff a).mp h⟩
  · exact ⟨u, by simp, (squareClass_eq_iff_isSquare_mul a u).mp h⟩
  · exact ⟨π, by simp, (squareClass_eq_iff_isSquare_mul a π).mp h⟩
  · exact ⟨u * π, by simp, (squareClass_eq_iff_isSquare_mul a (u * π)).mp h⟩

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
  · exact absurd hsq (not_isSquare_mul_of_isUniformizer hπ hw)
  · rw [← mul_assoc] at hsq
    exact absurd hsq (not_isSquare_mul_of_isUniformizer hπ
      (by rw [map_mul, toAdd_mul]; exact hw.add hu))

end TauCeti
