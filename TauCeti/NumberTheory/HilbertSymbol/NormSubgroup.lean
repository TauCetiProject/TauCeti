/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.QuadraticAlgebra.AlgHom

public import TauCeti.GroupTheory.Index.Indicator
public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

import Mathlib.Tactic.LinearCombination

/-!
# The quadratic norm subgroup

For `a : R` over a commutative ring `R`, this file packages the unit norms from the quadratic
algebra `R[√a] = QuadraticAlgebra R a 0` as a subgroup of `Rˣ`. Over a field the norm-equation
Hilbert symbol is exactly the sign indicator of this subgroup.

This separates the ring-generic group theory from the arithmetic input used over a
nonarchimedean local field. Once the quadratic norm subgroup is known to have index two, its
sign indicator is multiplicative, which is the group-theoretic step in the
bimultiplicativity of the local Hilbert symbol, and it takes the value `-1` off the subgroup,
which is the group-theoretic step in the nondegeneracy of that symbol.

The diagonal entry of the symbol, `TauCeti.hilbertSymbol_self`, needs no arithmetic input at
all: the norm subgroup for the radicand `a` contains the norm `-a` of the square-root generator,
so it contains `a` exactly when it contains `-1`.

The subgroup contains every square and, when `a` is a unit, `-a`, the norm of the square-root
generator. Thus its index may be computed in the square-class group, as in O'Meara,
*Introduction to Quadratic Forms*, §63A.

The unit values of a binary diagonal form `⟨a, b⟩` are the coset `a N` of the norm subgroup `N`
of its discriminant algebra `R[√(-a b)]`
(`TauCeti.mem_unitValueSet_binary_iff_mul_mem_quadraticNormSubgroup`); this is how the norm
subgroup computes the spinor norms of binary forms. In particular the unit values of the norm form
`⟨1, -b⟩` of the quadratic algebra `K[√b]` are the units `c` with `(b, c) = 1`
(`TauCeti.mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one`); this algebra is the field
`K(√b)` only when `b` is not a square.
-/

public section
noncomputable section

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R]

/-- The norm on the units of the quadratic algebra `R[√a]`, with values in `Rˣ`. -/
noncomputable def quadraticNormHom (a : R) :
    (QuadraticAlgebra R a 0)ˣ →* Rˣ :=
  Units.map (QuadraticAlgebra.norm (R := R) (a := a) (b := 0))

/-- The quadratic norm homomorphism evaluates to the quadratic-algebra norm. -/
@[simp]
theorem quadraticNormHom_apply (a : R) (z : (QuadraticAlgebra R a 0)ˣ) :
    ((quadraticNormHom a z : Rˣ) : R) =
      (z : QuadraticAlgebra R a 0).norm :=
  by simp [quadraticNormHom]

/-- The subgroup of `Rˣ` consisting of unit norms from `R[√a]`. -/
noncomputable def quadraticNormSubgroup (a : R) : Subgroup Rˣ :=
  (quadraticNormHom a).range

/-- The quadratic norm subgroup is the range of the norm homomorphism on units. -/
theorem quadraticNormSubgroup_def (a : R) :
    quadraticNormSubgroup a = (quadraticNormHom a).range :=
  (rfl)

/-- Membership in the quadratic norm subgroup is the existence of a unit with the given norm. -/
@[simp]
theorem mem_quadraticNormSubgroup_iff (a : R) (b : Rˣ) :
    b ∈ quadraticNormSubgroup a ↔
      ∃ z : (QuadraticAlgebra R a 0)ˣ,
        (z : QuadraticAlgebra R a 0).norm = b := by
  rw [quadraticNormSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (quadraticNormHom_apply a z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, Units.ext ?_⟩
    exact (quadraticNormHom_apply a z).trans hz

/-- An element of `R[√a]` whose norm is a unit already witnesses membership in the quadratic
norm subgroup, so no unit hypothesis on the witness is needed. -/
theorem mem_quadraticNormSubgroup_iff_exists_norm_eq (a : R) (b : Rˣ) :
    b ∈ quadraticNormSubgroup a ↔ ∃ z : QuadraticAlgebra R a 0, z.norm = b := by
  rw [mem_quadraticNormSubgroup_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    have hz' : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ b.isUnit)
    exact ⟨hz'.unit, by simpa using hz⟩

/-- Every square is a norm from a quadratic algebra. -/
theorem square_le_quadraticNormSubgroup (a : R) :
    Subgroup.square Rˣ ≤ quadraticNormSubgroup a := by
  intro b hb
  obtain ⟨c, rfl⟩ := Subgroup.mem_square.mp hb
  refine (mem_quadraticNormSubgroup_iff_exists_norm_eq _ _).mpr
    ⟨algebraMap R (QuadraticAlgebra R a 0) (c : R), ?_⟩
  rw [QuadraticAlgebra.norm_algebraMap, pow_two]
  exact (Units.val_mul c c).symm

/-- The index of the quadratic norm subgroup divides the number of square classes. -/
theorem quadraticNormSubgroup_index_dvd_square_index (a : R) :
    (quadraticNormSubgroup a).index ∣ (Subgroup.square Rˣ).index :=
  Subgroup.index_dvd_of_le (square_le_quadraticNormSubgroup a)

/-- Finiteness of the square-class group implies finite index for the quadratic norm subgroup. -/
theorem finiteIndex_quadraticNormSubgroup (a : R) [(Subgroup.square Rˣ).FiniteIndex] :
    (quadraticNormSubgroup a).FiniteIndex :=
  Subgroup.finiteIndex_of_le (square_le_quadraticNormSubgroup a)

/-- A unit equal to `ξ² - a` is a norm from `R[√a]`. -/
theorem sq_sub_mem_quadraticNormSubgroup (a ξ : R) {x : Rˣ}
    (hx : (x : R) = ξ ^ 2 - a) : x ∈ quadraticNormSubgroup a := by
  refine (mem_quadraticNormSubgroup_iff_exists_norm_eq _ _).mpr ⟨⟨ξ, 1⟩, ?_⟩
  simp only [QuadraticAlgebra.norm_def, mul_one]
  rw [hx]
  ring

/-- The element `-a` is the norm of the square-root generator of `R[√a]`. -/
theorem neg_radicand_mem_quadraticNormSubgroup (a : Rˣ) :
    -a ∈ quadraticNormSubgroup (a : R) := by
  apply sq_sub_mem_quadraticNormSubgroup (a : R) 0
  simp

/-- If `-a` is not a square, the norm `-a` of the square-root generator lies outside the squares,
so the quadratic norm subgroup has strictly smaller index than the subgroup of squares. -/
theorem quadraticNormSubgroup_index_lt_square_index (a : Rˣ) (ha : ¬IsSquare (-a))
    [(Subgroup.square Rˣ).FiniteIndex] :
    (quadraticNormSubgroup (a : R)).index < (Subgroup.square Rˣ).index :=
  Subgroup.index_strictAnti <| (square_le_quadraticNormSubgroup _).lt_of_ne fun h ↦
    ha (Subgroup.mem_square.mp (h ▸ neg_radicand_mem_quadraticNormSubgroup a))

/-- Rescaling the radicand by a square does not change the quadratic norm subgroup. -/
@[simp]
theorem quadraticNormSubgroup_mul_sq (a : R) (c : Rˣ) :
    quadraticNormSubgroup (a * (c : R) ^ 2) = quadraticNormSubgroup a := by
  have key : ∀ (x : R) (y : Rˣ),
      quadraticNormSubgroup (x * (y : R) ^ 2) ≤ quadraticNormSubgroup x := by
    intro x y b hb
    obtain ⟨z, hz⟩ := (mem_quadraticNormSubgroup_iff _ _).mp hb
    let e : QuadraticAlgebra R (x * (y : R) ^ 2) 0 ≃ₐ[R] QuadraticAlgebra R x 0 :=
      QuadraticAlgebra.changeGeneratorEquiv x 0 y 0 (by ring) (by simp)
    refine (mem_quadraticNormSubgroup_iff _ _).mpr ⟨Units.map e.toMonoidHom z, ?_⟩
    exact (QuadraticAlgebra.norm_algHom e.toAlgHom e.injective z).trans hz
  refine le_antisymm (key a c) ?_
  have h := key (a * (c : R) ^ 2) c⁻¹
  simpa [mul_assoc, ← mul_pow, ← Units.val_mul] using h

/-- **The values of a binary form are a coset of norms.** A unit `c` is represented by the binary
diagonal form `⟨a, b⟩` exactly when `a * c` is a norm from the discriminant algebra
`R[√(-a b)]`, because `a (a x² + b y²) = (a x)² + a b y²`. Over a field this says that the
nonzero values of `⟨a, b⟩` are the coset `a N` of the norm group `N` of `R[√(-a b)]`. -/
theorem mem_unitValueSet_binary_iff_mul_mem_quadraticNormSubgroup (a : Rˣ) (b : R) (c : Rˣ) :
    c ∈ QuadraticMap.unitValueSet (QuadraticMap.weightedSumSquares R ![(a : R), b]) ↔
      a * c ∈ quadraticNormSubgroup (-(a * b) : R) := by
  rw [QuadraticMap.mem_unitValueSet, QuadraticMap.represents_iff,
    mem_quadraticNormSubgroup_iff_exists_norm_eq]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨⟨a * v 0, v 1⟩, ?_⟩
    simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul] at hv
    rw [QuadraticAlgebra.norm_def, Units.val_mul, ← hv]
    ring
  · rintro ⟨z, hz⟩
    refine ⟨![(a⁻¹ : Rˣ) * z.re, z.im], ?_⟩
    rw [QuadraticAlgebra.norm_def, Units.val_mul] at hz
    simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    -- Divide the norm equation `z.re² + a b z.im² = a c` by `a`.
    linear_combination ((a⁻¹ : Rˣ) : R) * hz +
      (((a⁻¹ : Rˣ) : R) * z.re ^ 2 - b * z.im ^ 2 + c) * a.mul_inv

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The quadratic norm subgroup depends only on the square class of the radicand: radicands whose
product is a square have the same norm subgroup. This is the square-class form of
`TauCeti.quadraticNormSubgroup_mul_sq`. -/
theorem quadraticNormSubgroup_eq_of_isSquare_mul {a Δ : Kˣ} (h : IsSquare (a * Δ)) :
    quadraticNormSubgroup (a : K) = quadraticNormSubgroup (Δ : K) := by
  obtain ⟨c, hc⟩ := h
  -- `a` and `Δ` differ by the square `(c * Δ⁻¹)²`, so rescaling the radicand changes nothing.
  have hcd : (a : K) * (Δ : K) = (c : K) ^ 2 := by
    rw [← Units.val_mul, hc, Units.val_mul, pow_two]
  have hs : (a : K) = (Δ : K) * (((c * Δ⁻¹ : Kˣ) : K)) ^ 2 := by
    push_cast
    field_simp
    exact hcd
  rw [hs, quadraticNormSubgroup_mul_sq]

/-- The Hilbert symbol is positive exactly on the quadratic norm subgroup. -/
@[simp]
theorem hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔ b ∈ quadraticNormSubgroup (a : K) := by
  rw [mem_quadraticNormSubgroup_iff, hilbertSymbol_eq_one_iff_exists_unit_norm_eq]

/-- **The values of the norm form.** The binary form `⟨1, -b⟩`, the norm form of the quadratic
algebra `K[√b]`, represents a unit `c` exactly when the Hilbert symbol `(b, c)` is `1`. -/
theorem mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one (b c : Kˣ) :
    c ∈ QuadraticMap.unitValueSet (QuadraticMap.weightedSumSquares K ![1, -(b : K)]) ↔
      hilbertSymbol b c = 1 := by
  simpa using mem_unitValueSet_binary_iff_mul_mem_quadraticNormSubgroup 1 (-(b : K)) c

/-- **The diagonal entry of the Hilbert symbol.** The sign of `(a, a)` is the sign of `(a, -1)` for
every `a`, with no hypothesis beyond `K` being a field, so the diagonal entry is no separate
choice of normalization. -/
@[simp]
theorem hilbertSymbol_self (a : Kˣ) : hilbertSymbol a a = hilbertSymbol a (-1) := by
  -- The norm subgroup for the radicand `a` contains the norm `-a` of the square-root generator,
  -- hence contains `a` exactly when it contains `-1`.
  have hmem : a ∈ quadraticNormSubgroup (a : K) ↔ -1 ∈ quadraticNormSubgroup (a : K) := by
    constructor
    · intro ha
      have hmem' : a⁻¹ * -a ∈ quadraticNormSubgroup (a : K) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) (neg_radicand_mem_quadraticNormSubgroup a)
      -- `a⁻¹ * -a` is the unit `-1`, the identity being checked on the values in `K`
      have hunit : a⁻¹ * -a = -1 := Units.ext (by simp)
      rw [hunit] at hmem'
      exact hmem'
    · intro h
      have hmem' : -1 * -a ∈ quadraticNormSubgroup (a : K) :=
        Subgroup.mul_mem _ h (neg_radicand_mem_quadraticNormSubgroup a)
      -- likewise `-1 * -a` is the unit `a`
      have hunit : -1 * -a = a := Units.ext (by simp)
      rw [hunit] at hmem'
      exact hmem'
  by_cases ha_mem : a ∈ quadraticNormSubgroup (a : K)
  · rw [(hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a a).mpr ha_mem,
      (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a (-1)).mpr (hmem.mp ha_mem)]
  · have hself : hilbertSymbol a a ≠ 1 :=
      fun h ↦ ha_mem ((hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a a).mp h)
    have hneg : hilbertSymbol a (-1) ≠ 1 :=
      fun h ↦ ha_mem (hmem.mpr ((hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a (-1)).mp h))
    rw [Int.units_ne_iff_eq_neg.mp hself, Int.units_ne_iff_eq_neg.mp hneg]

/-- The Hilbert symbol is the sign indicator of the quadratic norm subgroup. -/
theorem hilbertSymbol_eq_signIndicator (a b : Kˣ) :
    hilbertSymbol a b = (quadraticNormSubgroup (a : K)).signIndicator b := by
  by_cases hb : b ∈ quadraticNormSubgroup (a : K)
  · rw [(hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mpr hb,
      Subgroup.signIndicator_of_mem _ hb]
  · have hhilbert : hilbertSymbol a b ≠ 1 :=
      fun h ↦ hb ((hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mp h)
    have hindicator : (quadraticNormSubgroup (a : K)).signIndicator b ≠ 1 :=
      fun h ↦ hb ((quadraticNormSubgroup (a : K)).signIndicator_eq_one_iff.mp h)
    rw [Int.units_ne_iff_eq_neg.mp hhilbert, Int.units_ne_iff_eq_neg.mp hindicator]

/-- The Hilbert symbol is multiplicative in its second argument exactly when the quadratic norm
subgroup has index dividing two. -/
theorem hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two (a : Kˣ) :
    (∀ b c : Kˣ, hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c) ↔
      (quadraticNormSubgroup (a : K)).index ∣ 2 := by
  simpa only [hilbertSymbol_eq_signIndicator] using
    (quadraticNormSubgroup (a : K)).signIndicator_mul_iff_index_dvd_two

/-- When the quadratic norm subgroup has index dividing two, the Hilbert symbol in the second
argument is a multiplicative character. -/
noncomputable def hilbertSymbolHom (a : Kˣ)
    (hindex : (quadraticNormSubgroup (a : K)).index ∣ 2) : Kˣ →* ℤˣ :=
  (quadraticNormSubgroup (a : K)).signIndicatorHom hindex

/-- Evaluation of the Hilbert-symbol character. -/
@[simp]
theorem hilbertSymbolHom_apply (a : Kˣ)
    (hindex : (quadraticNormSubgroup (a : K)).index ∣ 2) (b : Kˣ) :
    hilbertSymbolHom a hindex b = hilbertSymbol a b := by
  rw [hilbertSymbolHom, Subgroup.signIndicatorHom_apply, hilbertSymbol_eq_signIndicator]

/-- The kernel of the Hilbert-symbol character is the quadratic norm subgroup. -/
@[simp]
theorem ker_hilbertSymbolHom (a : Kˣ)
    (hindex : (quadraticNormSubgroup (a : K)).index ∣ 2) :
    (hilbertSymbolHom a hindex).ker = quadraticNormSubgroup (a : K) := by
  rw [hilbertSymbolHom, Subgroup.ker_signIndicatorHom]

/-- **Nondegeneracy of the Hilbert symbol for a radicand of norm index two.** If the quadratic
norm subgroup of `a` has index two, then the Hilbert symbol with first argument `a` is a
nontrivial sign-valued character, so it takes the value `-1`. This is the field-level form:
no arithmetic beyond the index is needed. -/
theorem exists_hilbertSymbol_eq_neg_one_of_index_eq_two (a : Kˣ)
    (hindex : (quadraticNormSubgroup (a : K)).index = 2) :
    ∃ b : Kˣ, hilbertSymbol a b = -1 := by
  -- The character of a proper subgroup of index dividing two is onto, so `-1` is a value.
  have hdvd : (quadraticNormSubgroup (a : K)).index ∣ 2 := hindex ▸ dvd_rfl
  obtain ⟨b, hb⟩ :=
    (Subgroup.signIndicatorHom_surjective_iff_index_eq_two
      (quadraticNormSubgroup (a : K)) hdvd).mpr hindex (-1)
  rw [Subgroup.signIndicatorHom_apply, ← hilbertSymbol_eq_signIndicator] at hb
  exact ⟨b, hb⟩

end Field

end TauCeti
