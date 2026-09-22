/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even

public import TauCeti.GroupTheory.Index.Indicator
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# The quadratic norm subgroup

For `a : Kˣ`, this file packages the nonzero norms from the quadratic algebra
`K[√a] = QuadraticAlgebra K a 0` as a subgroup of `Kˣ`. The norm-equation Hilbert symbol
is exactly the sign indicator of this subgroup.

This separates the field-generic group theory from the arithmetic input used over a
nonarchimedean local field. Once the quadratic norm subgroup is known to have index two, its
sign indicator is multiplicative, which is the group-theoretic step in the
bimultiplicativity of the local Hilbert symbol.

The subgroup contains every square and `-a`, the norm of the square-root generator. Thus its
index may be computed in the square-class group, as in O'Meara, *Introduction to Quadratic
Forms*, §63A.
-/

public section
noncomputable section

namespace TauCeti

variable {K : Type*} [Field K]

/-- The norm on the units of the quadratic algebra `K[√a]`, with values in `Kˣ`. -/
noncomputable def quadraticNormHom (a : Kˣ) :
    (QuadraticAlgebra K (a : K) 0)ˣ →* Kˣ :=
  Units.map (QuadraticAlgebra.norm (R := K) (a := (a : K)) (b := 0))

/-- The quadratic norm homomorphism evaluates to the quadratic-algebra norm. -/
@[simp]
theorem quadraticNormHom_apply (a : Kˣ) (z : (QuadraticAlgebra K (a : K) 0)ˣ) :
    ((quadraticNormHom a z : Kˣ) : K) =
      (z : QuadraticAlgebra K (a : K) 0).norm :=
  by simp [quadraticNormHom]

/-- The subgroup of `Kˣ` consisting of nonzero norms from `K[√a]`. -/
noncomputable def quadraticNormSubgroup (a : Kˣ) : Subgroup Kˣ :=
  (quadraticNormHom a).range

/-- Membership in the quadratic norm subgroup is the existence of a unit with the given norm. -/
@[simp]
theorem mem_quadraticNormSubgroup_iff (a b : Kˣ) :
    b ∈ quadraticNormSubgroup a ↔
      ∃ z : (QuadraticAlgebra K (a : K) 0)ˣ,
        (z : QuadraticAlgebra K (a : K) 0).norm = b := by
  rw [quadraticNormSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, Units.ext ?_⟩
    exact hz

/-- The Hilbert symbol is positive exactly on the quadratic norm subgroup. -/
@[simp]
theorem hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔ b ∈ quadraticNormSubgroup a := by
  rw [mem_quadraticNormSubgroup_iff, hilbertSymbol_eq_one_iff_exists_unit_norm_eq]

/-- The Hilbert symbol is negative exactly off the quadratic norm subgroup. -/
@[simp]
theorem hilbertSymbol_eq_neg_one_iff_not_mem_quadraticNormSubgroup (a b : Kˣ) :
    hilbertSymbol a b = -1 ↔ b ∉ quadraticNormSubgroup a := by
  rw [← not_congr (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b)]
  simpa using
    (Int.units_ne_iff_eq_neg (u := hilbertSymbol a b) (v := (1 : ℤˣ))).symm

/-- The Hilbert symbol is the sign indicator of the quadratic norm subgroup. -/
theorem hilbertSymbol_eq_signIndicator (a b : Kˣ) :
    hilbertSymbol a b = (quadraticNormSubgroup a).signIndicator b := by
  by_cases hb : b ∈ quadraticNormSubgroup a
  · rw [(hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mpr hb,
      Subgroup.signIndicator_of_mem _ hb]
  · rw [(hilbertSymbol_eq_neg_one_iff_not_mem_quadraticNormSubgroup a b).mpr hb,
      Subgroup.signIndicator_of_notMem _ hb]

/-- Every square is a norm from a quadratic algebra. -/
theorem square_le_quadraticNormSubgroup (a : Kˣ) :
    Subgroup.square Kˣ ≤ quadraticNormSubgroup a := by
  intro b hb
  rw [← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup]
  exact hilbertSymbol_eq_one_of_isSquare_right a (Subgroup.mem_square.mp hb)

/-- The index of the quadratic norm subgroup divides the number of square classes. -/
theorem quadraticNormSubgroup_index_dvd_square_index (a : Kˣ) :
    (quadraticNormSubgroup a).index ∣ (Subgroup.square Kˣ).index :=
  Subgroup.index_dvd_of_le (square_le_quadraticNormSubgroup a)

/-- Finiteness of the square-class group implies finite index for the quadratic norm subgroup. -/
theorem finiteIndex_quadraticNormSubgroup (a : Kˣ) [(Subgroup.square Kˣ).FiniteIndex] :
    (quadraticNormSubgroup a).FiniteIndex :=
  Subgroup.finiteIndex_of_le (square_le_quadraticNormSubgroup a)

/-- The element `-a` is the norm of the square-root generator of `K[√a]`. -/
theorem neg_self_mem_quadraticNormSubgroup (a : Kˣ) :
    -a ∈ quadraticNormSubgroup a := by
  rw [← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup]
  exact hilbertSymbol_neg_self a

/-- Rescaling the radicand by a square does not change the quadratic norm subgroup. -/
@[simp]
theorem quadraticNormSubgroup_mul_sq (a c : Kˣ) :
    quadraticNormSubgroup (a * c ^ 2) = quadraticNormSubgroup a := by
  ext b
  rw [← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup,
    ← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup, hilbertSymbol_mul_sq_left]

/-- The Hilbert symbol is multiplicative in its second argument exactly when the quadratic norm
subgroup has index dividing two. -/
theorem hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two (a : Kˣ) :
    (∀ b c : Kˣ, hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c) ↔
      (quadraticNormSubgroup a).index ∣ 2 := by
  simpa only [hilbertSymbol_eq_signIndicator] using
    (quadraticNormSubgroup a).signIndicator_mul_iff_index_dvd_two

/-- When the quadratic norm subgroup has index dividing two, the Hilbert symbol in the second
argument is a multiplicative character. -/
noncomputable def hilbertSymbolHom (a : Kˣ)
    (hindex : (quadraticNormSubgroup a).index ∣ 2) : Kˣ →* ℤˣ :=
  (quadraticNormSubgroup a).signIndicatorHom hindex

/-- Evaluation of the Hilbert-symbol character. -/
@[simp]
theorem hilbertSymbolHom_apply (a : Kˣ)
    (hindex : (quadraticNormSubgroup a).index ∣ 2) (b : Kˣ) :
    hilbertSymbolHom a hindex b = hilbertSymbol a b := by
  rw [hilbertSymbolHom, Subgroup.signIndicatorHom_apply, hilbertSymbol_eq_signIndicator]

/-- The kernel of the Hilbert-symbol character is the quadratic norm subgroup. -/
@[simp]
theorem ker_hilbertSymbolHom (a : Kˣ)
    (hindex : (quadraticNormSubgroup a).index ∣ 2) :
    (hilbertSymbolHom a hindex).ker = quadraticNormSubgroup a := by
  rw [hilbertSymbolHom, Subgroup.ker_signIndicatorHom]

end TauCeti
