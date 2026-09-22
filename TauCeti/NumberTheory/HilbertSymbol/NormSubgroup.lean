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

/-!
# The quadratic norm subgroup

For `a : Rˣ` over a commutative ring `R`, this file packages the unit norms from the quadratic
algebra `R[√a] = QuadraticAlgebra R a 0` as a subgroup of `Rˣ`. Over a field the norm-equation
Hilbert symbol is exactly the sign indicator of this subgroup.

This separates the ring-generic group theory from the arithmetic input used over a
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

section CommRing

variable {R : Type*} [CommRing R]

/-- The norm on the units of the quadratic algebra `R[√a]`, with values in `Rˣ`. -/
noncomputable def quadraticNormHom (a : Rˣ) :
    (QuadraticAlgebra R (a : R) 0)ˣ →* Rˣ :=
  Units.map (QuadraticAlgebra.norm (R := R) (a := (a : R)) (b := 0))

/-- The quadratic norm homomorphism evaluates to the quadratic-algebra norm. -/
@[simp]
theorem quadraticNormHom_apply (a : Rˣ) (z : (QuadraticAlgebra R (a : R) 0)ˣ) :
    ((quadraticNormHom a z : Rˣ) : R) =
      (z : QuadraticAlgebra R (a : R) 0).norm :=
  by simp [quadraticNormHom]

/-- The subgroup of `Rˣ` consisting of unit norms from `R[√a]`. -/
noncomputable def quadraticNormSubgroup (a : Rˣ) : Subgroup Rˣ :=
  (quadraticNormHom a).range

/-- The quadratic norm subgroup is the range of the norm homomorphism on units. -/
theorem quadraticNormSubgroup_def (a : Rˣ) :
    quadraticNormSubgroup a = (quadraticNormHom a).range :=
  (rfl)

/-- Membership in the quadratic norm subgroup is the existence of a unit with the given norm. -/
@[simp]
theorem mem_quadraticNormSubgroup_iff (a b : Rˣ) :
    b ∈ quadraticNormSubgroup a ↔
      ∃ z : (QuadraticAlgebra R (a : R) 0)ˣ,
        (z : QuadraticAlgebra R (a : R) 0).norm = b := by
  rw [quadraticNormSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (quadraticNormHom_apply a z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, Units.ext ?_⟩
    exact (quadraticNormHom_apply a z).trans hz

/-- An element of `R[√a]` whose norm is a unit already witnesses membership in the quadratic
norm subgroup, so no unit hypothesis on the witness is needed. -/
theorem mem_quadraticNormSubgroup_iff_exists_norm_eq (a b : Rˣ) :
    b ∈ quadraticNormSubgroup a ↔ ∃ z : QuadraticAlgebra R (a : R) 0, z.norm = b := by
  rw [mem_quadraticNormSubgroup_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    have hz' : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ b.isUnit)
    exact ⟨hz'.unit, by simpa using hz⟩

/-- Every square is a norm from a quadratic algebra. -/
theorem square_le_quadraticNormSubgroup (a : Rˣ) :
    Subgroup.square Rˣ ≤ quadraticNormSubgroup a := by
  intro b hb
  obtain ⟨c, rfl⟩ := Subgroup.mem_square.mp hb
  refine (mem_quadraticNormSubgroup_iff_exists_norm_eq _ _).mpr
    ⟨algebraMap R (QuadraticAlgebra R (a : R) 0) (c : R), ?_⟩
  rw [QuadraticAlgebra.norm_algebraMap, pow_two]
  exact (Units.val_mul c c).symm

/-- The index of the quadratic norm subgroup divides the number of square classes. -/
theorem quadraticNormSubgroup_index_dvd_square_index (a : Rˣ) :
    (quadraticNormSubgroup a).index ∣ (Subgroup.square Rˣ).index :=
  Subgroup.index_dvd_of_le (square_le_quadraticNormSubgroup a)

/-- Finiteness of the square-class group implies finite index for the quadratic norm subgroup. -/
theorem finiteIndex_quadraticNormSubgroup (a : Rˣ) [(Subgroup.square Rˣ).FiniteIndex] :
    (quadraticNormSubgroup a).FiniteIndex :=
  Subgroup.finiteIndex_of_le (square_le_quadraticNormSubgroup a)

/-- The element `-a` is the norm of the square-root generator of `R[√a]`. -/
theorem neg_self_mem_quadraticNormSubgroup (a : Rˣ) :
    -a ∈ quadraticNormSubgroup a := by
  refine (mem_quadraticNormSubgroup_iff_exists_norm_eq _ _).mpr ⟨⟨0, 1⟩, ?_⟩
  simp [QuadraticAlgebra.norm_def]

/-- Rescaling the radicand by a square does not change the quadratic norm subgroup. -/
@[simp]
theorem quadraticNormSubgroup_mul_sq (a c : Rˣ) :
    quadraticNormSubgroup (a * c ^ 2) = quadraticNormSubgroup a := by
  have key : ∀ x y : Rˣ, quadraticNormSubgroup (x * y ^ 2) ≤ quadraticNormSubgroup x := by
    intro x y b hb
    obtain ⟨z, hz⟩ := (mem_quadraticNormSubgroup_iff _ _).mp hb
    let e : QuadraticAlgebra R ((x * y ^ 2 : Rˣ) : R) 0 ≃ₐ[R]
        QuadraticAlgebra R (x : R) 0 :=
      QuadraticAlgebra.changeGeneratorEquiv (x : R) 0 y 0 (by push_cast; ring) (by simp)
    refine (mem_quadraticNormSubgroup_iff _ _).mpr ⟨Units.map e.toMonoidHom z, ?_⟩
    exact (QuadraticAlgebra.norm_algHom e.toAlgHom e.injective z).trans hz
  refine le_antisymm (key a c) ?_
  have h := key (a * c ^ 2) c⁻¹
  convert h using 1
  group

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The Hilbert symbol is positive exactly on the quadratic norm subgroup. -/
@[simp]
theorem hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔ b ∈ quadraticNormSubgroup a := by
  rw [mem_quadraticNormSubgroup_iff, hilbertSymbol_eq_one_iff_exists_unit_norm_eq]

/-- The Hilbert symbol is the sign indicator of the quadratic norm subgroup. -/
theorem hilbertSymbol_eq_signIndicator (a b : Kˣ) :
    hilbertSymbol a b = (quadraticNormSubgroup a).signIndicator b := by
  by_cases hb : b ∈ quadraticNormSubgroup a
  · rw [(hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mpr hb,
      Subgroup.signIndicator_of_mem _ hb]
  · have hhilbert : hilbertSymbol a b ≠ 1 :=
      fun h ↦ hb ((hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mp h)
    have hindicator : (quadraticNormSubgroup a).signIndicator b ≠ 1 :=
      fun h ↦ hb ((quadraticNormSubgroup a).signIndicator_eq_one_iff.mp h)
    rw [Int.units_ne_iff_eq_neg.mp hhilbert, Int.units_ne_iff_eq_neg.mp hindicator]

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

end Field

end TauCeti
