/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.Multiquadratic.Degree
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Square-class independence as `ZMod 2`-linear independence

The multiquadratic degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range` takes the
**square-class independence** hypothesis in the elaboration-friendly *Finset form*: no nonempty
subset product `∏_{i ∈ S} d i` of the radicands is a square in `K`. The Galois-theoretic
arguments instead want the structural form: the classes of the `d i` in the square-class group
`Kˣ ⧸ (Kˣ)²` are `ZMod 2`-linearly independent. This file connects the two.

The square-class group is the quotient of `Kˣ` by its squares. Every element has order dividing
`2`, so the quotient is an `𝔽₂ = ZMod 2`-vector space (Mathlib's `QuotientAddGroup.zmodModule`,
written additively on `Additive Kˣ`). A `ZMod 2`-linear combination of the classes is, up to the
`{0, 1}` coefficients, exactly a subset product, and it vanishes precisely when that subset
product is a square. So linear independence of the classes is the same statement as the Finset
form, one subset at a time.

## Main definitions and results

* `TauCeti.Multiquadratic.SquareClassGroup`: the square-class group `Kˣ ⧸ (Kˣ)²`, an
  `𝔽₂`-vector space.
* `TauCeti.Multiquadratic.squareClass`: the class of a unit, with
  `squareClass_eq_zero_iff` characterising the trivial class as the squares.
* `TauCeti.Multiquadratic.linearIndependent_squareClass_iff`: the classes of `d : ι → Kˣ` are
  `ZMod 2`-linearly independent iff no nonempty subset product is a square.
* `TauCeti.Multiquadratic.finrank_adjoin_range_of_linearIndependent`: the degree theorem
  `[K(rootᵢ : i) : K] = 2^|ι|` restated against linear independence of the unit classes.
-/

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K]

/-- The squares `(Kˣ)²`, viewed as an additive subgroup of `Additive Kˣ`. -/
def squaresAddSubgroup (K : Type*) [Field K] : AddSubgroup (Additive Kˣ) :=
  Subgroup.toAddSubgroup (powMonoidHom 2 : Kˣ →* Kˣ).range

/-- A unit lies in the squares subgroup iff it is a square. -/
theorem mem_squaresAddSubgroup_iff (g : Additive Kˣ) :
    g ∈ squaresAddSubgroup K ↔ IsSquare (Additive.toMul g) := by
  rw [squaresAddSubgroup, Additive.mem_toAddSubgroup, MonoidHom.mem_range,
    isSquare_iff_exists_sq]
  simp only [powMonoidHom_apply]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-- **The square-class group** `Kˣ ⧸ (Kˣ)²`, written additively on `Additive Kˣ`. -/
abbrev SquareClassGroup (K : Type*) [Field K] : Type _ :=
  Additive Kˣ ⧸ squaresAddSubgroup K

/-- The square-class group is a `ZMod 2`-module: every element has order dividing two, since the
double of any unit class is the class of a square. -/
instance : Module (ZMod 2) (SquareClassGroup K) :=
  QuotientAddGroup.zmodModule fun x => by
    rw [mem_squaresAddSubgroup_iff, toMul_nsmul]
    exact ⟨Additive.toMul x, pow_two _⟩

/-- The square class of a unit. -/
def squareClass (u : Kˣ) : SquareClassGroup K :=
  QuotientAddGroup.mk (Additive.ofMul u)

/-- A unit has trivial square class iff it is a square. -/
@[simp] theorem squareClass_eq_zero_iff (u : Kˣ) : squareClass u = 0 ↔ IsSquare u := by
  rw [squareClass, QuotientAddGroup.eq_zero_iff, mem_squaresAddSubgroup_iff]
  rfl

/-- The square class of a product is the sum of the square classes. -/
theorem squareClass_prod {ι : Type*} (S : Finset ι) (d : ι → Kˣ) :
    squareClass (∏ i ∈ S, d i) = ∑ i ∈ S, squareClass (d i) := by
  simp only [squareClass, ofMul_prod]
  rw [← QuotientAddGroup.mk'_apply, map_sum]
  simp only [QuotientAddGroup.mk'_apply]

private theorem zmod_two_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

/-- A `ZMod 2`-linear combination of square classes is the class of the corresponding subset
product (the subset where the coefficient is `1`). -/
theorem sum_smul_squareClass {ι : Type*} [Fintype ι] (d : ι → Kˣ)
    (g : ι → ZMod 2) :
    ∑ i, g i • squareClass (d i)
      = squareClass (∏ i ∈ Finset.univ.filter (fun i => g i = 1), d i) := by
  rw [squareClass_prod, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod_two_eq_zero_or_one (g i) with h | h
  · rw [h, zero_smul]; exact (if_neg (by decide)).symm
  · rw [h, one_smul]; exact (if_pos rfl).symm

/-- **Square-class independence is `ZMod 2`-linear independence.** For a finite family of units
`d : ι → Kˣ`, the square classes `squareClass (d i)` are `ZMod 2`-linearly independent in the
square-class group iff no nonempty subset product `∏_{i ∈ S} d i` is a square. The right-hand side
is the Finset form of square-class independence that the multiquadratic degree theorem consumes. -/
theorem linearIndependent_squareClass_iff {ι : Type*} [Finite ι] (d : ι → Kˣ) :
    LinearIndependent (ZMod 2) (fun i => squareClass (d i)) ↔
      ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i) := by
  classical
  letI := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  constructor
  · -- A nonempty square subset product would give a nontrivial linear dependence.
    intro H S hS hsq
    set g : ι → ZMod 2 := fun i => if i ∈ S then 1 else 0 with hg
    have hfilter : Finset.univ.filter (fun i => g i = 1) = S := by
      ext i
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨-, hi⟩
        by_contra hiS
        rw [hg] at hi
        simp only [hiS, if_false] at hi
        exact absurd hi (by decide)
      · intro hiS
        exact ⟨Finset.mem_univ i, by rw [hg]; simp [hiS]⟩
    have hsum : ∑ i, g i • squareClass (d i) = 0 := by
      rw [sum_smul_squareClass, hfilter, squareClass_eq_zero_iff]
      exact hsq
    obtain ⟨i, hiS⟩ := hS
    have hi0 := H g hsum i
    rw [hg] at hi0
    simp only [hiS, if_true] at hi0
    exact absurd hi0 (by decide)
  · -- A linear dependence singles out a nonempty square subset product.
    intro H g hsum i
    by_contra hgi
    have hg1 : g i = 1 := (zmod_two_eq_zero_or_one (g i)).resolve_left hgi
    set S : Finset ι := Finset.univ.filter (fun j => g j = 1) with hS
    have hiS : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hg1⟩
    rw [sum_smul_squareClass, squareClass_eq_zero_iff] at hsum
    exact H S ⟨i, hiS⟩ hsum

variable {L : Type*} [Field L] [Algebra K L]

/-- A unit is a square iff its underlying field element is. -/
theorem isSquare_units_val_iff {u : Kˣ} : IsSquare (u : K) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := fun h => u.ne_zero (by rw [hx, h, mul_zero])
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(v : K), by simp⟩

/-- **The multiquadratic degree theorem, restated via linear independence.** If the square classes
of the radicands `d : ι → Kˣ` are `ZMod 2`-linearly independent, then the field generated over `K`
by their square roots `root i` has degree `2^|ι|`. This is `finrank_adjoin_range` consuming the
structural form of square-class independence. -/
theorem finrank_adjoin_range_of_linearIndependent {ι : Type*} [Finite ι] {d : ι → Kˣ}
    {root : ι → L} (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) [NeZero (2 : K)]
    (hli : LinearIndependent (ZMod 2) (fun i => squareClass (d i))) :
    Module.finrank K (IntermediateField.adjoin K (Set.range root)) = 2 ^ Nat.card ι := by
  letI := Fintype.ofFinite ι
  refine finrank_adjoin_range (d := fun i => (d i : K)) hroot (fun S hS => ?_)
  have hne := (linearIndependent_squareClass_iff d).mp hli S hS
  rw [← Units.coe_prod, isSquare_units_val_iff]
  exact hne

end TauCeti.Multiquadratic
