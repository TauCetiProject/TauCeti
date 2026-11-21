/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Fiber
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.MulChar.Duality

/-!
# Orthogonality relations for multiplicative characters

Let `M` be a commutative monoid with finitely many units and `R` a domain with enough roots of
unity, such as `ℂ`. Mathlib's `MulChar.sum_eq_zero_of_ne_one` and `MulChar.sum_one_eq_card_units`
sum one character over a finite `M`, and Mathlib's `DirichletCharacter.sum_characters_eq` sums all
Dirichlet characters at one point. Tau Ceti's `CommGroup.sum_monoidHom_apply_eq_ite` and
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` sum the characters `G →* Rˣ` of a finite
commutative group. This file states these sums for the characters `MulChar M R`, through
`MulChar.equivToUnitHom`, in the forms that character sums over a finite field use.

The characters trivial on a subgroup `H` of `Mˣ` are the characters of `Mˣ ⧸ H`, so their values at
a unit `u` sum to the index of `H` if `u ∈ H` and to zero otherwise. For the subgroup of `d`-th
powers, the characters trivial on `H` are the characters `χ` with `χ ^ d = 1`, and the sum is the
number of `d`-th roots of `u` in `Mˣ`; for a finite field this gives the classical count of
solutions of `y ^ d = c`.

Throughout, a cardinality or an index on the right of an identity is a natural number cast into the
coefficient ring `R`. In positive characteristic the identities determine these numbers only modulo
the characteristic; with values in `ℂ` they are exact counts.

## Main results

* `MulChar.sum_apply_eq_ite`: `∑ a, χ a` is the cast of `#Mˣ` if `χ = 1` and zero otherwise.
* `Subgroup.sum_filter_mulChar_apply_eq_ite`: the values at a unit `u` of the characters trivial
  on `H` sum to the cast of `H.index` if `u ∈ H` and to zero otherwise.
* `TauCeti.sum_mulChar_apply_eq_ite`: `∑ χ, χ a` is the cast of `#Mˣ` if `a = 1` and zero
  otherwise.
* `TauCeti.sum_filter_pow_eq_one_apply_eq_card_pow_eq`: the values at a unit `u` of the characters
  `χ` with `χ ^ d = 1` sum to the cast of the number of `y ∈ Mˣ` with `y ^ d = u`.
* `TauCeti.card_units_mul_apply_eq_sum`: the Fourier expansion on `Mˣ` of a function `φ` on `M`,
  `#Mˣ · φ u = ∑ χ, χ u ∑ y, φ y χ⁻¹ y`, and `TauCeti.apply_eq_inv_card_units_mul_sum`, its
  normalized form `φ u = #Mˣ⁻¹ ∑ χ, χ u ∑ y, φ y (χ y)⁻¹` over a field in which `#Mˣ ≠ 0`.
* `TauCeti.card_pow_eq_eq_one_add_sum`: for a finite field `F` and `d ≠ 0`, the cast of the number
  of solutions of `y ^ d = c` in `F` is `1 + ∑_{χ ^ d = 1, χ ≠ 1} χ c`, also at `c = 0`. It holds
  for every finite commutative group with zero.
-/

public section

open Finset

namespace MulChar

/-- The sum of a character over a finite commutative monoid `M` is the cast of the number of
units of `M` for the trivial character and zero otherwise. This puts Mathlib's
`MulChar.sum_eq_zero_of_ne_one` and `MulChar.sum_one_eq_card_units` into one statement. -/
@[simp]
theorem sum_apply_eq_ite {M R : Type*} [CommMonoid M] [Fintype M] [CommRing R] [IsDomain R]
    (χ : MulChar M R) [Decidable (χ = 1)] :
    ∑ a, χ a = if χ = 1 then (Nat.card Mˣ : R) else 0 := by
  classical
  split_ifs with hχ
  · rw [hχ, sum_one_eq_card_units, Nat.card_eq_fintype_card]
  · exact sum_eq_zero_of_ne_one hχ

end MulChar

variable {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] [Fintype (MulChar M R)]

namespace Subgroup

/-- **Orthogonality for the characters trivial on a subgroup.** The values at a unit `u` of the
characters trivial on a subgroup `H` of `Mˣ` sum to the cast of the index of `H` if `u ∈ H` and to
zero otherwise. These characters are the characters of `Mˣ ⧸ H`, so this is
`CommGroup.sum_monoidHom_apply_eq_ite` on `Mˣ ⧸ H`. -/
@[simp]
theorem sum_filter_mulChar_apply_eq_ite (H : Subgroup Mˣ) (u : Mˣ) [DecidablePred (· ∈ H)]
    [DecidablePred fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1] :
    ∑ χ : MulChar M R with ∀ h ∈ H, χ h = 1, χ u = if u ∈ H then (H.index : R) else 0 := by
  classical
  have : HasEnoughRootsOfUnity R (Monoid.exponent (Mˣ ⧸ H)) :=
    HasEnoughRootsOfUnity.of_dvd R (Group.exponent_quotient_dvd H)
  -- The characters trivial on `H` correspond to the characters of `Mˣ ⧸ H`.
  let e : {χ : MulChar M R // ∀ h ∈ H, χ h = 1} ≃ (Mˣ ⧸ H →* Rˣ) :=
    (MulChar.equivToUnitHom.subtypeEquiv fun χ ↦ by
      simp [MonoidHom.mem_ker, MonoidHom.domRestrict_eq_one_iff, Units.ext_iff]).trans
      (MonoidHom.domRestrictHomKerEquiv Rˣ H).toEquiv
  rw [sum_subtype (univ.filter fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1)
      (p := fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1) (fun χ ↦ by simp) fun χ ↦ χ u,
    Fintype.sum_equiv e _ (fun ψ ↦ (ψ (u : Mˣ ⧸ H) : R)) fun χ ↦ by simp [e],
    CommGroup.sum_monoidHom_apply_eq_ite]
  simp only [QuotientGroup.eq_one_iff, index_eq_card]

end Subgroup

namespace TauCeti

open MulChar

/-- **Orthogonality for the characters at a point.** The values at `a` of all characters of `M`
sum to the cast of `#Mˣ` if `a = 1` and to zero otherwise. At a unit this is
`CommGroup.sum_monoidHom_apply_eq_ite` for the characters of `Mˣ`; at a nonunit every term is
zero. -/
@[simp]
theorem sum_mulChar_apply_eq_ite [DecidableEq M] (a : M) :
    ∑ χ : MulChar M R, χ a = if a = 1 then (Nat.card Mˣ : R) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    -- Transport the column orthogonality of the characters `Mˣ →* Rˣ` along `equivToUnitHom`.
    rw [Fintype.sum_equiv equivToUnitHom _ (fun φ : Mˣ →* Rˣ ↦ (φ u : R)) fun χ ↦ by simp,
      CommGroup.sum_monoidHom_apply_eq_ite]
    simp [Units.val_eq_one]
  · rw [ite_eq_right (by rintro rfl; exact ha isUnit_one)]
    exact sum_eq_zero fun χ _ ↦ χ.map_nonunit ha

/-- **Counting `d`-th roots.** The values at a unit `u` of the characters `χ` with `χ ^ d = 1`
sum to the cast of the number of `y ∈ Mˣ` with `y ^ d = u`. -/
theorem sum_filter_pow_eq_one_apply_eq_card_pow_eq (d : ℕ) (u : Mˣ)
    [DecidablePred fun χ : MulChar M R ↦ χ ^ d = 1] :
    ∑ χ : MulChar M R with χ ^ d = 1, χ u = (Nat.card {y : Mˣ // y ^ d = u} : R) := by
  classical
  set f : Mˣ →* Mˣ := powMonoidHom d
  have hfilter : (univ.filter fun χ : MulChar M R ↦ χ ^ d = 1) =
      univ.filter fun χ : MulChar M R ↦ ∀ h ∈ f.range, χ h = 1 := by
    ext χ
    simp [f, pow_eq_one_iff_forall_mem_range]
  rw [hfilter, Subgroup.sum_filter_mulChar_apply_eq_ite]
  split_ifs with hu
  · -- The `d`-th roots of `f x` form a fiber of `f`, which has as many elements as its kernel.
    obtain ⟨x, rfl⟩ := hu
    rw [Subgroup.index_range, ← f.card_fiber_eq_card_ker (a := x) rfl]
    rfl
  · rw [Nat.card_eq_zero.mpr (Or.inl ⟨fun y ↦ hu ⟨y.val, y.property⟩⟩), Nat.cast_zero]

/-- **The Fourier expansion on `Mˣ`.** For a function `φ` on a finite commutative monoid `M` and a
unit `u`, `#Mˣ · φ u = ∑ χ, χ u ∑ y, φ y χ⁻¹ y`. The terms at nonunits `y` vanish, since
`χ⁻¹ y = 0` there. At units it is `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` for the
characters of `Mˣ`. -/
theorem card_units_mul_apply_eq_sum [Fintype M] (φ : M → R) (u : Mˣ) :
    (Nat.card Mˣ : R) * φ u = ∑ χ : MulChar M R, χ u * ∑ y, φ y * χ⁻¹ y := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm (y : M) : ∑ χ : MulChar M R, χ u * (φ y * χ⁻¹ y) =
      if y = u then (Nat.card Mˣ : R) * φ y else 0 := by
    by_cases hy : IsUnit y
    · obtain ⟨v, rfl⟩ := hy
      -- Transport the tagged column orthogonality of the characters `Mˣ →* Rˣ`.
      have key := CommGroup.sum_inv_mul_monoidHom_apply_eq_ite (M := R) v u
      rw [← Fintype.sum_equiv (equivToUnitHom : MulChar M R ≃ (Mˣ →* Rˣ))
        (fun χ ↦ χ⁻¹ v * χ u) (fun φ ↦ (((φ v)⁻¹ : Rˣ) : R) * (φ u : R)) fun χ ↦ by
          rw [inv_apply_eq_inv, ← coe_equivToUnitHom, ← coe_equivToUnitHom, Ring.inverse_unit]]
        at key
      have hcomm (χ : MulChar M R) : χ u * (φ v * χ⁻¹ v) = φ v * (χ⁻¹ v * χ u) := by ring
      rw [sum_congr rfl fun χ _ ↦ hcomm χ, ← mul_sum, key]
      simp only [Units.val_inj, eq_comm (a := v)]
      split_ifs <;> ring
    · rw [ite_eq_right (by rintro rfl; exact hy u.isUnit)]
      exact sum_eq_zero fun χ _ ↦ by simp [χ⁻¹.map_nonunit hy]
  rw [sum_congr rfl fun y _ ↦ hterm y, sum_ite_eq']
  simp

/-- **The normalized Fourier expansion on `Mˣ`.** Over a field `K` in which `#Mˣ ≠ 0`, such as
`ℂ`, `φ u = #Mˣ⁻¹ ∑ χ, χ u ∑ y, φ y (χ y)⁻¹` for every unit `u`. -/
theorem apply_eq_inv_card_units_mul_sum {K : Type*} [Field K]
    [HasEnoughRootsOfUnity K (Monoid.exponent Mˣ)] [Fintype (MulChar M K)] [Fintype M]
    (hK : (Nat.card Mˣ : K) ≠ 0) (φ : M → K) (u : Mˣ) :
    φ u = (Nat.card Mˣ : K)⁻¹ * ∑ χ : MulChar M K, χ u * ∑ y, φ y * (χ y)⁻¹ := by
  simp_rw [← inv_apply_eq_inv']
  rw [← card_units_mul_apply_eq_sum, inv_mul_cancel_left₀ hK]

section GroupWithZero

variable {F : Type*} [CommGroupWithZero F] [Finite F] [HasEnoughRootsOfUnity R (Monoid.exponent Fˣ)]
  [Fintype (MulChar F R)]

/-- **The number of solutions of `y ^ d = c` in a finite field.** Let `F` be a finite field, or
more generally a finite commutative group with zero. For `d ≠ 0` and every `c ∈ F`, the cast into
`R` of the number of solutions is `1 + ∑ χ`, the sum over the nontrivial characters `χ` with
`χ ^ d = 1` at `c`. At `c = 0` both sides are `1`: every character, the trivial one included,
vanishes at `0`. -/
theorem card_pow_eq_eq_one_add_sum {d : ℕ} (hd : d ≠ 0) (c : F)
    [DecidablePred fun χ : MulChar F R ↦ χ ^ d = 1 ∧ χ ≠ 1] :
    (Nat.card {y : F // y ^ d = c} : R) = 1 + ∑ χ : MulChar F R with χ ^ d = 1 ∧ χ ≠ 1, χ c := by
  classical
  by_cases hc : c = 0
  · subst hc
    have : Nat.card {y : F // y ^ d = 0} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨0, zero_pow hd⟩, fun y ↦ Subtype.ext ((pow_eq_zero_iff hd).mp y.property)⟩
    rw [this, Nat.cast_one, left_eq_add]
    exact sum_eq_zero fun χ _ ↦ χ.map_zero
  · lift c to Fˣ using IsUnit.mk0 c hc
    have hsplit := sum_filter_add_sum_filter_not (univ.filter fun χ : MulChar F R ↦ χ ^ d = 1)
      (fun χ ↦ χ = 1) fun χ ↦ χ (c : F)
    rw [filter_filter, filter_filter, sum_filter_pow_eq_one_apply_eq_card_pow_eq] at hsplit
    have hone : (univ.filter fun χ : MulChar F R ↦ χ ^ d = 1 ∧ χ = 1) = {1} := by
      ext χ
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨And.right, fun h ↦ ⟨by rw [h, one_pow], h⟩⟩
    rw [hone, sum_singleton, one_apply_coe] at hsplit
    -- The solutions in `F` are nonzero, so they are the solutions in `Fˣ`.
    have hne {y : F} (hy : y ^ d = c) : y ≠ 0 := fun h ↦ hc (by rw [← hy, h, zero_pow hd])
    have hcard : Nat.card {y : F // y ^ d = c} = Nat.card {y : Fˣ // y ^ d = c} :=
      Nat.card_congr <| (Equiv.subtypeSubtypeEquivSubtype hne).symm.trans
        (unitsEquivNeZero.subtypeEquiv fun y ↦ by simp [Units.ext_iff]).symm
    rw [hcard, ← hsplit]
    -- The two sides differ only in the decidability instance of the filter.
    congr

end GroupWithZero

end TauCeti
