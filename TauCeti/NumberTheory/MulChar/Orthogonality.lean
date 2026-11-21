/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.MulChar.Duality
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality

/-!
# Orthogonality relations for multiplicative characters

Let `M` be a finite commutative monoid and `R` a domain with enough roots of unity, such as `ℂ`.
Mathlib's `MulChar.sum_eq_zero_of_ne_one` and `MulChar.sum_one_eq_card_units` sum one character
over `M`; Mathlib's `DirichletCharacter.sum_characters_eq` sums all Dirichlet characters at one
point, and `CommGroup.sum_monoidHom_apply_eq_ite` in
`TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality` sums the characters `G →* Rˣ` of a
finite commutative group. This file states these sums for the multiplicative characters
`MulChar M R` of every finite commutative monoid, and sums over the characters that are trivial
on a given subgroup `H` of `Mˣ`. These are the forms in which character sums over a finite field
use them.

The characters trivial on `H` are the dual subgroup of `H` (Mathlib's
`MulChar.subgroupOrderIsoSubgroupMulChar`). Their values at a unit `u` sum to the index of `H` if
`u ∈ H` and to zero otherwise. For the subgroup of `d`-th powers, the characters trivial on `H` are
the characters `χ` with `χ ^ d = 1`, and the sum counts the `d`-th roots of `u` in `Mˣ`; for a
finite field this is the classical count of solutions of `y ^ d = c`.

## Main results

* `MulChar.instFintypeMulChar`: the `Fintype` instance on `MulChar M R` for `Mˣ` finite and `R` a
  domain, from Mathlib's `MulChar.finite`. The sums over all characters use it.
* `MulChar.sum_apply_eq_ite`: `∑ a, χ a` is `#Mˣ` if `χ = 1` and zero otherwise.
* `MulChar.sum_filter_apply_eq_ite`: the values at a unit `u` of the characters trivial on a
  subgroup `H` sum to `H.index` if `u ∈ H` and to zero otherwise.
* `MulChar.sum_characters_eq`: `∑ χ, χ a` is `#Mˣ` if `a = 1` and zero otherwise.
* `MulChar.sum_filter_pow_eq_one_apply`: the values at a unit `u` of the characters `χ` with
  `χ ^ d = 1` sum to the number of `y ∈ Mˣ` with `y ^ d = u`.
* `MulChar.card_units_mul_apply_eq_sum`: the Fourier expansion on `Mˣ` of a function `φ` on `M`,
  `#Mˣ · φ u = ∑ χ, χ u ∑ y, φ y (χ y)⁻¹`.
* `MulChar.card_pow_eq_eq_one_add_sum`: for a finite field `F` and `d ≠ 0`, the number of
  solutions of `y ^ d = c` in `F` is `1 + ∑_{χ ^ d = 1, χ ≠ 1} χ c`, also at `c = 0`. It holds for
  every finite commutative group with zero.

-/

public section

open Finset

namespace MulChar

/-- The characters of a monoid with finitely many units, with values in a domain, form a finite
type (Mathlib's `MulChar.finite`). This instance lets one write sums over all characters. -/
noncomputable instance instFintypeMulChar {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R]
    [IsDomain R] : Fintype (MulChar M R) :=
  .ofFinite _

/-- The sum of a character over a finite commutative monoid `M` is the number of units of `M` for
the trivial character and zero otherwise. This puts Mathlib's `MulChar.sum_eq_zero_of_ne_one` and
`MulChar.sum_one_eq_card_units` into one statement. -/
theorem sum_apply_eq_ite {M R : Type*} [CommMonoid M] [Fintype M] [CommRing R] [IsDomain R]
    (χ : MulChar M R) [Decidable (χ = 1)] :
    ∑ a, χ a = if χ = 1 then (Nat.card Mˣ : R) else 0 := by
  classical
  split_ifs with hχ
  · rw [hχ, sum_one_eq_card_units, Nat.card_eq_fintype_card]
  · exact sum_eq_zero_of_ne_one hχ

/-- A character satisfies `χ ^ d = 1` if and only if it is trivial on the `d`-th powers of units. -/
theorem pow_eq_one_iff_forall_mem_range {M R : Type*} [CommMonoid M] [CommMonoidWithZero R]
    (χ : MulChar M R) (d : ℕ) :
    χ ^ d = 1 ↔ ∀ h ∈ (powMonoidHom d : Mˣ →* Mˣ).range, χ h = 1 := by
  simp only [MonoidHom.mem_range, powMonoidHom_apply, forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨fun hχ y ↦ ?_, fun hχ ↦ ext fun y ↦ ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, ← pow_apply_coe, hχ, one_apply_coe]
  · rw [pow_apply_coe, one_apply_coe, ← map_pow]
    exact hχ y

section Finite

variable {M R : Type*} [CommMonoid M] [Finite M] [CommRing R]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/-- A unit lies in a subgroup `H` of `Mˣ` if and only if every character trivial on `H` is
trivial at it. -/
theorem mem_iff_forall_apply_eq_one {H : Subgroup Mˣ} {u : Mˣ} :
    u ∈ H ↔ ∀ χ : MulChar M R, (∀ h ∈ H, χ h = 1) → χ u = 1 := by
  conv_lhs => rw [← (subgroupOrderIsoSubgroupMulChar M R).symm_apply_apply H]
  rw [show subgroupOrderIsoSubgroupMulChar M R H =
      OrderDual.toDual (OrderDual.ofDual (subgroupOrderIsoSubgroupMulChar M R H)) from rfl,
    mem_subgroupOrderIsoSubgroupMulChar_symm_iff]
  simp only [mem_subgroupOrderIsoSubgroupMulChar_iff]

variable [IsDomain R] [Fintype (MulChar M R)]

/-- **Orthogonality for the characters trivial on a subgroup.** The values at a unit `u` of the
characters trivial on a subgroup `H` of `Mˣ` sum to the index of `H` if `u ∈ H` and to zero
otherwise. -/
theorem sum_filter_apply_eq_ite (H : Subgroup Mˣ) (u : Mˣ) [DecidablePred (· ∈ H)]
    [DecidablePred fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1] :
    ∑ χ : MulChar M R with ∀ h ∈ H, χ h = 1, χ u = if u ∈ H then (H.index : R) else 0 := by
  split_ifs with hu
  · rw [sum_congr rfl fun χ hχ ↦ by simp only [mem_filter] at hχ; exact hχ.2 u hu, sum_const,
      nsmul_one]
    congr 1
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    calc Nat.card {χ : MulChar M R // ∀ h ∈ H, χ h = 1}
        _ = Nat.card (subgroupOrderIsoSubgroupMulChar M R H).ofDual :=
          Nat.card_congr (Equiv.subtypeEquivRight fun χ ↦ by simp)
        _ = H.index := card_subgroupOrderIsoSubgroupMulChar
  · obtain ⟨χ₀, hχ₀, hu₀⟩ : ∃ χ₀ : MulChar M R, (∀ h ∈ H, χ₀ h = 1) ∧ χ₀ u ≠ 1 := by
      simpa using (mem_iff_forall_apply_eq_one (R := R)).not.mp hu
    refine eq_zero_of_mul_eq_self_left hu₀ ?_
    rw [mul_sum]
    refine sum_nbij' (χ₀ * ·) (χ₀⁻¹ * ·) (fun χ hχ ↦ ?_) (fun χ hχ ↦ ?_) (fun χ _ ↦ by simp)
      (fun χ _ ↦ by simp) fun χ _ ↦ by simp
    · simp only [mem_filter, mem_univ, true_and] at hχ ⊢
      intro h hh
      simp [hχ₀ h hh, hχ h hh]
    · simp only [mem_filter, mem_univ, true_and] at hχ ⊢
      intro h hh
      rw [mul_apply, hχ h hh, mul_one, inv_apply_eq_inv, hχ₀ h hh, Ring.inverse_one]

/-- **Orthogonality for the characters at a point.** The values at `a` of all characters of a
finite commutative monoid `M` sum to `#Mˣ` if `a = 1` and to zero otherwise. At a unit this is
`CommGroup.sum_monoidHom_apply_eq_ite` for the characters of `Mˣ`; at a nonunit every term is
zero. -/
theorem sum_characters_eq [DecidableEq M] (a : M) :
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
sum to the number of `y ∈ Mˣ` with `y ^ d = u`. -/
theorem sum_filter_pow_eq_one_apply (d : ℕ) (u : Mˣ)
    [DecidablePred fun χ : MulChar M R ↦ χ ^ d = 1] :
    ∑ χ : MulChar M R with χ ^ d = 1, χ u = (Nat.card {y : Mˣ // y ^ d = u} : R) := by
  classical
  set f : Mˣ →* Mˣ := powMonoidHom d
  have hfilter : (univ.filter fun χ : MulChar M R ↦ χ ^ d = 1) =
      univ.filter fun χ : MulChar M R ↦ ∀ h ∈ f.range, χ h = 1 := by
    ext χ
    simp [f, pow_eq_one_iff_forall_mem_range]
  rw [hfilter, sum_filter_apply_eq_ite]
  split_ifs with hu
  · obtain ⟨x, rfl⟩ := hu
    congr 1
    -- The `d`-th roots of `f x` are the translates of the kernel of `f` by `x`.
    have hcard : Nat.card {y : Mˣ // y ^ d = f x} = Nat.card f.ker :=
      Nat.card_congr
        { toFun := fun y ↦ ⟨y * x⁻¹, by simp [f, MonoidHom.mem_ker, mul_pow, y.property]⟩
          invFun := fun y ↦ ⟨y * x, by
            have := (MonoidHom.mem_ker).mp y.property
            simp only [f, powMonoidHom_apply] at this ⊢
            rw [mul_pow, this, one_mul]⟩
          left_inv := fun y ↦ by simp
          right_inv := fun y ↦ by simp }
    rw [hcard]
    have h1 := Subgroup.card_mul_index f.ker
    have h2 := Subgroup.card_mul_index f.range
    rw [Subgroup.index_ker] at h1
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h2, mul_comm, h1])
  · rw [Nat.card_eq_zero.mpr (Or.inl ⟨fun y ↦ hu ⟨y.val, y.property⟩⟩), Nat.cast_zero]

omit [Finite M] in
/-- **The Fourier expansion on `Mˣ`.** For a function `φ` on `M` with values in a field `K` with
enough roots of unity and a unit `u`, `#Mˣ · φ u = ∑ χ, χ u ∑ y, φ y (χ y)⁻¹`. The terms at
nonunits `y` vanish, since `χ y = 0` there. For the characters `G →* Kˣ` of a finite commutative
group, the corresponding statement is `CommGroup.sum_inv_smul_sum_smul`. -/
theorem card_units_mul_apply_eq_sum {K : Type*} [Field K]
    [HasEnoughRootsOfUnity K (Monoid.exponent Mˣ)] [Fintype (MulChar M K)] [Fintype M]
    (φ : M → K) (u : Mˣ) :
    (Nat.card Mˣ : K) * φ u = ∑ χ : MulChar M K, χ u * ∑ y, φ y * (χ y)⁻¹ := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm (y : M) : ∑ χ : MulChar M K, χ u * (φ y * (χ y)⁻¹) =
      if y = u then (Nat.card Mˣ : K) * φ y else 0 := by
    by_cases hy : IsUnit y
    · obtain ⟨v, rfl⟩ := hy
      have (χ : MulChar M K) : χ u * (φ v * (χ v)⁻¹) = φ v * χ ((u * v⁻¹ : Mˣ) : M) := by
        have hinv : χ ((v⁻¹ : Mˣ) : M) = (χ v)⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        rw [Units.val_mul, map_mul, hinv]
        ring
      rw [sum_congr rfl fun χ _ ↦ this χ, ← mul_sum, sum_characters_eq]
      by_cases h : v = u
      · subst h
        simp [mul_comm]
      · have h₁ : ¬((u * v⁻¹ : Mˣ) : M) = 1 := by
          rw [Units.val_eq_one, mul_inv_eq_one]
          exact Ne.symm h
        have h₂ : (v : M) ≠ u := fun e ↦ h (Units.ext e)
        rw [ite_eq_right h₁, ite_eq_right h₂, mul_zero]
    · rw [ite_eq_right (by rintro rfl; exact hy u.isUnit)]
      exact sum_eq_zero fun χ _ ↦ by simp [χ.map_nonunit hy]
  rw [sum_congr rfl fun y _ ↦ hterm y, sum_ite_eq']
  simp

end Finite

section GroupWithZero

variable {F R : Type*} [CommGroupWithZero F] [Finite F] [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent Fˣ)] [Fintype (MulChar F R)]

/-- **The number of solutions of `y ^ d = c` in a finite field.** Let `F` be a finite field, or
more generally a finite commutative group with zero. For `d ≠ 0` and every `c ∈ F`, the number of
solutions is `1 + ∑ χ`, the sum over the nontrivial characters `χ` with `χ ^ d = 1` at `c`.
At `c = 0` both sides are `1`: every character, the trivial one included, vanishes at `0`. -/
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
    rw [filter_filter, filter_filter, MulChar.sum_filter_pow_eq_one_apply] at hsplit
    have hone : (univ.filter fun χ : MulChar F R ↦ χ ^ d = 1 ∧ χ = 1) = {1} := by
      ext χ
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨And.right, fun h ↦ ⟨by rw [h, one_pow], h⟩⟩
    rw [hone, sum_singleton, MulChar.one_apply_coe] at hsplit
    have hcard : Nat.card {y : F // y ^ d = c} = Nat.card {y : Fˣ // y ^ d = c} :=
      Nat.card_congr
        { toFun := fun y ↦
            ⟨(IsUnit.mk0 y.val fun h ↦ hc (by simpa [h, zero_pow hd] using y.property.symm)).unit,
              Units.ext (by simpa using y.property)⟩
          invFun := fun y ↦ ⟨y.val, by simpa using congrArg Units.val y.property⟩
          left_inv := fun y ↦ rfl
          right_inv := fun y ↦ Subtype.ext (Units.ext rfl) }
    rw [hcard, ← hsplit]
    -- The two sides differ only in the decidability instance of the filter.
    congr

end GroupWithZero

end MulChar
