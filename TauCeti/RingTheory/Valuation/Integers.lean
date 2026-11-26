/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Rings of integers: domains and perfection

A ring of integers `O` for a valuation `v` on a domain `R` (in the sense of `Valuation.Integers`)
embeds into `R`, so it is a domain.

If `O` is a ring of integers for a valuation `v` on a ring `R` (in the sense of
`Valuation.Integers`) and `R` is perfect, then so is `O`: a `p`-th root of an integral element is
integral, since `v y ^ p ≤ 1` forces `v y ≤ 1`. For instance the ring of integers `𝒪_F` of a
perfect valued field `F` of characteristic `p` is perfect, as is needed to form the Witt vectors
`W(𝒪_F)` with their Teichmüller expansions.

A ring is its own ring of integers for any valuation that is at most `1` everywhere, for instance
a domain for its trivial valuation. So constructions taking a ring of integers, such as the Gauss
valuations on Witt vectors, apply to a perfect field with its trivial valuation.

Multiplication by a unit of valuation one maps the ring of integers `v.integer` onto itself; on a
local field this says that the units of `𝒪[K]` preserve additive Haar measure.

## Main results

* `Valuation.Integers.isDomain`: the ring of integers of a domain is a domain.
* `Valuation.Integers.equivInteger`: a ring of integers is isomorphic to the integer subring.
* `Valuation.Integers.perfectRing`: the ring of integers of a perfect ring is perfect.
* `Valuation.Integers.isNontrivial_of_ne_zero_of_not_isUnit`: if the ring of integers of a
  valuation on a field contains a nonzero nonunit, the valuation is nontrivial.
* `Valuation.integers_self_iff`: a ring is the ring of integers of a valuation on it iff the
  valuation is at most `1` everywhere.
* `Valuation.units_smul_integer`: a unit of valuation one maps the ring of integers onto itself.
-/

public section

namespace Valuation.Integers

variable {R Γ₀ O : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
  [CommRing O] [Algebra O R]

/-- **The ring of integers of a domain is a domain**, as it embeds into it. -/
theorem isDomain [IsDomain R] (hv : v.Integers O) : IsDomain O :=
  Function.Injective.isDomain _ hv.hom_inj

/-- A ring of integers for a valuation is isomorphic to its integer subring. -/
noncomputable def equivInteger (hv : v.Integers O) : O ≃+* v.integer := by
  let j := (algebraMap O R).codRestrict v.integer fun x ↦
    (v.mem_integer_iff _).mpr (hv.map_le_one x)
  refine RingEquiv.ofBijective j ⟨RingHom.injective_codRestrict.mpr hv.hom_inj, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hv.exists_of_le_one y.property
  exact ⟨x, Subtype.ext hx⟩

/-- The integer-subring equivalence induces the structural map into the valued ring. -/
@[simp]
theorem coe_equivInteger_apply (hv : v.Integers O) (x : O) :
    (hv.equivInteger x : R) = algebraMap O R x := by
  unfold equivInteger
  exact (congrArg Subtype.val (RingEquiv.ofBijective_apply _ _ x)).trans
    (RingHom.codRestrict_apply _ _ _ x)

/-- The inverse integer-subring equivalence recovers the underlying element in the valued ring. -/
@[simp]
theorem algebraMap_equivInteger_symm_apply (hv : v.Integers O) (y : v.integer) :
    algebraMap O R (hv.equivInteger.symm y) = (y : R) := by
  rw [← hv.coe_equivInteger_apply, RingEquiv.apply_symm_apply]

/-- **The ring of integers of a perfect ring is perfect.** If `O` is a ring of integers for a
valuation on a ring `R` that is perfect for the exponent `p`, then `O` is perfect for `p`. -/
theorem perfectRing (hv : v.Integers O) (p : ℕ) [PerfectRing R p] : PerfectRing O p := by
  have hR := PerfectRing.bijective_frobenius (R := R) (p := p)
  refine ⟨⟨fun x y hxy ↦ hv.hom_inj <| hR.1 ?_, fun x ↦ ?_⟩⟩
  · simpa only [map_pow] using congrArg (algebraMap O R) hxy
  obtain ⟨y, hy⟩ : ∃ y, y ^ p = algebraMap O R x := hR.2 _
  have hyv : v y ≤ 1 := by
    rcases eq_or_ne p 0 with rfl | hp
    · -- For `p = 0` the injectivity of `x ↦ x ^ 0` forces `y = 1`.
      rw [hR.1 (show y ^ 0 = 1 ^ 0 by simp only [pow_zero]), map_one]
    · rw [← pow_le_one_iff hp, ← map_pow, hy]
      exact hv.map_le_one x
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hyv
  exact ⟨z, hv.hom_inj (by simpa only [map_pow] using hy)⟩

/-- **A ring of integers of a field with a nonzero nonunit witnesses a nontrivial valuation.**
If `O` is a ring of integers for a valuation `v` on a field `F`, any nonzero nonunit `ϖ : O` maps
to an element of `F` with `0 < v (algebraMap O F ϖ) < 1`. That `F` is a field is needed: by
`Valuation.integers_self_iff`, any domain that is not a field is its own ring of integers for the
trivial valuation. -/
theorem isNontrivial_of_ne_zero_of_not_isUnit {F Γ₀ O : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀} [CommRing O] [Algebra O F]
    (hv : v.Integers O) {ϖ : O} (hϖ0 : ϖ ≠ 0) (hϖu : ¬ IsUnit ϖ) : v.IsNontrivial where
  exists_val_nontrivial := by
    have hϖF : algebraMap O F ϖ ≠ 0 := (map_ne_zero_iff _ hv.hom_inj).mpr hϖ0
    exact ⟨algebraMap O F ϖ, (Valuation.ne_zero_iff _).mpr hϖF,
      fun h1 ↦ hϖu (hv.isUnit_of_one (isUnit_iff_ne_zero.mpr hϖF) h1)⟩

end Valuation.Integers

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}

/-- **A ring is the ring of integers of a valuation on it exactly when the valuation is at most
`1` everywhere.** For instance a domain is the ring of integers of its trivial valuation
(`Valuation.one_apply_le_one`). -/
theorem integers_self_iff : v.Integers R ↔ ∀ x, v x ≤ 1 :=
  ⟨fun hv ↦ hv.map_le_one, fun h ↦ ⟨Function.injective_id, h, fun r _ ↦ ⟨r, rfl⟩⟩⟩

open scoped Pointwise in
/-- **A unit of valuation one maps the ring of integers onto itself.** -/
theorem units_smul_integer {u : Rˣ} (hu : v u = 1) : u • (v.integer : Set R) = v.integer := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp [Units.smul_def, Valuation.mem_integer_iff, hu]

end Valuation
