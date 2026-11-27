/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Localization.DenIdeal
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Membership in embedded localizations

For an arbitrary subalgebra of an ambient commutative semiring, an `IsLocalization` instance
characterizes its elements by the denominators that clear them into the coefficient image.
The general criterion uses `Algebra.denIdeal`; for principal localizations it specializes to
power-denominator clearing. No field, total-quotient-ring or Dedekind hypothesis is required.
-/

public section

namespace TauCeti.IsLocalization

variable {R K : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]

/-- An element belongs to an embedded localization precisely when its denominator ideal
`Algebra.denIdeal K x` meets the denominator monoid. -/
theorem mem_subalgebra_iff_exists_mem_denIdeal (S : Submonoid R) (A : Subalgebra R K)
    [IsLocalization S A] (x : K) :
    x ∈ A ↔ ∃ s ∈ S, s ∈ Algebra.denIdeal K x := by
  constructor
  · intro hx
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj S (⟨x, hx⟩ : A)
    have h := congrArg (fun y : A ↦ (y : K)) he
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at h
    exact ⟨s, s.property, (Algebra.mem_denIdeal_iff K).mpr
      ⟨r, by simpa only [mul_comm] using h⟩⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨r, hr⟩ := (Algebra.mem_denIdeal_iff K).mp hx
    obtain ⟨v, hv⟩ := IsLocalization.map_units A (⟨s, hs⟩ : S)
    have hvK : ((v : A) : K) = algebraMap R K s := by
      simpa only [Subalgebra.coe_algebraMap] using
        congrArg (fun y : A ↦ (y : K)) hv
    let u : Kˣ := Units.map (A.val : A →* K) v
    have hu : (u : K) = algebraMap R K s := by
      simpa only [u, Units.coe_map, AlgHom.coe_toMonoidHom, Subalgebra.val_apply] using hvK
    have he : x = (↑u⁻¹ : K) * algebraMap R K r := by
      rw [← hr, ← hu]
      exact (Units.inv_mul_cancel_left u x).symm
    rw [he]
    exact A.mul_mem (by
      simpa only [u, Units.coe_map_inv, AlgHom.coe_toMonoidHom, Subalgebra.val_apply] using
        (v⁻¹).val.property) (A.algebraMap_mem r)

/-- In a principal embedded localization, membership means that some power of the
localizing element clears the denominator into the coefficient image. -/
theorem mem_subalgebra_iff_exists_pow_mul_mem_range (a : R) (A : Subalgebra R K)
    [IsLocalization (Submonoid.powers a) A] (x : K) :
    x ∈ A ↔ ∃ n : ℕ, algebraMap R K a ^ n * x ∈ Set.range (algebraMap R K) := by
  rw [mem_subalgebra_iff_exists_mem_denIdeal (Submonoid.powers a) A x]
  simp only [Submonoid.mem_powers_iff, exists_exists_eq_and]
  simp only [Algebra.mem_denIdeal_iff, map_pow, Set.mem_range, eq_comm]

end TauCeti.IsLocalization
