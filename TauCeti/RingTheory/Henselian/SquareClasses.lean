/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Unit square classes in a Henselian local ring

When two is invertible, a unit of a Henselian local ring is a square exactly when its residue
is a square. With finite residue field, any nonsquare unit represents the only nontrivial unit
square class. These are the square tests used to select the two unimodular bilinear forms of
each positive rank.

The root lifting uses `TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq`; the finite
field calculation uses Mathlib's `FiniteField.isSquare_iff` and `FiniteField.pow_dichotomy`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §2.
-/

public section

namespace TauCeti.HenselianLocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- Away from residue characteristic two, a unit is a square exactly when its residue is. -/
theorem isSquare_iff_residue_isSquare (h2 : IsUnit (2 : R)) {a : R} (ha : IsUnit a) :
    IsSquare a ↔ IsSquare (residue R a) := by
  refine ⟨fun h ↦ h.map (residue R), ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨x₀, rfl⟩ := residue_surjective x
  have hx₀ : IsUnit x₀ := (residue_ne_zero_iff_isUnit x₀).mp fun h0 ↦
    (ha.map (residue R)).ne_zero (by simpa [h0] using hx)
  obtain ⟨y, hy, -⟩ := exists_pow_eq_of_residue_pow_eq (n := 2)
    (by exact_mod_cast h2) hx₀ (by simpa [pow_two] using hx.symm)
  exact ⟨y, by simpa [pow_two] using hy.symm⟩

/-- With finite residue field of odd characteristic, multiplication by a fixed nonsquare unit
interchanges the two unit square classes. -/
theorem isSquare_mul_iff_of_not_isSquare [Finite (ResidueField R)]
    (h2 : IsUnit (2 : R)) {a u : R} (ha : IsUnit a) (hu : IsUnit u) (husq : ¬IsSquare u) :
    IsSquare (a * u) ↔ ¬IsSquare a := by
  classical
  let _ := Fintype.ofFinite (ResidueField R)
  have hchar : ringChar (ResidueField R) ≠ 2 := by
    intro h
    have hne := (h2.map (residue R)).ne_zero
    rw [map_ofNat] at hne
    exact hne (by exact_mod_cast h ▸ ringChar.Nat.cast_ringChar)
  have ha0 := (ha.map (residue R)).ne_zero
  have hu0 := (hu.map (residue R)).ne_zero
  have hun : ¬IsSquare (residue R u) :=
    (isSquare_iff_residue_isSquare h2 hu).not.mp husq
  have hup : residue R u ^ (Fintype.card (ResidueField R) / 2) = -1 :=
    (FiniteField.pow_dichotomy hchar hu0).resolve_left
      (fun h ↦ hun ((FiniteField.isSquare_iff hchar hu0).mpr h))
  rw [isSquare_iff_residue_isSquare h2 (ha.mul hu), map_mul,
    FiniteField.isSquare_iff hchar (mul_ne_zero ha0 hu0), mul_pow, hup,
    isSquare_iff_residue_isSquare h2 ha, FiniteField.isSquare_iff hchar ha0]
  rcases FiniteField.pow_dichotomy hchar ha0 with h | h <;>
    simp [h, Ring.neg_one_ne_one_of_char_ne_two hchar]

end TauCeti.HenselianLocalRing
