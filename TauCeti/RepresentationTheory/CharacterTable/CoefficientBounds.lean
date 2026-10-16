/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RingTheory.Cyclotomic.Bounds

/-!
# Quantitative power-basis bounds for character values

A character at an element satisfying `g ^ e = 1` is a sum of `dim V` many `e`-th roots of unity.
Consequently its exact cyclotomic representative has coefficients of absolute value at most
`dim V * Cyclotomic.rootCoeffBound e`. For a central character on a class of size `m`, the
identity `dim V * ω = m * χ` cancels the degree and gives the bound `m * rootCoeffBound e`.

These bounds apply to the actual coefficient vectors used by modular reconstruction. They do
not assume that the roots of unity have coefficients bounded by one in the power basis.

The eigenvalue description used here is `Representation.exists_multiset_rootsOfUnity_char_eq_sum`.
See J.-P. Serre, *Linear Representations of Finite Groups*, §§2.1 and 6.3, for characters as sums
of eigenvalues and the central-character conversion.
-/

public section

open Module TauCeti

namespace Representation

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
variable [FiniteDimensional ℂ V] {e : ℕ} [NeZero e]

/-- Every power-basis coefficient of an exact character value is bounded by the degree times
the largest coefficient of an `e`-th root of unity. No irreducibility hypothesis is needed. -/
theorem coeff_natAbs_le_of_complexEmbedding_eq_char (ρ : Representation ℂ G V)
    {g : G} (hg : g ^ e = 1) {x : Cyclotomic e}
    (hx : Cyclotomic.complexEmbedding x = ρ.character g) (j : ℕ) :
    (x.coeff j).natAbs ≤ finrank ℂ V * Cyclotomic.rootCoeffBound e := by
  obtain ⟨s, hcard, hroot, hsum⟩ := ρ.exists_multiset_rootsOfUnity_char_eq_sum hg
  obtain ⟨y, hy, hbound⟩ :=
    Cyclotomic.exists_complexEmbedding_eq_sum_and_coeff_natAbs_le s hroot
  have hxy : x = y := Cyclotomic.complexEmbedding_injective (hx.trans (hsum.trans hy.symm))
  simpa only [hxy, hcard] using hbound j

/-- For an exact value satisfying `dim V * ω = m * χ(g)`, every coefficient is bounded by
`m * rootCoeffBound e`. This is the degree-independent bound on central-character values. -/
theorem coeff_natAbs_le_of_finrank_mul_complexEmbedding_eq_natCast_mul_char
    (ρ : Representation ℂ G V)
    {g : G} (hg : g ^ e = 1) (hdim : 0 < finrank ℂ V) {x : Cyclotomic e} {m : ℕ}
    (hx : (finrank ℂ V : ℂ) * Cyclotomic.complexEmbedding x = m * ρ.character g)
    (j : ℕ) : (x.coeff j).natAbs ≤ m * Cyclotomic.rootCoeffBound e := by
  obtain ⟨s, hcard, hroot, hsum⟩ := ρ.exists_multiset_rootsOfUnity_char_eq_sum hg
  obtain ⟨y, hy, hbound⟩ :=
    Cyclotomic.exists_complexEmbedding_eq_sum_and_coeff_natAbs_le s hroot
  have heq : (finrank ℂ V : Cyclotomic e) * x = (m : Cyclotomic e) * y := by
    apply Cyclotomic.complexEmbedding_injective
    simpa only [map_mul, map_natCast, hy, ← hsum] using hx
  have hc := congrArg (fun z : Cyclotomic e ↦ (z.coeff j).natAbs) heq
  rw [← Int.cast_natCast (R := Cyclotomic e) (finrank ℂ V),
    ← Int.cast_natCast (R := Cyclotomic e) m] at hc
  simp only [Cyclotomic.coeff_intCast_mul, Int.natAbs_mul, Int.natAbs_natCast] at hc
  apply Nat.le_of_mul_le_mul_left _ hdim
  calc
    finrank ℂ V * (x.coeff j).natAbs = m * (y.coeff j).natAbs := hc
    _ ≤ m * (finrank ℂ V * Cyclotomic.rootCoeffBound e) := by
      exact Nat.mul_le_mul_left m (hcard ▸ hbound j)
    _ = finrank ℂ V * (m * Cyclotomic.rootCoeffBound e) := by ac_rfl

end Representation
