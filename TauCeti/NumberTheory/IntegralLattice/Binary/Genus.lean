/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.NormForm
public import TauCeti.NumberTheory.IntegralLattice.Genus

/-!
# Genus invariants of binary lattices

The content `c` and the primitive discriminant `Δ` of a rank-two lattice depend only on its genus.
The content generates the norm ideal (`TauCeti.IntegralLattice.normIdeal_eq_span_binaryContent`),
which is a genus invariant (`TauCeti.IntegralLattice.SameGenus.normIdeal_eq`), and the primitive
discriminant is then fixed by `c² Δ = -4 det L`, the determinant being a genus invariant as well.

Consequently all lattices of one genus have the same quadratic order `𝒪(L) = ℤ[(Δ + √Δ)/2]`, so
for a definite binary genus their special orthogonal groups have a common order, the number of
units of `𝒪(L)`.

## Main results

* `TauCeti.IntegralLattice.SameGenus.binaryContent_eq`: lattices in one genus have the same
  content.
* `TauCeti.IntegralLattice.SameGenus.binaryDiscriminant_eq`: lattices in one genus have the same
  primitive discriminant.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13, for binary forms and their genera.
-/

public section

open Module

namespace TauCeti.IntegralLattice.SameGenus

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

/-- **The content of a binary lattice is a genus invariant.** -/
theorem binaryContent_eq (h : L.SameGenus M) (hV : finrank ℚ V = 2) (hW : finrank ℚ W = 2) :
    L.binaryContent hV = M.binaryContent hW := by
  have hspan := (L.normIdeal_eq_span_binaryContent hV).symm.trans
    (h.normIdeal_eq.trans (M.normIdeal_eq_span_binaryContent hW))
  simpa using Int.natAbs_eq_iff_associated.mpr (Ideal.span_singleton_eq_span_singleton.mp hspan)

/-- **The primitive discriminant of a binary lattice is a genus invariant.** -/
theorem binaryDiscriminant_eq (h : L.SameGenus M) (hV : finrank ℚ V = 2)
    (hW : finrank ℚ W = 2) : L.binaryDiscriminant hV = M.binaryDiscriminant hW := by
  have hc := h.binaryContent_eq hV hW
  by_cases h₀ : L.binaryContent hV = 0
  · -- Both norm forms vanish, so both primitive discriminants are that of the zero form.
    let b := finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
    let b' := finBasisOfFinrankEq ℤ M (M.finrank_carrier.trans hW)
    have hL := (L.binaryNormForm b).content_eq_zero_iff.mp
      ((L.binaryContent_eq_content_binaryNormForm b hV).symm.trans h₀)
    have hM := (M.binaryNormForm b').content_eq_zero_iff.mp
      ((M.binaryContent_eq_content_binaryNormForm b' hW).symm.trans (hc ▸ h₀))
    rw [L.binaryDiscriminant_eq_discrim_primPart b hV,
      M.binaryDiscriminant_eq_discrim_primPart b' hW, hL, hM]
  · have hL := L.binaryContent_sq_mul_binaryDiscriminant hV
    rw [h.determinant_eq, ← M.binaryContent_sq_mul_binaryDiscriminant hW, hc] at hL
    exact mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hc ▸ h₀)) hL

end TauCeti.IntegralLattice.SameGenus
