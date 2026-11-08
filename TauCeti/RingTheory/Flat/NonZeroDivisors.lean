/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Nonzerodivisors in flat algebras

A flat algebra `A` over a commutative ring `R` is torsion-free: multiplication by a nonzerodivisor
of `R` is injective on `A` (`Module.Flat.isSMulRegular_of_nonZeroDivisors`). Since the image of
`R` in `A` is central, this says that the structure map sends nonzerodivisors of `R` to
nonzerodivisors of `A`. Over a Bezout domain, such as a discrete valuation ring, torsion-freeness
is also sufficient for flatness, so an algebra over a Bezout domain is flat exactly when every
nonzero scalar becomes a nonzerodivisor.

## Main results

* `Module.Flat.algebraMap_mem_nonZeroDivisors`: the image of a nonzerodivisor of `R` in a flat
  `R`-algebra is a nonzerodivisor.
* `Module.Flat.flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout`: over a Bezout domain, an
  algebra is flat exactly when the structure map sends nonzero elements to nonzerodivisors.
* `Module.Flat.of_algebraMap_injective_of_isBezout`: a domain is flat over a Bezout domain mapping
  injectively into it.
* `Module.Flat.not_quotient_of_mem_nonZeroDivisors`: the quotient `R ⧸ I` by a proper ideal `I`
  containing a nonzerodivisor is not flat over `R`.
-/

public section

namespace Module.Flat

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Flat R A]

/-- The structure map of a flat algebra sends nonzerodivisors to nonzerodivisors. -/
theorem algebraMap_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have h : IsSMulRegular A r := isSMulRegular_of_nonZeroDivisors hr
  refine ⟨fun a ha ↦ h ?_, fun a ha ↦ h ?_⟩ <;> simpa [Algebra.smul_def, Algebra.commutes] using ha

omit [Flat R A] in
/-- Over a Bezout domain, an algebra is flat exactly when the structure map sends every nonzero
element to a nonzerodivisor. -/
theorem flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout [IsDomain R] [IsBezout R] :
    Flat R A ↔ ∀ r : R, r ≠ 0 → algebraMap R A r ∈ nonZeroDivisors A := by
  refine ⟨fun _ r hr ↦ algebraMap_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr),
    fun h ↦ ?_⟩
  rw [flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  rintro a ⟨⟨r, hr⟩, hra⟩
  rw [Submonoid.smul_def, Algebra.smul_def] at hra
  exact (h r (nonZeroDivisors.ne_zero hr)).1 a hra

omit [Flat R A] in
/-- A domain is flat over a Bezout domain mapping injectively into it: over a Bezout domain,
torsion-free modules are flat. -/
theorem of_algebraMap_injective_of_isBezout [IsDomain R] [IsBezout R] [IsDomain A]
    (h : Function.Injective (algebraMap R A)) : Flat R A := by
  rwa [flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot,
    isTorsionFree_iff_algebraMap_injective]

/-- The quotient `R ⧸ I` by a proper ideal `I` containing a nonzerodivisor `r` is not flat over
`R`: the nonzerodivisor `r` would map to a nonzerodivisor of `R ⧸ I`, but it maps to zero in this
nonzero ring. -/
theorem not_quotient_of_mem_nonZeroDivisors {I : Ideal R} (hI : I ≠ ⊤) {r : R}
    (hr : r ∈ nonZeroDivisors R) (hrI : r ∈ I) : ¬ Flat R (R ⧸ I) := by
  intro _
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h0 := algebraMap_mem_nonZeroDivisors (A := R ⧸ I) hr
  rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hrI] at h0
  exact zero_notMem_nonZeroDivisors h0

end Module.Flat
