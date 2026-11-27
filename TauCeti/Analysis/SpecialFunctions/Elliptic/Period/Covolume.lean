/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import TauCeti.Algebra.Module.ZLattice.Complex

/-!
# The covolume of a period lattice

The covolume of the lattice of a period pair `(ω₁, ω₂)`, for the Lebesgue measure of `ℂ`, is the
area `|Im (conj ω₁ * ω₂)|` of the parallelogram spanned by `ω₁` and `ω₂`
(`PeriodPair.covolume_lattice`). Rescaling the period pair by `c` multiplies it by `‖c‖ ^ 2`
(`PeriodPair.covolume_lattice_smul`), and the lattice `ℤ τ + ℤ` has covolume `Im τ`
(`UpperHalfPlane.covolume_lattice_periodPair`).
-/

public section

open scoped ComplexConjugate Pointwise UpperHalfPlane

namespace PeriodPair

variable (L : PeriodPair)

/-- The covolume of the lattice of the period pair `(ω₁, ω₂)` is `|Im (conj ω₁ * ω₂)|`, the area of
the parallelogram spanned by `ω₁` and `ω₂`. -/
theorem covolume_lattice :
    ZLattice.covolume L.lattice = |(conj L.ω₁ * L.ω₂).im| := by
  simpa using ZLattice.covolume_eq_abs_im L.lattice L.latticeBasis

/-- Rescaling a period pair by `c` multiplies the covolume of its lattice by `‖c‖ ^ 2`. -/
@[simp]
theorem covolume_lattice_smul (c : ℂˣ) :
    ZLattice.covolume (c • L).lattice = ‖(c : ℂ)‖ ^ 2 * ZLattice.covolume L.lattice := by
  have : NeZero (c : ℂ) := ⟨c.ne_zero⟩
  have h : (c • L).lattice = (c : ℂ) • L.lattice := by
    ext x
    simp [lattice_smul, Submodule.mem_smul_pointwise_iff_exists]
  rw [← ZLattice.covolume_complex_smul]
  -- The covolumes of the two sides are those of the submodules identified by `h`; the instance
  -- arguments of `ZLattice.covolume` are propositions.
  congr 1

end PeriodPair

namespace UpperHalfPlane

/-- The lattice `ℤ τ + ℤ` has covolume `Im τ`. -/
@[simp]
theorem covolume_lattice_periodPair (τ : ℍ) :
    ZLattice.covolume τ.periodPair.lattice = τ.im := by
  rw [PeriodPair.covolume_lattice, periodPair_ω₁, periodPair_ω₂, mul_one, Complex.conj_im,
    coe_im, abs_neg, abs_of_pos τ.im_pos]

end UpperHalfPlane
