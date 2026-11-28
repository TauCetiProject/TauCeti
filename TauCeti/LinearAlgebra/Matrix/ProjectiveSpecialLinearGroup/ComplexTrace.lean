/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Traces of torsion elements of the complex projective special linear group

A lift of a nonidentity finite-order element of `PSL(2, ℂ)` has real trace strictly between
`-2` and `2`. Its eigenvalues are reciprocal roots of unity. The endpoints would give a
scalar or a parabolic element, and parabolic elements have infinite order.

For the classification of Möbius transformations by trace, see J. Elstrodt, F. Grunewald
and J. Mennicke, *Groups Acting on Hyperbolic Space*, Chapter 1.
-/

public section

open scoped MatrixGroups ComplexConjugate

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The trace of either lift of a nonidentity torsion element of `PSL(2, ℂ)` lies in the
open real interval `(-2, 2)`. -/
theorem trace_mem_ofReal_image_Ioo_of_isOfFinOrder_mk {A : SL(2, ℂ)}
    (hfin : IsOfFinOrder (A : PSL(2, ℂ))) (hne : (A : PSL(2, ℂ)) ≠ 1) :
    A.val.trace ∈ Complex.ofReal '' Set.Ioo (-2) 2 := by
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
  have hA : IsOfFinOrder A :=
    (Submonoid.isOfFinOrder_coe.2 (isOfFinOrder_of_finite
      (⟨A ^ n, hpow⟩ : Subgroup.center SL(2, ℂ)))).of_pow hn.ne'
  obtain ⟨m, hm, hAm⟩ := hA.exists_pow_eq_one
  obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional (𝕜 := ℂ) A.val
  have hzm : z ^ m = 1 := by
    simpa only [← SpecialLinearGroup.coe_pow, hAm, SpecialLinearGroup.coe_one, spectrum.one_eq,
      Set.mem_singleton_iff] using spectrum.pow_mem_pow A.val m hz
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hzm hm.ne'
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero)
  have hroot : z ^ 2 - A.val.trace * z + 1 = 0 := by
    simpa [Polynomial.IsRoot.def, charpoly_fin_two, A.det_coe] using
      mem_spectrum_iff_isRoot_charpoly.mp hz
  have htr : A.val.trace = z + z⁻¹ := by
    field_simp
    linear_combination -hroot
  rw [Complex.inv_eq_conj hnorm, Complex.add_conj] at htr
  have hbound := abs_le.mp ((Complex.abs_re_le_norm z).trans_eq hnorm)
  have hsq : A.val.trace ^ 2 ≠ 4 := fun h ↦
    (eq_one_or_isParabolic_of_trace_sq_eq_four h).elim hne (fun hp ↦ hp.not_isOfFinOrder hfin)
  refine ⟨2 * z.re, ⟨?_, ?_⟩, by simpa using htr.symm⟩
  all_goals
    by_contra! h
    apply hsq
    have he : z.re = -1 ∨ z.re = 1 := by grind
    rcases he with h | h <;> norm_num [htr, h]

end Matrix.ProjectiveSpecialLinearGroup
