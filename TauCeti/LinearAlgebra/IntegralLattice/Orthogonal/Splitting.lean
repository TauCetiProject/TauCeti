/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Orthogonal splitting of integral lattices

A sublattice with perfect restricted pairing is complementary to its orthogonal complement.
A vector of unit norm spans such a summand. These specialize the corresponding results for
symmetric bilinear forms over commutative rings.
The lattice theorems expose these results on `IntegralLattice` without requiring callers to
provide the symmetry of `integralForm` separately. The orthogonal complement of a vector
with nonzero pairing functional has integral rank one less than the lattice.

The unimodular splitting theorem is from O. T. O'Meara, *Introduction to Quadratic Forms*, §82.
-/

public section

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- A sublattice with perfect restricted integral pairing is complementary to its orthogonal
complement. -/
theorem isCompl_orthogonal_of_restrict_bijective (L : IntegralLattice V)
    (S : Submodule ℤ L) (h : Function.Bijective (L.integralForm.restrict S)) :
    IsCompl S (L.integralForm.orthogonal S) :=
  L.integralForm.isCompl_orthogonal_of_restrict_bijective S
    (L.isSymm_integralForm.restrict S) h

/-- A vector of unit norm spans an orthogonal direct summand of an integral lattice. -/
theorem isCompl_span_singleton_orthogonal_of_isUnit (L : IntegralLattice V) (x : L)
    (hx : IsUnit (L.integralForm x x)) :
    IsCompl (ℤ ∙ x) (L.integralForm.orthogonal (ℤ ∙ x)) :=
  L.integralForm.isCompl_span_singleton_orthogonal_of_isUnit x hx

/-- The orthogonal complement of a vector with nonzero pairing functional has integral rank
one less than the lattice, without any assumption on the radical of the ambient form. -/
theorem finrank_orthogonal_span_singleton_add_one (L : IntegralLattice V) (x : L)
    (hx : L.integralForm x ≠ 0) :
    Module.finrank ℤ (L.integralForm.orthogonal (ℤ ∙ x)) + 1 = Module.finrank ℤ L := by
  let f := L.integralForm x
  have hr := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq] at hr
  have hle : Module.finrank ℤ f.range ≤ 1 := by
    simpa using f.range.finrank_le
  have hpos : 0 < Module.finrank ℤ f.range :=
    Module.finrank_pos_iff.mpr
      (Submodule.nontrivial_iff_ne_bot.mpr (LinearMap.range_eq_bot.not.mpr hx))
  have hs : Module.finrank ℤ f.range = 1 := by omega
  rw [LinearMap.BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton]
  simpa only [hs, add_comm, f] using hr

end IntegralLattice

end TauCeti
