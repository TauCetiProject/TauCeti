/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.NormIndex
public import TauCeti.FieldTheory.Galois.Complex
public import TauCeti.RingTheory.Norm.Archimedean
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Archimedean multiplicative-group Herbrand quotients

For every finite extension `L` of `ℝ` or `ℂ`, the Herbrand quotient of `Lˣ` with its
Galois action equals the extension degree. Thus a real place which becomes complex
contributes `2`, whereas an unchanged real place or a complex place contributes `1`.
These are the archimedean factors in the Herbrand quotient calculation for `S`-ideles.

The real calculation uses Mathlib's `Real.nonempty_algEquiv_or`: an algebraic extension
of `ℝ` is isomorphic to `ℝ` or `ℂ`. For `ℂ/ℝ` the norm group consists of the positive
units, whose subgroup has index two (`Units.index_posSubgroup`). Hilbert 90
and cyclic two-periodicity identify each Herbrand quotient with this norm index.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Proposition 2.7, the local factors
  of the `S`-idele Herbrand quotient: https://www.jmilne.org/math/CourseNotes/CFT.pdf
-/

public noncomputable section

namespace TauCeti

/-- The multiplicative group of any finite real extension has Herbrand quotient equal to
its degree, including the contribution `2` when a real place becomes complex. -/
@[simp]
theorem herbrandQuotient_units_eq_finrank_real (L : Type) [Field L] [Algebra ℝ L]
    [FiniteDimensional ℝ L] :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[ℝ] L) Lˣ) =
      Module.finrank ℝ L := by
  rcases Real.nonempty_algEquiv_or L with h | h
  · obtain ⟨e⟩ := h
    have : IsGalois ℝ L := IsGalois.of_algEquiv e.symm
    have : IsCyclic (L ≃ₐ[ℝ] L) :=
      isCyclic_of_injective e.autCongr.toMonoidHom e.autCongr.injective
    rw [herbrandQuotient_units_eq_index_normGroup, index_normGroup_real]
  · obtain ⟨e⟩ := h
    have : IsGalois ℝ L := IsGalois.of_algEquiv e.symm
    have : IsCyclic (L ≃ₐ[ℝ] L) :=
      isCyclic_of_injective e.autCongr.toMonoidHom e.autCongr.injective
    rw [herbrandQuotient_units_eq_index_normGroup, index_normGroup_real]


end TauCeti
