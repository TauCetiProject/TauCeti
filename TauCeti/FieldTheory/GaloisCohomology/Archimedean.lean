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

The same holds over any field `F` isomorphic to `ℝ`
(`TauCeti.herbrandQuotient_units_eq_finrank_of_ringEquiv`), such as the completion of a number
field at a real place: through the isomorphism a finite extension of `F` becomes an `ℝ`-algebra
with the same automorphisms.

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

/-- The multiplicative group of any finite extension `L` of a field `F` isomorphic to `ℝ` has
Herbrand quotient equal to its degree. This applies to the completion of a number field at a
real place, which is isomorphic to `ℝ` without being an `ℝ`-algebra. -/
theorem herbrandQuotient_units_eq_finrank_of_ringEquiv {F : Type} [Field F] (φ : ℝ ≃+* F)
    (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[F] L) Lˣ) =
      Module.finrank F L := by
  -- make `L` an `ℝ`-algebra through `φ`; its `ℝ`- and `F`-automorphisms are then the same
  let : Algebra ℝ F := φ.toRingHom.toAlgebra
  let : Algebra ℝ L := ((algebraMap F L).comp φ.toRingHom).toAlgebra
  have : IsScalarTower ℝ F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hrank : Module.finrank ℝ L = Module.finrank F L :=
    Algebra.finrank_eq_of_equiv_equiv φ (RingEquiv.refl L) rfl
  have : FiniteDimensional ℝ L := Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)
  have hsurj : Function.Surjective
      (AlgEquiv.restrictScalarsHom ℝ : (L ≃ₐ[F] L) →* (L ≃ₐ[ℝ] L)) := fun ψ ↦ by
    refine ⟨AlgEquiv.ofRingEquiv (f := ψ.toRingEquiv) fun a ↦ ?_, AlgEquiv.ext fun _ ↦ rfl⟩
    obtain ⟨r, rfl⟩ := φ.surjective a
    exact ψ.commutes r
  rw [← hrank, ← herbrandQuotient_units_eq_finrank_real L,
    ← TateCohomology.herbrandQuotient_res_of_bijective
      ⟨AlgEquiv.restrictScalarsHom_injective ℝ, hsurj⟩]
  -- `restrictScalars` does not change the underlying map, so restricting the action of the
  -- `ℝ`-automorphisms on `Lˣ` along it is the action of the `F`-automorphisms
  rfl

end TauCeti
