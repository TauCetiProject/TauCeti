/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Determinant

/-!
# Lattices under a linear change of variables

A continuous linear automorphism `A` of a finite-dimensional real vector space carries a full
`ℤ`-lattice `L` to the full lattice `A L`, which Mathlib writes as the pullback
`ZLattice.comap ℝ L A⁻¹`. Pulling back along `A` divides the covolume by `|det A|`
(`ZLattice.covolume_comap_continuousLinearEquiv`), so `covolume (A L) = |det A| * covolume L`, and
the dual lattice transforms by the adjoint of `A⁻¹` (`ZLattice.dual_comap_continuousLinearEquiv`).

In a finite-dimensional real inner product space this exhibits every full lattice as a linear
image of the self-dual lattice spanned by an orthonormal basis: for every orthonormal basis there
is an automorphism `A` carrying that lattice onto `L`, with `(A⁻¹)ᵀ` carrying it onto `L^∨` and
with `|det A| = covolume L` (`ZLattice.exists_comap_span_orthonormalBasis_eq`). With the Fourier
change of variables `ContinuousLinearEquiv.fourier_comp`, this is what reduces a summation formula
over a general lattice and its dual to the same formula over `ℤⁿ`, the constant `|det A|` becoming
the covolume.

## Main statement

* `ZLattice.exists_comap_span_orthonormalBasis_eq`: every full lattice in a finite-dimensional
  real inner product space is the image of the lattice spanned by a given orthonormal basis under
  an automorphism `A` with `|det A| = covolume L`, and its pullback along the adjoint of `A` is
  `L^∨`.
-/

public section

open Module Submodule MeasureTheory

namespace ZLattice

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every full lattice `L` in a finite-dimensional real inner product space is the image of the
lattice spanned by an orthonormal basis `o` under a linear automorphism `A` with
`|det A| = covolume L`. The adjoint of `A` pulls that self-dual lattice back to the dual `L^∨`;
read through images, `L^∨ = (A⁻¹)ᵀ (span ℤ (range o))`. -/
theorem exists_comap_span_orthonormalBasis_eq (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ E) :
    ∃ A : E ≃L[ℝ] E, ZLattice.comap ℝ (span ℤ (Set.range o)) A.symm.toLinearMap = L ∧
      ZLattice.comap ℝ (span ℤ (Set.range o))
        (ContinuousLinearMap.adjoint (A : E →L[ℝ] E)).toLinearMap = dual L ∧
      |A.toLinearMap.det| = covolume L := by
  classical
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = Fintype.card ι := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, finrank_eq_card_basis o.toBasis]
  -- `A` sends the orthonormal basis `o` to a `ℤ`-basis `b` of `L`.
  let b : Basis ι ℤ L := (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)
  let A : E ≃L[ℝ] E :=
    (o.toBasis.equiv (b.ofZLatticeBasis ℝ L) (Equiv.refl ι)).toContinuousLinearEquiv
  have hA : ZLattice.comap ℝ (span ℤ (Set.range o)) A.symm.toLinearMap = L := by
    -- The pullback along `A⁻¹` is the image under `A`, the span of the image basis `A ∘ o`.
    have hmap : o.toBasis.map A.toLinearEquiv = b.ofZLatticeBasis ℝ L := by
      simp [A]
    rw [ZLattice.comap, ← o.coe_toBasis, ← b.ofZLatticeBasis_span ℝ L, ← hmap, ← ZSpan.map]
    exact comap_equiv_eq_map_symm (A.symm.toLinearEquiv.restrictScalars ℤ) _
  refine ⟨A, hA, ?_, ?_⟩
  · rw [← hA, dual_comap_continuousLinearEquiv, dual_span_orthonormalBasis,
      ContinuousLinearEquiv.symm_symm]
  · -- The lattice spanned by `o` is unimodular, so it has covolume `1`.
    have hu := isUnimodular_span_orthonormalBasis o
    -- The lattice instances of `span ℤ (Set.range o)` are those of the `ℤ`-span of a basis.
    rw [← o.coe_toBasis] at hA hu
    have h := covolume_comap_continuousLinearEquiv (span ℤ (Set.range o.toBasis)) A.symm
    rw [hA, hu.covolume_eq_one, mul_one, ContinuousLinearEquiv.toLinearEquiv_symm,
      LinearEquiv.det_coe_symm, abs_inv, inv_inv] at h
    exact h.symm

end InnerProductSpace

end ZLattice
