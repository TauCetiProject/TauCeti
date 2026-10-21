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
`ZLattice.comap ℝ L A⁻¹`. This file computes how the covolume changes: pulling back along `A`
divides the covolume by `|det A|` (`ZLattice.covolume_comap_continuousLinearEquiv`), for every
Haar measure. Equivalently `covolume (A L) = |det A| * covolume L`. The dual lattice transforms by
the adjoint of `A⁻¹`, `ZLattice.dual_comap_continuousLinearEquiv`.

In a finite-dimensional real inner product space this exhibits every full lattice as a linear
image of the self-dual lattice spanned by an orthonormal basis: for every orthonormal basis there
is an automorphism `A` carrying that lattice onto `L`, with `(A⁻¹)ᵀ` carrying it onto `L^∨` and
with `|det A| = covolume L` (`ZLattice.exists_comap_span_orthonormalBasis_eq`). With the Fourier
change of variables `ContinuousLinearEquiv.fourier_comp`, this is what reduces a summation formula
over a general lattice and its dual to the same formula over `ℤⁿ`, the constant `|det A|` becoming
the covolume.

## Main statements

* `ZLattice.covolume_comap_continuousLinearEquiv`: the covolume of the pullback of `L` along a
  continuous linear automorphism `A` is `|det A|⁻¹ * covolume L`.
* `ZLattice.exists_comap_span_orthonormalBasis_eq`: every full lattice in a finite-dimensional
  real inner product space is the image of the lattice spanned by a given orthonormal basis under
  an automorphism `A` with `|det A| = covolume L`, and its pullback along the adjoint of `A` is
  `L^∨`.
-/

public section

open Module Submodule MeasureTheory

namespace ZLattice

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Pulling a full lattice back along a continuous linear automorphism `A` divides its covolume
by `|det A|`, for any Haar measure. Read through images, `covolume (A L) = |det A| * covolume L`.
Mathlib's `ZLattice.covolume_comap` is the measure-preserving case. -/
theorem covolume_comap_continuousLinearEquiv (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (A : E ≃L[ℝ] E) (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    covolume (ZLattice.comap ℝ L A.toLinearMap) μ = |A.toLinearMap.det|⁻¹ * covolume L μ := by
  let b := Free.chooseBasis ℤ L
  -- The fundamental domain of the pulled-back basis is the image of that of `b` under `A⁻¹`.
  rw [covolume_eq_measure_fundamentalDomain _ μ (isAddFundamentalDomain b μ),
    covolume_eq_measure_fundamentalDomain _ μ
      (isAddFundamentalDomain (b.ofZLatticeComap ℝ L A.toLinearEquiv) μ),
    Basis.ofZLatticeBasis_comap, ← ZSpan.map_fundamentalDomain, measureReal_def, measureReal_def]
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, Measure.addHaar_image_continuousLinearEquiv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv]

end NormedSpace

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
    have hrange : Set.range (b.ofZLatticeBasis ℝ L) =
        (A.toLinearMap.restrictScalars ℤ) '' Set.range o := by
      rw [← Set.range_comp]
      congr 1
      ext i
      rw [Function.comp_apply, ← o.coe_toBasis]
      simp only [A, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
        Basis.equiv_apply, Equiv.refl_apply, Basis.ofZLatticeBasis_apply]
    ext x
    rw [← b.ofZLatticeBasis_span ℝ L, hrange]
    simpa using (apply_mem_span_image_iff_mem_span (f := A.toLinearMap.restrictScalars ℤ)
      (x := A.symm x) (s := Set.range o) A.injective).symm
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
