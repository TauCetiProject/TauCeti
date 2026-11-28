/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic
import TauCeti.Analysis.InnerProductSpace.Gram.NormDet
import TauCeti.NumberTheory.Height.FamilyOverPairs.GramDeterminant

/-!
# Covolume bounds from twisted Gram determinants

`LinearMap.covolumeBudget_add_nonneg_of_heightLe_scaled_det_gram` gives a lower bound on
the logarithmic squared covolume budget of the first block of a basis. It takes uniform
archimedean bounds in rational metric coordinates and height budgets for the scaled twisted
Gram determinants, the inverse squared scale, and the reference-to-twist determinant ratio.
It uses `LinearMap.det_gram_comp_basis_div_det_gram_comp_basis` to compare the determinants
and `Matrix.CovolumeLE.add_sum_add_height_nonneg` for the product-formula bound.

The comparison is that of `New.TwistedLattice.covolume_add_index_nonneg` in
`grh/src/New/Reduction/Lattices/TwistedLattice.lean` of [lsernau/grh-lean][short-proof]
(Apache 2.0, Copyright 2026 Anthropic, PBC).

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open Matrix TauCeti TauCeti.PrimePadicIso
open scoped ComplexOrder

namespace LinearMap

/-- For a basis split into two blocks whose reference Gram matrix is represented in a rational
positive semidefinite metric, the logarithmic squared covolume budget of the first block is at
least the negative sum of the remaining budgets. Each auxiliary vector has a squared-length
budget uniform over all field automorphisms applied to its coordinates before evaluating the
metric. The other budgets bound the heights of the scaled twisted Gram determinants, the inverse
squared scale per auxiliary vector, and the reference-to-twist squared norm determinant ratio. -/
theorem covolumeBudget_add_nonneg_of_heightLe_scaled_det_gram
    {U V m n p : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Fintype m] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (f : U →ₗ[ℂ] V) (b : Module.Basis (n ⊕ p) ℂ U)
    {W : PrimePadicIso → Type*} [∀ ι, NormedAddCommGroup (W ι)] [∀ ι, InnerProductSpace ℂ (W ι)]
    (g : ∀ ι, U →ₗ[ℂ] W ι) (γ : PrimePadicIso → ℂˣ)
    (hf : Function.Injective f) (hg : ∀ ι, Function.Injective (g ι))
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef)
    {A : Matrix m n ℂ} {B : Matrix m p ℂ}
    (hcoord : gram ℂ (f ∘ b) = (fromCols A B)ᴴ * G.map (algebraMap ℚ ℂ) * fromCols A B)
    {c d denom volume : ℝ} {short : p → ℝ}
    (hc : A.CovolumeLE G c)
    (hshort : ∀ (σ : ℂ ≃+* ℂ) j,
      ‖((B.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * B.map σ) j j‖ ≤ Real.exp (short j))
    (hscaled : HeightLe (fun ι ↦ ((‖(γ ι : ℂ)‖ ^ (2 * Fintype.card p) : ℝ) : ℂ) *
      (gram ℂ (g ι ∘ b)).det) d)
    (hdenom : HeightLe (fun ι ↦ ((‖(γ ι : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹) denom)
    (hvolume : HeightLe (fun ι ↦ ((f.normDet ^ 2 / (g ι).normDet ^ 2 : ℝ) : ℂ)) volume) :
    0 ≤ c + d + (∑ j, short j) + Fintype.card p * denom + volume := by
  have hheight : HeightLe (fun _ ↦ (gram ℂ (f ∘ b)).det)
      (d + Fintype.card p * denom + volume) := by
    refine ((hscaled.mul (hdenom.pow (Fintype.card p))).mul hvolume).mono le_rfl ?_
    intro ι
    apply le_of_eq
    apply congrArg (fun z : ℂ ↦ ‖ι.iso z‖)
    have hγ : (‖(γ ι : ℂ)‖ : ℂ) ≠ 0 := by simp
    have hg₀ : (gram ℂ (g ι ∘ b)).det ≠ 0 :=
      det_gram_ne_zero_iff_linearIndependent.mpr
        (b.linearIndependent.map' (g ι) (ker_eq_bot.mpr (hg ι)))
    have hratio : (gram ℂ (f ∘ b)).det / (gram ℂ (g ι ∘ b)).det =
        (↑(f.normDet ^ 2 / (g ι).normDet ^ 2 : ℝ) : ℂ) := by
      simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_div] using
        f.det_gram_comp_basis_div_det_gram_comp_basis (g ι) b
    simp only [Pi.mul_apply, Pi.pow_apply, ← hratio, Complex.ofReal_pow, inv_pow, ← pow_mul]
    field_simp
  have hdet : (gram ℂ (f ∘ b)).det ≠ 0 :=
    det_gram_ne_zero_iff_linearIndependent.mpr (b.linearIndependent.map' f (ker_eq_bot.mpr hf))
  rw [hcoord] at hdet hheight
  have h := hc.add_sum_add_height_nonneg hG hshort hdet hheight
  linarith

end LinearMap
