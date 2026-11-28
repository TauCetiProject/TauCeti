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
import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Completion
import TauCeti.NumberTheory.Height.FamilyOverPairs.ProductFormula

/-!
# Covolume bounds from twisted Gram determinants

`LinearMap.covolume_add_nonneg_of_heightLe_scaled_gram` compares the squared covolume of
the first block of a basis with the height budgets for the completed basis at varying twists.
It uses `LinearMap.det_gram_comp_basis_eq_normDet_sq_mul` to compare Gram determinants,
`Matrix.norm_map_det_gram_sumElim_le` to bound the conjugates of the reference determinant,
and `TauCeti.PrimePadicIso.HeightLe.neg_le_of_norm_map_le` for the product formula.

The comparison is that of `New.TwistedLattice.covolume_add_index_nonneg` in
`grh/src/New/Reduction/Lattices/TwistedLattice.lean` of [lsernau/grh-lean][short-proof]
(Apache 2.0, Copyright 2026 Anthropic, PBC).

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open Matrix TauCeti TauCeti.PrimePadicIso
open scoped ComplexOrder InnerProductSpace

namespace LinearMap

/-- For a basis split into two blocks, the logarithmic squared covolume budget of the first
block is bounded below by the negative sum of the remaining budgets. These are the conjugated
squared-length budgets of the second block, the height of the scaled twisted Gram determinants,
the inverse squared scale height per auxiliary vector, and the height of the reference-to-twist
squared norm determinant ratio. -/
theorem covolume_add_nonneg_of_heightLe_scaled_gram
    {U V m n p : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Fintype m] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (f : U →ₗ[ℂ] V) (b : Module.Basis (n ⊕ p) ℂ U)
    {W : PrimePadicIso → Type*} [∀ ι, NormedAddCommGroup (W ι)] [∀ ι, InnerProductSpace ℂ (W ι)]
    (g : ∀ ι, U →ₗ[ℂ] W ι) (γ : PrimePadicIso → ℂˣ)
    (hf : Function.Injective f) (hg : ∀ ι, Function.Injective (g ι))
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) (coord : V → m → ℂ)
    (hcoord : ∀ x y, ⟪x, y⟫_ℂ = star (coord x) ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ coord y))
    {c d denom volume : ℝ} {short : p → ℝ}
    (hc : (of fun i j ↦ coord (f (b (.inl j))) i).CovolumeLE G c)
    (hshort : ∀ (σ : ℂ ≃+* ℂ) j,
      (star (σ ∘ coord (f (b (.inr j)))) ⬝ᵥ
        (G.map (algebraMap ℚ ℂ) *ᵥ (σ ∘ coord (f (b (.inr j)))))).re ≤ Real.exp (short j))
    (hscaled : HeightLe (fun ι ↦ ((‖(γ ι : ℂ)‖ ^ (2 * Fintype.card p) : ℝ) : ℂ) *
      (gram ℂ (g ι ∘ b)).det) d)
    (hdenom : HeightLe (fun ι ↦ ((‖(γ ι : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹) denom)
    (hvolume : HeightLe (fun ι ↦ ((f.normDet ^ 2 / (g ι).normDet ^ 2 : ℝ) : ℂ)) volume) :
    0 ≤ c + d + (∑ j, short j) + Fintype.card p * denom + volume := by
  have harch (σ : ℂ ≃+* ℂ) :
      ‖σ (gram ℂ (f ∘ b)).det‖ ≤ Real.exp (c + ∑ j, short j) := by
    have heq : Sum.elim (fun i ↦ f (b (.inl i))) (fun j ↦ f (b (.inr j))) = f ∘ b := by
      grind
    rw [← heq]
    exact norm_map_det_gram_sumElim_le hG coord hcoord hc hshort σ
  have hheight : HeightLe (fun _ ↦ (gram ℂ (f ∘ b)).det)
      (d + Fintype.card p * denom + volume) := by
    refine ((hscaled.mul (hdenom.pow (Fintype.card p))).mul hvolume).mono le_rfl ?_
    intro ι
    apply le_of_eq
    apply congrArg (fun z : ℂ ↦ ‖ι.iso z‖)
    have hγ : (‖(γ ι : ℂ)‖ : ℂ) ≠ 0 := by simp
    have hg₀ : ((g ι).normDet : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (((g ι).normDet_ne_zero_tfae.out 1 5).mpr (hg ι))
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [f.det_gram_comp_basis_eq_normDet_sq_mul, (g ι).det_gram_comp_basis_eq_normDet_sq_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_div, Complex.ofReal_pow,
      inv_pow, ← pow_mul]
    field_simp
  have hdet : (gram ℂ (f ∘ b)).det ≠ 0 := by
    exact det_gram_ne_zero_iff_linearIndependent.mpr
      (b.linearIndependent.map' f ((LinearMap.ker_eq_bot).mpr hf))
  have h := hheight.neg_le_of_norm_map_le hdet harch
  linarith

end LinearMap
