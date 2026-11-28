/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import TauCeti.NumberTheory.Height.IndexOverPairs
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.NumberTheory.Height.FamilyOverPairs.IndexGram
import TauCeti.NumberTheory.Height.FamilyOverPairs.TwistedCovolume

/-!
# A lower bound for covolume from local indices

Complete the family to a basis and choose a lift at each prime-adic embedding. The two
index witnesses, at the embedding and at its conjugate, control the Gram determinant
of the chosen lift after scaling the added basis vectors. The product formula compares
these local estimates with the covolume measured using a single reference lift.

This is the comparison of `New.TwistedLattice.covolume_add_index_nonneg` in
`grh/src/New/Reduction/Lattices/TwistedLattice.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.PrimePadicIso

/-- The sum of a covolume budget, twice an index budget, and the costs of completing the
basis and changing the lift is nonnegative. The first block of `b` has index at most `δ`
relative to `L`, and covolume at most `c` in the rational coordinates of the reference lift
`f`. The remaining vectors have conjugated squared lengths at most `exp (short j)` and
are locally integral on both sides after scaling by `γ`. At `ι`, the left integral condition
contains `L` at the conjugate embedding, while the right contains `L ι`. Both conditions
are for the *same* chosen lift `g ι`. No compatibility among the choices of lifts at different
embeddings is required. -/
theorem IndexLe.covolumeBudget_add_nonneg_of_indexLe
    {U V m n p : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Fintype m] [Fintype n] [DecidableEq n] [Fintype p]
    {L : (ι : PrimePadicIso) → Submodule ι.integers U}
    {b : Module.Basis (n ⊕ p) ℂ U} {c δ denom volume : ℝ} {short : p → ℝ}
    (hy : IndexLe L (b ∘ Sum.inl) δ) (f : U →ₗ[ℂ] V) (hf : Function.Injective f)
    {W : PrimePadicIso → Type*} [∀ ι, NormedAddCommGroup (W ι)] [∀ ι, InnerProductSpace ℂ (W ι)]
    (g : ∀ ι, U →ₗ[ℂ] W ι) (hg : ∀ ι, Function.Injective (g ι)) (γ : PrimePadicIso → ℂˣ)
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) (coord : n ⊕ p → m → ℂ)
    (hcoord : ∀ i j, ⟪f (b i), f (b j)⟫_ℂ =
      star (coord i) ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ coord j))
    (hc : (of fun i j ↦ coord (.inl j) i).CovolumeLE G c)
    (hshort : ∀ (σ : ℂ ≃+* ℂ) j, let v := σ ∘ coord (.inr j)
      ‖star v ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ v)‖ ≤ Real.exp (short j))
    {L₁ L₂ : PrimePadicIso → Set U}
    (h₁ : ∀ ι, (L { ι with iso := Complex.conjAe.toRingEquiv.trans ι.iso } : Set U) ⊆ L₁ ι)
    (h₂ : ∀ ι, (L ι : Set U) ⊆ L₂ ι)
    (hz₁ : ∀ ι j, (γ ι : ℂ) • b (.inr j) ∈ L₁ ι)
    (hz₂ : ∀ ι j, (γ ι : ℂ) • b (.inr j) ∈ L₂ ι)
    (hpair : ∀ ι ⦃u v⦄, u ∈ L₁ ι → v ∈ L₂ ι → ‖ι.iso ⟪g ι u, g ι v⟫_ℂ‖ ≤ 1)
    (hdenom : HeightLe (fun ι ↦ ((‖(γ ι : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹) denom)
    (hvolume : HeightLe (fun ι ↦ ((f.normDet ^ 2 / (g ι).normDet ^ 2 : ℝ) : ℂ)) volume) :
    0 ≤ c + 2 * δ + (∑ j, short j) + Fintype.card p * denom + volume := by
  classical
  let A : Matrix m n ℂ := of fun i j ↦ coord (.inl j) i
  let B : Matrix m p ℂ := of fun i j ↦ coord (.inr j) i
  have hcol (j : n ⊕ p) : (fromCols A B).col j = coord j := by
    funext i
    cases j <;> simp [Matrix.col, A, B]
  have hgram : gram ℂ (f ∘ b) = (fromCols A B)ᴴ * G.map (algebraMap ℚ ℂ) * fromCols A B := by
    ext i j
    simpa only [gram_apply, conjTranspose_mul_mul_apply, hcol, Function.comp_apply] using hcoord i j
  have hscaled := hy.heightLe_scaled_det_gram (b ∘ Sum.inr) g (fun ι ↦ ↑(γ ι))
    h₁ h₂ hz₁ hz₂ hpair
  have hsplit (ι : PrimePadicIso) :
      Sum.elim (fun i ↦ g ι (b (.inl i))) (fun j ↦ g ι (b (.inr j))) = g ι ∘ b :=
    Sum.elim_comp_inl_inr (g ι ∘ b)
  simp only [Function.comp_apply, hsplit] at hscaled
  refine f.covolumeBudget_add_nonneg_of_heightLe_scaled_det_gram b g γ hf hg hG hgram
    hc (B := B) (fun σ j ↦ ?_) hscaled hdenom hvolume
  have hBcol : (B.map σ).col j = σ ∘ coord (.inr j) := by
    funext i
    simp only [Matrix.col, transpose_apply, Matrix.map_apply, B, of_apply, Function.comp_apply]
  simpa only [conjTranspose_mul_mul_apply, hBcol] using hshort σ j

end TauCeti.PrimePadicIso
