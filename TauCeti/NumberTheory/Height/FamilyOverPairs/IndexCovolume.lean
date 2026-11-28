/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FamilyOverPairs.TwistedCovolume
public import TauCeti.NumberTheory.Height.IndexOverPairs
import TauCeti.NumberTheory.Height.FamilyOverPairs.IndexGram

/-!
# Covolume and index for a family of twisted lifts

A basis is split into a family with bounded index and auxiliary vectors used to complete it.
At each prime-adic embedding one can use a different lift. Its integral pairing must hold
between vectors integral at opposite embeddings, using the **same** lift on both sides.
The resulting finite-place determinant budget is twice the index, which can be combined
with a reference covolume bound and the height of the lift determinant ratios.

This is the index-to-covolume comparison of `New.TwistedLattice.covolume_add_index_nonneg`
in [lsernau/grh-lean, `TwistedLattice.lean`][short-proof].

[short-proof]:
https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Lattices/TwistedLattice.lean
-/

public section

open Matrix TauCeti TauCeti.PrimePadicIso
open scoped ComplexOrder InnerProductSpace

namespace LinearMap

/-- A covolume budget `c` for the first block of a basis and an index budget `δ` for that
block satisfy `0 ≤ c + 2 * δ + ∑ j, short j + card p * denom + volume`. The reference lift
has rational metric coordinates, with conjugate squared lengths of the auxiliary images
bounded by `exp (short j)`. At each embedding `ι`, the chosen lift has integral pairings
between vectors in `L₁ ι` and `L₂ ι`. These sets contain the index submodules at the opposite
and original embeddings, respectively, as well as the auxiliary vectors scaled by `γ ι`.
The remaining budgets `denom` and `volume` bound the heights of the inverse squared scales
and the reference-to-twist determinant ratios. -/
theorem covolumeBudget_add_nonneg_of_indexLe
    {U V m n p : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Fintype m] [Fintype n] [DecidableEq n] [Fintype p]
    (f : U →ₗ[ℂ] V) (b : Module.Basis (n ⊕ p) ℂ U)
    {W : PrimePadicIso → Type*} [∀ ι, NormedAddCommGroup (W ι)] [∀ ι, InnerProductSpace ℂ (W ι)]
    (g : ∀ ι, U →ₗ[ℂ] W ι) (γ : PrimePadicIso → ℂˣ)
    (hf : Function.Injective f) (hg : ∀ ι, Function.Injective (g ι))
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef)
    {A : Matrix m n ℂ} {B : Matrix m p ℂ}
    (hcoord : gram ℂ (f ∘ b) = (fromCols A B)ᴴ * G.map (algebraMap ℚ ℂ) * fromCols A B)
    {c δ denom volume : ℝ} {short : p → ℝ}
    (hc : A.CovolumeLE G c)
    (hshort : ∀ (σ : ℂ ≃+* ℂ) j,
      ‖((B.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * B.map σ) j j‖ ≤ Real.exp (short j))
    {L : (ι : PrimePadicIso) → Submodule ι.integers U}
    (hindex : IndexLe L (b ∘ Sum.inl) δ)
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
  have hscaled := hindex.heightLe_scaled_det_gram (b ∘ Sum.inr) g (fun ι ↦ ↑(γ ι))
    h₁ h₂ hz₁ hz₂ hpair
  have hfamily (ι : PrimePadicIso) :
      Sum.elim (fun i ↦ g ι (b (.inl i))) (fun j ↦ g ι (b (.inr j))) = g ι ∘ b :=
    Sum.elim_comp_inl_inr (g ι ∘ b)
  refine f.covolumeBudget_add_nonneg_of_heightLe_scaled_det_gram b g γ hf hg hG hcoord hc hshort
    ?_ hdenom hvolume
  simpa only [Function.comp_apply, hfamily] using hscaled

end LinearMap
