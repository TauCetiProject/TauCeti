/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import TauCeti.NumberTheory.Height.FamilyOverPairs.IndexGram
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Completion
import TauCeti.NumberTheory.Height.FamilyOverPairs.TwistedCovolume

/-!
# The covolume-index inequality for twisted lifts

At each prime-adic embedding one may use a different lift to estimate the height of a
Gram determinant. A basis completed by short vectors with controlled denominators lets
one combine the prime-adic estimate with the covolume of the original independent family.
This gives a lower bound for the sum of its logarithmic squared covolume and twice its index.

The comparison follows `New.TwistedLattice.covolume_add_index_nonneg` and the use of auxiliary
vectors in `New.Data.integral_forms_long` in [lsernau/grh-lean][short-proof] (Apache 2.0),
in `New/Reduction/Lattices/TwistedLattice.lean` and `New/Determinant/Twist/LongForms.lean`.

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src
-/

public section

open Matrix TauCeti TauCeti.PrimePadicIso
open scoped ComplexOrder InnerProductSpace

namespace LinearIndependent

/-- The sum of a covolume budget and twice an index budget is bounded below by minus the
cost of basis completion and the height of the determinant ratio. The vectors of `S` span
modulo `y`; each costs `short` at infinity and has locally integral lifted pairings after
scaling. The inverse squared scale costs `denom` per added vector. The integrality test pairs
vectors from the two opposite embeddings, using the **same** selected lift `g ι` on both sides. -/
theorem covolumeBudget_add_index_nonneg
    {V E m I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype m] [Fintype I] [DecidableEq I]
    {y : I → V} (hy : LinearIndependent ℂ y) {S : Set V}
    (hS : Submodule.span ℂ (Set.range y ∪ S) = ⊤)
    (f : V →ₗ[ℂ] E) (hf : Function.Injective f) (coord : V → m → ℂ)
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef)
    (hcoord : ∀ u v, ⟪f u, f v⟫_ℂ = star (coord u) ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ coord v))
    {W : PrimePadicIso → Type*} [∀ ι, NormedAddCommGroup (W ι)] [∀ ι, InnerProductSpace ℂ (W ι)]
    (g : ∀ ι, V →ₗ[ℂ] W ι) (hg : ∀ ι, Function.Injective (g ι))
    (γ : PrimePadicIso → ℂˣ) {L : (ι : PrimePadicIso) → Submodule ι.integers V}
    {L₁ L₂ : PrimePadicIso → Set V}
    (h₁ : ∀ ι, (L { ι with iso := Complex.conjAe.toRingEquiv.trans ι.iso } : Set V) ⊆ L₁ ι)
    (h₂ : ∀ ι, (L ι : Set V) ⊆ L₂ ι)
    (hpair : ∀ ι ⦃u v⦄, u ∈ L₁ ι → v ∈ L₂ ι → ‖ι.iso ⟪g ι u, g ι v⟫_ℂ‖ ≤ 1)
    {c δ short denom volume : ℝ}
    (hc : (Matrix.of fun a i ↦ coord (y i) a).CovolumeLE G c) (hδ : IndexLe L y δ)
    (hshort : ∀ v ∈ S, ∀ σ : ℂ ≃+* ℂ,
      ‖star (σ ∘ coord v) ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ (σ ∘ coord v))‖ ≤ Real.exp short)
    (hint₁ : ∀ v ∈ S, ∀ ι, (γ ι : ℂ) • v ∈ L₁ ι)
    (hint₂ : ∀ v ∈ S, ∀ ι, (γ ι : ℂ) • v ∈ L₂ ι)
    (hdenom : HeightLe (fun ι ↦ ((‖(γ ι : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹) denom)
    (hvolume : HeightLe (fun ι ↦ ((f.normDet ^ 2 / (g ι).normDet ^ 2 : ℝ) : ℂ)) volume) :
    0 ≤ c + 2 * δ + (Module.finrank ℂ V - Fintype.card I : ℕ) * (short + denom) + volume := by
  -- Keep the original family in the first block and choose the second from the auxiliary set.
  let k := Module.finrank ℂ V - Fintype.card I
  obtain ⟨b, hleft, hright, -⟩ := hy.exists_basis_completion_of_covolumeLE hS coord hG hc hshort
  let z : Fin k → V := fun j ↦ b (.inr j)
  have hb : (b : I ⊕ Fin k → V) = Sum.elim y z := by
    funext i
    cases i with
    | inl i => exact hleft i
    | inr j => rfl
  let A : Matrix m I ℂ := Matrix.of fun a i ↦ coord (y i) a
  let B : Matrix m (Fin k) ℂ := Matrix.of fun a j ↦ coord (z j) a
  have hcol (i : I ⊕ Fin k) : (fromCols A B).col i = coord (b i) := by
    rw [hb]
    cases i <;> rfl
  have hgram : gram ℂ (f ∘ b) = (fromCols A B)ᴴ * G.map (algebraMap ℚ ℂ) * fromCols A B := by
    ext i j
    simp only [gram_apply, Function.comp_apply, hcoord, conjTranspose_mul_mul_apply, hcol]
  have hdiag (σ : ℂ ≃+* ℂ) (j : Fin k) :
      ‖((B.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * B.map σ) j j‖ ≤ Real.exp short := by
    rw [conjTranspose_mul_mul_apply]
    have hcol' : (B.map σ).col j = σ ∘ coord (z j) := (rfl)
    rw [hcol']
    exact hshort _ (hright j) σ
  -- The same completed family is used for both the finite-place height and the covolume.
  have hscaled := hδ.heightLe_scaled_det_gram z g (fun ι ↦ (γ ι : ℂ)) h₁ h₂
    (fun ι j ↦ hint₁ _ (hright j) ι) (fun ι j ↦ hint₂ _ (hright j) ι) hpair
  have hfamily (ι : PrimePadicIso) : (g ι ∘ b) =
      Sum.elim (fun i ↦ g ι (y i)) (fun j ↦ g ι (z j)) := by
    exact (congrArg (⇑(g ι) ∘ ·) hb).trans (Sum.comp_elim (g ι) y z)
  have h := f.covolumeBudget_add_nonneg_of_heightLe_scaled_det_gram b g γ hf hg hG hgram hc
    (short := fun _ ↦ short) hdiag (by simpa only [hfamily] using hscaled) hdenom hvolume
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
    add_assoc] using h

end LinearIndependent
