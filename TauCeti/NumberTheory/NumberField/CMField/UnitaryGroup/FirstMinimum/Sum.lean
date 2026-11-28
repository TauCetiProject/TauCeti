/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.FirstMinimum.Basic
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.OrthogonalSum

/-!
# First minima of orthogonal sums of framed hermitian spaces

The inverse adelic frame acts blockwise on an orthogonal sum. The finite lattice is the
product of the two lattices, and the archimedean lengths satisfy Pythagoras. Consequently
adding an orthogonal summand replaces the truncated first minimum by the smaller of the
two minima. This also computes the separation scale at block-diagonal adelic points.

The lower bound is the one in `New.Rows.inf_le_firstMinimum_sum` in
`Lib/Adelic/Reduction/FirstMinimumShortBases.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Matrix NumberField

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {s : ι → ℤˣ} {t : κ → ℤˣ} (V : FramedHermitianSpace E s) (W : FramedHermitianSpace E t)

/-- An archimedean coordinate in the first block is computed in the first frame. -/
theorem archCoords_sum_inl (y : ι ⊕ κ → E) (i : ι) (w : InfinitePlace E) :
    (V.sum W).archCoords y (Sum.inl i, w) = V.archCoords (y ∘ Sum.inl) (i, w) := by
  simp only [archCoords_apply, frame_sum, ← map_inv, Prod.inv_mk, coe_fromBlocksGL,
    fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_inl, Function.comp_assoc]

/-- An archimedean coordinate in the second block is computed in the second frame. -/
theorem archCoords_sum_inr (y : ι ⊕ κ → E) (j : κ) (w : InfinitePlace E) :
    (V.sum W).archCoords y (Sum.inr j, w) = W.archCoords (y ∘ Sum.inr) (j, w) := by
  simp only [archCoords_apply, frame_sum, ← map_inv, Prod.inv_mk, coe_fromBlocksGL,
    fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_inr, Function.comp_assoc]

/-- The squared archimedean length in an orthogonal sum is the sum of the two squared lengths. -/
theorem sq_vectorLength_sum (y : ι ⊕ κ → E) :
    (V.sum W).vectorLength y ^ 2 =
      V.vectorLength (y ∘ Sum.inl) ^ 2 + W.vectorLength (y ∘ Sum.inr) ^ 2 := by
  simp only [vectorLength_def, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    Fintype.sum_sum_type, archCoords_sum_inl, archCoords_sum_inr]

/-- The truncated first minimum of the orthogonal sum is the smaller of the two minima.
This includes rank zero, for which the first minimum is one. -/
@[simp] theorem firstMinimum_sum : (V.sum W).firstMinimum = min V.firstMinimum W.firstMinimum := by
  apply le_antisymm
  · -- Embed a vector from either summand by adjoining zero.
    refine le_min (V.le_firstMinimum_iff.mpr ⟨(V.sum W).firstMinimum_le_one, ?_⟩)
      (W.le_firstMinimum_iff.mpr ⟨(V.sum W).firstMinimum_le_one, ?_⟩)
    · intro y hy hy₀
      let z := Sum.elim y (0 : κ → E)
      have hz₀ : z ≠ 0 := fun h ↦ hy₀ (congrArg (· ∘ Sum.inl) h)
      have hz : z ∈ (V.sum W).lattice := by
        simpa only [z, mem_lattice_sum_iff, Sum.elim_comp_inl, Sum.elim_comp_inr,
          Submodule.zero_mem, and_true] using hy
      have hlen : (V.sum W).vectorLength z = V.vectorLength y := by
        apply (sq_eq_sq₀ ((V.sum W).vectorLength_nonneg _) (V.vectorLength_nonneg _)).mp
        simpa [z] using V.sq_vectorLength_sum W z
      exact hlen ▸ (V.sum W).firstMinimum_le_vectorLength hz hz₀
    · intro y hy hy₀
      let z := Sum.elim (0 : ι → E) y
      have hz₀ : z ≠ 0 := fun h ↦ hy₀ (congrArg (· ∘ Sum.inr) h)
      have hz : z ∈ (V.sum W).lattice := by
        simpa only [z, mem_lattice_sum_iff, Sum.elim_comp_inl, Sum.elim_comp_inr,
          Submodule.zero_mem, true_and] using hy
      have hlen : (V.sum W).vectorLength z = W.vectorLength y := by
        apply (sq_eq_sq₀ ((V.sum W).vectorLength_nonneg _) (W.vectorLength_nonneg _)).mp
        simpa [z] using V.sq_vectorLength_sum W z
      exact hlen ▸ (V.sum W).firstMinimum_le_vectorLength hz hz₀
  · -- Every nonzero vector has a nonzero component, and its length bounds that component's.
    refine (V.sum W).le_firstMinimum_iff.mpr ⟨(min_le_left ..).trans V.firstMinimum_le_one, ?_⟩
    intro y hy hy₀
    obtain ⟨hyL, hyR⟩ := (V.mem_lattice_sum_iff W).mp hy
    have hsq := V.sq_vectorLength_sum W y
    by_cases hL : y ∘ Sum.inl = 0
    · have hR : y ∘ Sum.inr ≠ 0 := fun hR ↦ hy₀ <|
        (Sum.elim_comp_inl_inr y).symm.trans <|
          (congrArg₂ Sum.elim hL hR).trans (Sum.elim_comp_inl_inr (0 : ι ⊕ κ → E))
      refine (min_le_right ..).trans ((W.firstMinimum_le_vectorLength hyR hR).trans ?_)
      exact (sq_le_sq₀ (W.vectorLength_nonneg _) ((V.sum W).vectorLength_nonneg _)).mp
        (hsq ▸ le_add_of_nonneg_left (sq_nonneg _))
    · refine (min_le_left ..).trans ((V.firstMinimum_le_vectorLength hyL hL).trans ?_)
      exact (sq_le_sq₀ (V.vectorLength_nonneg _) ((V.sum W).vectorLength_nonneg _)).mp
        (hsq ▸ le_add_of_nonneg_right (sq_nonneg _))

end TauCeti.FramedHermitianSpace
