/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain

/-!
# Bicollars given on a closed interval

An injective continuous map `β : N × [-1, 1] → M`, where the manifolds `N × ℝ`
and `M` have the same dimension, gives a bicollar of its zero slice. Reparametrize
its open strip by Mathlib's `Homeomorph.unitBall` from `ℝ` to the open unit ball;
`Continuous.isOpenEmbedding_of_injective` (invariance of domain) makes the resulting
map an open embedding.

`TauCeti.bicollarOfClosedInterval` retains the actual parametrization `β`, rather
than choosing a new collar. Its range and its two sides are precisely the images
of the open strip and its positive and negative halves. For compact `N` and
Hausdorff `M`, the closure of this range is the whole closed strip image, and
its frontier is exactly the two end slices. These identifications let a
closed-interval bicollar be used in separation and collapsing constructions.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math.
  Soc. 66 (1960), 74–76, Theorem 5.
-/

public section

noncomputable section

open Function Metric Set Topology

namespace TauCeti

variable {N M : Type*}

/-- Reparametrize the open part of a closed-interval collar by `ℝ`. The depth is
`t / sqrt (1 + |t|²)`, so zero and the two signs of the depth are preserved. -/
def bicollarOfClosedInterval (β : N × Icc (-1 : ℝ) 1 → M) : N × ℝ → M :=
  fun p ↦ β (p.1, ⟨Homeomorph.unitBall p.2, by
    exact Ioo_subset_Icc_self (by
      simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using
        (Homeomorph.unitBall p.2).property)⟩)

/-- The value of the reparametrized collar in the original closed strip. -/
theorem bicollarOfClosedInterval_apply (β : N × Icc (-1 : ℝ) 1 → M) (x : N) (t : ℝ) :
    bicollarOfClosedInterval β (x, t) =
      β (x, ⟨Homeomorph.unitBall t, by
        exact Ioo_subset_Icc_self (by
          simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using
            (Homeomorph.unitBall t).property)⟩) := (rfl)

/-- Reparametrization fixes the zero slice. -/
@[simp]
theorem bicollarOfClosedInterval_apply_zero (β : N × Icc (-1 : ℝ) 1 → M) (x : N) :
    bicollarOfClosedInterval β (x, 0) = β (x, ⟨0, by norm_num⟩) := by
  simp [bicollarOfClosedInterval]

/-- A continuous closed-strip map remains continuous after reparametrization. -/
theorem continuous_bicollarOfClosedInterval [TopologicalSpace N] [TopologicalSpace M]
    {β : N × Icc (-1 : ℝ) 1 → M}
    (hβ : Continuous β) : Continuous (bicollarOfClosedInterval β) := by
  exact hβ.comp (continuous_fst.prodMk
    ((continuous_subtype_val.comp
      (Homeomorph.unitBall.continuous.comp continuous_snd)).subtype_mk _))

/-- An injective closed-strip map remains injective after reparametrization. -/
theorem injective_bicollarOfClosedInterval {β : N × Icc (-1 : ℝ) 1 → M}
    (hβ : Injective β) : Injective (bicollarOfClosedInterval β) := by
  intro p q hpq
  have h := Prod.mk.inj (hβ hpq)
  exact Prod.ext h.1 (Homeomorph.unitBall.injective
    (Subtype.ext (congrArg (fun a : Icc (-1 : ℝ) 1 ↦ (a : ℝ)) h.2)))

/-- The reparametrized collar covers exactly the image of the open strip. -/
theorem range_bicollarOfClosedInterval (β : N × Icc (-1 : ℝ) 1 → M) :
    range (bicollarOfClosedInterval β) = β '' {p | -1 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} := by
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, rfl⟩
    refine ⟨_, ?_, rfl⟩
    have h := (Homeomorph.unitBall t).property
    simpa [Real.ball_eq_Ioo] using h
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    let u : ball (0 : ℝ) 1 := ⟨t, by simpa [Real.ball_eq_Ioo] using ht⟩
    refine ⟨(x, Homeomorph.unitBall.symm u), ?_⟩
    simp [bicollarOfClosedInterval, u]

/-- The positive half of the reparametrized collar is the original positive
open half-strip. -/
theorem image_bicollarOfClosedInterval_Ioi (β : N × Icc (-1 : ℝ) 1 → M) :
    bicollarOfClosedInterval β '' (univ ×ˢ Ioi 0) =
      β '' {p | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} := by
  have hpos (t : ℝ) : 0 < (Homeomorph.unitBall t : ℝ) ↔ 0 < t := by
    rw [Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply,
      smul_eq_mul, mul_pos_iff_of_pos_left (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))]
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    refine ⟨_, ⟨(hpos t).mpr ht.2, ?_⟩, rfl⟩
    have h : -1 < (Homeomorph.unitBall t : ℝ) ∧ (Homeomorph.unitBall t : ℝ) < 1 := by
      simpa only [Real.ball_eq_Ioo, zero_sub, zero_add, mem_Ioo] using
        (Homeomorph.unitBall t).property
    exact h.2
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    let u : ball (0 : ℝ) 1 := ⟨t, by
      simp only [Real.ball_eq_Ioo, zero_sub, zero_add, mem_Ioo]
      exact ⟨by linarith [ht.1], ht.2⟩⟩
    refine ⟨(x, Homeomorph.unitBall.symm u), ⟨mem_univ _, ?_⟩, ?_⟩
    · exact (hpos _).mp (by simpa only [Homeomorph.apply_symm_apply] using ht.1)
    · simp [bicollarOfClosedInterval, u]

/-- The negative half of the reparametrized collar is the original negative
open half-strip. -/
theorem image_bicollarOfClosedInterval_Iio (β : N × Icc (-1 : ℝ) 1 → M) :
    bicollarOfClosedInterval β '' (univ ×ˢ Iio 0) =
      β '' {p | -1 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 0} := by
  have hneg (t : ℝ) : (Homeomorph.unitBall t : ℝ) < 0 ↔ t < 0 := by
    rw [Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply,
      smul_neg_iff_of_pos_left (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))]
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    refine ⟨_, ⟨?_, (hneg t).mpr ht.2⟩, rfl⟩
    have h : -1 < (Homeomorph.unitBall t : ℝ) ∧ (Homeomorph.unitBall t : ℝ) < 1 := by
      simpa only [Real.ball_eq_Ioo, zero_sub, zero_add, mem_Ioo] using
        (Homeomorph.unitBall t).property
    exact h.1
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    let u : ball (0 : ℝ) 1 := ⟨t, by
      simp only [Real.ball_eq_Ioo, zero_sub, zero_add, mem_Ioo]
      exact ⟨ht.1, by linarith [ht.2]⟩⟩
    refine ⟨(x, Homeomorph.unitBall.symm u), ⟨mem_univ _, ?_⟩, ?_⟩
    · exact (hneg _).mp (by simpa only [Homeomorph.apply_symm_apply] using ht.2)
    · simp [bicollarOfClosedInterval, u]

section Topology

variable [TopologicalSpace N] [TopologicalSpace M]

/-- For a compact closed strip in a Hausdorff space, the image of the closed
strip is the closure of the reparametrized open strip. Injectivity is not needed. -/
theorem closure_range_bicollarOfClosedInterval [CompactSpace N] [T2Space M]
    {β : N × Icc (-1 : ℝ) 1 → M} (hβ : Continuous β) :
    closure (range (bicollarOfClosedInterval β)) = range β := by
  let j := inclusion (Ioo_subset_Icc_self (a := (-1 : ℝ)) (b := 1))
  have hj : DenseRange j := (denseRange_inclusion_iff _).mpr (by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  have hd : Dense {p : N × Icc (-1 : ℝ) 1 | -1 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} := by
    have hs : (univ : Set N) ×ˢ {t : Icc (-1 : ℝ) 1 | -1 < (t : ℝ) ∧ (t : ℝ) < 1} =
        {p : N × Icc (-1 : ℝ) 1 | -1 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} := by
      ext p
      simp
    rw [← hs]
    simpa only [j, DenseRange, range_prodMap, range_id, range_inclusion, mem_Ioo] using
      (denseRange_id : DenseRange (id : N → N)).prodMap hj
  rw [range_bicollarOfClosedInterval]
  apply subset_antisymm
  · exact closure_minimal (image_subset_range _ _) (isCompact_range hβ).isClosed
  · have h := image_closure_subset_closure_image hβ
      (s := {p : N × Icc (-1 : ℝ) 1 | -1 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})
    simpa only [hd.closure_eq, image_univ] using h

end Topology

section Manifold

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ F]
  [TopologicalSpace N] [TopologicalSpace M]
  [ChartedSpace F N] [ChartedSpace E M]

/-- A continuous injection of a closed strip in codimension one is a bicollar
of its zero slice. No smoothness, local-flatness or collaring theorem is needed. -/
theorem isBicollar_bicollarOfClosedInterval {β : N × Icc (-1 : ℝ) 1 → M}
    (hβ : Continuous β) (hinj : Injective β)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    IsBicollar (fun x ↦ β (x, ⟨0, by norm_num⟩)) (bicollarOfClosedInterval β) := by
  let : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  -- Read the native product atlas through the definitionally equal `ModelProd` type tag.
  let : ChartedSpace (F × ℝ) (N × ℝ) :=
    inferInstanceAs (ChartedSpace (ModelProd F ℝ) (N × ℝ))
  exact ⟨(continuous_bicollarOfClosedInterval hβ).isOpenEmbedding_of_injective
    (E := F × ℝ) (F := E) (injective_bicollarOfClosedInterval hinj)
    (by simpa using hdim.symm), bicollarOfClosedInterval_apply_zero β⟩

/-- The frontier of a compact embedded closed strip consists of its two end
slices. In particular neither end slice lies in the open bicollar. -/
theorem frontier_range_bicollarOfClosedInterval [CompactSpace N] [T2Space M]
    {β : N × Icc (-1 : ℝ) 1 → M} (hβ : Continuous β) (hinj : Injective β)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    frontier (range (bicollarOfClosedInterval β)) =
      β '' {p | (p.2 : ℝ) = -1 ∨ (p.2 : ℝ) = 1} := by
  have hopen := (isBicollar_bicollarOfClosedInterval hβ hinj hdim).isOpenEmbedding.isOpen_range
  rw [frontier, closure_range_bicollarOfClosedInterval hβ, hopen.interior_eq,
    range_bicollarOfClosedInterval, ← image_univ, ← image_sdiff hinj]
  congr 1
  ext ⟨x, t⟩
  simp only [mem_sdiff, mem_univ, mem_ofPred_eq, true_and, not_and_or, not_lt]
  have ht := t.property
  constructor
  · rintro (h | h)
    · exact Or.inl (le_antisymm h ht.1)
    · exact Or.inr (le_antisymm ht.2 h)
  · rintro (h | h)
    · exact Or.inl h.le
    · exact Or.inr h.ge

end Manifold

end TauCeti
