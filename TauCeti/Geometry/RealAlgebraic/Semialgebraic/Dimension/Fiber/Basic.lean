/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Projection

/-!
# Finite fibers and semialgebraic dimension

A semialgebraic function with finite fibers on its domain preserves dimension, without any
continuity assumption. The fibers need not have a common cardinality, and the function need
not be injective. This is the zero-dimensional-fiber case of the semialgebraic fiber-dimension
theorem; in particular, semialgebraic bijections preserve dimension.

The key observation is that a cylindrical cell has order-connected vertical fibers. If these
are finite, they contain at most one point. The continuous section of the cell's projection
therefore parametrizes the whole cell, so projection is an embedding on each cell of an adapted
decomposition. Finite unions then give the dimension equality, and iteration handles arbitrary
coordinate projections. Applying this to the two projections of a semialgebraic graph gives
the result for arbitrary semialgebraic functions.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Section 2.8.
-/

public section

open Function Set Topology

namespace TauCeti

variable {m n : ℕ}

/-- Forgetting one coordinate preserves the dimension of a semialgebraic set if every
vertical fiber is finite. Empty sets and empty fibers are allowed. -/
theorem IsSemialgebraic.semialgebraicDim_image_tail_of_finite
    {s : Set (Fin (n + 1) → ℝ)} (hs : IsSemialgebraic s)
    (hfin : ∀ x, {t : ℝ | Fin.cons t x ∈ s}.Finite) :
    semialgebraicDim (Fin.tail '' s) = semialgebraicDim s := by
  obtain ⟨𝒞, h𝒞, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
  refine le_antisymm hs.semialgebraicDim_image_tail_le ?_
  rw [h𝒞.semialgebraicDim_eq_iSup hsub]
  refine iSup₂_le fun E hE ↦ ?_
  exact semialgebraicDim_le_of_isEmbedding
    (h𝒞.isEmbedding_tail_of_injOn hE.1
      (h𝒞.injOn_tail_of_finite hE.1 fun x ↦ (hfin x).subset fun _ ht ↦ hE.2 ht))
    (by rintro _ ⟨x, rfl⟩; exact mem_image_of_mem _ (hE.2 x.2))

/-- **Finite-fiber dimension theorem for coordinate projections.** A coordinate projection
with finite fibers on a semialgebraic set preserves dimension. Coordinates may be repeated or
reordered, and no uniform bound on the finite fibers is required. -/
theorem IsSemialgebraic.semialgebraicDim_image_comp_of_finite
    {s : Set (Fin n → ℝ)} (hs : IsSemialgebraic s) (ι : Fin m → Fin n)
    (hfin : ∀ y, {x ∈ s | x ∘ ι = y}.Finite) :
    semialgebraicDim ((fun x ↦ x ∘ ι) '' s) = semialgebraicDim s := by
  induction n generalizing m with
  | zero => exact semialgebraicDim_image_comp_of_surjective (·.elim0) s
  | succ n ih =>
    by_cases hsurj : Surjective ι
    · exact semialgebraicDim_image_comp_of_surjective hsurj s
    obtain ⟨j, hj⟩ := not_forall.1 hsurj
    let σ := Equiv.swap (0 : Fin (n + 1)) j
    have hne (i : Fin m) : σ (ι i) ≠ 0 := fun h ↦
      hj ⟨i, by simpa [σ, Equiv.swap_apply_eq_iff] using h⟩
    let ι' : Fin m → Fin n := fun i ↦ (σ (ι i)).pred (hne i)
    have hcomp (z : Fin (n + 1) → ℝ) : Fin.tail (z ∘ σ) ∘ ι' = z ∘ ι := by
      funext i
      simp [ι', Fin.tail, σ]
    let t := (fun z : Fin (n + 1) → ℝ ↦ z ∘ σ) '' s
    have ht : IsSemialgebraic t := hs.image_comp σ
    have hvert (x : Fin n → ℝ) : {a : ℝ | Fin.cons a x ∈ t}.Finite := by
      refine ((hfin (x ∘ ι')).image (fun z ↦ z (σ 0))).subset ?_
      rintro a ⟨z, hzs, hz⟩
      have htail : Fin.tail (z ∘ σ) = x := by
        simpa only [Fin.tail_cons] using congrArg Fin.tail hz
      exact ⟨z, ⟨hzs, by rw [← hcomp, htail]⟩, congrFun hz 0⟩
    have hbase (y : Fin m → ℝ) : {x ∈ Fin.tail '' t | x ∘ ι' = y}.Finite := by
      refine ((hfin y).image (fun z ↦ Fin.tail (z ∘ σ))).subset ?_
      rintro x ⟨⟨_, ⟨z, hzs, rfl⟩, rfl⟩, hxy⟩
      exact ⟨z, ⟨hzs, (hcomp z).symm.trans hxy⟩, rfl⟩
    have heq : (fun x ↦ x ∘ ι) '' s = (fun x ↦ x ∘ ι') '' (Fin.tail '' t) := by
      simp only [t, image_image]
      exact image_congr fun z _ ↦ (hcomp z).symm
    rw [heq, ih (HasSemialgebraicProjections.isSemialgebraic_image_tail ht) ι' hbase,
      ht.semialgebraicDim_image_tail_of_finite hvert,
      semialgebraicDim_image_comp_of_surjective σ.surjective]

/-- **Finite-fiber dimension theorem.** A semialgebraic function with finite fibers on its
domain preserves dimension. In particular this applies to semialgebraic bijections, without
requiring continuity of the function or its inverse. -/
theorem IsSemialgebraicOn.semialgebraicDim_image_of_finite
    {s : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → Fin m → ℝ}
    (hf : IsSemialgebraicOn f s) (hfin : ∀ y, {x ∈ s | f x = y}.Finite) :
    semialgebraicDim (f '' s) = semialgebraicDim s := by
  let G := Fin.appendEquiv n m '' s.graphOn f
  have hmem (z : Fin (n + m) → ℝ) : z ∈ G ↔
      (z ∘ Fin.castAdd m) ∈ s ∧ f (z ∘ Fin.castAdd m) = z ∘ Fin.natAdd n := by
    simp [G, Equiv.image_eq_preimage_symm, mem_graphOn, comp_def]
  have hG : IsSemialgebraic G := by
    convert hf.graph.preimage_comp (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) using 1
    ext z
    rw [hmem, mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn]
    rfl
  have hleft : (fun z : Fin (n + m) → ℝ ↦ z ∘ Fin.castAdd m) '' G = s := by
    simp [G, image_image, comp_def]
  have hright : (fun z : Fin (n + m) → ℝ ↦ z ∘ Fin.natAdd n) '' G = f '' s := by
    simp [G, image_image, comp_def]
  have hfinite (y : Fin m → ℝ) :
      {z ∈ G | z ∘ Fin.natAdd n = y}.Finite := by
    refine ((hfin y).image (fun x ↦ Fin.append x (f x))).subset ?_
    rintro z ⟨hz, hzy⟩
    obtain ⟨hx, hfx⟩ := (hmem z).1 hz
    refine ⟨z ∘ Fin.castAdd m, ⟨hx, hfx.trans hzy⟩, ?_⟩
    exact (congrArg (Fin.append (z ∘ Fin.castAdd m)) hfx).trans Fin.append_castAdd_natAdd
  have hsingle (x : Fin n → ℝ) :
      {z ∈ G | z ∘ Fin.castAdd m = x}.Finite := by
    refine (finite_singleton (Fin.append x (f x))).subset ?_
    rintro z ⟨hz, hzx⟩
    obtain ⟨_, hfx⟩ := (hmem z).1 hz
    exact (Fin.append_castAdd_natAdd (f := z)).symm.trans
      (congrArg₂ Fin.append hzx (hfx.symm.trans (congrArg f hzx)))
  rw [← hright, hG.semialgebraicDim_image_comp_of_finite (Fin.natAdd n) hfinite,
    ← hG.semialgebraicDim_image_comp_of_finite (Fin.castAdd m) hsingle, hleft]

end TauCeti
