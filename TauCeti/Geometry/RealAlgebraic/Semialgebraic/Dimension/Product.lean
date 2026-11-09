/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic

/-!
# Dimension of products of semialgebraic sets

The dimension of a product is the sum of the dimensions of its factors. Products are read in
`Fin (m + n) → ℝ` through `Fin.appendEquiv`, as in the semialgebraic product API. The formula
includes empty factors: the dimension of the empty set is `⊥`, which is absorbing for addition.

The proof uses finite decompositions into locally closed Euclidean cells. The product of two
cells has the sum of their dimensions, and a cell of maximal dimension in each factor realizes
the lower bound. This gives the product calculus needed to compare dimensions in triangulations.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Section 2.8.
-/

public section

open Set Topology

namespace TauCeti

variable {m n : ℕ} {s : Set (Fin m → ℝ)} {t : Set (Fin n → ℝ)}

/-- The product of two nonempty Euclidean cells has the sum of their dimensions, with the
product read in concatenated coordinates. No semialgebraicity assumption is needed. -/
theorem semialgebraicDim_image_appendEquiv_prod_of_isOpenEmbedding
    (hs : s.Nonempty) (ht : t.Nonempty) {a b : ℕ}
    {f : s → Fin a → ℝ} {g : t → Fin b → ℝ}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) :
    semialgebraicDim (Fin.appendEquiv m n '' s ×ˢ t) = (a + b : ℕ) := by
  let e := ((Fin.appendHomeomorph (X := ℝ) m n).image (s ×ˢ t)).symm.trans
    (Homeomorph.Set.prod s t)
  exact semialgebraicDim_eq_of_isOpenEmbedding
    ((hs.prod ht).image _) (((Fin.appendHomeomorph a b).isOpenEmbedding.comp
      (hf.prodMap hg)).comp e.isOpenEmbedding)

/-- **Dimension of products.** The dimension of a product of semialgebraic sets is the sum
of their dimensions, including when either factor is empty. -/
theorem IsSemialgebraic.semialgebraicDim_image_appendEquiv_prod
    (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    semialgebraicDim (Fin.appendEquiv m n '' s ×ˢ t) =
      semialgebraicDim s + semialgebraicDim t := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  rcases t.eq_empty_or_nonempty with rfl | htne
  · simp
  obtain ⟨𝒮, h𝒮, hsU, hl⟩ := hs.exists_finite_sUnion_eq
  obtain ⟨𝒯, h𝒯, htU, hl'⟩ := ht.exists_finite_sUnion_eq
  have := h𝒮.to_subtype
  have := h𝒯.to_subtype
  let P : 𝒮 × 𝒯 → Set (Fin (m + n) → ℝ) :=
    fun uv ↦ Fin.appendEquiv m n '' uv.1.val ×ˢ uv.2.val
  have hcover : Fin.appendEquiv m n '' s ×ˢ t = ⋃ uv, P uv := by
    rw [← hsU, ← htU]
    ext x
    simp only [P, mem_image, mem_prod, mem_sUnion, mem_iUnion]
    aesop
  have hlocal (uv : 𝒮 × 𝒯) : IsLocallyClosed (P uv) := by
    have hprod : IsLocallyClosed (uv.1.val ×ˢ uv.2.val) :=
      ((hl _ uv.1.property).1.preimage continuous_fst).inter
        ((hl' _ uv.2.property).1.preimage continuous_snd)
    simpa only [P, Equiv.image_eq_preimage_symm, ← Fin.appendHomeomorph_toEquiv,
      Homeomorph.coe_symm_toEquiv] using
      hprod.preimage (Fin.appendHomeomorph (X := ℝ) m n).symm.continuous
  refine le_antisymm ?_ ?_
  · -- Every product cell has dimension bounded by the sum of the factor dimensions.
    rw [hcover, semialgebraicDim_iUnion_of_isLocallyClosed hlocal]
    refine iSup_le fun uv ↦ ?_
    rcases uv.1.val.eq_empty_or_nonempty with he | hu
    · simp [P, he]
    rcases uv.2.val.eq_empty_or_nonempty with he | hv
    · simp [P, he]
    obtain ⟨a, f, hf⟩ := (hl _ uv.1.property).2
    obtain ⟨b, g, hg⟩ := (hl' _ uv.2.property).2
    have ha : (a : WithBot ℕ∞) ≤ semialgebraicDim s := by
      rw [← semialgebraicDim_eq_of_isOpenEmbedding hu hf]
      exact semialgebraicDim_mono (hsU ▸ subset_sUnion_of_mem uv.1.property)
    have hb : (b : WithBot ℕ∞) ≤ semialgebraicDim t := by
      rw [← semialgebraicDim_eq_of_isOpenEmbedding hv hg]
      exact semialgebraicDim_mono (htU ▸ subset_sUnion_of_mem uv.2.property)
    simpa only [P, semialgebraicDim_image_appendEquiv_prod_of_isOpenEmbedding hu hv hf hg,
      Nat.cast_add] using add_le_add ha hb
  · -- Maximal-dimensional cells in the two factors attain the bound.
    obtain ⟨u, hus, _, hune, a, ha, f, hf⟩ :=
      hs.exists_isOpenEmbedding_semialgebraicDim_eq hsne
    obtain ⟨v, hvt, _, hvne, b, hb, g, hg⟩ :=
      ht.exists_isOpenEmbedding_semialgebraicDim_eq htne
    rw [ha, hb, ← Nat.cast_add,
      ← semialgebraicDim_image_appendEquiv_prod_of_isOpenEmbedding hune hvne hf hg]
    exact semialgebraicDim_mono (image_mono (prod_mono hus hvt))

end TauCeti
