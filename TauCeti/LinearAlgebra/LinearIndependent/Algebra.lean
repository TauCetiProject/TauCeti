/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lifting linear independence by expanding coefficients

Suppose the image of a scalar semiring `S` in an algebra `L` lies in the `R`-span of a family `γ`.
If the products `γ m * β i` are linearly independent over `R`, then `β` is linearly independent
over `S`, provided `S` acts faithfully on `L`. This reduces independence over `S` to independence
over `R` by expanding the coefficients in the spanning family.
-/

public section

namespace TauCeti

/-- If every element of `S` is an `R`-linear combination of a family `γ` in `L`, and the
products `γ m * β i` are linearly independent over `R`, then `β` is linearly independent over `S`.
The scalar map from `S` to `L` must be injective. -/
theorem linearIndependent_of_linearIndependent_mul_of_mem_span {R S L : Type*} [CommSemiring R]
    [CommSemiring S] [Semiring L] [Algebra R L] [Algebra S L] [FaithfulSMul S L]
    {κ ι : Type*} {γ : κ → L} {β : ι → L}
    (hγ : ∀ x : S, algebraMap S L x ∈ Submodule.span R (Set.range γ))
    (h : LinearIndependent R fun p : ι × κ ↦ γ p.2 * β p.1) :
    LinearIndependent S β := by
  classical
  choose c hc using fun x ↦ Finsupp.mem_span_range_iff_exists_finsupp.mp (hγ x)
  rw [linearIndependent_iff'ₛ] at h ⊢
  intro s f g hfg i hi
  let T := s.biUnion fun j ↦ (c (f j)).support ∪ (c (g j)).support
  have hexpand (x : S) (hx : (c x).support ⊆ T) :
      algebraMap S L x = ∑ m ∈ T, c x m • γ m := by
    rw [← hc x, Finsupp.sum_of_support_subset _ hx]
    intro m _
    simp
  have hsum (a : ι → S) (ha : ∀ j ∈ s, (c (a j)).support ⊆ T) :
      ∑ j ∈ s, a j • β j = ∑ p ∈ s ×ˢ T, c (a p.1) p.2 • (γ p.2 * β p.1) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Algebra.smul_def, hexpand (a j) (ha j hj), Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ ↦ smul_mul_assoc _ _ _
  have hT (j : ι) (hj : j ∈ s) : (c (f j)).support ∪ (c (g j)).support ⊆ T :=
    Finset.subset_biUnion_of_mem (fun j ↦ (c (f j)).support ∪ (c (g j)).support) hj
  have hf : ∀ j ∈ s, (c (f j)).support ⊆ T := fun j hj ↦
    Finset.subset_union_left.trans (hT j hj)
  have hg : ∀ j ∈ s, (c (g j)).support ⊆ T := fun j hj ↦
    Finset.subset_union_right.trans (hT j hj)
  have hcoeff := h (s ×ˢ T) (fun p ↦ c (f p.1) p.2) (fun p ↦ c (g p.1) p.2)
    ((hsum f hf).symm.trans (hfg.trans (hsum g hg)))
  apply FaithfulSMul.algebraMap_injective S L
  rw [hexpand (f i) (hf i hi), hexpand (g i) (hg i hi)]
  exact Finset.sum_congr rfl fun m hm ↦ by
    rw [hcoeff (i, m) (Finset.mem_product.mpr ⟨hi, hm⟩)]

end TauCeti
