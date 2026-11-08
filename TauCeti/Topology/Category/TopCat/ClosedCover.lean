/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Adjunction spaces from finite closed covers

A space `X` which is the union of a closed subspace `L` and finitely many pairwise disjoint closed
pieces `χ i (D i)`, each meeting `L` exactly in the image of a subspace `A i ⊆ D i`, is obtained
from `L` by attaching the spaces `D i` along the maps `A i → L`: the square

```
  ⨆ᵢ A i ──> L
     │        │
     v        v
  ⨆ᵢ D i ──> X
```

is a pushout in `TopCat` (`TauCeti.TopCat.isPushout_sigmaDesc_of_isClosedEmbedding`). The map
from the abstract pushout to `X` is a continuous bijection, and it is closed because a closed
subset of the pushout is the union of its finitely many pieces in `L` and in the `D i`, each
carried onto a closed subset of `X`.

This recognizes a space given concretely as a union, such as a sublevel of a Morse function with
handles attached, as the corresponding attaching construction, a pushout in `TopCat`.
-/

public section

open CategoryTheory Limits Topology

universe u

namespace TauCeti.TopCat

variable {ι : Type u} {A D : ι → TopCat.{u}} {L X : TopCat.{u}} {α : ∀ i, A i ⟶ L}
  {j : ∀ i, A i ⟶ D i} {g : L ⟶ X} {χ : ∀ i, D i ⟶ X}

/-- **Attaching spaces along a finite closed cover.** Let `g : L ⟶ X` and `χ i : D i ⟶ X`, for
finitely many `i`, be closed embeddings whose ranges cover `X`, with the ranges of the `χ i`
pairwise disjoint. Let `j i : A i ⟶ D i` and `α i : A i ⟶ L` satisfy `α i ≫ g = j i ≫ χ i`, and
suppose every point of `D i` carried by `χ i` into the range of `g` lies in the range of `j i`.
Then `X` is the pushout of `L` and `⨆ᵢ D i` along `⨆ᵢ A i`, with legs `g` and the `χ i`. -/
theorem isPushout_sigmaDesc_of_isClosedEmbedding [Finite ι] (hw : ∀ i, α i ≫ g = j i ≫ χ i)
    (hg : IsClosedEmbedding g) (hχ : ∀ i, IsClosedEmbedding (χ i))
    (hdisj : Pairwise (Function.onFun Disjoint fun i ↦ Set.range (χ i)))
    (hmeet : ∀ i d, χ i d ∈ Set.range g → d ∈ Set.range (j i))
    (hcover : Set.range g ∪ ⋃ i, Set.range (χ i) = Set.univ) :
    IsPushout (Sigma.desc α) (Limits.Sigma.map j) g (Sigma.desc χ) := by
  have sq := IsPushout.of_hasPushout (Sigma.desc α) (Limits.Sigma.map j)
  have hw' : Sigma.desc α ≫ g = Limits.Sigma.map j ≫ Sigma.desc χ :=
    Sigma.hom_ext _ _ fun i ↦ by simp [hw]
  set φ := pushout.desc g (Sigma.desc χ) hw'
  set inl := pushout.inl (Sigma.desc α) (Limits.Sigma.map j)
  set inr := pushout.inr (Sigma.desc α) (Limits.Sigma.map j)
  have hinl (x : L) : φ (inl x) = g x := by
    rw [← ConcreteCategory.comp_apply, pushout.inl_desc]
  have hinr (i : ι) (d : D i) : φ (inr (Sigma.ι D i d)) = χ i d := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, pushout.inr_desc,
      Sigma.ι_comp_desc]
  -- Every point of the pushout comes from `L` or from one of the `D i`.
  have hP (y : (pushout (Sigma.desc α) (Limits.Sigma.map j) : TopCat.{u})) :
      (∃ x, inl x = y) ∨ ∃ i d, inr (Sigma.ι D i d) = y := by
    obtain ⟨x, hx⟩ | ⟨z, rfl⟩ := Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout sq) y
    · exact Or.inl ⟨x, hx⟩
    · obtain ⟨⟨i⟩, d, rfl⟩ := Concrete.colimit_exists_rep (Discrete.functor D) z
      exact Or.inr ⟨i, d, rfl⟩
  -- A point of `L` and a point of `D i` with the same image in `X` are identified in the pushout.
  have hglue (x : L) (i : ι) (d : D i) (h : g x = χ i d) : inl x = inr (Sigma.ι D i d) := by
    obtain ⟨a, rfl⟩ := hmeet i d ⟨x, h⟩
    have ha : g (α i a) = g x := by
      rw [← ConcreteCategory.comp_apply, hw, ConcreteCategory.comp_apply, h]
    have hsq : inl (α i a) = inr (Sigma.ι D i (j i a)) := by
      simpa [Sigma.ι_map_apply] using ConcreteCategory.congr_hom sq.w (Sigma.ι A i a)
    rwa [← hg.injective ha]
  have hinj : Function.Injective φ := by
    intro a b hab
    rcases hP a with ⟨x, rfl⟩ | ⟨i, d, rfl⟩ <;> rcases hP b with ⟨x', rfl⟩ | ⟨i', d', rfl⟩
    · rw [hinl, hinl] at hab
      rw [hg.injective hab]
    · rw [hinl, hinr] at hab
      exact hglue x i' d' hab
    · rw [hinl, hinr] at hab
      exact (hglue x' i d hab.symm).symm
    · rw [hinr, hinr] at hab
      obtain rfl : i = i' := by_contra fun hii' ↦
        Set.disjoint_left.1 (hdisj hii') ⟨d, rfl⟩ ⟨d', hab.symm⟩
      rw [(hχ i).injective hab]
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ | hy := (Set.eq_univ_iff_forall.1 hcover) y
    · exact ⟨inl x, hinl x⟩
    · obtain ⟨i, d, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨inr (Sigma.ι D i d), hinr i d⟩
  -- A closed set of the pushout is carried onto the union of the images of its finitely many
  -- pieces in `L` and in the `D i`, each closed in `X`.
  have hclosed : IsClosedMap φ := by
    intro C hC
    have hC' : φ '' C = g '' (inl ⁻¹' C) ∪ ⋃ i, χ i '' ((inr ∘ Sigma.ι D i) ⁻¹' C) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hP z with ⟨x, rfl⟩ | ⟨i, d, rfl⟩
        · exact Or.inl ⟨x, hz, (hinl x).symm⟩
        · exact Or.inr (Set.mem_iUnion.2 ⟨i, d, hz, (hinr i d).symm⟩)
      · rintro (⟨x, hx, rfl⟩ | hy)
        · exact ⟨inl x, hx, hinl x⟩
        · obtain ⟨i, d, hd, rfl⟩ := Set.mem_iUnion.1 hy
          exact ⟨inr (Sigma.ι D i d), hd, hinr i d⟩
    rw [hC']
    exact (hg.isClosedMap _ (hC.preimage inl.hom.continuous)).union
      (isClosed_iUnion_of_finite fun i ↦ (hχ i).isClosedMap _
        (hC.preimage (inr.hom.continuous.comp (Sigma.ι D i).hom.continuous)))
  have := TopCat.isIso_of_bijective_of_isClosedMap φ ⟨hinj, hsurj⟩ hclosed
  exact sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso φ) (by simp) (by simp)
    (by simp [φ, inl]) (by simp [φ, inr])

end TauCeti.TopCat
