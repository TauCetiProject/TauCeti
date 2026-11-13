/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.Coprod.FreelyIndecomposable.Basic
public import TauCeti.GroupTheory.CoprodI.Split

/-!
# Freely indecomposable groups as free products of many factors

A freely indecomposable group which is a free product `∗ᵢ Mᵢ` of a nonempty family of groups is
one of the `Mᵢ`. If it is a free product `P ∗ F(X)` with a free group and is not infinite cyclic,
then `X` is empty. Together: a freely indecomposable group, not infinite cyclic, which is a free
product `(∗ᵢ Mᵢ) ∗ F(X)` is one of the `Mᵢ`. This is the form in which free indecomposability
meets the Kurosh decomposition of a group acting on a tree with trivial edge stabilizers, whose
factors are vertex stabilizers and a free group.

## Main results

* `TauCeti.IsFreelyIndecomposable.exists_surjective_of_coprodI`: a freely indecomposable free
  product of a nonempty family is the image of one of its factors.
* `TauCeti.IsFreelyIndecomposable.isEmpty_of_coprod_freeGroup`: a freely indecomposable group
  which is not infinite cyclic has no free part in a free product decomposition `P ∗ F(X)`.
* `TauCeti.IsFreelyIndecomposable.exists_surjective_of_coprodI_coprod_freeGroup`: a freely
  indecomposable group, not infinite cyclic, which is a free product `(∗ᵢ Mᵢ) ∗ F(X)` is the image
  of one of the `Mᵢ`.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), Introduction
  (freely indecomposable groups and Grushko decompositions, pp. 1 and 3) and §3.2 (`ℤ` as a
  freely decomposable group, p. 30).
-/

public section

open Monoid Function
open scoped Monoid.Coprod

namespace TauCeti.IsFreelyIndecomposable

variable {G : Type*} [Group G] {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]

/-- A freely indecomposable group which is the free product of a nonempty family of groups is
the image of one of them. -/
theorem exists_surjective_of_coprodI [Nonempty ι] (hG : IsFreelyIndecomposable G)
    {f : CoprodI M →* G} (hf : Bijective f) : ∃ i, Surjective (f.comp (CoprodI.of (i := i))) := by
  obtain h | ⟨i, hi⟩ := forall_or_exists_not fun i ↦ Subsingleton (M i)
  · -- all the factors are trivial, hence so is `G`
    have := hf.2.subsingleton
    exact ⟨Classical.arbitrary ι, fun _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  -- `G = Mᵢ ∗ (∗_{j ≠ i} Mⱼ)` with `Mᵢ` nontrivial, so the second factor is trivial
  have hf' := hf.comp (CoprodI.ofCoprodNe_bijective M i)
  obtain h | h :=
    hG.subsingleton_or_subsingleton (.ofBijective (f.comp (CoprodI.ofCoprodNe M i)) hf')
  · exact (hi h).elim
  exact ⟨i, by simpa [comp_def] using hf'.2.comp Coprod.inl_surjective⟩

/-- If a freely indecomposable group which is not infinite cyclic is the free product of a group
and of the free group on `X`, then `X` is empty. -/
theorem isEmpty_of_coprod_freeGroup {P : Type*} [Group P] {X : Type*}
    (hG : IsFreelyIndecomposable G) (hZ : IsEmpty (G ≃* Multiplicative ℤ))
    {f : P ∗ FreeGroup X →* G} (hf : Bijective f) : IsEmpty X := by
  by_contra! hX
  obtain hP | hF := hG.subsingleton_or_subsingleton (.ofBijective f hf)
  · -- `G` is the free group on `X`, the free product of copies of `ℤ` indexed by `X`, so it is one
    -- of these copies of `ℤ`
    let g := (f.comp Coprod.inr).comp (freeGroupEquivCoprodI (ι := X)).symm.toMonoidHom
    have hg : Bijective g :=
      (hf.comp ⟨Coprod.inr_injective, Coprod.inr_surjective⟩).comp (MulEquiv.bijective _)
    obtain ⟨x, hx⟩ := hG.exists_surjective_of_coprodI hg
    exact hZ.false ((MulEquiv.ofBijective (g.comp CoprodI.of)
      ⟨hg.1.comp (CoprodI.of_injective x), hx⟩).symm.trans FreeGroup.mulEquivIntOfUnique)
  · exact not_subsingleton _ hF

/-- A freely indecomposable group, not infinite cyclic, which is the free product of a nonempty
family of groups and of a free group is the image of one of the groups of the family. -/
theorem exists_surjective_of_coprodI_coprod_freeGroup [Nonempty ι] {X : Type*}
    (hG : IsFreelyIndecomposable G) (hZ : IsEmpty (G ≃* Multiplicative ℤ))
    {f : CoprodI M ∗ FreeGroup X →* G} (hf : Bijective f) :
    ∃ i, Surjective (f.comp (Coprod.inl.comp (CoprodI.of (i := i)))) := by
  have := hG.isEmpty_of_coprod_freeGroup hZ hf
  exact hG.exists_surjective_of_coprodI (f := f.comp Coprod.inl)
    ⟨hf.1.comp Coprod.inl_injective, hf.2.comp Coprod.inl_surjective⟩

end TauCeti.IsFreelyIndecomposable
