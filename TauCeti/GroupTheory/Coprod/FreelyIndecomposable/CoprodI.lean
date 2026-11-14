/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.Coprod.Basic
public import TauCeti.GroupTheory.Coprod.FreelyIndecomposable.Basic
public import TauCeti.GroupTheory.CoprodI.Split

/-!
# Freely indecomposable groups as free products of many factors

A freely indecomposable group which is a free product `∗ᵢ Mᵢ` of a family of groups is one of the
`Mᵢ`, provided the family is nonempty or that group is nontrivial. The free group on `X` is freely
indecomposable exactly when `X` has at most one element, so a freely indecomposable free group
which is not infinite cyclic is trivial. Hence a freely indecomposable group which is not infinite
cyclic has no free part in a free product decomposition `P ∗ F` with `F` free, and if it is a free
product `(∗ᵢ Mᵢ) ∗ F` with `F` free, it is one of the `Mᵢ`, again provided the family is nonempty
or that group is nontrivial. This is the form in which free indecomposability meets the Kurosh
decomposition of a group acting on a tree with trivial edge stabilizers, whose factors are vertex
stabilizers and a free group.

## Main results

* `TauCeti.IsFreelyIndecomposable.exists_surjective_of_coprodI`,
  `TauCeti.IsFreelyIndecomposable.exists_surjective_of_coprodI_of_nontrivial`: a freely
  indecomposable group `G` which is a free product `∗ᵢ Mᵢ` is the image of one of the `Mᵢ`, when
  the index type is nonempty, respectively when `G` is nontrivial.
* `TauCeti.isFreelyIndecomposable_freeGroup_iff`: the free group on `X` is freely indecomposable
  if and only if `X` has at most one element.
* `TauCeti.IsFreelyIndecomposable.subsingleton_of_isFreeGroup`: a freely indecomposable free group
  which is not infinite cyclic is trivial.
* `TauCeti.IsFreelyIndecomposable.subsingleton_of_coprod_of_isFreeGroup`,
  `TauCeti.IsFreelyIndecomposable.isEmpty_of_coprod_freeGroup`: a freely indecomposable group
  which is not infinite cyclic has no free part in a free product decomposition `P ∗ F` with `F`
  free, respectively `P ∗ F(X)`.
* `TauCeti.IsFreelyIndecomposable.exists_surjective_of_coprodI_coprod_of_isFreeGroup`,
  `TauCeti.IsFreelyIndecomposable.exists_surjective_of_coprodI_coprod_of_isFreeGroup_of_nontrivial`:
  a freely indecomposable group `G`, not infinite cyclic, which is a free product `(∗ᵢ Mᵢ) ∗ F`
  with `F` free is the image of one of the `Mᵢ`, when the index type is nonempty, respectively
  when `G` is nontrivial.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), Introduction
  (freely indecomposable groups and Grushko decompositions, pp. 1 and 3) and §3.2 (`ℤ` as a
  freely decomposable group, p. 30).
-/

public section

open Monoid Function
open scoped Monoid.Coprod

namespace TauCeti

variable {G : Type*} [Group G] {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]

namespace IsFreelyIndecomposable

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

/-- A nontrivial freely indecomposable group which is the free product of a family of groups is
the image of one of them. -/
theorem exists_surjective_of_coprodI_of_nontrivial [Nontrivial G] (hG : IsFreelyIndecomposable G)
    {f : CoprodI M →* G} (hf : Bijective f) : ∃ i, Surjective (f.comp (CoprodI.of (i := i))) :=
  have : Nonempty ι := not_isEmpty_iff.1 fun _ ↦ not_subsingleton G hf.2.subsingleton
  hG.exists_surjective_of_coprodI hf

end IsFreelyIndecomposable

/-- The free group on `X` is freely indecomposable if and only if `X` has at most one element. -/
@[simp]
theorem isFreelyIndecomposable_freeGroup_iff {X : Type*} :
    IsFreelyIndecomposable (FreeGroup X) ↔ Subsingleton X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases isEmpty_or_nonempty X
    · infer_instance
    -- `F(X)` is the free product of copies of `ℤ` indexed by `X`, so it is the image of one of them
    obtain ⟨x, hx⟩ := h.exists_surjective_of_coprodI
      (f := (freeGroupEquivCoprodI (ι := X)).symm.toMonoidHom) (MulEquiv.bijective _)
    have := FreeGroup.isMulCommutative_iff_subsingleton.2 (inferInstance : Subsingleton Unit)
    exact FreeGroup.isMulCommutative_iff_subsingleton.1 hx.isMulCommutative
  · have := FreeGroup.isMulCommutative_iff_subsingleton.2 h
    exact isFreelyIndecomposable_of_isMulCommutative _

namespace IsFreelyIndecomposable

/-- A freely indecomposable free group which is not infinite cyclic is trivial. -/
theorem subsingleton_of_isFreeGroup [IsFreeGroup G] (hG : IsFreelyIndecomposable G)
    (hZ : IsEmpty (G ≃* Multiplicative ℤ)) : Subsingleton G := by
  let e := IsFreeGroup.toFreeGroup G
  obtain _ | ⟨⟨_⟩⟩ := (subsingleton_iff_isEmpty_or_unique _).1 <|
    isFreelyIndecomposable_freeGroup_iff.1 (hG.of_mulEquiv e)
  · exact e.toEquiv.subsingleton
  · exact hZ.elim (e.trans FreeGroup.mulEquivIntOfUnique)

/-- If a freely indecomposable group which is not infinite cyclic is the free product of a group
and of a free group `F`, then `F` is trivial. -/
theorem subsingleton_of_coprod_of_isFreeGroup {P F : Type*} [Group P] [Group F] [IsFreeGroup F]
    (hG : IsFreelyIndecomposable G) (hZ : IsEmpty (G ≃* Multiplicative ℤ))
    {f : P ∗ F →* G} (hf : Bijective f) : Subsingleton F := by
  obtain _ | hF := hG.subsingleton_or_subsingleton (.ofBijective f hf)
  · -- `P` is trivial, so `G` is isomorphic to the free group `F`
    let e : F ≃* G := .ofBijective (f.comp Coprod.inr)
      (hf.comp ⟨Coprod.inr_injective, Coprod.inr_surjective⟩)
    have := IsFreeGroup.ofMulEquiv e
    have := hG.subsingleton_of_isFreeGroup hZ
    exact e.toEquiv.subsingleton
  · exact hF

/-- If a freely indecomposable group which is not infinite cyclic is the free product of a group
and of the free group on `X`, then `X` is empty. -/
theorem isEmpty_of_coprod_freeGroup {P : Type*} [Group P] {X : Type*}
    (hG : IsFreelyIndecomposable G) (hZ : IsEmpty (G ≃* Multiplicative ℤ))
    {f : P ∗ FreeGroup X →* G} (hf : Bijective f) : IsEmpty X :=
  have := hG.subsingleton_of_coprod_of_isFreeGroup hZ hf
  ⟨fun x ↦ FreeGroup.of_ne_one x (Subsingleton.elim _ _)⟩

/-- A freely indecomposable group, not infinite cyclic, which is the free product of a nonempty
family of groups and of a free group is the image of one of the groups of the family. -/
theorem exists_surjective_of_coprodI_coprod_of_isFreeGroup [Nonempty ι] {F : Type*} [Group F]
    [IsFreeGroup F] (hG : IsFreelyIndecomposable G) (hZ : IsEmpty (G ≃* Multiplicative ℤ))
    {f : CoprodI M ∗ F →* G} (hf : Bijective f) :
    ∃ i, Surjective ((f.comp Coprod.inl).comp (CoprodI.of (i := i))) :=
  have := hG.subsingleton_of_coprod_of_isFreeGroup hZ hf
  hG.exists_surjective_of_coprodI ⟨hf.1.comp Coprod.inl_injective, hf.2.comp Coprod.inl_surjective⟩

/-- A nontrivial freely indecomposable group, not infinite cyclic, which is the free product of a
family of groups and of a free group is the image of one of the groups of the family. -/
theorem exists_surjective_of_coprodI_coprod_of_isFreeGroup_of_nontrivial [Nontrivial G]
    {F : Type*} [Group F] [IsFreeGroup F] (hG : IsFreelyIndecomposable G)
    (hZ : IsEmpty (G ≃* Multiplicative ℤ)) {f : CoprodI M ∗ F →* G} (hf : Bijective f) :
    ∃ i, Surjective ((f.comp Coprod.inl).comp (CoprodI.of (i := i))) :=
  have := hG.subsingleton_of_coprod_of_isFreeGroup hZ hf
  hG.exists_surjective_of_coprodI_of_nontrivial
    ⟨hf.1.comp Coprod.inl_injective, hf.2.comp Coprod.inl_surjective⟩

end IsFreelyIndecomposable

end TauCeti
