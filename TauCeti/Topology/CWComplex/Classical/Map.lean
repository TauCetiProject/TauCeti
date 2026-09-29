/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Skeleton

/-!
# Cellular maps of relative CW complexes

A cellular map preserves the skeletal filtration of a relative CW complex. This condition
ensures that the map restricts to each skeleton and to each consecutive skeletal pair, the
restrictions used to act on cellular chains.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

open CategoryTheory Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X Y Z : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  {D : Set X} {E : Set Y} {F : Set Z}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

/-- A map of relative CW complexes is cellular if it preserves every stage of the skeletal
filtration. In particular, it sends the base (stage zero) into the target base. -/
abbrev IsCellular (f : TopCat.of C ⟶ TopCat.of C') : Prop :=
  ∀ n : ℕ, Set.MapsTo f
    {x : C | x.1 ∈ skeletonLT C (n : ℕ∞)}
    {y : C' | y.1 ∈ skeletonLT C' (n : ℕ∞)}

/-- The identity map preserves every skeleton. -/
lemma isCellular_id : IsCellular C C (𝟙 (TopCat.of C)) := fun _ _ h ↦ h

/-- The composite of cellular maps is cellular. -/
lemma IsCellular.comp {C'' : Set Z} [RelCWComplex C'' F]
    {f : TopCat.of C ⟶ TopCat.of C'} {g : TopCat.of C' ⟶ TopCat.of C''}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g) :
    IsCellular C C'' (f ≫ g) := fun n _ hx ↦ hg n (hf n hx)

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- The restriction of a cellular map to the `n`-th stage of the skeletal filtration. -/
def skeletonMap (n : ℕ) : skeletonObj C n ⟶ skeletonObj C' n :=
  TopCat.ofHom ⟨fun x ↦ ⟨(f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩).1,
    hf n x.2⟩, by fun_prop⟩

/-- On points, the restriction to a skeleton agrees with the original cellular map. -/
@[simp]
lemma skeletonMap_apply (n : ℕ) (x : skeletonObj C n) :
    (skeletonMap C C' hf n).hom.toFun x =
      ⟨(f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩).1, hf n x.2⟩ := by
  simp [skeletonMap]

/-- Restriction of a cellular map commutes with the inclusions of consecutive skeleta. -/
@[reassoc]
lemma skeletonMap_comp_inclusion (n : ℕ) :
    skeletonMap C C' hf n ≫
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (C := C')
        (mod_cast n.le_succ))) =
    TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (C := C)
      (mod_cast n.le_succ))) ≫ skeletonMap C C' hf (n + 1) := by
  ext x
  rfl

/-- Restriction of the identity map to a skeleton is the identity. -/
@[simp]
lemma skeletonMap_id (n : ℕ) :
    skeletonMap C C (isCellular_id C) n = 𝟙 (skeletonObj C n) := by
  ext x
  rfl

variable (C'' : Set Z) [RelCWComplex C'' F]
  {g : TopCat.of C' ⟶ TopCat.of C''} (hg : IsCellular C' C'' g)

/-- Restriction to a skeleton respects composition of cellular maps. -/
@[reassoc]
lemma skeletonMap_comp (n : ℕ) :
    skeletonMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonMap C C' hf n ≫ skeletonMap C' C'' hg n := by
  ext x
  rfl

end TauCeti
