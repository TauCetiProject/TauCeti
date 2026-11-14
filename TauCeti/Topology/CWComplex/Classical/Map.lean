/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
import TauCeti.Topology.Category.TopCat.Subspace

/-!
# Cellular maps of relative CW complexes

A cellular map preserves the skeletal filtration of a relative CW complex. This condition
ensures that the map restricts to each skeleton and to each consecutive skeletal pair, the
restrictions used to act on cellular chains; on `Set.univ`, `TauCeti.isCellular_univ_iff`
characterizes cellularity via `Set.MapsTo` on skeleta and `TauCeti.skeletonMap_univ_comm` gives
skeletal commutativity for commuting squares. A map carrying the base into the base and the
characteristic map of every cell onto the characteristic map of a cell of the same dimension is
cellular (`TauCeti.isCellular_of_map_eq`, `TauCeti.isCellular_univ_of_map_eq`).

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

open CategoryTheory Metric Topology Topology.RelCWComplex

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

/-- A map of relative CW complexes carrying the base into the base and the characteristic map of
every cell onto the characteristic map of a cell of the same dimension, on the closed unit ball,
is cellular. -/
lemma isCellular_of_map_eq {f : TopCat.of C ⟶ TopCat.of C'}
    (hD : ∀ x : C, x.1 ∈ D → (f x).1 ∈ E)
    (hf : ∀ (n : ℕ) (i : cell C n), ∃ i' : cell C' n, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1,
      ∀ hx : map n i x ∈ C, (f ⟨map n i x, hx⟩).1 = map n i' x) :
    IsCellular C C' f := by
  rintro n ⟨x, hxC⟩ (hx : x ∈ skeletonLT C n)
  change (f ⟨x, hxC⟩).1 ∈ skeletonLT C' n  -- the membership of a subtype point in a set
  rw [RelCWComplex.mem_skeletonLT_iff] at hx ⊢
  obtain hxD | ⟨m, hm, i, y, hy, rfl⟩ := hx
  · exact Or.inl (hD _ hxD)
  · obtain ⟨i', hi'⟩ := hf m i
    exact Or.inr ⟨m, hm, i', y, hy, (hi' y (ball_subset_closedBall hy) hxC).symm⟩

/-- For relative CW structures on `Set.univ`, `f : C(X, Y)` is cellular via
`f.restrictPreimage Set.univ` iff `f` maps each skeleton of `X` into that of `Y`. -/
theorem isCellular_univ_iff [RelCWComplex (Set.univ : Set X) D] [RelCWComplex (Set.univ : Set Y) E]
    {f : C(X, Y)} :
    IsCellular (Set.univ : Set X) (Set.univ : Set Y)
      (TopCat.ofHom (f.restrictPreimage Set.univ)) ↔
      ∀ n : ℕ, Set.MapsTo f (skeletonLT (Set.univ : Set X) (n : ℕ∞))
        (skeletonLT (Set.univ : Set Y) (n : ℕ∞)) := by
  rw [TopCat.ofHom_restrictPreimage_univ_eq]
  exact forall_congr' fun _ ↦ ⟨fun hf x hx ↦ @hf ⟨x, trivial⟩ hx, fun hf x hx ↦ @hf x.1 hx⟩

/-- A continuous map from a CW structure on `Set.univ` to a relative CW structure on `Set.univ`
sending each characteristic map onto one of the same dimension on the closed ball is cellular. -/
theorem isCellular_univ_of_map_eq [CWComplex (Set.univ : Set X)]
    [RelCWComplex (Set.univ : Set Y) E] {f : C(X, Y)}
    (hf : ∀ (n : ℕ) (i : cell (Set.univ : Set X) n), ∃ i' : cell (Set.univ : Set Y) n,
      ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, f (map n i x) = map n i' x) :
    IsCellular (Set.univ : Set X) (Set.univ : Set Y)
      (TopCat.ofHom (f.restrictPreimage Set.univ)) := by
  rw [TopCat.ofHom_restrictPreimage_univ_eq]
  refine isCellular_of_map_eq _ _ (fun _ h ↦ h.elim) fun n i ↦ ?_
  obtain ⟨i', hi'⟩ := hf n i
  exact ⟨i', fun x hx _ ↦ by simpa [TopCat.ofHom_apply] using hi' x hx⟩

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- The restriction of a cellular map to the `n`-th stage of the skeletal filtration. -/
def skeletonMap (n : ℕ) : skeletonObj C n ⟶ skeletonObj C' n :=
  TopCat.ofHom ⟨fun x ↦ ⟨(f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩).1,
    hf n x.2⟩, by fun_prop⟩

/-- Skeletal restrictions of equal cellular maps are equal. -/
lemma skeletonMap_congr {f₁ f₂ : TopCat.of C ⟶ TopCat.of C'} (h : f₁ = f₂)
    (hf₁ : IsCellular C C' f₁) (hf₂ : IsCellular C C' f₂) (n : ℕ) :
    skeletonMap C C' hf₁ n = skeletonMap C C' hf₂ n := by subst h; rfl

/-- On points, the restriction to a skeleton agrees with the original cellular map. -/
@[simp]
lemma skeletonMap_apply (n : ℕ) (x : skeletonObj C n) :
    (skeletonMap C C' hf n).hom.toFun x =
      ⟨(f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩).1, hf n x.2⟩ := by
  simp [skeletonMap]

/-- Restriction of a cellular map commutes with inclusions of skeleta. -/
@[reassoc]
lemma skeletonMap_comp_inclusion {n m : ℕ} (h : n ≤ m) :
    skeletonMap C C' hf n ≫
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (C := C') (mod_cast h))) =
    TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (C := C) (mod_cast h))) ≫
      skeletonMap C C' hf m := by
  ext x
  rfl

/-- Restriction of a cellular map commutes with inclusion of a skeleton into the complex. -/
@[reassoc]
lemma skeletonMap_comp_inclusion_complex (n : ℕ) :
    skeletonMap C C' hf n ≫
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C' n).subset_complex) =
    TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C n).subset_complex) ≫ f := by
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

/-- For a commuting square of continuous maps that are cellular on `Set.univ`, the induced
restrictions `skeletonMap` commute on every skeleton. -/
@[reassoc]
theorem skeletonMap_univ_comm {X₁ X₂ Y₁ Y₂ : Type w}
    [TopologicalSpace X₁] [T2Space X₁] [TopologicalSpace X₂] [T2Space X₂]
    [TopologicalSpace Y₁] [T2Space Y₁] [TopologicalSpace Y₂] [T2Space Y₂]
    {D₁ : Set X₁} {D₂ : Set X₂} {E₁ : Set Y₁} {E₂ : Set Y₂}
    [RelCWComplex (Set.univ : Set X₁) D₁] [RelCWComplex (Set.univ : Set X₂) D₂]
    [RelCWComplex (Set.univ : Set Y₁) E₁] [RelCWComplex (Set.univ : Set Y₂) E₂]
    {i₁ : C(X₁, Y₁)} {i₂ : C(X₂, Y₂)} {f : C(X₁, X₂)} {g : C(Y₁, Y₂)}
    (hi₁ : IsCellular (Set.univ : Set X₁) (Set.univ : Set Y₁)
      (TopCat.ofHom (i₁.restrictPreimage Set.univ)))
    (hi₂ : IsCellular (Set.univ : Set X₂) (Set.univ : Set Y₂)
      (TopCat.ofHom (i₂.restrictPreimage Set.univ)))
    (hf : IsCellular (Set.univ : Set X₁) (Set.univ : Set X₂)
      (TopCat.ofHom (f.restrictPreimage Set.univ)))
    (hg : IsCellular (Set.univ : Set Y₁) (Set.univ : Set Y₂)
      (TopCat.ofHom (g.restrictPreimage Set.univ)))
    (hcomm : ∀ x, g (i₁ x) = i₂ (f x)) (n : ℕ) :
    skeletonMap _ _ hi₁ n ≫ skeletonMap _ _ hg n =
      skeletonMap _ _ hf n ≫ skeletonMap _ _ hi₂ n := by
  rw [← skeletonMap_comp, ← skeletonMap_comp]
  refine skeletonMap_congr _ _ ?_ _ _ n
  rw [TopCat.ofHom_restrictPreimage_univ_eq, TopCat.ofHom_restrictPreimage_univ_eq,
    TopCat.ofHom_restrictPreimage_univ_eq, TopCat.ofHom_restrictPreimage_univ_eq]
  refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
  simpa [TopCat.ofHom_apply] using hcomm x.1

end TauCeti
