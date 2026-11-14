/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CellAction
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Cellular maps of relative CW complexes

A cellular map preserves the skeletal filtration of a relative CW complex. This condition
ensures that the map restricts to each skeleton and to each consecutive skeletal pair, the
restrictions used to act on cellular chains. A map carrying the base into the base and every open
cell into an open cell of the same dimension is cellular (`TauCeti.isCellular_of_mapsTo_openCell`),
as is one matching characteristic maps on the closed unit ball (`TauCeti.isCellular_of_map_eq`).
In particular, continuous scalar multiplication preserving open cells of a CW complex restricts to
cellular self-maps (`TauCeti.cellularSMul`, `TauCeti.isCellular_cellularSMul`).

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

/-- A map of relative CW complexes carrying the base into the base and every open cell into an open
cell of the same dimension is cellular. -/
lemma isCellular_of_mapsTo_openCell {f : TopCat.of C ⟶ TopCat.of C'}
    (hD : ∀ x : C, x.1 ∈ D → (f x).1 ∈ E)
    (hf : ∀ (n : ℕ) (i : cell C n), ∃ i' : cell C' n,
      ∀ x : C, x.1 ∈ openCell n i → (f x).1 ∈ openCell n i') :
    IsCellular C C' f := by
  rintro n ⟨x, hxC⟩ (hx : x ∈ skeletonLT C n)
  change (f ⟨x, hxC⟩).1 ∈ skeletonLT C' n
  rw [RelCWComplex.mem_skeletonLT_iff] at hx ⊢
  obtain hxD | ⟨m, hm, i, hxi⟩ := hx
  · exact Or.inl (hD _ hxD)
  · obtain ⟨i', hi'⟩ := hf m i
    exact Or.inr ⟨m, hm, i', hi' ⟨x, hxC⟩ hxi⟩

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

section CellularSMul

open scoped Pointwise

variable {W : Type w} [TopologicalSpace W] (K : Set W) [CWComplex K] {G : Type*}

/-- Continuous translation by `g`, restricted to a CW complex `K` whose open cells are carried onto
open cells of the same dimension. -/
def cellularSMul [SMul G W] [ContinuousConstSMul G W]
    (hcell : ∀ (g : G) (n : ℕ) (i : cell K n), ∃ j : cell K n, g • openCell n i = openCell n j)
    (g : G) : TopCat.of K ⟶ TopCat.of K :=
  TopCat.ofHom ⟨fun x ↦ ⟨g • x.1, smul_mem_complex g (hcell g) x.2⟩, by fun_prop⟩

/-- On points, `TauCeti.cellularSMul` acts by scalar multiplication in the ambient space. -/
@[simp]
lemma coe_cellularSMul_apply [SMul G W] [ContinuousConstSMul G W]
    (hcell : ∀ (g : G) (n : ℕ) (i : cell K n), ∃ j : cell K n, g • openCell n i = openCell n j)
    (g : G) (x : K) :
    (cellularSMul K hcell g x : W) = g • (x : W) :=
  (rfl)

/-- Translation by `1` on a CW complex is the identity morphism. -/
@[simp]
lemma cellularSMul_one [Monoid G] [MulAction G W] [ContinuousConstSMul G W]
    (hcell : ∀ (g : G) (n : ℕ) (i : cell K n), ∃ j : cell K n, g • openCell n i = openCell n j) :
    cellularSMul K hcell (1 : G) = 𝟙 (TopCat.of K) := by
  ext x
  exact one_smul G x.1

/-- Translation by `g * h` on a CW complex is successive translation by `h` then `g`. -/
lemma cellularSMul_mul [Monoid G] [MulAction G W] [ContinuousConstSMul G W]
    (hcell : ∀ (g : G) (n : ℕ) (i : cell K n), ∃ j : cell K n, g • openCell n i = openCell n j)
    (g h : G) :
    cellularSMul K hcell (g * h) = cellularSMul K hcell h ≫ cellularSMul K hcell g := by
  ext x
  exact mul_smul g h x.1

/-- Continuous translation preserving open cells of a Hausdorff CW complex is cellular. -/
lemma isCellular_cellularSMul [T2Space W] [SMul G W] [ContinuousConstSMul G W]
    (hcell : ∀ (g : G) (n : ℕ) (i : cell K n), ∃ j : cell K n, g • openCell n i = openCell n j)
    (g : G) :
    IsCellular K K (cellularSMul K hcell g) := by
  refine isCellular_of_mapsTo_openCell K K (fun _ hx ↦ hx.elim) fun n i ↦ ?_
  obtain ⟨j, hj⟩ := hcell g n i
  exact ⟨j, fun x hx ↦ hj ▸ Set.smul_mem_smul_set hx⟩

end CellularSMul

end TauCeti
