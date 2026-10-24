/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Cylinder

/-!
# Homology cobordisms

Let `R` be a ring. An `R`-*homology cobordism* between two manifolds `Y₀` and `Y₁` is a
compact manifold `W` whose boundary is the disjoint union of copies of `Y₀` and `Y₁`, such that both
inclusions induce isomorphisms on singular homology with coefficients in `R`. Thus `W` looks like
the product `Y₀ × [0, 1]` to `R`-homology. Homology cobordisms of integral homology `3`-spheres are
the ambient spaces of homology concordance of knots, and the homology cobordism group of homology
spheres is built from them.

The boundary of `W` is not given its own manifold structure here. Instead the two ends are smooth
embeddings `ι₀ : Y₀ → W` and `ι₁ : Y₁ → W` of manifolds modelled on `I` into the manifold `W`
modelled on `J`, with disjoint images whose union is the manifold boundary `J.boundary W`
(`TauCeti.IsHomologyCobordism R I J n ι₀ ι₁`). No orientations are involved: an integral homology
cobordism between integral homology spheres is automatically orientable, since its first homology
vanishes.

The cylinder `Y × [a, b]` over a compact boundaryless manifold `Y`, modelled on `I.prod (𝓡∂ 1)`, is
a homology cobordism between two copies of `Y`, embedded as its bottom and top
(`TauCeti.isHomologyCobordism_cylinder`), for every coefficient ring.

## Main definitions

* `TauCeti.IsHomologyCobordism R I J n ι₀ ι₁`: `ι₀` and `ι₁` exhibit `W` as an `R`-homology
  cobordism between `Y₀` and `Y₁`.
* `TauCeti.IsHomologyCobordism.singularHomologyIso`: the isomorphism `Hₖ(Y₀; R) ≅ Hₖ(Y₁; R)` that a
  homology cobordism induces.

## Main results

* `TauCeti.IsHomologyCobordism.symm`: a homology cobordism read backwards.
* `TauCeti.isHomologyCobordism_cylinder`: a cylinder over a compact boundaryless manifold is a
  homology cobordism between its ends.

## Implementation notes

All three spaces live in one universe with the coefficient ring, because singular homology is
taken in `ModuleCat.{u} R` of topological spaces in `TopCat.{u}`.

## References

* A. S. Levine, *Nonsurjective satellite operators and piecewise-linear concordance*, Forum Math.
  Sigma 4 (2016), e34, Remark 1.5, for homology cobordisms between homology spheres and the
  homology concordance of knots in them.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Manifold Set Topology Fact.Manifold
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable (R : Type u) [Ring R]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) (n : ℕ∞ω)
  {Y₀ Y₁ W : Type u} [TopologicalSpace Y₀] [ChartedSpace H Y₀] [TopologicalSpace Y₁]
  [ChartedSpace H Y₁] [TopologicalSpace W] [ChartedSpace G W]

/-- The smooth embeddings `ι₀ : Y₀ → W` and `ι₁ : Y₁ → W` exhibit `W` as an **`R`-homology
cobordism** between `Y₀` and `Y₁`: `W` is compact, the two embeddings have disjoint images whose
union is the boundary of `W`, and each induces an isomorphism on singular homology with
coefficients in `R` in every degree. -/
structure IsHomologyCobordism (ι₀ : SmoothEmbedding I J n Y₀ W)
    (ι₁ : SmoothEmbedding I J n Y₁ W) : Prop where
  /-- A cobordism is compact. -/
  compactSpace : CompactSpace W
  /-- The two ends are disjoint. -/
  disjoint_range : Disjoint (range ι₀) (range ι₁)
  /-- The two ends make up the boundary. -/
  range_union_range : range ι₀ ∪ range ι₁ = J.boundary W
  /-- The first end induces isomorphisms on singular homology. -/
  isIso_left (k : ℕ) : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj
    (ModuleCat.of R R)).map (TopCat.ofHom ι₀.toContinuousMap))
  /-- The second end induces isomorphisms on singular homology. -/
  isIso_right (k : ℕ) : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj
    (ModuleCat.of R R)).map (TopCat.ofHom ι₁.toContinuousMap))

namespace IsHomologyCobordism

variable {R I J n} {ι₀ : SmoothEmbedding I J n Y₀ W} {ι₁ : SmoothEmbedding I J n Y₁ W}

/-- A homology cobordism from `Y₀` to `Y₁` is one from `Y₁` to `Y₀`. -/
theorem symm (h : IsHomologyCobordism R I J n ι₀ ι₁) : IsHomologyCobordism R I J n ι₁ ι₀ where
  compactSpace := h.compactSpace
  disjoint_range := h.disjoint_range.symm
  range_union_range := (union_comm _ _).trans h.range_union_range
  isIso_left := h.isIso_right
  isIso_right := h.isIso_left

/-- A homology cobordism between `Y₀` and `Y₁` identifies their singular homology: the
isomorphism `Hₖ(Y₀; R) ≅ Hₖ(W; R) ≅ Hₖ(Y₁; R)` through the two ends. -/
def singularHomologyIso (h : IsHomologyCobordism R I J n ι₀ ι₁) (k : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj (TopCat.of Y₀) ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
        (TopCat.of Y₁) :=
  haveI := h.isIso_left k
  haveI := h.isIso_right k
  asIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (TopCat.ofHom ι₀.toContinuousMap)) ≪≫
    (asIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (TopCat.ofHom ι₁.toContinuousMap))).symm

/-- The isomorphism of a homology cobordism is compatible with the two ends: following it by the
second end is the first end. -/
@[reassoc (attr := simp)]
theorem singularHomologyIso_hom_comp (h : IsHomologyCobordism R I J n ι₀ ι₁) (k : ℕ) :
    (h.singularHomologyIso k).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
          (TopCat.ofHom ι₁.toContinuousMap) =
      ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
        (TopCat.ofHom ι₀.toContinuousMap) := by
  simp [singularHomologyIso]

/-- Reading a homology cobordism backwards inverts its isomorphism. -/
@[simp]
theorem singularHomologyIso_symm (h : IsHomologyCobordism R I J n ι₀ ι₁) (k : ℕ) :
    h.symm.singularHomologyIso k = (h.singularHomologyIso k).symm := by
  ext1
  simp [singularHomologyIso]

end IsHomologyCobordism

/-! ### The cylinder -/

section Cylinder

variable {I n} {a b : ℝ} [Fact (a < b)]

/-- **The cylinder is a homology cobordism.** For a compact boundaryless manifold `Y`, the cylinder
`Y × [a, b]` is an `R`-homology cobordism between two copies of `Y`, embedded as its bottom and its
top. -/
theorem isHomologyCobordism_cylinder {Y : Type u} [TopologicalSpace Y] [ChartedSpace H Y]
    [IsManifold I n Y] [I.Boundaryless] [CompactSpace Y] :
    IsHomologyCobordism R I (I.prod (𝓡∂ 1)) n (SmoothEmbedding.cylinderBot I n a b Y)
      (SmoothEmbedding.cylinderTop I n a b Y) where
  compactSpace := inferInstance
  disjoint_range := by
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨y, rfl⟩, ⟨y', h⟩⟩
    have := congrArg (fun p : Y × Icc a b ↦ (p.2 : ℝ)) h
    simp only [SmoothEmbedding.cylinderBot_apply, SmoothEmbedding.cylinderTop_apply] at this
    exact (Fact.out : a < b).ne' (by simpa using this)
  range_union_range := by
    rw [boundary_product]
    ext ⟨y, t⟩
    simp [Set.prod, eq_comm]
  isIso_left k := by
    rw [SmoothEmbedding.toContinuousMap_cylinderBot,
      ← ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
    infer_instance
  isIso_right k := by
    rw [SmoothEmbedding.toContinuousMap_cylinderTop,
      ← ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
    infer_instance

end Cylinder

end TauCeti
